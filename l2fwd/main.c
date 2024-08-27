/*
1. 在虚拟机内，实现基于二层协议的转发。
2. 两个端口（网卡）互相转发。比如有4个端口0、1、2、3，则 0 - 1 互相转发， 2 - 3 互相转发。
3. 基于轮询或者事件驱动模式
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <sys/types.h>
#include <sys/queue.h>
#include <setjmp.h>
#include <stdarg.h>
#include <ctype.h>
#include <errno.h>
#include <getopt.h>
#include <signal.h>
#include <stdbool.h>

#include <rte_common.h>
#include <rte_log.h>
#include <rte_malloc.h>
#include <rte_memory.h>
#include <rte_memcpy.h>
#include <rte_eal.h>
#include <rte_launch.h>
#include <rte_cycles.h>
#include <rte_prefetch.h>
#include <rte_lcore.h>
#include <rte_per_lcore.h>
#include <rte_branch_prediction.h>
#include <rte_interrupts.h>
#include <rte_random.h>
#include <rte_debug.h>
#include <rte_ether.h>
#include <rte_ethdev.h>
#include <rte_mempool.h>
#include <rte_mbuf.h>
#include <rte_string_fns.h>

static volatile bool force_quit;

/* MAC updating enabled by default */
static int mac_updating = 1;

/* Ports set in promiscuous mode off by default. */
static int promiscuous_on;

#define RTE_LOGTYPE_L2FWD RTE_LOGTYPE_USER1

#define MAX_PKT_BURST 32
#define BURST_TX_DRAIN_US 100 /* TX drain every ~100us */
#define MEMPOOL_CACHE_SIZE 256

/*
 * Configurable number of RX/TX ring descriptors
 */
#define RX_DESC_DEFAULT 1024
#define TX_DESC_DEFAULT 1024
static uint16_t nb_rxd = RX_DESC_DEFAULT;
static uint16_t nb_txd = TX_DESC_DEFAULT;

/* ethernet addresses of ports */
static struct rte_ether_addr l2fwd_ports_eth_addr[RTE_MAX_ETHPORTS];

/* mask of enabled ports */
static uint32_t l2fwd_enabled_port_mask = 0;

/* list of enabled ports */
static uint32_t l2fwd_dst_ports[RTE_MAX_ETHPORTS];

struct port_pair_params {
#define NUM_PORTS	2
	uint16_t port[NUM_PORTS];
} __rte_cache_aligned;

static struct port_pair_params port_pair_params_array[RTE_MAX_ETHPORTS / 2];
static struct port_pair_params *port_pair_params;
static uint16_t nb_port_pair_params;

static unsigned int l2fwd_rx_queue_per_lcore = 1;

#define MAX_RX_QUEUE_PER_LCORE 16
#define MAX_TX_QUEUE_PER_PORT 16
/* List of queues to be polled for a given lcore. 8< */
struct lcore_queue_conf {
	unsigned n_rx_port;
	unsigned rx_port_list[MAX_RX_QUEUE_PER_LCORE];
} __rte_cache_aligned;
struct lcore_queue_conf lcore_queue_conf[RTE_MAX_LCORE];
/* >8 End of list of queues to be polled for a given lcore. */

static struct rte_eth_dev_tx_buffer *tx_buffer[RTE_MAX_ETHPORTS];

static struct rte_eth_conf port_conf = {
	.txmode = {
		.mq_mode = RTE_ETH_MQ_TX_NONE,
	},
};

struct rte_mempool * l2fwd_pktmbuf_pool = NULL;

/* Per-port statistics struct */
struct l2fwd_port_statistics {
	uint64_t tx;
	uint64_t rx;
	uint64_t dropped;
} __rte_cache_aligned;
struct l2fwd_port_statistics port_statistics[RTE_MAX_ETHPORTS];

#define MAX_TIMER_PERIOD 86400 /* 1 day max */
/* A tsc-based timer responsible for triggering statistics printout */
static uint64_t timer_period = 10; /* default period is 10 seconds */

#define NUM_MBUFS 8192
#define MBUF_CACHE_SIZE 250
#define MBUF_PRIV_SIZE 0
#define MBUF_DATA_SIZE RTE_MBUF_DEFAULT_BUF_SIZE

uint32_t l2fwd_dst_ports[RTE_MAX_ETHPORTS];
uint32_t nb_port_pair_params;

enum {
	/* long options mapped to a short option */

	/* first long only option value must be >= 256, so that we won't
	 * conflict with short options */
	CMD_LINE_OPT_NO_MAC_UPDATING_NUM = 256,
	CMD_LINE_OPT_PORTMAP_NUM,
};

static const char short_options[] =
	"p:"  /* portmask */
	"P"   /* promiscuous */
	"q:"  /* number of queues */
	"T:"  /* timer period */
	;

static const struct option lgopts[] = {
	{ CMD_LINE_OPT_NO_MAC_UPDATING, no_argument, 0,
		CMD_LINE_OPT_NO_MAC_UPDATING_NUM},
	{ CMD_LINE_OPT_PORTMAP_CONFIG, 1, 0, CMD_LINE_OPT_PORTMAP_NUM},
	{NULL, 0, 0, 0}
};

/* Parse the argument given in the command line of the application */
static int
l2fwd_parse_args(int argc, char **argv)
{
	int opt, ret, timer_secs;
	char **argvopt;
	int option_index;
	char *prgname = argv[0];

	argvopt = argv;
	port_pair_params = NULL;

	while ((opt = getopt_long(argc, argvopt, short_options,
				  lgopts, &option_index)) != EOF) {

		switch (opt) {
		/* portmask */
		case 'p':
			l2fwd_enabled_port_mask = l2fwd_parse_portmask(optarg);
			if (l2fwd_enabled_port_mask == 0) {
				printf("invalid portmask\n");
				l2fwd_usage(prgname);
				return -1;
			}
			break;
		case 'P':
			promiscuous_on = 1;
			break;

		/* nqueue */
		case 'q':
			l2fwd_rx_queue_per_lcore = l2fwd_parse_nqueue(optarg);
			if (l2fwd_rx_queue_per_lcore == 0) {
				printf("invalid queue number\n");
				l2fwd_usage(prgname);
				return -1;
			}
			break;

		/* timer period */
		case 'T':
			timer_secs = l2fwd_parse_timer_period(optarg);
			if (timer_secs < 0) {
				printf("invalid timer period\n");
				l2fwd_usage(prgname);
				return -1;
			}
			timer_period = timer_secs;
			break;

		/* long options */
		case CMD_LINE_OPT_PORTMAP_NUM:
			ret = l2fwd_parse_port_pair_config(optarg);
			if (ret) {
				fprintf(stderr, "Invalid config\n");
				l2fwd_usage(prgname);
				return -1;
			}
			break;

		case CMD_LINE_OPT_NO_MAC_UPDATING_NUM:
			mac_updating = 0;
			break;

		default:
			l2fwd_usage(prgname);
			return -1;
		}
	}

	if (optind >= 0)
		argv[optind-1] = prgname;

	ret = optind-1;
	optind = 1; /* reset getopt lib */
	return ret;
}

void l2fwd_launch_one_lcore(__rte_unused void *dummy)
{
	l2fwd_main_loop();
	return 0;
}

int main(int argc, char** argv)
{
    int ret;
    struct rte_mempool* l2fwd_pktmbuf_pool;
    int portid;
    int last_port;
    uint32_t l2fwd_enabled_port_mask;
    unsigned nb_ports_in_mask = 0;
    int nb_port_available = 0;
    uint16_t nb_ports_available = 0;
    int lcore_id;

    /* init EAL */
    ret = rte_eal_init(argc, argv);
    if (ret < 0) {
        rte_panic("Cannot init EAL\n");
    }
    argc -= ret;
    argv += ret;

    /* parse application arguments (after the EAL ones) */
    ret = l2fwd_parse_args(argc, argv);
    if (ret < 0)
        rte_exit(EXIT_FAILURE, "Invalid L2FWD arguments\n");

    /* init driver */
    /* reset l2fwd_dst_ports */
    for (portid = 0; portid < RTE_MAX_ETHPORTS; portid++)
        l2fwd_dst_ports[portid] = 0;
    last_port = 0;

    /* populate destination port details */
    if (port_pair_params != NULL) {
        /* 如果传入参数已经定义好了转发对，直接使用 */
        uint16_t idx, p;

        for (idx = 0; idx < (nb_port_pair_params << 1); idx++) {
            p = idx & 1;
            portid = port_pair_params[idx >> 1].port[p];
            l2fwd_dst_ports[portid] =
                port_pair_params[idx >> 1].port[p ^ 1];
        }
    } else {
        /* 把端口两两组成转发对 */
        RTE_ETH_FOREACH_DEV(portid) {
            /* skip ports that are not enabled */
            if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
                continue;

            if (nb_ports_in_mask % 2) {
                l2fwd_dst_ports[portid] = last_port;
                l2fwd_dst_ports[last_port] = portid;
            } else {
                last_port = portid;
            }

            nb_ports_in_mask++;
        }
        if (nb_ports_in_mask % 2) {
            printf("Notice: odd number of ports in portmask.\n");
            l2fwd_dst_ports[last_port] = last_port;
        }
    }

    /* Create the mbuf pool */
    l2fwd_pktmbuf_pool = rte_pktmbuf_pool_create("l2fwd_mbuf_pool", NUM_MBUFS, MBUF_CACHE_SIZE, MBUF_PRIV_SIZE, MBUF_DATA_SIZE, rte_socket_id());
    if (l2fwd_pktmbuf_pool == NULL) {
        rte_exit(EXIT_FAILURE, "Cannot create mbuf pool\n");
    }
    /* >8 End of create the mbuf pool */
   
    RTE_ETH_FOREACH_DEV(portid) {
        struct rte_eth_rxconf rxq_conf;
        struct rte_eth_txconf txq_conf;
        struct rte_eth_conf local_port_conf = port_conf;
        struct rte_eth_dev_info dev_info;

        /* skip port that are not enabled */
        if ((l2fwd_enabled_port_mask & (1 << portid)) == 0) {
            printf("Skipping disabled port %u\n", portid);
            continue;
        }
        nb_port_available++;

        /* init port */
        printf("Initializing port %u...", portid);
        fflush(stdout);

        ret = rte_eth_dev_info_get(portid, &dev_info);
        if (ret != 0) {
            rte_exit(EXIT_FAILURE,
                "Error during getting device (port %u) info: %s\n",
                portid, strerror(-ret));
        }

        /* Configure the number of queues for a port. */
        ret = rte_eth_dev_configure(portid, 1, 1, &local_port_conf);
        if (ret < 0) {
            rte_exit(EXIT_FAILURE, "Cannot configure device: err=%d, port=%u\n",
                ret, portid);
        }

        ret = rte_eth_dev_adjust_nb_rx_tx_desc(portid, &nb_rxd, &nb_txd);
        if (ret != 0)
            rte_exit(EXIT_FAILURE, "Cannot adjust number of descriptors: err=%d, port=%u\n",
                ret, portid);
        
        /* Mac address get */

        /* init one RX queue */
        fflush(stdout);
        rxq_conf = dev_info.default_rxconf;
        rxq_conf.offloads = local_port_conf.rxmode.offloads;
        /* RX queue setup. 8< */
        ret = rte_eth_rx_queue_setup(portid, 0, nb_rxd,
                        rte_eth_dev_socket_id(portid),
                        &rxq_conf,
                        l2fwd_pktmbuf_pool);
        if (ret != 0)
            rte_exit(EXIT_FAILURE, "rte_eth_rx_queue_setup:err=%d, port=%u\n",
                ret, portid);
        /* >8 End of RX queue setup. */
        
        txq_conf = dev_info.default_txconf;
        txq_conf.offloads = local_port_conf.txmode.offloads;
        /* TX queue setup. 8< */
        ret = rte_eth_tx_queue_setup(portid, 0, nb_txd,
                        rte_eth_dev_socket_id(portid),
                        &txq_conf);
        if (ret != 0)
            rte_exit(EXIT_FAILURE, "rte_eth_tx_queue_setup:err=%d, port=%u\n",
                ret, portid);   
        /* >8 End of init one TX queue on each port. */

        /* Initialize TX buffers */

        /* Start device */
        ret = rte_eth_dev_start(portid);
        if (ret != 0)
            rte_exit(EXIT_FAILURE, "rte_eth_dev_start:err=%d, port=%u\n",
                ret, portid);
        
        printf("done: \n");

        printf("Port %u, MAC address: " RTE_ETHER_ADDR_PRT_FMT "\n\n",
                    portid,
                    RTE_ETHER_ADDR_BYTES(&l2fwd_ports_eth_addr[portid]));
    }

	if (!nb_ports_available) {
		rte_exit(EXIT_FAILURE,
			"All available ports are disabled. Please set portmask.\n");
	}

	ret = 0;
	/* launch per-lcore init on every lcore */
	rte_eal_mp_remote_launch(l2fwd_launch_one_lcore, NULL, CALL_MAIN);
	RTE_LCORE_FOREACH_WORKER(lcore_id) {
		if (rte_eal_wait_lcore(lcore_id) < 0) {
			ret = -1;
			break;
		}
	}

	RTE_ETH_FOREACH_DEV(portid) {
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
			continue;
		printf("Closing port %d...", portid);
		ret = rte_eth_dev_stop(portid);
		if (ret != 0)
			printf("rte_eth_dev_stop: err=%d, port=%d\n",
			       ret, portid);
		rte_eth_dev_close(portid);
		printf(" Done\n");
	}

	/* clean up the EAL */
	rte_eal_cleanup();
	printf("Bye...\n");

	return ret;
}