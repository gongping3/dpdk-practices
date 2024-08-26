/**
 * usage: ./helloworld -l 0-1 -n 4
*/

#include <stdlib.h>

#include <rte_eal.h>
#include <rte_lcore.h>
#include <rte_common.h>
#include <rte_launch.h>
#include <rte_debug.h>

/* Launch a function on lcore */
static int
lcore_hello(__rte_unused void *arg)
{
    unsigned lcore_id;
    lcore_id = rte_lcore_id();
    printf("hello from core %u\n", lcore_id);
    return 0;
}

int
main(int argc, char** argv)
{
    int ret;
    unsigned lcore_id;

    ret = rte_eal_init(argc, argv);
    if (ret != 0) {
        rte_panic("Cannot init EAL\n");
    }
    
    RTE_LCORE_FOREACH_WORKER(lcore_id) {
        rte_eal_remote_launch(lcore_hello, NULL, lcore_id);
    }

    printf("main thread print\n");
    lcore_hello(NULL);

    rte_eal_mp_wait_lcore();

    rte_eal_cleanup();

    return 0;
}
