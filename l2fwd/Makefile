APP = l2fwd

SRCS := main.c

PKGCONF ?= pkg-config

# check dpdk exist
ifneq ($(shell $(PKGCONF) --exists libdpdk && echo 0), 0)
$(error "no installation of DPDK found")
endif

CFLAGS = $(shell $(PKGCONF) --cflags libdpdk)
LDFLAGS_SHARED = $(shell $(PKGCONF) --libs libdpdk)

all :
	$(CC) $(SRCS) $(LDFLAGS) -o $(APP) $(LDFLAGS_SHARED) $(CFLAGS) 

clean :
	rm -f $(APP)
