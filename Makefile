KERNELDIR ?= /lib/modules/`uname -r`/build

obj-m = ip_gre.o

all clean modules modules_install:
	$(MAKE) -C $(KERNELDIR) M=$(PWD) $@

install: modules_install
