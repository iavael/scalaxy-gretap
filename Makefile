KERNELDIR ?= /lib/modules/`uname -r`/build

obj-m = ip_gre.o

all: modules

install: modules_install

clean modules modules_install:
	$(MAKE) -C $(KERNELDIR) M=$(PWD) $@
