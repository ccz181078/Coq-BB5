SUBDIRS := BusyCoq CoqBB5

all: $(SUBDIRS)

BusyCoq:
	$(MAKE) -C $@

CoqBB5: BusyCoq
	$(MAKE) -C $@

.PHONY: all $(SUBDIRS)