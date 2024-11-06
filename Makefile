SUBDIRS := BusyCoq/. CoqBB5/.

all: $(SUBDIRS)
$(SUBDIRS):
		$(MAKE) -C $@

.PHONY: all $(SUBDIRS)