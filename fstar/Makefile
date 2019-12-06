FSTAR_HOME ?= ../../FStar

CACHE_DIR     ?= .cache
HINT_DIR      ?= .hints

#include ../Makefile.include

.PHONY: all verify clean

all:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) verify

FSTAR_INCLUDE_DIRS =


FSTAR_FLAGS = --cmi \
  --cache_checked_modules --cache_dir $(CACHE_DIR) \
  --already_cached "'Prims+FStar+LowStar+C+Spec.Loops+TestLib'" \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS) $(OTHERFLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ALL_SOURCES = $(wildcard *.fst) $(wildcard *.fsti)

TESTS= Test.Impl.Signal.fst Test.Impl.Signal.fsti Test.Spec.Signal.fst

ROOTS = $(filter-out $(TESTS),$(ALL_SOURCES))

.depend:
	$(info $(ROOTS))
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -LowStar -FStar' > $@

include .depend

$(HINT_DIR):
	mkdir -p $@

$(CACHE_DIR):
	mkdir -p $@

$(CACHE_DIR)/%.checked: | .depend $(HINT_DIR) $(CACHE_DIR)
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $*).hints && \
	touch -c $@

verify: $(addsuffix .checked, $(addprefix $(CACHE_DIR)/,$(ROOTS)))

test:
	$(MAKE) -f Makefile.test

# Targets for interactive mode

%.fst-in:
	@echo $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fst.hints

%.fsti-in:
	@echo $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fsti.hints

# Clean targets

SHELL=/bin/bash

clean:
	rm -rf *.checked *~ .cache/*
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe *-ml

distclean: clean
