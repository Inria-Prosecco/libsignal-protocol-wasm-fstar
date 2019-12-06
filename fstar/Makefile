SIGNAL_HOME ?= $(realpath .)

KREMLIN_HOME ?= /opt/kremlin
HACL_HOME ?= /opt/hacl-star


all: test

test: obj/test.exe
	$<

# Configuration
# -------------
include $(HACL_HOME)/Makefile.include

FSTAR_INCLUDE_PATH= \
	$(KREMLIN_HOME)/kremlib \
	$(addprefix $(HACL_HOME)/,obj lib specs specs/lemmas specs/alternative specs/experimental code/hash code/hmac code/hkdf code/meta code/curve25519 code/ed25519 code/experimental/aes code/experimental/aes-256-cbc providers/evercrypt providers/evercrypt/fst vale/specs/hardware vale/specs/defs)

# In interactive mode, chill out and don't roll over if
# something isn't cached somewhere.
FSTAR_NO_FLAGS= \
	$(addprefix --include ,$(FSTAR_INCLUDE_PATH)) \
	--cache_checked_modules \
	--cache_dir $(SIGNAL_HOME)/obj \
	--odir $(SIGNAL_HOME)/obj \
	--cmi \
	--query_stats \
	--use_hints \
	--record_hints \
	$(OTHERFLAGS)

FSTAR_FLAGS=$(FSTAR_NO_FLAGS) \
	--warn_error @241 \

FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

%.fst-in %.fsti-in:
	@echo $(FSTAR_NO_FLAGS)

# Project
# -------

PROJECT_ROOTS=Test.Impl.Signal.fst

# This is the right way to ensure the .depend file always gets re-built.
ifndef NODEPEND
ifndef MAKE_RESTARTS
.depend: .FORCE
	$(FSTAR) $(FSTAR_NO_FLAGS) --dep full $(notdir $(PROJECT_ROOTS)) \
	    --extract '-* +Impl.Signal.Crypto +Impl.Signal.Messages +Impl.Signal.Core +Test.Impl.Signal' \
	    > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

clean-dist:
	rm -rf dist

clean: clean-dist
	rm -rf obj .depend

.PHONY: clean clean-dist

# Verification
# ------------

%.checked:
	$(FSTAR) --hint_file hints/$(notdir $*).hints $(notdir $<) && touch -c $@

# OCaml
# -------

TAC = $(shell which tac >/dev/null 2>&1 && echo "tac" || echo "tail -r")
PROJECT_ML_FILES = $(shell echo $(ALL_ML_FILES) | $(TAC))
PROJECT_CMX_FILES = $(patsubst %.ml,%.cmx,$(PROJECT_ML_FILES))

ifeq ($(OS),Windows_NT)
  export OCAMLPATH := $(FSTAR_HOME)/bin;$(OCAMLPATH)
else
  export OCAMLPATH := $(FSTAR_HOME)/bin:$(OCAMLPATH)
endif

# Warning 8: this pattern-matching is not exhaustive.
# Warning 20: this argument will not be used by the function.
# Warning 26: unused variable
OCAMLOPT = ocamlfind opt -package fstarlib -linkpkg -g -I $(SIGNAL_HOME)/obj -I $(HACL_HOME)/obj -w -8-20-26
OCAMLSHARED = ocamlfind opt -shared -package fstar-tactics-lib -g -I $(SIGNAL_HOME)/obj -I $(HACL_HOME)/obj -w -8-20-26

%.ml:
	$(FSTAR) --codegen OCaml \
	    --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	    $(notdir $(subst .checked,,$<))

%.cmx: %.ml
	$(OCAMLOPT) -c $< -o $@


extract: $(PROJECT_ML_FILES)

# HACL
# ----

$(HACL_HOME)/obj/hacl.cmxa:
	$(MAKE) -f $(HACL_HOME)/specs/Makefile.OCaml

# Tests
# -----

obj/test.exe: $(FSTAR_HOME)/bin/fstarlib/fstarlib.cmxa $(HACL_HOME)/obj/hacl.cmxa $(PROJECT_CMX_FILES)
	$(OCAMLOPT) -package cryptokit $^ -o $@
