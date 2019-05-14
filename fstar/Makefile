OUTPUT_DIR    = .output
HINT_DIR      = .hints
GENERATED_DIR = signal-c
GENERATED_DIR_WASM = signal-wasm
OUT_DIR	      = signal-c
OUT_DIR_WASM = signal-wasm

.PHONY: all test stage1 stage2 clean clean-c distclean

all: compile-c compile-wasm

compile-c: $(GENERATED_DIR)/Makefile.include
	$(MAKE) -C $(GENERATED_DIR) -f Makefile.basic
compile-c: EXTRA+=-o libsignal.a

test-c: $(GENERATED_DIR)/Makefile.include
	$(MAKE) -C $(GENERATED_DIR) -f Makefile.basic Test_Impl_Signal.exe
	signal-c/Test_Impl_Signal.exe
test-c: EXTRA+=-o Test_Impl_Signal.exe -fbuiltin-uint128 -fnocompound-literals -fc89-scope \
	-fparentheses -fcurly-braces -funroll-loops 8 -warn-error +9 -add-include '"kremlib.h"' \
	-add-include '"TestLib.h"' -add-include '"C_String.h"'

test-wasm: $(GENERATED_DIR_WASM)/Makefile.include
	cd $(GENERATED_DIR_WASM) && node main.js


compile-wasm: $(GENERATED_DIR_WASM)/Makefile.include

FSTAR_INCLUDE_DIRS = \
  $(HACL_KREMLIN) \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/specs/lemmas \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/lib/c \
  $(HACL_HOME)/code/experimental/aes-256-cbc \
  $(HACL_HOME)/code/curve25519 \
  $(HACL_HOME)/code/curve25519/lemmas \
  $(HACL_HOME)/code/experimental/ed25519 \
  $(HACL_HOME)/code/hash \
  $(HACL_HOME)/code/hmac \
  $(HACL_HOME)/code/experimental/hkdf \
  $(KREMLIN_HOME)/runtime


FSTAR_FLAGS = $(OTHERFLAGS) --cmi \
  --cache_checked_modules  --odir $(OUTPUT_DIR) \
  --already_cached "*-Impl.Signal-Spec.Signal" \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ROOTS = Impl.Signal.Core.fst $(KREMLIN_HOME)/runtime/WasmSupport.fst \
	$(HACL_HOME)/code/experimental/ed25519/Hacl.Ed25519.fst \
	Test.Spec.Signal.fst Test.Impl.Signal.fst

.PRECIOUS: %.krml

ifndef MAKE_RESTARTS
.depend: .FORCE
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar -LowStar -Impl.Signal -Test.Impl -Hacl' > $@
.PHONY: .FORCE
.FORCE:
endif
include .depend

$(HINT_DIR):
	mkdir -p $@

%.checked: | .depend $(HINT_DIR)
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $*).hints && \
	touch -c $@

$(OUTPUT_DIR)/%.krml: | .depend
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

KREMLIN=$(KREMLIN_HOME)/krml

# 2. Generation of .c files

$(GENERATED_DIR_WASM)/Makefile.include: EXTRA+=-wasm -d backtraces -d wasm -d calls
$(GENERATED_DIR)/Makefile.include: EXTRA+=-fparentheses

# We use -drop (deprecated) only to avoid creating unnecessary .c,.h files
%/Makefile.include: $(ALL_KRML_FILES) | .depend
	$(KREMLIN) -skip-compilation \
	-no-prefix 'Impl.Signal.Core' \
	-no-prefix 'Impl.Signal.Crypto' \
	-no-prefix 'Impl.Signal.Messages' \
	-no-prefix 'Test.Impl.Signal' \
	-bundle WasmSupport \
	-bundle Prims -bundle LowStar.Endianness -bundle C.Endianness \
	-bundle C.String -bundle TestLib -bundle FStar.* \
	-bundle 'Lib.*,Spec.*,LowStar,Spec,Prims,Lib,C.Loops.*,Hacl.Spec.*[rename=Misc]' \
	-bundle 'Hacl.Hash.SHA2=Hacl.Hash.*,Hacl.HMAC,Hacl.Impl.HKDF_SHA2_256,Hacl.HKDF_SHA2_256' \
	-bundle 'Hacl.Impl.AES_256_CBC=Hacl.Impl.AES_256.*,Hacl.Impl.AES_256' \
	-bundle 'Hacl.Ed25519=Hacl.Impl.Ed25519.*,Hacl.Bignum25519,Hacl.Impl.BignumQ,Hacl.Impl.BignumQ.*,Hacl.SHA512,Hacl.Impl.Store56,Hacl.Impl.Load56,Hacl.Impl.SHA512.*' \
	-bundle 'Hacl.Curve25519_51=Hacl.Impl.Curve25519.*' \
	-bundle 'Impl.Signal.Core=Impl.Signal.Messages' \
	-bundle 'Test.Impl.Signal=Test.Spec.Signal' \
	-tmpdir $* \
	$(EXTRA) \
	$^

# 5. Targets for interactive mode

%.fst-in:
	@echo $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fst.hints

%.fsti-in:
	@echo $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fsti.hints

# 6. Clean targets

SHELL=/bin/bash

clean:
	rm -rf $(GENERATED_DIR) $(OUT_DIR)/*.exe $(OUT_DIR)/*.a
	rm -rf include/*.o include/*.d

clean-c:
	rm -rf $(GENERATED_DIR)/{*.{c,h},Makefile.include}

distclean: clean
	rm -rf $(OUT_DIR) $(OUTPUT_DIR) *.checked


# 7. Extracting to OCaml

TAC = $(shell which tac >/dev/null 2>&1 && echo "tac" || echo "tail -r")
ALL_CMX_FILES = $(patsubst %.ml,%.cmx,$(shell echo $(ALL_ML_FILES) | $(TAC)))

OCAMLOPT = ocamlfind opt -package fstarlib -linkpkg -g -I $(OUTPUT_DIR) -w -8-20-26
ifeq ($(OS),Windows_NT)
  export OCAMLPATH := $(FSTAR_HOME)/bin;$(OCAMLPATH)
else
  export OCAMLPATH := $(FSTAR_HOME)/bin:$(OCAMLPATH)
endif

.PRECIOUS: $(OUTPUT_DIR)/%.cmx
%.cmx: %.ml
	$(OCAMLOPT) -c $< -o $@

$(OUTPUT_DIR)/%.ml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	    --extract_module $(subst .fst.checked,,$(notdir $<))


test-spec.exe: $(ALL_CMX_FILES) main.cmx
	$(OCAMLOPT) $^ -o $@
