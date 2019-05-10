# Signal*

This folder contains the F\* implementation of the Signal protocol. It is meant to be used with F\* on branch `master`, and HACL* on branch `_dev`.

## Usage

To verify all the code, and produce `.hints` and `.checked` files:

    make verify

To extract to OCaml and test the Signal* spec:

    make test-spec.exe

To extract to C in the `signal-c` folder:

    make compile-c

To extract to WebAssembly in the `signal-wasm` folder:

    make compile-wasm

The files in `signal-wasm` are then directly used by the signal test suite, when the wasm mode is enabled (see `README.md` of the parent folder).

## Overview

The code is separated in two different sets of files: `Spec.Signal.*.fst` and `Impl.Signal.*.fst`. The specifications are written in pure F\* and are meant to be easily auditable. For each specification file, there is a corresponding implementation file that contains a Low* code equivalent to that specification.

Here is the breakdown of the files:
* `Spec/Impl.Signal.Crypto` offers wrappers around the various HACL* cryptographic primitives used in Signal.
* `Spec/Impl.Signal.Messages` describes how Signal messages are serialized before being sent on the network, using the `protobuf` protocol.
* `Spec/Impl.Signal.Core` describes the five core operations of the Signal protocol : `initiate`, `respond`, `fill_message_keys`, `encrypt` and `decrypt`.  
