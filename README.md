# Signal*

The original `README` for Signal is `README.LIBSIGNAL.md`; this `README` describes the Signal* fork.

## Presentation

[Signal](https://signal.org/) is a secure messaging application that relies on a special cryptographic protocol for exchanging messages between participants. The Signal web application runs inside the browser using the [Web Crypto API](https://developer.mozilla.org/en-US/docs/Web/API/Web_Crypto_API) and [Emscripten](http://kripken.github.io/emscripten-site/)-generated Javascript code for encryption.


In order to make the Signal web application more secure, the [Prosecco](https://prosecco.gforge.inria.fr/) research team at [Inria](https://inria.fr), in collaboration with [Microsoft Research](https://www.microsoft.com/en-us/research) through [Project Everest](https://project-everest.github.io/), developed a reimplementation of the core protocol, called Signal*, using [WebAssembly](https://webassembly.org/). WebAssembly is a portable execution environment supported by all major browsers and Web application frameworks. It is designed to be an alternative to but interoperable with JavaScript. WebAssembly defines a compact, portable instruction set for a stack-based machine. These features make WebAssembly a better language in which to implement the cryptographic primitives that lack from the Web Crypto API, such as [elliptic curve cryptography](https://en.wikipedia.org/wiki/Curve25519).

The WebAssembly used in this demo is generated from [F\*](https://www.fstar-lang.org/) sources using the [KreMLin compiler](https://github.com/FStarLang/kremlin). The F\* implementation, contains the cryptographic top-level functions of the Signal protocol like `encrypt` or `respond`. F\* is a verification framework, that we use to prove three properties about this Signal protocol implementation:
* memory safety;
* secret independence (absence of some timing attacks);
* functional correctness, compared to a concise functional specification.

## IEEE2019 Paper

This details of the verification of the Signal protocol is described in [an article accepted at IEEE S&amp;P 2019](https://www.computer.org/csdl/proceedings-article/sp/2019/666000b002/19skg8v5fZS). The F\* code is then compiled into WebAssembly using a custom, small and auditable toolchain that allows for higher assurance about the generated code, at the expense of some performance losses compared to [Emscripten](https://emscripten.org/)-generated WebAssembly.

## Diff with `lisignal-protocol-javascript`

We forked [the official implementation of Signal in Javascript](https://github.com/signalapp/libsignal-protocol-javascript). The main modifications to the implementation concern the files `src/SessionBuilder.js` and `src/SessionCipher.js`. We carved out from those files a core module of cryptographic constructions, called `src/SessionCore.js` in our implementation.

`src/SessionCore.js` then calls the WebAssembly functions generated from F\*. These functions are accessible through a wrapper called `src/SignalCoreWasm.js`. `src/SignalCore.js` is a alternative Javascript implementation of what is inside the F\*-generated WebAssembly code.

We also modified `crypto.js` to divert calls to `Curve25519` and other cryptographic primitives to use our F\*-generated WebAssembly code.

## Running the test suite

We include in this repo a pre-generated snapshot of the WebAssembly files, in the folder `fstar/signal-wasm`. You can test it by firing up a web server from the repo's root directory and then accessing the `test/` directory.

## Switching Signal flavors

To switch between the all-Javascript implementation of Signal and the implementation
using WebAssembly compiled from F\*, use:

    make vanilla

and

    make fstar

In order to use `make fstar` above and re-generate the WebAssembly artifacts, you need to setup the F\* toolchain. See the `README.md` in the `fstar` folder.

## Demo

To update the `demo` website with the sources from the `src` and `fstar` directory,
use `make update-demo`.
