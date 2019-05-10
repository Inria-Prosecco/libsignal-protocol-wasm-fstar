;(function(){
var Internal = {};
var libsignal = {};
// The Module object: Our interface to the outside world. We import
// and export values on it. There are various ways Module can be used:
// 1. Not defined. We create it here
// 2. A function parameter, function(Module) { ..generated code.. }
// 3. pre-run appended it, var Module = {}; ..generated code..
// 4. External script tag defines var Module.
// We need to check if Module already exists (e.g. case 3 above).
// Substitution will be replaced with actual code on later stage of the build,
// this way Closure Compiler will not mangle it (e.g. case 4. above).
// Note that if you want to run closure, and also to use Module
// after the generated code, you will need to define   var Module = {};
// before the code. Then that object will be used in the code, and you
// can continue to use Module afterwards as well.
var Module = typeof Module !== 'undefined' ? Module : {};

// --pre-jses are emitted after the Module integration code, so that they can
// refer to Module (if they choose; they can also define Module)
// {{PRE_JSES}}

// Sometimes an existing Module object exists with properties
// meant to overwrite the default module functionality. Here
// we collect those properties and reapply _after_ we configure
// the current environment's defaults to avoid having to be so
// defensive during initialization.
var moduleOverrides = {};
var key;
for (key in Module) {
  if (Module.hasOwnProperty(key)) {
    moduleOverrides[key] = Module[key];
  }
}

Module['arguments'] = [];
Module['thisProgram'] = './this.program';
Module['quit'] = function(status, toThrow) {
  throw toThrow;
};
Module['preRun'] = [];
Module['postRun'] = [];

// The environment setup code below is customized to use Module.
// *** Environment setup code ***
var ENVIRONMENT_IS_WEB = false;
var ENVIRONMENT_IS_WORKER = false;
var ENVIRONMENT_IS_NODE = false;
var ENVIRONMENT_IS_SHELL = false;

// Three configurations we can be running in:
// 1) We could be the application main() thread running in the main JS UI thread. (ENVIRONMENT_IS_WORKER == false and ENVIRONMENT_IS_PTHREAD == false)
// 2) We could be the application main() thread proxied to worker. (with Emscripten -s PROXY_TO_WORKER=1) (ENVIRONMENT_IS_WORKER == true, ENVIRONMENT_IS_PTHREAD == false)
// 3) We could be an application pthread running in a worker. (ENVIRONMENT_IS_WORKER == true and ENVIRONMENT_IS_PTHREAD == true)

if (Module['ENVIRONMENT']) {
  if (Module['ENVIRONMENT'] === 'WEB') {
    ENVIRONMENT_IS_WEB = true;
  } else if (Module['ENVIRONMENT'] === 'WORKER') {
    ENVIRONMENT_IS_WORKER = true;
  } else if (Module['ENVIRONMENT'] === 'NODE') {
    ENVIRONMENT_IS_NODE = true;
  } else if (Module['ENVIRONMENT'] === 'SHELL') {
    ENVIRONMENT_IS_SHELL = true;
  } else {
    throw new Error('Module[\'ENVIRONMENT\'] value is not valid. must be one of: WEB|WORKER|NODE|SHELL.');
  }
} else {
  ENVIRONMENT_IS_WEB = typeof window === 'object';
  ENVIRONMENT_IS_WORKER = typeof importScripts === 'function';
  ENVIRONMENT_IS_NODE = typeof process === 'object' && typeof require === 'function' && !ENVIRONMENT_IS_WEB && !ENVIRONMENT_IS_WORKER;
  ENVIRONMENT_IS_SHELL = !ENVIRONMENT_IS_WEB && !ENVIRONMENT_IS_NODE && !ENVIRONMENT_IS_WORKER;
}


if (ENVIRONMENT_IS_NODE) {
  // Expose functionality in the same simple way that the shells work
  // Note that we pollute the global namespace here, otherwise we break in node
  var nodeFS;
  var nodePath;

  Module['read'] = function shell_read(filename, binary) {
    var ret;
    ret = tryParseAsDataURI(filename);
    if (!ret) {
      if (!nodeFS) nodeFS = require('fs');
      if (!nodePath) nodePath = require('path');
      filename = nodePath['normalize'](filename);
      ret = nodeFS['readFileSync'](filename);
    }
    return binary ? ret : ret.toString();
  };

  Module['readBinary'] = function readBinary(filename) {
    var ret = Module['read'](filename, true);
    if (!ret.buffer) {
      ret = new Uint8Array(ret);
    }
    assert(ret.buffer);
    return ret;
  };

  if (process['argv'].length > 1) {
    Module['thisProgram'] = process['argv'][1].replace(/\\/g, '/');
  }

  Module['arguments'] = process['argv'].slice(2);

  if (typeof module !== 'undefined') {
    module['exports'] = Module;
  }

  process['on']('uncaughtException', function(ex) {
    // suppress ExitStatus exceptions from showing an error
    if (!(ex instanceof ExitStatus)) {
      throw ex;
    }
  });
  // Currently node will swallow unhandled rejections, but this behavior is
  // deprecated, and in the future it will exit with error status.
  process['on']('unhandledRejection', function(reason, p) {
    process['exit'](1);
  });

  Module['inspect'] = function () { return '[Emscripten Module object]'; };
}
else if (ENVIRONMENT_IS_SHELL) {
  if (typeof read != 'undefined') {
    Module['read'] = function shell_read(f) {
      var data = tryParseAsDataURI(f);
      if (data) {
        return intArrayToString(data);
      }
      return read(f);
    };
  }

  Module['readBinary'] = function readBinary(f) {
    var data;
    data = tryParseAsDataURI(f);
    if (data) {
      return data;
    }
    if (typeof readbuffer === 'function') {
      return new Uint8Array(readbuffer(f));
    }
    data = read(f, 'binary');
    assert(typeof data === 'object');
    return data;
  };

  if (typeof scriptArgs != 'undefined') {
    Module['arguments'] = scriptArgs;
  } else if (typeof arguments != 'undefined') {
    Module['arguments'] = arguments;
  }

  if (typeof quit === 'function') {
    Module['quit'] = function(status, toThrow) {
      quit(status);
    }
  }
}
else if (ENVIRONMENT_IS_WEB || ENVIRONMENT_IS_WORKER) {
  Module['read'] = function shell_read(url) {
    try {
      var xhr = new XMLHttpRequest();
      xhr.open('GET', url, false);
      xhr.send(null);
      return xhr.responseText;
    } catch (err) {
      var data = tryParseAsDataURI(url);
      if (data) {
        return intArrayToString(data);
      }
      throw err;
    }
  };

  if (ENVIRONMENT_IS_WORKER) {
    Module['readBinary'] = function readBinary(url) {
      try {
        var xhr = new XMLHttpRequest();
        xhr.open('GET', url, false);
        xhr.responseType = 'arraybuffer';
        xhr.send(null);
        return new Uint8Array(xhr.response);
      } catch (err) {
        var data = tryParseAsDataURI(url);
        if (data) {
          return data;
        }
        throw err;
      }
    };
  }

  Module['readAsync'] = function readAsync(url, onload, onerror) {
    var xhr = new XMLHttpRequest();
    xhr.open('GET', url, true);
    xhr.responseType = 'arraybuffer';
    xhr.onload = function xhr_onload() {
      if (xhr.status == 200 || (xhr.status == 0 && xhr.response)) { // file URLs can return 0
        onload(xhr.response);
        return;
      }
      var data = tryParseAsDataURI(url);
      if (data) {
        onload(data.buffer);
        return;
      }
      onerror();
    };
    xhr.onerror = onerror;
    xhr.send(null);
  };

  if (typeof arguments != 'undefined') {
    Module['arguments'] = arguments;
  }

  Module['setWindowTitle'] = function(title) { document.title = title };
}

// console.log is checked first, as 'print' on the web will open a print dialogue
// printErr is preferable to console.warn (works better in shells)
// bind(console) is necessary to fix IE/Edge closed dev tools panel behavior.
Module['print'] = typeof console !== 'undefined' ? console.log.bind(console) : (typeof print !== 'undefined' ? print : null);
Module['printErr'] = typeof printErr !== 'undefined' ? printErr : ((typeof console !== 'undefined' && console.warn.bind(console)) || Module['print']);

// *** Environment setup code ***

// Closure helpers
Module.print = Module['print'];
Module.printErr = Module['printErr'];

// Merge back in the overrides
for (key in moduleOverrides) {
  if (moduleOverrides.hasOwnProperty(key)) {
    Module[key] = moduleOverrides[key];
  }
}
// Free the object hierarchy contained in the overrides, this lets the GC
// reclaim data used e.g. in memoryInitializerRequest, which is a large typed array.
moduleOverrides = undefined;



// {{PREAMBLE_ADDITIONS}}

var STACK_ALIGN = 16;


function staticAlloc(size) {
  assert(!staticSealed);
  var ret = STATICTOP;
  STATICTOP = (STATICTOP + size + 15) & -16;
  return ret;
}

function dynamicAlloc(size) {
  assert(DYNAMICTOP_PTR);
  var ret = HEAP32[DYNAMICTOP_PTR>>2];
  var end = (ret + size + 15) & -16;
  HEAP32[DYNAMICTOP_PTR>>2] = end;
  if (end >= TOTAL_MEMORY) {
    var success = enlargeMemory();
    if (!success) {
      HEAP32[DYNAMICTOP_PTR>>2] = ret;
      return 0;
    }
  }
  return ret;
}

function alignMemory(size, factor) {
  if (!factor) factor = STACK_ALIGN; // stack alignment (16-byte) by default
  var ret = size = Math.ceil(size / factor) * factor;
  return ret;
}

function getNativeTypeSize(type) {
  switch (type) {
    case 'i1': case 'i8': return 1;
    case 'i16': return 2;
    case 'i32': return 4;
    case 'i64': return 8;
    case 'float': return 4;
    case 'double': return 8;
    default: {
      if (type[type.length-1] === '*') {
        return 4; // A pointer
      } else if (type[0] === 'i') {
        var bits = parseInt(type.substr(1));
        assert(bits % 8 === 0);
        return bits / 8;
      } else {
        return 0;
      }
    }
  }
}

function warnOnce(text) {
  if (!warnOnce.shown) warnOnce.shown = {};
  if (!warnOnce.shown[text]) {
    warnOnce.shown[text] = 1;
    Module.printErr(text);
  }
}



var jsCallStartIndex = 1;
var functionPointers = new Array(0);

// 'sig' parameter is only used on LLVM wasm backend
function addFunction(func, sig) {
  var base = 0;
  for (var i = base; i < base + 0; i++) {
    if (!functionPointers[i]) {
      functionPointers[i] = func;
      return jsCallStartIndex + i;
    }
  }
  throw 'Finished up all reserved function pointers. Use a higher value for RESERVED_FUNCTION_POINTERS.';
}

function removeFunction(index) {
  functionPointers[index-jsCallStartIndex] = null;
}

var funcWrappers = {};

function getFuncWrapper(func, sig) {
  if (!func) return; // on null pointer, return undefined
  assert(sig);
  if (!funcWrappers[sig]) {
    funcWrappers[sig] = {};
  }
  var sigCache = funcWrappers[sig];
  if (!sigCache[func]) {
    // optimize away arguments usage in common cases
    if (sig.length === 1) {
      sigCache[func] = function dynCall_wrapper() {
        return dynCall(sig, func);
      };
    } else if (sig.length === 2) {
      sigCache[func] = function dynCall_wrapper(arg) {
        return dynCall(sig, func, [arg]);
      };
    } else {
      // general case
      sigCache[func] = function dynCall_wrapper() {
        return dynCall(sig, func, Array.prototype.slice.call(arguments));
      };
    }
  }
  return sigCache[func];
}


function makeBigInt(low, high, unsigned) {
  return unsigned ? ((+((low>>>0)))+((+((high>>>0)))*4294967296.0)) : ((+((low>>>0)))+((+((high|0)))*4294967296.0));
}

function dynCall(sig, ptr, args) {
  if (args && args.length) {
    return Module['dynCall_' + sig].apply(null, [ptr].concat(args));
  } else {
    return Module['dynCall_' + sig].call(null, ptr);
  }
}



var Runtime = {
  // FIXME backwards compatibility layer for ports. Support some Runtime.*
  //       for now, fix it there, then remove it from here. That way we
  //       can minimize any period of breakage.
  dynCall: dynCall, // for SDL2 port
};

// The address globals begin at. Very low in memory, for code size and optimization opportunities.
// Above 0 is static memory, starting with globals.
// Then the stack.
// Then 'dynamic' memory for sbrk.
var GLOBAL_BASE = 8;



// === Preamble library stuff ===

// Documentation for the public APIs defined in this file must be updated in:
//    site/source/docs/api_reference/preamble.js.rst
// A prebuilt local version of the documentation is available at:
//    site/build/text/docs/api_reference/preamble.js.txt
// You can also build docs locally as HTML or other formats in site/
// An online HTML version (which may be of a different version of Emscripten)
//    is up at http://kripken.github.io/emscripten-site/docs/api_reference/preamble.js.html



//========================================
// Runtime essentials
//========================================

var ABORT = 0; // whether we are quitting the application. no code should run after this. set in exit() and abort()
var EXITSTATUS = 0;

/** @type {function(*, string=)} */
function assert(condition, text) {
  if (!condition) {
    abort('Assertion failed: ' + text);
  }
}

var globalScope = this;

// Returns the C function with a specified identifier (for C++, you need to do manual name mangling)
function getCFunc(ident) {
  var func = Module['_' + ident]; // closure exported function
  assert(func, 'Cannot call unknown function ' + ident + ', make sure it is exported');
  return func;
}

var JSfuncs = {
  // Helpers for cwrap -- it can't refer to Runtime directly because it might
  // be renamed by closure, instead it calls JSfuncs['stackSave'].body to find
  // out what the minified function name is.
  'stackSave': function() {
    stackSave()
  },
  'stackRestore': function() {
    stackRestore()
  },
  // type conversion from js to c
  'arrayToC' : function(arr) {
    var ret = stackAlloc(arr.length);
    writeArrayToMemory(arr, ret);
    return ret;
  },
  'stringToC' : function(str) {
    var ret = 0;
    if (str !== null && str !== undefined && str !== 0) { // null string
      // at most 4 bytes per UTF-8 code point, +1 for the trailing '\0'
      var len = (str.length << 2) + 1;
      ret = stackAlloc(len);
      stringToUTF8(str, ret, len);
    }
    return ret;
  }
};
// For fast lookup of conversion functions
var toC = {'string' : JSfuncs['stringToC'], 'array' : JSfuncs['arrayToC']};

// C calling interface.
function ccall (ident, returnType, argTypes, args, opts) {
  var func = getCFunc(ident);
  var cArgs = [];
  var stack = 0;
  if (args) {
    for (var i = 0; i < args.length; i++) {
      var converter = toC[argTypes[i]];
      if (converter) {
        if (stack === 0) stack = stackSave();
        cArgs[i] = converter(args[i]);
      } else {
        cArgs[i] = args[i];
      }
    }
  }
  var ret = func.apply(null, cArgs);
  if (returnType === 'string') ret = Pointer_stringify(ret);
  if (stack !== 0) {
    stackRestore(stack);
  }
  return ret;
}

function cwrap (ident, returnType, argTypes) {
  argTypes = argTypes || [];
  var cfunc = getCFunc(ident);
  // When the function takes numbers and returns a number, we can just return
  // the original function
  var numericArgs = argTypes.every(function(type){ return type === 'number'});
  var numericRet = returnType !== 'string';
  if (numericRet && numericArgs) {
    return cfunc;
  }
  return function() {
    return ccall(ident, returnType, argTypes, arguments);
  }
}

/** @type {function(number, number, string, boolean=)} */
function setValue(ptr, value, type, noSafe) {
  type = type || 'i8';
  if (type.charAt(type.length-1) === '*') type = 'i32'; // pointers are 32-bit
    switch(type) {
      case 'i1': HEAP8[((ptr)>>0)]=value; break;
      case 'i8': HEAP8[((ptr)>>0)]=value; break;
      case 'i16': HEAP16[((ptr)>>1)]=value; break;
      case 'i32': HEAP32[((ptr)>>2)]=value; break;
      case 'i64': (tempI64 = [value>>>0,(tempDouble=value,(+(Math_abs(tempDouble))) >= 1.0 ? (tempDouble > 0.0 ? ((Math_min((+(Math_floor((tempDouble)/4294967296.0))), 4294967295.0))|0)>>>0 : (~~((+(Math_ceil((tempDouble - +(((~~(tempDouble)))>>>0))/4294967296.0)))))>>>0) : 0)],HEAP32[((ptr)>>2)]=tempI64[0],HEAP32[(((ptr)+(4))>>2)]=tempI64[1]); break;
      case 'float': HEAPF32[((ptr)>>2)]=value; break;
      case 'double': HEAPF64[((ptr)>>3)]=value; break;
      default: abort('invalid type for setValue: ' + type);
    }
}

/** @type {function(number, string, boolean=)} */
function getValue(ptr, type, noSafe) {
  type = type || 'i8';
  if (type.charAt(type.length-1) === '*') type = 'i32'; // pointers are 32-bit
    switch(type) {
      case 'i1': return HEAP8[((ptr)>>0)];
      case 'i8': return HEAP8[((ptr)>>0)];
      case 'i16': return HEAP16[((ptr)>>1)];
      case 'i32': return HEAP32[((ptr)>>2)];
      case 'i64': return HEAP32[((ptr)>>2)];
      case 'float': return HEAPF32[((ptr)>>2)];
      case 'double': return HEAPF64[((ptr)>>3)];
      default: abort('invalid type for getValue: ' + type);
    }
  return null;
}

var ALLOC_NORMAL = 0; // Tries to use _malloc()
var ALLOC_STACK = 1; // Lives for the duration of the current function call
var ALLOC_STATIC = 2; // Cannot be freed
var ALLOC_DYNAMIC = 3; // Cannot be freed except through sbrk
var ALLOC_NONE = 4; // Do not allocate

// allocate(): This is for internal use. You can use it yourself as well, but the interface
//             is a little tricky (see docs right below). The reason is that it is optimized
//             for multiple syntaxes to save space in generated code. So you should
//             normally not use allocate(), and instead allocate memory using _malloc(),
//             initialize it with setValue(), and so forth.
// @slab: An array of data, or a number. If a number, then the size of the block to allocate,
//        in *bytes* (note that this is sometimes confusing: the next parameter does not
//        affect this!)
// @types: Either an array of types, one for each byte (or 0 if no type at that position),
//         or a single type which is used for the entire block. This only matters if there
//         is initial data - if @slab is a number, then this does not matter at all and is
//         ignored.
// @allocator: How to allocate memory, see ALLOC_*
/** @type {function((TypedArray|Array<number>|number), string, number, number=)} */
function allocate(slab, types, allocator, ptr) {
  var zeroinit, size;
  if (typeof slab === 'number') {
    zeroinit = true;
    size = slab;
  } else {
    zeroinit = false;
    size = slab.length;
  }

  var singleType = typeof types === 'string' ? types : null;

  var ret;
  if (allocator == ALLOC_NONE) {
    ret = ptr;
  } else {
    ret = [typeof _malloc === 'function' ? _malloc : staticAlloc, stackAlloc, staticAlloc, dynamicAlloc][allocator === undefined ? ALLOC_STATIC : allocator](Math.max(size, singleType ? 1 : types.length));
  }

  if (zeroinit) {
    var stop;
    ptr = ret;
    assert((ret & 3) == 0);
    stop = ret + (size & ~3);
    for (; ptr < stop; ptr += 4) {
      HEAP32[((ptr)>>2)]=0;
    }
    stop = ret + size;
    while (ptr < stop) {
      HEAP8[((ptr++)>>0)]=0;
    }
    return ret;
  }

  if (singleType === 'i8') {
    if (slab.subarray || slab.slice) {
      HEAPU8.set(/** @type {!Uint8Array} */ (slab), ret);
    } else {
      HEAPU8.set(new Uint8Array(slab), ret);
    }
    return ret;
  }

  var i = 0, type, typeSize, previousType;
  while (i < size) {
    var curr = slab[i];

    type = singleType || types[i];
    if (type === 0) {
      i++;
      continue;
    }

    if (type == 'i64') type = 'i32'; // special case: we have one i32 here, and one i32 later

    setValue(ret+i, curr, type);

    // no need to look up size unless type changes, so cache it
    if (previousType !== type) {
      typeSize = getNativeTypeSize(type);
      previousType = type;
    }
    i += typeSize;
  }

  return ret;
}

// Allocate memory during any stage of startup - static memory early on, dynamic memory later, malloc when ready
function getMemory(size) {
  if (!staticSealed) return staticAlloc(size);
  if (!runtimeInitialized) return dynamicAlloc(size);
  return _malloc(size);
}

/** @type {function(number, number=)} */
function Pointer_stringify(ptr, length) {
  if (length === 0 || !ptr) return '';
  // TODO: use TextDecoder
  // Find the length, and check for UTF while doing so
  var hasUtf = 0;
  var t;
  var i = 0;
  while (1) {
    t = HEAPU8[(((ptr)+(i))>>0)];
    hasUtf |= t;
    if (t == 0 && !length) break;
    i++;
    if (length && i == length) break;
  }
  if (!length) length = i;

  var ret = '';

  if (hasUtf < 128) {
    var MAX_CHUNK = 1024; // split up into chunks, because .apply on a huge string can overflow the stack
    var curr;
    while (length > 0) {
      curr = String.fromCharCode.apply(String, HEAPU8.subarray(ptr, ptr + Math.min(length, MAX_CHUNK)));
      ret = ret ? ret + curr : curr;
      ptr += MAX_CHUNK;
      length -= MAX_CHUNK;
    }
    return ret;
  }
  return UTF8ToString(ptr);
}

// Given a pointer 'ptr' to a null-terminated ASCII-encoded string in the emscripten HEAP, returns
// a copy of that string as a Javascript String object.

function AsciiToString(ptr) {
  var str = '';
  while (1) {
    var ch = HEAP8[((ptr++)>>0)];
    if (!ch) return str;
    str += String.fromCharCode(ch);
  }
}

// Copies the given Javascript String object 'str' to the emscripten HEAP at address 'outPtr',
// null-terminated and encoded in ASCII form. The copy will require at most str.length+1 bytes of space in the HEAP.

function stringToAscii(str, outPtr) {
  return writeAsciiToMemory(str, outPtr, false);
}

// Given a pointer 'ptr' to a null-terminated UTF8-encoded string in the given array that contains uint8 values, returns
// a copy of that string as a Javascript String object.

var UTF8Decoder = typeof TextDecoder !== 'undefined' ? new TextDecoder('utf8') : undefined;
function UTF8ArrayToString(u8Array, idx) {
  var endPtr = idx;
  // TextDecoder needs to know the byte length in advance, it doesn't stop on null terminator by itself.
  // Also, use the length info to avoid running tiny strings through TextDecoder, since .subarray() allocates garbage.
  while (u8Array[endPtr]) ++endPtr;

  if (endPtr - idx > 16 && u8Array.subarray && UTF8Decoder) {
    return UTF8Decoder.decode(u8Array.subarray(idx, endPtr));
  } else {
    var u0, u1, u2, u3, u4, u5;

    var str = '';
    while (1) {
      // For UTF8 byte structure, see http://en.wikipedia.org/wiki/UTF-8#Description and https://www.ietf.org/rfc/rfc2279.txt and https://tools.ietf.org/html/rfc3629
      u0 = u8Array[idx++];
      if (!u0) return str;
      if (!(u0 & 0x80)) { str += String.fromCharCode(u0); continue; }
      u1 = u8Array[idx++] & 63;
      if ((u0 & 0xE0) == 0xC0) { str += String.fromCharCode(((u0 & 31) << 6) | u1); continue; }
      u2 = u8Array[idx++] & 63;
      if ((u0 & 0xF0) == 0xE0) {
        u0 = ((u0 & 15) << 12) | (u1 << 6) | u2;
      } else {
        u3 = u8Array[idx++] & 63;
        if ((u0 & 0xF8) == 0xF0) {
          u0 = ((u0 & 7) << 18) | (u1 << 12) | (u2 << 6) | u3;
        } else {
          u4 = u8Array[idx++] & 63;
          if ((u0 & 0xFC) == 0xF8) {
            u0 = ((u0 & 3) << 24) | (u1 << 18) | (u2 << 12) | (u3 << 6) | u4;
          } else {
            u5 = u8Array[idx++] & 63;
            u0 = ((u0 & 1) << 30) | (u1 << 24) | (u2 << 18) | (u3 << 12) | (u4 << 6) | u5;
          }
        }
      }
      if (u0 < 0x10000) {
        str += String.fromCharCode(u0);
      } else {
        var ch = u0 - 0x10000;
        str += String.fromCharCode(0xD800 | (ch >> 10), 0xDC00 | (ch & 0x3FF));
      }
    }
  }
}

// Given a pointer 'ptr' to a null-terminated UTF8-encoded string in the emscripten HEAP, returns
// a copy of that string as a Javascript String object.

function UTF8ToString(ptr) {
  return UTF8ArrayToString(HEAPU8,ptr);
}

// Copies the given Javascript String object 'str' to the given byte array at address 'outIdx',
// encoded in UTF8 form and null-terminated. The copy will require at most str.length*4+1 bytes of space in the HEAP.
// Use the function lengthBytesUTF8 to compute the exact number of bytes (excluding null terminator) that this function will write.
// Parameters:
//   str: the Javascript string to copy.
//   outU8Array: the array to copy to. Each index in this array is assumed to be one 8-byte element.
//   outIdx: The starting offset in the array to begin the copying.
//   maxBytesToWrite: The maximum number of bytes this function can write to the array. This count should include the null
//                    terminator, i.e. if maxBytesToWrite=1, only the null terminator will be written and nothing else.
//                    maxBytesToWrite=0 does not write any bytes to the output, not even the null terminator.
// Returns the number of bytes written, EXCLUDING the null terminator.

function stringToUTF8Array(str, outU8Array, outIdx, maxBytesToWrite) {
  if (!(maxBytesToWrite > 0)) // Parameter maxBytesToWrite is not optional. Negative values, 0, null, undefined and false each don't write out any bytes.
    return 0;

  var startIdx = outIdx;
  var endIdx = outIdx + maxBytesToWrite - 1; // -1 for string null terminator.
  for (var i = 0; i < str.length; ++i) {
    // Gotcha: charCodeAt returns a 16-bit word that is a UTF-16 encoded code unit, not a Unicode code point of the character! So decode UTF16->UTF32->UTF8.
    // See http://unicode.org/faq/utf_bom.html#utf16-3
    // For UTF8 byte structure, see http://en.wikipedia.org/wiki/UTF-8#Description and https://www.ietf.org/rfc/rfc2279.txt and https://tools.ietf.org/html/rfc3629
    var u = str.charCodeAt(i); // possibly a lead surrogate
    if (u >= 0xD800 && u <= 0xDFFF) u = 0x10000 + ((u & 0x3FF) << 10) | (str.charCodeAt(++i) & 0x3FF);
    if (u <= 0x7F) {
      if (outIdx >= endIdx) break;
      outU8Array[outIdx++] = u;
    } else if (u <= 0x7FF) {
      if (outIdx + 1 >= endIdx) break;
      outU8Array[outIdx++] = 0xC0 | (u >> 6);
      outU8Array[outIdx++] = 0x80 | (u & 63);
    } else if (u <= 0xFFFF) {
      if (outIdx + 2 >= endIdx) break;
      outU8Array[outIdx++] = 0xE0 | (u >> 12);
      outU8Array[outIdx++] = 0x80 | ((u >> 6) & 63);
      outU8Array[outIdx++] = 0x80 | (u & 63);
    } else if (u <= 0x1FFFFF) {
      if (outIdx + 3 >= endIdx) break;
      outU8Array[outIdx++] = 0xF0 | (u >> 18);
      outU8Array[outIdx++] = 0x80 | ((u >> 12) & 63);
      outU8Array[outIdx++] = 0x80 | ((u >> 6) & 63);
      outU8Array[outIdx++] = 0x80 | (u & 63);
    } else if (u <= 0x3FFFFFF) {
      if (outIdx + 4 >= endIdx) break;
      outU8Array[outIdx++] = 0xF8 | (u >> 24);
      outU8Array[outIdx++] = 0x80 | ((u >> 18) & 63);
      outU8Array[outIdx++] = 0x80 | ((u >> 12) & 63);
      outU8Array[outIdx++] = 0x80 | ((u >> 6) & 63);
      outU8Array[outIdx++] = 0x80 | (u & 63);
    } else {
      if (outIdx + 5 >= endIdx) break;
      outU8Array[outIdx++] = 0xFC | (u >> 30);
      outU8Array[outIdx++] = 0x80 | ((u >> 24) & 63);
      outU8Array[outIdx++] = 0x80 | ((u >> 18) & 63);
      outU8Array[outIdx++] = 0x80 | ((u >> 12) & 63);
      outU8Array[outIdx++] = 0x80 | ((u >> 6) & 63);
      outU8Array[outIdx++] = 0x80 | (u & 63);
    }
  }
  // Null-terminate the pointer to the buffer.
  outU8Array[outIdx] = 0;
  return outIdx - startIdx;
}

// Copies the given Javascript String object 'str' to the emscripten HEAP at address 'outPtr',
// null-terminated and encoded in UTF8 form. The copy will require at most str.length*4+1 bytes of space in the HEAP.
// Use the function lengthBytesUTF8 to compute the exact number of bytes (excluding null terminator) that this function will write.
// Returns the number of bytes written, EXCLUDING the null terminator.

function stringToUTF8(str, outPtr, maxBytesToWrite) {
  return stringToUTF8Array(str, HEAPU8,outPtr, maxBytesToWrite);
}

// Returns the number of bytes the given Javascript string takes if encoded as a UTF8 byte array, EXCLUDING the null terminator byte.

function lengthBytesUTF8(str) {
  var len = 0;
  for (var i = 0; i < str.length; ++i) {
    // Gotcha: charCodeAt returns a 16-bit word that is a UTF-16 encoded code unit, not a Unicode code point of the character! So decode UTF16->UTF32->UTF8.
    // See http://unicode.org/faq/utf_bom.html#utf16-3
    var u = str.charCodeAt(i); // possibly a lead surrogate
    if (u >= 0xD800 && u <= 0xDFFF) u = 0x10000 + ((u & 0x3FF) << 10) | (str.charCodeAt(++i) & 0x3FF);
    if (u <= 0x7F) {
      ++len;
    } else if (u <= 0x7FF) {
      len += 2;
    } else if (u <= 0xFFFF) {
      len += 3;
    } else if (u <= 0x1FFFFF) {
      len += 4;
    } else if (u <= 0x3FFFFFF) {
      len += 5;
    } else {
      len += 6;
    }
  }
  return len;
}

// Given a pointer 'ptr' to a null-terminated UTF16LE-encoded string in the emscripten HEAP, returns
// a copy of that string as a Javascript String object.

var UTF16Decoder = typeof TextDecoder !== 'undefined' ? new TextDecoder('utf-16le') : undefined;
function UTF16ToString(ptr) {
  var endPtr = ptr;
  // TextDecoder needs to know the byte length in advance, it doesn't stop on null terminator by itself.
  // Also, use the length info to avoid running tiny strings through TextDecoder, since .subarray() allocates garbage.
  var idx = endPtr >> 1;
  while (HEAP16[idx]) ++idx;
  endPtr = idx << 1;

  if (endPtr - ptr > 32 && UTF16Decoder) {
    return UTF16Decoder.decode(HEAPU8.subarray(ptr, endPtr));
  } else {
    var i = 0;

    var str = '';
    while (1) {
      var codeUnit = HEAP16[(((ptr)+(i*2))>>1)];
      if (codeUnit == 0) return str;
      ++i;
      // fromCharCode constructs a character from a UTF-16 code unit, so we can pass the UTF16 string right through.
      str += String.fromCharCode(codeUnit);
    }
  }
}

// Copies the given Javascript String object 'str' to the emscripten HEAP at address 'outPtr',
// null-terminated and encoded in UTF16 form. The copy will require at most str.length*4+2 bytes of space in the HEAP.
// Use the function lengthBytesUTF16() to compute the exact number of bytes (excluding null terminator) that this function will write.
// Parameters:
//   str: the Javascript string to copy.
//   outPtr: Byte address in Emscripten HEAP where to write the string to.
//   maxBytesToWrite: The maximum number of bytes this function can write to the array. This count should include the null
//                    terminator, i.e. if maxBytesToWrite=2, only the null terminator will be written and nothing else.
//                    maxBytesToWrite<2 does not write any bytes to the output, not even the null terminator.
// Returns the number of bytes written, EXCLUDING the null terminator.

function stringToUTF16(str, outPtr, maxBytesToWrite) {
  // Backwards compatibility: if max bytes is not specified, assume unsafe unbounded write is allowed.
  if (maxBytesToWrite === undefined) {
    maxBytesToWrite = 0x7FFFFFFF;
  }
  if (maxBytesToWrite < 2) return 0;
  maxBytesToWrite -= 2; // Null terminator.
  var startPtr = outPtr;
  var numCharsToWrite = (maxBytesToWrite < str.length*2) ? (maxBytesToWrite / 2) : str.length;
  for (var i = 0; i < numCharsToWrite; ++i) {
    // charCodeAt returns a UTF-16 encoded code unit, so it can be directly written to the HEAP.
    var codeUnit = str.charCodeAt(i); // possibly a lead surrogate
    HEAP16[((outPtr)>>1)]=codeUnit;
    outPtr += 2;
  }
  // Null-terminate the pointer to the HEAP.
  HEAP16[((outPtr)>>1)]=0;
  return outPtr - startPtr;
}

// Returns the number of bytes the given Javascript string takes if encoded as a UTF16 byte array, EXCLUDING the null terminator byte.

function lengthBytesUTF16(str) {
  return str.length*2;
}

function UTF32ToString(ptr) {
  var i = 0;

  var str = '';
  while (1) {
    var utf32 = HEAP32[(((ptr)+(i*4))>>2)];
    if (utf32 == 0)
      return str;
    ++i;
    // Gotcha: fromCharCode constructs a character from a UTF-16 encoded code (pair), not from a Unicode code point! So encode the code point to UTF-16 for constructing.
    // See http://unicode.org/faq/utf_bom.html#utf16-3
    if (utf32 >= 0x10000) {
      var ch = utf32 - 0x10000;
      str += String.fromCharCode(0xD800 | (ch >> 10), 0xDC00 | (ch & 0x3FF));
    } else {
      str += String.fromCharCode(utf32);
    }
  }
}

// Copies the given Javascript String object 'str' to the emscripten HEAP at address 'outPtr',
// null-terminated and encoded in UTF32 form. The copy will require at most str.length*4+4 bytes of space in the HEAP.
// Use the function lengthBytesUTF32() to compute the exact number of bytes (excluding null terminator) that this function will write.
// Parameters:
//   str: the Javascript string to copy.
//   outPtr: Byte address in Emscripten HEAP where to write the string to.
//   maxBytesToWrite: The maximum number of bytes this function can write to the array. This count should include the null
//                    terminator, i.e. if maxBytesToWrite=4, only the null terminator will be written and nothing else.
//                    maxBytesToWrite<4 does not write any bytes to the output, not even the null terminator.
// Returns the number of bytes written, EXCLUDING the null terminator.

function stringToUTF32(str, outPtr, maxBytesToWrite) {
  // Backwards compatibility: if max bytes is not specified, assume unsafe unbounded write is allowed.
  if (maxBytesToWrite === undefined) {
    maxBytesToWrite = 0x7FFFFFFF;
  }
  if (maxBytesToWrite < 4) return 0;
  var startPtr = outPtr;
  var endPtr = startPtr + maxBytesToWrite - 4;
  for (var i = 0; i < str.length; ++i) {
    // Gotcha: charCodeAt returns a 16-bit word that is a UTF-16 encoded code unit, not a Unicode code point of the character! We must decode the string to UTF-32 to the heap.
    // See http://unicode.org/faq/utf_bom.html#utf16-3
    var codeUnit = str.charCodeAt(i); // possibly a lead surrogate
    if (codeUnit >= 0xD800 && codeUnit <= 0xDFFF) {
      var trailSurrogate = str.charCodeAt(++i);
      codeUnit = 0x10000 + ((codeUnit & 0x3FF) << 10) | (trailSurrogate & 0x3FF);
    }
    HEAP32[((outPtr)>>2)]=codeUnit;
    outPtr += 4;
    if (outPtr + 4 > endPtr) break;
  }
  // Null-terminate the pointer to the HEAP.
  HEAP32[((outPtr)>>2)]=0;
  return outPtr - startPtr;
}

// Returns the number of bytes the given Javascript string takes if encoded as a UTF16 byte array, EXCLUDING the null terminator byte.

function lengthBytesUTF32(str) {
  var len = 0;
  for (var i = 0; i < str.length; ++i) {
    // Gotcha: charCodeAt returns a 16-bit word that is a UTF-16 encoded code unit, not a Unicode code point of the character! We must decode the string to UTF-32 to the heap.
    // See http://unicode.org/faq/utf_bom.html#utf16-3
    var codeUnit = str.charCodeAt(i);
    if (codeUnit >= 0xD800 && codeUnit <= 0xDFFF) ++i; // possibly a lead surrogate, so skip over the tail surrogate.
    len += 4;
  }

  return len;
}

// Allocate heap space for a JS string, and write it there.
// It is the responsibility of the caller to free() that memory.
function allocateUTF8(str) {
  var size = lengthBytesUTF8(str) + 1;
  var ret = _malloc(size);
  if (ret) stringToUTF8Array(str, HEAP8, ret, size);
  return ret;
}

// Allocate stack space for a JS string, and write it there.
function allocateUTF8OnStack(str) {
  var size = lengthBytesUTF8(str) + 1;
  var ret = stackAlloc(size);
  stringToUTF8Array(str, HEAP8, ret, size);
  return ret;
}

function demangle(func) {
  return func;
}

function demangleAll(text) {
  var regex =
    /__Z[\w\d_]+/g;
  return text.replace(regex,
    function(x) {
      var y = demangle(x);
      return x === y ? x : (x + ' [' + y + ']');
    });
}

function jsStackTrace() {
  var err = new Error();
  if (!err.stack) {
    // IE10+ special cases: It does have callstack info, but it is only populated if an Error object is thrown,
    // so try that as a special-case.
    try {
      throw new Error(0);
    } catch(e) {
      err = e;
    }
    if (!err.stack) {
      return '(no stack trace available)';
    }
  }
  return err.stack.toString();
}

function stackTrace() {
  var js = jsStackTrace();
  if (Module['extraStackTrace']) js += '\n' + Module['extraStackTrace']();
  return demangleAll(js);
}

// Memory management

var PAGE_SIZE = 16384;
var WASM_PAGE_SIZE = 65536;
var ASMJS_PAGE_SIZE = 16777216;
var MIN_TOTAL_MEMORY = 16777216;

function alignUp(x, multiple) {
  if (x % multiple > 0) {
    x += multiple - (x % multiple);
  }
  return x;
}

var HEAP,
/** @type {ArrayBuffer} */
  buffer,
/** @type {Int8Array} */
  HEAP8,
/** @type {Uint8Array} */
  HEAPU8,
/** @type {Int16Array} */
  HEAP16,
/** @type {Uint16Array} */
  HEAPU16,
/** @type {Int32Array} */
  HEAP32,
/** @type {Uint32Array} */
  HEAPU32,
/** @type {Float32Array} */
  HEAPF32,
/** @type {Float64Array} */
  HEAPF64;

function updateGlobalBuffer(buf) {
  Module['buffer'] = buffer = buf;
}

function updateGlobalBufferViews() {
  Module['HEAP8'] = HEAP8 = new Int8Array(buffer);
  Module['HEAP16'] = HEAP16 = new Int16Array(buffer);
  Module['HEAP32'] = HEAP32 = new Int32Array(buffer);
  Module['HEAPU8'] = HEAPU8 = new Uint8Array(buffer);
  Module['HEAPU16'] = HEAPU16 = new Uint16Array(buffer);
  Module['HEAPU32'] = HEAPU32 = new Uint32Array(buffer);
  Module['HEAPF32'] = HEAPF32 = new Float32Array(buffer);
  Module['HEAPF64'] = HEAPF64 = new Float64Array(buffer);
}

var STATIC_BASE, STATICTOP, staticSealed; // static area
var STACK_BASE, STACKTOP, STACK_MAX; // stack area
var DYNAMIC_BASE, DYNAMICTOP_PTR; // dynamic area handled by sbrk

  STATIC_BASE = STATICTOP = STACK_BASE = STACKTOP = STACK_MAX = DYNAMIC_BASE = DYNAMICTOP_PTR = 0;
  staticSealed = false;



function abortOnCannotGrowMemory() {
  abort('Cannot enlarge memory arrays. Either (1) compile with  -s TOTAL_MEMORY=X  with X higher than the current value ' + TOTAL_MEMORY + ', (2) compile with  -s ALLOW_MEMORY_GROWTH=1  which allows increasing the size at runtime but prevents some optimizations, (3) set Module.TOTAL_MEMORY to a higher value before the program runs, or (4) if you want malloc to return NULL (0) instead of this abort, compile with  -s ABORTING_MALLOC=0 ');
}


function enlargeMemory() {
  abortOnCannotGrowMemory();
}


var TOTAL_STACK = Module['TOTAL_STACK'] || 5242880;
var TOTAL_MEMORY = Module['TOTAL_MEMORY'] || 16777216;
if (TOTAL_MEMORY < TOTAL_STACK) Module.printErr('TOTAL_MEMORY should be larger than TOTAL_STACK, was ' + TOTAL_MEMORY + '! (TOTAL_STACK=' + TOTAL_STACK + ')');

// Initialize the runtime's memory



// Use a provided buffer, if there is one, or else allocate a new one
if (Module['buffer']) {
  buffer = Module['buffer'];
} else {
  // Use a WebAssembly memory where available
  {
    buffer = new ArrayBuffer(TOTAL_MEMORY);
  }
  Module['buffer'] = buffer;
}
updateGlobalBufferViews();


function getTotalMemory() {
  return TOTAL_MEMORY;
}

// Endianness check (note: assumes compiler arch was little-endian)
  HEAP32[0] = 0x63736d65; /* 'emsc' */
HEAP16[1] = 0x6373;
if (HEAPU8[2] !== 0x73 || HEAPU8[3] !== 0x63) throw 'Runtime error: expected the system to be little-endian!';

function callRuntimeCallbacks(callbacks) {
  while(callbacks.length > 0) {
    var callback = callbacks.shift();
    if (typeof callback == 'function') {
      callback();
      continue;
    }
    var func = callback.func;
    if (typeof func === 'number') {
      if (callback.arg === undefined) {
        Module['dynCall_v'](func);
      } else {
        Module['dynCall_vi'](func, callback.arg);
      }
    } else {
      func(callback.arg === undefined ? null : callback.arg);
    }
  }
}

var __ATPRERUN__  = []; // functions called before the runtime is initialized
var __ATINIT__    = []; // functions called during startup
var __ATMAIN__    = []; // functions called when main() is to be run
var __ATEXIT__    = []; // functions called during shutdown
var __ATPOSTRUN__ = []; // functions called after the runtime has exited

var runtimeInitialized = false;
var runtimeExited = false;


function preRun() {
  // compatibility - merge in anything from Module['preRun'] at this time
  if (Module['preRun']) {
    if (typeof Module['preRun'] == 'function') Module['preRun'] = [Module['preRun']];
    while (Module['preRun'].length) {
      addOnPreRun(Module['preRun'].shift());
    }
  }
  callRuntimeCallbacks(__ATPRERUN__);
}

function ensureInitRuntime() {
  if (runtimeInitialized) return;
  runtimeInitialized = true;
  callRuntimeCallbacks(__ATINIT__);
}

function preMain() {
  callRuntimeCallbacks(__ATMAIN__);
}

function exitRuntime() {
  callRuntimeCallbacks(__ATEXIT__);
  runtimeExited = true;
}

function postRun() {
  // compatibility - merge in anything from Module['postRun'] at this time
  if (Module['postRun']) {
    if (typeof Module['postRun'] == 'function') Module['postRun'] = [Module['postRun']];
    while (Module['postRun'].length) {
      addOnPostRun(Module['postRun'].shift());
    }
  }
  callRuntimeCallbacks(__ATPOSTRUN__);
}

function addOnPreRun(cb) {
  __ATPRERUN__.unshift(cb);
}

function addOnInit(cb) {
  __ATINIT__.unshift(cb);
}

function addOnPreMain(cb) {
  __ATMAIN__.unshift(cb);
}

function addOnExit(cb) {
  __ATEXIT__.unshift(cb);
}

function addOnPostRun(cb) {
  __ATPOSTRUN__.unshift(cb);
}

// Deprecated: This function should not be called because it is unsafe and does not provide
// a maximum length limit of how many bytes it is allowed to write. Prefer calling the
// function stringToUTF8Array() instead, which takes in a maximum length that can be used
// to be secure from out of bounds writes.
/** @deprecated */
function writeStringToMemory(string, buffer, dontAddNull) {
  warnOnce('writeStringToMemory is deprecated and should not be called! Use stringToUTF8() instead!');

  var /** @type {number} */ lastChar, /** @type {number} */ end;
  if (dontAddNull) {
    // stringToUTF8Array always appends null. If we don't want to do that, remember the
    // character that existed at the location where the null will be placed, and restore
    // that after the write (below).
    end = buffer + lengthBytesUTF8(string);
    lastChar = HEAP8[end];
  }
  stringToUTF8(string, buffer, Infinity);
  if (dontAddNull) HEAP8[end] = lastChar; // Restore the value under the null character.
}

function writeArrayToMemory(array, buffer) {
  HEAP8.set(array, buffer);
}

function writeAsciiToMemory(str, buffer, dontAddNull) {
  for (var i = 0; i < str.length; ++i) {
    HEAP8[((buffer++)>>0)]=str.charCodeAt(i);
  }
  // Null-terminate the pointer to the HEAP.
  if (!dontAddNull) HEAP8[((buffer)>>0)]=0;
}

function unSign(value, bits, ignore) {
  if (value >= 0) {
    return value;
  }
  return bits <= 32 ? 2*Math.abs(1 << (bits-1)) + value // Need some trickery, since if bits == 32, we are right at the limit of the bits JS uses in bitshifts
                    : Math.pow(2, bits)         + value;
}
function reSign(value, bits, ignore) {
  if (value <= 0) {
    return value;
  }
  var half = bits <= 32 ? Math.abs(1 << (bits-1)) // abs is needed if bits == 32
                        : Math.pow(2, bits-1);
  if (value >= half && (bits <= 32 || value > half)) { // for huge values, we can hit the precision limit and always get true here. so don't do that
                                                       // but, in general there is no perfect solution here. With 64-bit ints, we get rounding and errors
                                                       // TODO: In i64 mode 1, resign the two parts separately and safely
    value = -2*half + value; // Cannot bitshift half, as it may be at the limit of the bits JS uses in bitshifts
  }
  return value;
}


var Math_abs = Math.abs;
var Math_cos = Math.cos;
var Math_sin = Math.sin;
var Math_tan = Math.tan;
var Math_acos = Math.acos;
var Math_asin = Math.asin;
var Math_atan = Math.atan;
var Math_atan2 = Math.atan2;
var Math_exp = Math.exp;
var Math_log = Math.log;
var Math_sqrt = Math.sqrt;
var Math_ceil = Math.ceil;
var Math_floor = Math.floor;
var Math_pow = Math.pow;
var Math_imul = Math.imul;
var Math_fround = Math.fround;
var Math_round = Math.round;
var Math_min = Math.min;
var Math_max = Math.max;
var Math_clz32 = Math.clz32;
var Math_trunc = Math.trunc;

// A counter of dependencies for calling run(). If we need to
// do asynchronous work before running, increment this and
// decrement it. Incrementing must happen in a place like
// PRE_RUN_ADDITIONS (used by emcc to add file preloading).
// Note that you can add dependencies in preRun, even though
// it happens right before run - run will be postponed until
// the dependencies are met.
var runDependencies = 0;
var runDependencyWatcher = null;
var dependenciesFulfilled = null; // overridden to take different actions when all run dependencies are fulfilled

function getUniqueRunDependency(id) {
  return id;
}

function addRunDependency(id) {
  runDependencies++;
  if (Module['monitorRunDependencies']) {
    Module['monitorRunDependencies'](runDependencies);
  }
}

function removeRunDependency(id) {
  runDependencies--;
  if (Module['monitorRunDependencies']) {
    Module['monitorRunDependencies'](runDependencies);
  }
  if (runDependencies == 0) {
    if (runDependencyWatcher !== null) {
      clearInterval(runDependencyWatcher);
      runDependencyWatcher = null;
    }
    if (dependenciesFulfilled) {
      var callback = dependenciesFulfilled;
      dependenciesFulfilled = null;
      callback(); // can add another dependenciesFulfilled
    }
  }
}

Module["preloadedImages"] = {}; // maps url to image data
Module["preloadedAudios"] = {}; // maps url to audio data



var memoryInitializer = null;






// Prefix of data URIs emitted by SINGLE_FILE and related options.
var dataURIPrefix = 'data:application/octet-stream;base64,';

// Indicates whether filename is a base64 data URI.
function isDataURI(filename) {
  return String.prototype.startsWith ?
      filename.startsWith(dataURIPrefix) :
      filename.indexOf(dataURIPrefix) === 0;
}





// === Body ===

var ASM_CONSTS = [];





STATIC_BASE = GLOBAL_BASE;

STATICTOP = STATIC_BASE + 33056;
/* global initializers */  __ATINIT__.push();


memoryInitializer = "data:application/octet-stream;base64,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";





/* no memory initializer */
var tempDoublePtr = STATICTOP; STATICTOP += 16;

function copyTempFloat(ptr) { // functions, because inlining this code increases code size too much

  HEAP8[tempDoublePtr] = HEAP8[ptr];

  HEAP8[tempDoublePtr+1] = HEAP8[ptr+1];

  HEAP8[tempDoublePtr+2] = HEAP8[ptr+2];

  HEAP8[tempDoublePtr+3] = HEAP8[ptr+3];

}

function copyTempDouble(ptr) {

  HEAP8[tempDoublePtr] = HEAP8[ptr];

  HEAP8[tempDoublePtr+1] = HEAP8[ptr+1];

  HEAP8[tempDoublePtr+2] = HEAP8[ptr+2];

  HEAP8[tempDoublePtr+3] = HEAP8[ptr+3];

  HEAP8[tempDoublePtr+4] = HEAP8[ptr+4];

  HEAP8[tempDoublePtr+5] = HEAP8[ptr+5];

  HEAP8[tempDoublePtr+6] = HEAP8[ptr+6];

  HEAP8[tempDoublePtr+7] = HEAP8[ptr+7];

}

// {{PRE_LIBRARY}}


  
    

   

   

   

   

   

  function _llvm_stackrestore(p) {
      var self = _llvm_stacksave;
      var ret = self.LLVM_SAVEDSTACKS[p];
      self.LLVM_SAVEDSTACKS.splice(p, 1);
      stackRestore(ret);
    }

  function _llvm_stacksave() {
      var self = _llvm_stacksave;
      if (!self.LLVM_SAVEDSTACKS) {
        self.LLVM_SAVEDSTACKS = [];
      }
      self.LLVM_SAVEDSTACKS.push(stackSave());
      return self.LLVM_SAVEDSTACKS.length-1;
    }

  
  function _emscripten_memcpy_big(dest, src, num) {
      HEAPU8.set(HEAPU8.subarray(src, src+num), dest);
      return dest;
    } 

   

   

  
  function ___setErrNo(value) {
      if (Module['___errno_location']) HEAP32[((Module['___errno_location']())>>2)]=value;
      return value;
    } 
DYNAMICTOP_PTR = staticAlloc(4);

STACK_BASE = STACKTOP = alignMemory(STATICTOP);

STACK_MAX = STACK_BASE + TOTAL_STACK;

DYNAMIC_BASE = alignMemory(STACK_MAX);

HEAP32[DYNAMICTOP_PTR>>2] = DYNAMIC_BASE;

staticSealed = true; // seal the static portion of memory

var ASSERTIONS = false;

/** @type {function(string, boolean=, number=)} */
function intArrayFromString(stringy, dontAddNull, length) {
  var len = length > 0 ? length : lengthBytesUTF8(stringy)+1;
  var u8array = new Array(len);
  var numBytesWritten = stringToUTF8Array(stringy, u8array, 0, u8array.length);
  if (dontAddNull) u8array.length = numBytesWritten;
  return u8array;
}

function intArrayToString(array) {
  var ret = [];
  for (var i = 0; i < array.length; i++) {
    var chr = array[i];
    if (chr > 0xFF) {
      if (ASSERTIONS) {
        assert(false, 'Character code ' + chr + ' (' + String.fromCharCode(chr) + ')  at offset ' + i + ' not in 0x00-0xFF.');
      }
      chr &= 0xFF;
    }
    ret.push(String.fromCharCode(chr));
  }
  return ret.join('');
}


// Copied from https://github.com/strophe/strophejs/blob/e06d027/src/polyfills.js#L149

// This code was written by Tyler Akins and has been placed in the
// public domain.  It would be nice if you left this header intact.
// Base64 code from Tyler Akins -- http://rumkin.com

/**
 * Decodes a base64 string.
 * @param {String} input The string to decode.
 */
var decodeBase64 = typeof atob === 'function' ? atob : function (input) {
  var keyStr = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=';

  var output = '';
  var chr1, chr2, chr3;
  var enc1, enc2, enc3, enc4;
  var i = 0;
  // remove all characters that are not A-Z, a-z, 0-9, +, /, or =
  input = input.replace(/[^A-Za-z0-9\+\/\=]/g, '');
  do {
    enc1 = keyStr.indexOf(input.charAt(i++));
    enc2 = keyStr.indexOf(input.charAt(i++));
    enc3 = keyStr.indexOf(input.charAt(i++));
    enc4 = keyStr.indexOf(input.charAt(i++));

    chr1 = (enc1 << 2) | (enc2 >> 4);
    chr2 = ((enc2 & 15) << 4) | (enc3 >> 2);
    chr3 = ((enc3 & 3) << 6) | enc4;

    output = output + String.fromCharCode(chr1);

    if (enc3 !== 64) {
      output = output + String.fromCharCode(chr2);
    }
    if (enc4 !== 64) {
      output = output + String.fromCharCode(chr3);
    }
  } while (i < input.length);
  return output;
};

// Converts a string of base64 into a byte array.
// Throws error on invalid input.
function intArrayFromBase64(s) {
  if (typeof ENVIRONMENT_IS_NODE === 'boolean' && ENVIRONMENT_IS_NODE) {
    var buf;
    try {
      buf = Buffer.from(s, 'base64');
    } catch (_) {
      buf = new Buffer(s, 'base64');
    }
    return new Uint8Array(buf.buffer, buf.byteOffset, buf.byteLength);
  }

  try {
    var decoded = decodeBase64(s);
    var bytes = new Uint8Array(decoded.length);
    for (var i = 0 ; i < decoded.length ; ++i) {
      bytes[i] = decoded.charCodeAt(i);
    }
    return bytes;
  } catch (_) {
    throw new Error('Converting base64 string to bytes failed.');
  }
}

// If filename is a base64 data URI, parses and returns data (Buffer on node,
// Uint8Array otherwise). If filename is not a base64 data URI, returns undefined.
function tryParseAsDataURI(filename) {
  if (!isDataURI(filename)) {
    return;
  }

  return intArrayFromBase64(filename.slice(dataURIPrefix.length));
}



Module.asmGlobalArg = { "Math": Math, "Int8Array": Int8Array, "Int16Array": Int16Array, "Int32Array": Int32Array, "Uint8Array": Uint8Array, "Uint16Array": Uint16Array, "Uint32Array": Uint32Array, "Float32Array": Float32Array, "Float64Array": Float64Array, "NaN": NaN, "Infinity": Infinity };

Module.asmLibraryArg = { "abort": abort, "assert": assert, "enlargeMemory": enlargeMemory, "getTotalMemory": getTotalMemory, "abortOnCannotGrowMemory": abortOnCannotGrowMemory, "___setErrNo": ___setErrNo, "_emscripten_memcpy_big": _emscripten_memcpy_big, "_llvm_stackrestore": _llvm_stackrestore, "_llvm_stacksave": _llvm_stacksave, "DYNAMICTOP_PTR": DYNAMICTOP_PTR, "tempDoublePtr": tempDoublePtr, "ABORT": ABORT, "STACKTOP": STACKTOP, "STACK_MAX": STACK_MAX };
// EMSCRIPTEN_START_ASM
var asm = (/** @suppress {uselessCode} */ function(global, env, buffer) {
'use asm';


  var HEAP8 = new global.Int8Array(buffer);
  var HEAP16 = new global.Int16Array(buffer);
  var HEAP32 = new global.Int32Array(buffer);
  var HEAPU8 = new global.Uint8Array(buffer);
  var HEAPU16 = new global.Uint16Array(buffer);
  var HEAPU32 = new global.Uint32Array(buffer);
  var HEAPF32 = new global.Float32Array(buffer);
  var HEAPF64 = new global.Float64Array(buffer);

  var DYNAMICTOP_PTR=env.DYNAMICTOP_PTR|0;
  var tempDoublePtr=env.tempDoublePtr|0;
  var ABORT=env.ABORT|0;
  var STACKTOP=env.STACKTOP|0;
  var STACK_MAX=env.STACK_MAX|0;

  var __THREW__ = 0;
  var threwValue = 0;
  var setjmpId = 0;
  var undef = 0;
  var nan = global.NaN, inf = global.Infinity;
  var tempInt = 0, tempBigInt = 0, tempBigIntS = 0, tempValue = 0, tempDouble = 0.0;
  var tempRet0 = 0;

  var Math_floor=global.Math.floor;
  var Math_abs=global.Math.abs;
  var Math_sqrt=global.Math.sqrt;
  var Math_pow=global.Math.pow;
  var Math_cos=global.Math.cos;
  var Math_sin=global.Math.sin;
  var Math_tan=global.Math.tan;
  var Math_acos=global.Math.acos;
  var Math_asin=global.Math.asin;
  var Math_atan=global.Math.atan;
  var Math_atan2=global.Math.atan2;
  var Math_exp=global.Math.exp;
  var Math_log=global.Math.log;
  var Math_ceil=global.Math.ceil;
  var Math_imul=global.Math.imul;
  var Math_min=global.Math.min;
  var Math_max=global.Math.max;
  var Math_clz32=global.Math.clz32;
  var abort=env.abort;
  var assert=env.assert;
  var enlargeMemory=env.enlargeMemory;
  var getTotalMemory=env.getTotalMemory;
  var abortOnCannotGrowMemory=env.abortOnCannotGrowMemory;
  var ___setErrNo=env.___setErrNo;
  var _emscripten_memcpy_big=env._emscripten_memcpy_big;
  var _llvm_stackrestore=env._llvm_stackrestore;
  var _llvm_stacksave=env._llvm_stacksave;
  var tempFloat = 0.0;

// EMSCRIPTEN_START_FUNCS

function stackAlloc(size) {
  size = size|0;
  var ret = 0;
  ret = STACKTOP;
  STACKTOP = (STACKTOP + size)|0;
  STACKTOP = (STACKTOP + 15)&-16;

  return ret|0;
}
function stackSave() {
  return STACKTOP|0;
}
function stackRestore(top) {
  top = top|0;
  STACKTOP = top;
}
function establishStackSpace(stackBase, stackMax) {
  stackBase = stackBase|0;
  stackMax = stackMax|0;
  STACKTOP = stackBase;
  STACK_MAX = stackMax;
}

function setThrew(threw, value) {
  threw = threw|0;
  value = value|0;
  if ((__THREW__|0) == 0) {
    __THREW__ = threw;
    threwValue = value;
  }
}

function setTempRet0(value) {
  value = value|0;
  tempRet0 = value;
}
function getTempRet0() {
  return tempRet0|0;
}

function _crypto_verify_32_ref($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0, $113 = 0, $114 = 0, $115 = 0, $116 = 0, $117 = 0;
 var $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0, $133 = 0, $134 = 0, $135 = 0;
 var $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0, $15 = 0, $150 = 0, $151 = 0, $152 = 0, $153 = 0;
 var $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $159 = 0, $16 = 0, $160 = 0, $161 = 0, $162 = 0, $163 = 0, $164 = 0, $165 = 0, $166 = 0, $167 = 0, $168 = 0, $169 = 0, $17 = 0, $170 = 0, $171 = 0;
 var $172 = 0, $173 = 0, $174 = 0, $175 = 0, $176 = 0, $177 = 0, $178 = 0, $179 = 0, $18 = 0, $180 = 0, $181 = 0, $182 = 0, $183 = 0, $184 = 0, $185 = 0, $186 = 0, $187 = 0, $188 = 0, $189 = 0, $19 = 0;
 var $190 = 0, $191 = 0, $192 = 0, $193 = 0, $194 = 0, $195 = 0, $2 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0, $29 = 0, $3 = 0, $30 = 0, $31 = 0;
 var $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $4 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0, $46 = 0, $47 = 0, $48 = 0, $49 = 0, $5 = 0;
 var $50 = 0, $51 = 0, $52 = 0, $53 = 0, $54 = 0, $55 = 0, $56 = 0, $57 = 0, $58 = 0, $59 = 0, $6 = 0, $60 = 0, $61 = 0, $62 = 0, $63 = 0, $64 = 0, $65 = 0, $66 = 0, $67 = 0, $68 = 0;
 var $69 = 0, $7 = 0, $70 = 0, $71 = 0, $72 = 0, $73 = 0, $74 = 0, $75 = 0, $76 = 0, $77 = 0, $78 = 0, $79 = 0, $8 = 0, $80 = 0, $81 = 0, $82 = 0, $83 = 0, $84 = 0, $85 = 0, $86 = 0;
 var $87 = 0, $88 = 0, $89 = 0, $9 = 0, $90 = 0, $91 = 0, $92 = 0, $93 = 0, $94 = 0, $95 = 0, $96 = 0, $97 = 0, $98 = 0, $99 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = HEAP8[$0>>0]|0;
 $3 = HEAP8[$1>>0]|0;
 $4 = $3 ^ $2;
 $5 = ((($0)) + 1|0);
 $6 = HEAP8[$5>>0]|0;
 $7 = ((($1)) + 1|0);
 $8 = HEAP8[$7>>0]|0;
 $9 = $8 ^ $6;
 $10 = $9 | $4;
 $11 = ((($0)) + 2|0);
 $12 = HEAP8[$11>>0]|0;
 $13 = ((($1)) + 2|0);
 $14 = HEAP8[$13>>0]|0;
 $15 = $14 ^ $12;
 $16 = $10 | $15;
 $17 = ((($0)) + 3|0);
 $18 = HEAP8[$17>>0]|0;
 $19 = ((($1)) + 3|0);
 $20 = HEAP8[$19>>0]|0;
 $21 = $20 ^ $18;
 $22 = $16 | $21;
 $23 = ((($0)) + 4|0);
 $24 = HEAP8[$23>>0]|0;
 $25 = ((($1)) + 4|0);
 $26 = HEAP8[$25>>0]|0;
 $27 = $26 ^ $24;
 $28 = $22 | $27;
 $29 = ((($0)) + 5|0);
 $30 = HEAP8[$29>>0]|0;
 $31 = ((($1)) + 5|0);
 $32 = HEAP8[$31>>0]|0;
 $33 = $32 ^ $30;
 $34 = $28 | $33;
 $35 = ((($0)) + 6|0);
 $36 = HEAP8[$35>>0]|0;
 $37 = ((($1)) + 6|0);
 $38 = HEAP8[$37>>0]|0;
 $39 = $38 ^ $36;
 $40 = $34 | $39;
 $41 = ((($0)) + 7|0);
 $42 = HEAP8[$41>>0]|0;
 $43 = ((($1)) + 7|0);
 $44 = HEAP8[$43>>0]|0;
 $45 = $44 ^ $42;
 $46 = $40 | $45;
 $47 = ((($0)) + 8|0);
 $48 = HEAP8[$47>>0]|0;
 $49 = ((($1)) + 8|0);
 $50 = HEAP8[$49>>0]|0;
 $51 = $50 ^ $48;
 $52 = $46 | $51;
 $53 = ((($0)) + 9|0);
 $54 = HEAP8[$53>>0]|0;
 $55 = ((($1)) + 9|0);
 $56 = HEAP8[$55>>0]|0;
 $57 = $56 ^ $54;
 $58 = $52 | $57;
 $59 = ((($0)) + 10|0);
 $60 = HEAP8[$59>>0]|0;
 $61 = ((($1)) + 10|0);
 $62 = HEAP8[$61>>0]|0;
 $63 = $62 ^ $60;
 $64 = $58 | $63;
 $65 = ((($0)) + 11|0);
 $66 = HEAP8[$65>>0]|0;
 $67 = ((($1)) + 11|0);
 $68 = HEAP8[$67>>0]|0;
 $69 = $68 ^ $66;
 $70 = $64 | $69;
 $71 = ((($0)) + 12|0);
 $72 = HEAP8[$71>>0]|0;
 $73 = ((($1)) + 12|0);
 $74 = HEAP8[$73>>0]|0;
 $75 = $74 ^ $72;
 $76 = $70 | $75;
 $77 = ((($0)) + 13|0);
 $78 = HEAP8[$77>>0]|0;
 $79 = ((($1)) + 13|0);
 $80 = HEAP8[$79>>0]|0;
 $81 = $80 ^ $78;
 $82 = $76 | $81;
 $83 = ((($0)) + 14|0);
 $84 = HEAP8[$83>>0]|0;
 $85 = ((($1)) + 14|0);
 $86 = HEAP8[$85>>0]|0;
 $87 = $86 ^ $84;
 $88 = $82 | $87;
 $89 = ((($0)) + 15|0);
 $90 = HEAP8[$89>>0]|0;
 $91 = ((($1)) + 15|0);
 $92 = HEAP8[$91>>0]|0;
 $93 = $92 ^ $90;
 $94 = $88 | $93;
 $95 = ((($0)) + 16|0);
 $96 = HEAP8[$95>>0]|0;
 $97 = ((($1)) + 16|0);
 $98 = HEAP8[$97>>0]|0;
 $99 = $98 ^ $96;
 $100 = $94 | $99;
 $101 = ((($0)) + 17|0);
 $102 = HEAP8[$101>>0]|0;
 $103 = ((($1)) + 17|0);
 $104 = HEAP8[$103>>0]|0;
 $105 = $104 ^ $102;
 $106 = $100 | $105;
 $107 = ((($0)) + 18|0);
 $108 = HEAP8[$107>>0]|0;
 $109 = ((($1)) + 18|0);
 $110 = HEAP8[$109>>0]|0;
 $111 = $110 ^ $108;
 $112 = $106 | $111;
 $113 = ((($0)) + 19|0);
 $114 = HEAP8[$113>>0]|0;
 $115 = ((($1)) + 19|0);
 $116 = HEAP8[$115>>0]|0;
 $117 = $116 ^ $114;
 $118 = $112 | $117;
 $119 = ((($0)) + 20|0);
 $120 = HEAP8[$119>>0]|0;
 $121 = ((($1)) + 20|0);
 $122 = HEAP8[$121>>0]|0;
 $123 = $122 ^ $120;
 $124 = $118 | $123;
 $125 = ((($0)) + 21|0);
 $126 = HEAP8[$125>>0]|0;
 $127 = ((($1)) + 21|0);
 $128 = HEAP8[$127>>0]|0;
 $129 = $128 ^ $126;
 $130 = $124 | $129;
 $131 = ((($0)) + 22|0);
 $132 = HEAP8[$131>>0]|0;
 $133 = ((($1)) + 22|0);
 $134 = HEAP8[$133>>0]|0;
 $135 = $134 ^ $132;
 $136 = $130 | $135;
 $137 = ((($0)) + 23|0);
 $138 = HEAP8[$137>>0]|0;
 $139 = ((($1)) + 23|0);
 $140 = HEAP8[$139>>0]|0;
 $141 = $140 ^ $138;
 $142 = $136 | $141;
 $143 = ((($0)) + 24|0);
 $144 = HEAP8[$143>>0]|0;
 $145 = ((($1)) + 24|0);
 $146 = HEAP8[$145>>0]|0;
 $147 = $146 ^ $144;
 $148 = $142 | $147;
 $149 = ((($0)) + 25|0);
 $150 = HEAP8[$149>>0]|0;
 $151 = ((($1)) + 25|0);
 $152 = HEAP8[$151>>0]|0;
 $153 = $152 ^ $150;
 $154 = $148 | $153;
 $155 = ((($0)) + 26|0);
 $156 = HEAP8[$155>>0]|0;
 $157 = ((($1)) + 26|0);
 $158 = HEAP8[$157>>0]|0;
 $159 = $158 ^ $156;
 $160 = $154 | $159;
 $161 = ((($0)) + 27|0);
 $162 = HEAP8[$161>>0]|0;
 $163 = ((($1)) + 27|0);
 $164 = HEAP8[$163>>0]|0;
 $165 = $164 ^ $162;
 $166 = $160 | $165;
 $167 = ((($0)) + 28|0);
 $168 = HEAP8[$167>>0]|0;
 $169 = ((($1)) + 28|0);
 $170 = HEAP8[$169>>0]|0;
 $171 = $170 ^ $168;
 $172 = $166 | $171;
 $173 = ((($0)) + 29|0);
 $174 = HEAP8[$173>>0]|0;
 $175 = ((($1)) + 29|0);
 $176 = HEAP8[$175>>0]|0;
 $177 = $176 ^ $174;
 $178 = $172 | $177;
 $179 = ((($0)) + 30|0);
 $180 = HEAP8[$179>>0]|0;
 $181 = ((($1)) + 30|0);
 $182 = HEAP8[$181>>0]|0;
 $183 = $182 ^ $180;
 $184 = $178 | $183;
 $185 = ((($0)) + 31|0);
 $186 = HEAP8[$185>>0]|0;
 $187 = ((($1)) + 31|0);
 $188 = HEAP8[$187>>0]|0;
 $189 = $188 ^ $186;
 $190 = $184 | $189;
 $191 = $190&255;
 $192 = (($191) + 511)|0;
 $193 = $192 >>> 8;
 $194 = $193 & 1;
 $195 = (($194) + -1)|0;
 return ($195|0);
}
function _curve25519_sign($0,$1,$2,$3) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 $3 = $3|0;
 var $$alloca_mul = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $20 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, dest = 0, label = 0;
 var sp = 0, src = 0, stop = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 240|0;
 $4 = sp + 8|0;
 $5 = sp + 168|0;
 $6 = sp;
 $7 = (($3) + 64)|0;
 $8 = (_llvm_stacksave()|0);
 $$alloca_mul = $7;
 $9 = STACKTOP; STACKTOP = STACKTOP + ((((1*$$alloca_mul)|0)+15)&-16)|0;;
 $10 = $6;
 $11 = $10;
 HEAP32[$11>>2] = 0;
 $12 = (($10) + 4)|0;
 $13 = $12;
 HEAP32[$13>>2] = 0;
 dest=$5; src=$1; stop=dest+32|0; do { HEAP8[dest>>0]=HEAP8[src>>0]|0; dest=dest+1|0; src=src+1|0; } while ((dest|0) < (stop|0));
 _crypto_sign_ed25519_ref10_ge_scalarmult_base($4,$1);
 $14 = ((($5)) + 32|0);
 _crypto_sign_ed25519_ref10_ge_p3_tobytes($14,$4);
 $15 = ((($5)) + 63|0);
 $16 = HEAP8[$15>>0]|0;
 $17 = $16 & -128;
 (_crypto_sign_modified($9,$6,$2,$3,0,$5)|0);
 dest=$0; src=$9; stop=dest+64|0; do { HEAP8[dest>>0]=HEAP8[src>>0]|0; dest=dest+1|0; src=src+1|0; } while ((dest|0) < (stop|0));
 $18 = ((($0)) + 63|0);
 $19 = HEAP8[$18>>0]|0;
 $20 = $19 | $17;
 HEAP8[$18>>0] = $20;
 _llvm_stackrestore(($8|0));
 STACKTOP = sp;return;
}
function _curve25519_verify($0,$1,$2,$3) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 $3 = $3|0;
 var $$alloca_mul = 0, $$alloca_mul9 = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $4 = 0, $5 = 0, $6 = 0;
 var $7 = 0, $8 = 0, $9 = 0, dest = 0, label = 0, sp = 0, src = 0, stop = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 288|0;
 $4 = sp + 208|0;
 $5 = sp + 168|0;
 $6 = sp + 128|0;
 $7 = sp + 88|0;
 $8 = sp + 48|0;
 $9 = sp + 8|0;
 $10 = sp + 248|0;
 $11 = sp;
 $12 = (($3) + 64)|0;
 $13 = (_llvm_stacksave()|0);
 $$alloca_mul = $12;
 $14 = STACKTOP; STACKTOP = STACKTOP + ((((1*$$alloca_mul)|0)+15)&-16)|0;;
 $$alloca_mul9 = $12;
 $15 = STACKTOP; STACKTOP = STACKTOP + ((((1*$$alloca_mul9)|0)+15)&-16)|0;;
 _crypto_sign_ed25519_ref10_fe_frombytes($4,$1);
 _crypto_sign_ed25519_ref10_fe_1($8);
 _crypto_sign_ed25519_ref10_fe_sub($5,$4,$8);
 _crypto_sign_ed25519_ref10_fe_add($6,$4,$8);
 _crypto_sign_ed25519_ref10_fe_invert($7,$6);
 _crypto_sign_ed25519_ref10_fe_mul($9,$5,$7);
 _crypto_sign_ed25519_ref10_fe_tobytes($10,$9);
 $16 = ((($0)) + 63|0);
 $17 = HEAP8[$16>>0]|0;
 $18 = $17 & -128;
 $19 = ((($10)) + 31|0);
 $20 = HEAP8[$19>>0]|0;
 $21 = $20 | $18;
 HEAP8[$19>>0] = $21;
 $22 = $17 & 127;
 HEAP8[$16>>0] = $22;
 dest=$14; src=$0; stop=dest+64|0; do { HEAP8[dest>>0]=HEAP8[src>>0]|0; dest=dest+1|0; src=src+1|0; } while ((dest|0) < (stop|0));
 $23 = ((($14)) + 64|0);
 _memcpy(($23|0),($2|0),($3|0))|0;
 $24 = (_crypto_sign_edwards25519sha512batch_ref10_open($15,$11,$14,$12,0,$10)|0);
 _llvm_stackrestore(($13|0));
 STACKTOP = sp;return ($24|0);
}
function _crypto_hash_sha512_ref($0,$1,$2,$3) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 $3 = $3|0;
 var $4 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 208|0;
 $4 = sp;
 _sph_sha512_init($4);
 _sph_sha384($4,$1,$2);
 _sph_sha512_close($4,$0);
 STACKTOP = sp;return 0;
}
function _crypto_sign_modified($0,$1,$2,$3,$4,$5) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 $3 = $3|0;
 $4 = $4|0;
 $5 = $5|0;
 var $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $20 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, dest = 0, label = 0, sp = 0, src = 0, stop = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 320|0;
 $6 = sp + 288|0;
 $7 = sp + 224|0;
 $8 = sp + 160|0;
 $9 = sp;
 $10 = ((($5)) + 32|0);
 dest=$6; src=$10; stop=dest+32|0; do { HEAP8[dest>>0]=HEAP8[src>>0]|0; dest=dest+1|0; src=src+1|0; } while ((dest|0) < (stop|0));
 $11 = (_i64Add(($3|0),($4|0),64,0)|0);
 $12 = tempRet0;
 $13 = $1;
 $14 = $13;
 HEAP32[$14>>2] = $11;
 $15 = (($13) + 4)|0;
 $16 = $15;
 HEAP32[$16>>2] = $12;
 $17 = ((($0)) + 64|0);
 _memmove(($17|0),($2|0),($3|0))|0;
 $18 = ((($0)) + 32|0);
 _memmove(($18|0),($5|0),32)|0;
 $19 = (_i64Add(($3|0),($4|0),32,0)|0);
 $20 = tempRet0;
 (_crypto_hash_sha512_ref($7,$18,$19,$20)|0);
 dest=$18; src=$6; stop=dest+32|0; do { HEAP8[dest>>0]=HEAP8[src>>0]|0; dest=dest+1|0; src=src+1|0; } while ((dest|0) < (stop|0));
 _crypto_sign_ed25519_ref10_sc_reduce($7);
 _crypto_sign_ed25519_ref10_ge_scalarmult_base($9,$7);
 _crypto_sign_ed25519_ref10_ge_p3_tobytes($0,$9);
 (_crypto_hash_sha512_ref($8,$0,$11,$12)|0);
 _crypto_sign_ed25519_ref10_sc_reduce($8);
 _crypto_sign_ed25519_ref10_sc_muladd($18,$8,$5,$7);
 STACKTOP = sp;return 0;
}
function _curve25519_donna($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, dest = 0, label = 0, sp = 0, src = 0, stop = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 368|0;
 $3 = sp + 248|0;
 $4 = sp + 168|0;
 $5 = sp + 80|0;
 $6 = sp;
 $7 = sp + 328|0;
 dest=$7; src=$1; stop=dest+32|0; do { HEAP8[dest>>0]=HEAP8[src>>0]|0; dest=dest+1|0; src=src+1|0; } while ((dest|0) < (stop|0));
 _fexpand($3,$2);
 _cmult($4,$5,$7,$3);
 _crecip($6,$5);
 _fmul($5,$4,$6);
 _fcontract($0,$5);
 STACKTOP = sp;return 0;
}
function _fexpand($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0, $113 = 0, $114 = 0, $115 = 0, $116 = 0, $117 = 0;
 var $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0, $133 = 0, $134 = 0, $135 = 0;
 var $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0, $15 = 0, $150 = 0, $151 = 0, $152 = 0, $153 = 0;
 var $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $159 = 0, $16 = 0, $160 = 0, $161 = 0, $162 = 0, $163 = 0, $164 = 0, $165 = 0, $166 = 0, $167 = 0, $168 = 0, $169 = 0, $17 = 0, $170 = 0, $171 = 0;
 var $172 = 0, $173 = 0, $174 = 0, $175 = 0, $176 = 0, $177 = 0, $178 = 0, $179 = 0, $18 = 0, $180 = 0, $181 = 0, $182 = 0, $183 = 0, $184 = 0, $185 = 0, $186 = 0, $187 = 0, $188 = 0, $189 = 0, $19 = 0;
 var $190 = 0, $191 = 0, $192 = 0, $193 = 0, $194 = 0, $195 = 0, $196 = 0, $197 = 0, $198 = 0, $199 = 0, $2 = 0, $20 = 0, $200 = 0, $201 = 0, $202 = 0, $203 = 0, $204 = 0, $205 = 0, $206 = 0, $207 = 0;
 var $208 = 0, $209 = 0, $21 = 0, $210 = 0, $211 = 0, $212 = 0, $213 = 0, $214 = 0, $215 = 0, $216 = 0, $217 = 0, $218 = 0, $219 = 0, $22 = 0, $220 = 0, $221 = 0, $222 = 0, $223 = 0, $224 = 0, $225 = 0;
 var $226 = 0, $227 = 0, $228 = 0, $229 = 0, $23 = 0, $230 = 0, $231 = 0, $232 = 0, $233 = 0, $234 = 0, $235 = 0, $236 = 0, $237 = 0, $238 = 0, $239 = 0, $24 = 0, $240 = 0, $241 = 0, $242 = 0, $243 = 0;
 var $244 = 0, $245 = 0, $246 = 0, $247 = 0, $248 = 0, $249 = 0, $25 = 0, $250 = 0, $251 = 0, $252 = 0, $253 = 0, $254 = 0, $255 = 0, $256 = 0, $257 = 0, $258 = 0, $259 = 0, $26 = 0, $260 = 0, $261 = 0;
 var $262 = 0, $263 = 0, $264 = 0, $265 = 0, $266 = 0, $267 = 0, $268 = 0, $269 = 0, $27 = 0, $270 = 0, $271 = 0, $272 = 0, $273 = 0, $274 = 0, $275 = 0, $276 = 0, $277 = 0, $278 = 0, $279 = 0, $28 = 0;
 var $280 = 0, $281 = 0, $282 = 0, $283 = 0, $284 = 0, $285 = 0, $286 = 0, $287 = 0, $288 = 0, $289 = 0, $29 = 0, $290 = 0, $291 = 0, $292 = 0, $293 = 0, $294 = 0, $295 = 0, $3 = 0, $30 = 0, $31 = 0;
 var $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $4 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0, $46 = 0, $47 = 0, $48 = 0, $49 = 0, $5 = 0;
 var $50 = 0, $51 = 0, $52 = 0, $53 = 0, $54 = 0, $55 = 0, $56 = 0, $57 = 0, $58 = 0, $59 = 0, $6 = 0, $60 = 0, $61 = 0, $62 = 0, $63 = 0, $64 = 0, $65 = 0, $66 = 0, $67 = 0, $68 = 0;
 var $69 = 0, $7 = 0, $70 = 0, $71 = 0, $72 = 0, $73 = 0, $74 = 0, $75 = 0, $76 = 0, $77 = 0, $78 = 0, $79 = 0, $8 = 0, $80 = 0, $81 = 0, $82 = 0, $83 = 0, $84 = 0, $85 = 0, $86 = 0;
 var $87 = 0, $88 = 0, $89 = 0, $9 = 0, $90 = 0, $91 = 0, $92 = 0, $93 = 0, $94 = 0, $95 = 0, $96 = 0, $97 = 0, $98 = 0, $99 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = HEAP8[$1>>0]|0;
 $3 = $2&255;
 $4 = ((($1)) + 1|0);
 $5 = HEAP8[$4>>0]|0;
 $6 = $5&255;
 $7 = (_bitshift64Shl(($6|0),0,8)|0);
 $8 = tempRet0;
 $9 = $7 | $3;
 $10 = ((($1)) + 2|0);
 $11 = HEAP8[$10>>0]|0;
 $12 = $11&255;
 $13 = (_bitshift64Shl(($12|0),0,16)|0);
 $14 = tempRet0;
 $15 = $9 | $13;
 $16 = $8 | $14;
 $17 = ((($1)) + 3|0);
 $18 = HEAP8[$17>>0]|0;
 $19 = $18&255;
 $20 = (_bitshift64Shl(($19|0),0,24)|0);
 $21 = tempRet0;
 $22 = $20 & 50331648;
 $23 = $15 | $22;
 $24 = $0;
 $25 = $24;
 HEAP32[$25>>2] = $23;
 $26 = (($24) + 4)|0;
 $27 = $26;
 HEAP32[$27>>2] = $16;
 $28 = HEAP8[$17>>0]|0;
 $29 = $28&255;
 $30 = ((($1)) + 4|0);
 $31 = HEAP8[$30>>0]|0;
 $32 = $31&255;
 $33 = (_bitshift64Shl(($32|0),0,8)|0);
 $34 = tempRet0;
 $35 = $33 | $29;
 $36 = ((($1)) + 5|0);
 $37 = HEAP8[$36>>0]|0;
 $38 = $37&255;
 $39 = (_bitshift64Shl(($38|0),0,16)|0);
 $40 = tempRet0;
 $41 = $35 | $39;
 $42 = $34 | $40;
 $43 = ((($1)) + 6|0);
 $44 = HEAP8[$43>>0]|0;
 $45 = $44&255;
 $46 = (_bitshift64Shl(($45|0),0,24)|0);
 $47 = tempRet0;
 $48 = $41 | $46;
 $49 = $42 | $47;
 $50 = (_bitshift64Lshr(($48|0),($49|0),2)|0);
 $51 = tempRet0;
 $52 = $50 & 33554431;
 $53 = ((($0)) + 8|0);
 $54 = $53;
 $55 = $54;
 HEAP32[$55>>2] = $52;
 $56 = (($54) + 4)|0;
 $57 = $56;
 HEAP32[$57>>2] = 0;
 $58 = HEAP8[$43>>0]|0;
 $59 = $58&255;
 $60 = ((($1)) + 7|0);
 $61 = HEAP8[$60>>0]|0;
 $62 = $61&255;
 $63 = (_bitshift64Shl(($62|0),0,8)|0);
 $64 = tempRet0;
 $65 = $63 | $59;
 $66 = ((($1)) + 8|0);
 $67 = HEAP8[$66>>0]|0;
 $68 = $67&255;
 $69 = (_bitshift64Shl(($68|0),0,16)|0);
 $70 = tempRet0;
 $71 = $65 | $69;
 $72 = $64 | $70;
 $73 = ((($1)) + 9|0);
 $74 = HEAP8[$73>>0]|0;
 $75 = $74&255;
 $76 = (_bitshift64Shl(($75|0),0,24)|0);
 $77 = tempRet0;
 $78 = $71 | $76;
 $79 = $72 | $77;
 $80 = (_bitshift64Lshr(($78|0),($79|0),3)|0);
 $81 = tempRet0;
 $82 = $80 & 67108863;
 $83 = ((($0)) + 16|0);
 $84 = $83;
 $85 = $84;
 HEAP32[$85>>2] = $82;
 $86 = (($84) + 4)|0;
 $87 = $86;
 HEAP32[$87>>2] = 0;
 $88 = HEAP8[$73>>0]|0;
 $89 = $88&255;
 $90 = ((($1)) + 10|0);
 $91 = HEAP8[$90>>0]|0;
 $92 = $91&255;
 $93 = (_bitshift64Shl(($92|0),0,8)|0);
 $94 = tempRet0;
 $95 = $93 | $89;
 $96 = ((($1)) + 11|0);
 $97 = HEAP8[$96>>0]|0;
 $98 = $97&255;
 $99 = (_bitshift64Shl(($98|0),0,16)|0);
 $100 = tempRet0;
 $101 = $95 | $99;
 $102 = $94 | $100;
 $103 = ((($1)) + 12|0);
 $104 = HEAP8[$103>>0]|0;
 $105 = $104&255;
 $106 = (_bitshift64Shl(($105|0),0,24)|0);
 $107 = tempRet0;
 $108 = $101 | $106;
 $109 = $102 | $107;
 $110 = (_bitshift64Lshr(($108|0),($109|0),5)|0);
 $111 = tempRet0;
 $112 = $110 & 33554431;
 $113 = ((($0)) + 24|0);
 $114 = $113;
 $115 = $114;
 HEAP32[$115>>2] = $112;
 $116 = (($114) + 4)|0;
 $117 = $116;
 HEAP32[$117>>2] = 0;
 $118 = HEAP8[$103>>0]|0;
 $119 = $118&255;
 $120 = ((($1)) + 13|0);
 $121 = HEAP8[$120>>0]|0;
 $122 = $121&255;
 $123 = (_bitshift64Shl(($122|0),0,8)|0);
 $124 = tempRet0;
 $125 = $123 | $119;
 $126 = ((($1)) + 14|0);
 $127 = HEAP8[$126>>0]|0;
 $128 = $127&255;
 $129 = (_bitshift64Shl(($128|0),0,16)|0);
 $130 = tempRet0;
 $131 = $125 | $129;
 $132 = $124 | $130;
 $133 = ((($1)) + 15|0);
 $134 = HEAP8[$133>>0]|0;
 $135 = $134&255;
 $136 = (_bitshift64Shl(($135|0),0,24)|0);
 $137 = tempRet0;
 $138 = $131 | $136;
 $139 = $132 | $137;
 $140 = (_bitshift64Lshr(($138|0),($139|0),6)|0);
 $141 = tempRet0;
 $142 = $140 & 67108863;
 $143 = ((($0)) + 32|0);
 $144 = $143;
 $145 = $144;
 HEAP32[$145>>2] = $142;
 $146 = (($144) + 4)|0;
 $147 = $146;
 HEAP32[$147>>2] = 0;
 $148 = ((($1)) + 16|0);
 $149 = HEAP8[$148>>0]|0;
 $150 = $149&255;
 $151 = ((($1)) + 17|0);
 $152 = HEAP8[$151>>0]|0;
 $153 = $152&255;
 $154 = (_bitshift64Shl(($153|0),0,8)|0);
 $155 = tempRet0;
 $156 = $154 | $150;
 $157 = ((($1)) + 18|0);
 $158 = HEAP8[$157>>0]|0;
 $159 = $158&255;
 $160 = (_bitshift64Shl(($159|0),0,16)|0);
 $161 = tempRet0;
 $162 = $156 | $160;
 $163 = $155 | $161;
 $164 = ((($1)) + 19|0);
 $165 = HEAP8[$164>>0]|0;
 $166 = $165&255;
 $167 = (_bitshift64Shl(($166|0),0,24)|0);
 $168 = tempRet0;
 $169 = $167 & 16777216;
 $170 = $162 | $169;
 $171 = ((($0)) + 40|0);
 $172 = $171;
 $173 = $172;
 HEAP32[$173>>2] = $170;
 $174 = (($172) + 4)|0;
 $175 = $174;
 HEAP32[$175>>2] = $163;
 $176 = HEAP8[$164>>0]|0;
 $177 = $176&255;
 $178 = ((($1)) + 20|0);
 $179 = HEAP8[$178>>0]|0;
 $180 = $179&255;
 $181 = (_bitshift64Shl(($180|0),0,8)|0);
 $182 = tempRet0;
 $183 = $181 | $177;
 $184 = ((($1)) + 21|0);
 $185 = HEAP8[$184>>0]|0;
 $186 = $185&255;
 $187 = (_bitshift64Shl(($186|0),0,16)|0);
 $188 = tempRet0;
 $189 = $183 | $187;
 $190 = $182 | $188;
 $191 = ((($1)) + 22|0);
 $192 = HEAP8[$191>>0]|0;
 $193 = $192&255;
 $194 = (_bitshift64Shl(($193|0),0,24)|0);
 $195 = tempRet0;
 $196 = $189 | $194;
 $197 = $190 | $195;
 $198 = (_bitshift64Lshr(($196|0),($197|0),1)|0);
 $199 = tempRet0;
 $200 = $198 & 67108863;
 $201 = ((($0)) + 48|0);
 $202 = $201;
 $203 = $202;
 HEAP32[$203>>2] = $200;
 $204 = (($202) + 4)|0;
 $205 = $204;
 HEAP32[$205>>2] = 0;
 $206 = HEAP8[$191>>0]|0;
 $207 = $206&255;
 $208 = ((($1)) + 23|0);
 $209 = HEAP8[$208>>0]|0;
 $210 = $209&255;
 $211 = (_bitshift64Shl(($210|0),0,8)|0);
 $212 = tempRet0;
 $213 = $211 | $207;
 $214 = ((($1)) + 24|0);
 $215 = HEAP8[$214>>0]|0;
 $216 = $215&255;
 $217 = (_bitshift64Shl(($216|0),0,16)|0);
 $218 = tempRet0;
 $219 = $213 | $217;
 $220 = $212 | $218;
 $221 = ((($1)) + 25|0);
 $222 = HEAP8[$221>>0]|0;
 $223 = $222&255;
 $224 = (_bitshift64Shl(($223|0),0,24)|0);
 $225 = tempRet0;
 $226 = $219 | $224;
 $227 = $220 | $225;
 $228 = (_bitshift64Lshr(($226|0),($227|0),3)|0);
 $229 = tempRet0;
 $230 = $228 & 33554431;
 $231 = ((($0)) + 56|0);
 $232 = $231;
 $233 = $232;
 HEAP32[$233>>2] = $230;
 $234 = (($232) + 4)|0;
 $235 = $234;
 HEAP32[$235>>2] = 0;
 $236 = HEAP8[$221>>0]|0;
 $237 = $236&255;
 $238 = ((($1)) + 26|0);
 $239 = HEAP8[$238>>0]|0;
 $240 = $239&255;
 $241 = (_bitshift64Shl(($240|0),0,8)|0);
 $242 = tempRet0;
 $243 = $241 | $237;
 $244 = ((($1)) + 27|0);
 $245 = HEAP8[$244>>0]|0;
 $246 = $245&255;
 $247 = (_bitshift64Shl(($246|0),0,16)|0);
 $248 = tempRet0;
 $249 = $243 | $247;
 $250 = $242 | $248;
 $251 = ((($1)) + 28|0);
 $252 = HEAP8[$251>>0]|0;
 $253 = $252&255;
 $254 = (_bitshift64Shl(($253|0),0,24)|0);
 $255 = tempRet0;
 $256 = $249 | $254;
 $257 = $250 | $255;
 $258 = (_bitshift64Lshr(($256|0),($257|0),4)|0);
 $259 = tempRet0;
 $260 = $258 & 67108863;
 $261 = ((($0)) + 64|0);
 $262 = $261;
 $263 = $262;
 HEAP32[$263>>2] = $260;
 $264 = (($262) + 4)|0;
 $265 = $264;
 HEAP32[$265>>2] = 0;
 $266 = HEAP8[$251>>0]|0;
 $267 = $266&255;
 $268 = ((($1)) + 29|0);
 $269 = HEAP8[$268>>0]|0;
 $270 = $269&255;
 $271 = (_bitshift64Shl(($270|0),0,8)|0);
 $272 = tempRet0;
 $273 = $271 | $267;
 $274 = ((($1)) + 30|0);
 $275 = HEAP8[$274>>0]|0;
 $276 = $275&255;
 $277 = (_bitshift64Shl(($276|0),0,16)|0);
 $278 = tempRet0;
 $279 = $273 | $277;
 $280 = $272 | $278;
 $281 = ((($1)) + 31|0);
 $282 = HEAP8[$281>>0]|0;
 $283 = $282&255;
 $284 = (_bitshift64Shl(($283|0),0,24)|0);
 $285 = tempRet0;
 $286 = $279 | $284;
 $287 = $280 | $285;
 $288 = (_bitshift64Lshr(($286|0),($287|0),6)|0);
 $289 = tempRet0;
 $290 = $288 & 33554431;
 $291 = ((($0)) + 72|0);
 $292 = $291;
 $293 = $292;
 HEAP32[$293>>2] = $290;
 $294 = (($292) + 4)|0;
 $295 = $294;
 HEAP32[$295>>2] = 0;
 return;
}
function _cmult($0,$1,$2,$3) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 $3 = $3|0;
 var $$0104 = 0, $$06994 = 0, $$07093 = 0, $$071103 = 0, $$072102 = 0, $$074101 = 0, $$076100 = 0, $$07899 = 0, $$08098 = 0, $$08297 = 0, $$08496 = 0, $$17392 = 0, $$17392$phi = 0, $$17591 = 0, $$17591$phi = 0, $$17790 = 0, $$17790$phi = 0, $$17989 = 0, $$17989$phi = 0, $$18188 = 0;
 var $$18188$phi = 0, $$18387 = 0, $$18387$phi = 0, $$18586 = 0, $$18586$phi = 0, $$195 = 0, $$195$phi = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $20 = 0, $21 = 0, $22 = 0;
 var $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0, $29 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $4 = 0, $40 = 0, $41 = 0;
 var $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, $exitcond = 0, $exitcond105 = 0, dest = 0, label = 0, sp = 0, src = 0, stop = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 1216|0;
 $4 = sp + 1064|0;
 $5 = sp + 912|0;
 $6 = sp + 760|0;
 $7 = sp + 608|0;
 $8 = sp + 456|0;
 $9 = sp + 304|0;
 $10 = sp + 152|0;
 $11 = sp;
 $12 = ((($5)) + 8|0);
 _memset(($12|0),0,144)|0;
 $13 = $5;
 $14 = $13;
 HEAP32[$14>>2] = 1;
 $15 = (($13) + 4)|0;
 $16 = $15;
 HEAP32[$16>>2] = 0;
 $17 = ((($6)) + 8|0);
 _memset(($17|0),0,144)|0;
 $18 = $6;
 $19 = $18;
 HEAP32[$19>>2] = 1;
 $20 = (($18) + 4)|0;
 $21 = $20;
 HEAP32[$21>>2] = 0;
 _memset(($7|0),0,152)|0;
 _memset(($8|0),0,152)|0;
 $22 = ((($9)) + 8|0);
 _memset(($22|0),0,144)|0;
 $23 = $9;
 $24 = $23;
 HEAP32[$24>>2] = 1;
 $25 = (($23) + 4)|0;
 $26 = $25;
 HEAP32[$26>>2] = 0;
 _memset(($10|0),0,152)|0;
 $27 = ((($11)) + 8|0);
 _memset(($27|0),0,144)|0;
 $28 = $11;
 $29 = $28;
 HEAP32[$29>>2] = 1;
 $30 = (($28) + 4)|0;
 $31 = $30;
 HEAP32[$31>>2] = 0;
 $32 = ((($4)) + 80|0);
 dest=$32; stop=dest+72|0; do { HEAP32[dest>>2]=0|0; dest=dest+4|0; } while ((dest|0) < (stop|0));
 dest=$4; src=$3; stop=dest+80|0; do { HEAP32[dest>>2]=HEAP32[src>>2]|0; dest=dest+4|0; src=src+4|0; } while ((dest|0) < (stop|0));
 $$0104 = $4;$$071103 = 0;$$072102 = $11;$$074101 = $10;$$076100 = $9;$$07899 = $8;$$08098 = $5;$$08297 = $7;$$08496 = $6;
 while(1) {
  $33 = (31 - ($$071103))|0;
  $34 = (($2) + ($33)|0);
  $35 = HEAP8[$34>>0]|0;
  $$06994 = $35;$$07093 = 0;$$17392 = $$072102;$$17591 = $$074101;$$17790 = $$076100;$$17989 = $$07899;$$18188 = $$08098;$$18387 = $$08297;$$18586 = $$08496;$$195 = $$0104;
  while(1) {
   $36 = $$06994&255;
   $37 = $36 >>> 7;
   _swap_conditional($$18586,$$195,$37,0);
   _swap_conditional($$18387,$$18188,$37,0);
   _fmonty($$17591,$$17392,$$17989,$$17790,$$18586,$$18387,$$195,$$18188,$3);
   _swap_conditional($$17591,$$17989,$37,0);
   _swap_conditional($$17392,$$17790,$37,0);
   $38 = $36 << 1;
   $39 = $38&255;
   $40 = (($$07093) + 1)|0;
   $exitcond = ($40|0)==(8);
   if ($exitcond) {
    break;
   } else {
    $$195$phi = $$17989;$$18586$phi = $$17591;$$18387$phi = $$17392;$$18188$phi = $$17790;$$17989$phi = $$195;$$17790$phi = $$18188;$$17591$phi = $$18586;$$17392$phi = $$18387;$$06994 = $39;$$07093 = $40;$$195 = $$195$phi;$$18586 = $$18586$phi;$$18387 = $$18387$phi;$$18188 = $$18188$phi;$$17989 = $$17989$phi;$$17790 = $$17790$phi;$$17591 = $$17591$phi;$$17392 = $$17392$phi;
   }
  }
  $41 = (($$071103) + 1)|0;
  $exitcond105 = ($41|0)==(32);
  if ($exitcond105) {
   break;
  } else {
   $$0104 = $$17989;$$071103 = $41;$$072102 = $$18387;$$074101 = $$18586;$$076100 = $$18188;$$07899 = $$195;$$08098 = $$17790;$$08297 = $$17392;$$08496 = $$17591;
  }
 }
 dest=$0; src=$$17591; stop=dest+80|0; do { HEAP32[dest>>2]=HEAP32[src>>2]|0; dest=dest+4|0; src=src+4|0; } while ((dest|0) < (stop|0));
 dest=$1; src=$$17392; stop=dest+80|0; do { HEAP32[dest>>2]=HEAP32[src>>2]|0; dest=dest+4|0; src=src+4|0; } while ((dest|0) < (stop|0));
 STACKTOP = sp;return;
}
function _crecip($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $$317 = 0, $$416 = 0, $$515 = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0;
 var sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 800|0;
 $2 = sp + 720|0;
 $3 = sp + 640|0;
 $4 = sp + 560|0;
 $5 = sp + 480|0;
 $6 = sp + 400|0;
 $7 = sp + 320|0;
 $8 = sp + 240|0;
 $9 = sp + 160|0;
 $10 = sp + 80|0;
 $11 = sp;
 _fsquare($2,$1);
 _fsquare($11,$2);
 _fsquare($10,$11);
 _fmul($3,$10,$1);
 _fmul($4,$3,$2);
 _fsquare($10,$4);
 _fmul($5,$10,$3);
 _fsquare($10,$5);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fmul($6,$10,$5);
 _fsquare($10,$6);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fmul($7,$11,$6);
 _fsquare($10,$7);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fmul($10,$11,$7);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fmul($8,$10,$6);
 _fsquare($10,$8);
 _fsquare($11,$10);
 $$317 = 2;
 while(1) {
  _fsquare($10,$11);
  _fsquare($11,$10);
  $12 = (($$317) + 2)|0;
  $13 = ($$317|0)<(48);
  if ($13) {
   $$317 = $12;
  } else {
   break;
  }
 }
 _fmul($9,$11,$8);
 _fsquare($11,$9);
 _fsquare($10,$11);
 $$416 = 2;
 while(1) {
  _fsquare($11,$10);
  _fsquare($10,$11);
  $14 = (($$416) + 2)|0;
  $15 = ($$416|0)<(98);
  if ($15) {
   $$416 = $14;
  } else {
   break;
  }
 }
 _fmul($11,$10,$9);
 _fsquare($10,$11);
 _fsquare($11,$10);
 $$515 = 2;
 while(1) {
  _fsquare($10,$11);
  _fsquare($11,$10);
  $16 = (($$515) + 2)|0;
  $17 = ($$515|0)<(48);
  if ($17) {
   $$515 = $16;
  } else {
   break;
  }
 }
 _fmul($10,$11,$8);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fsquare($10,$11);
 _fsquare($11,$10);
 _fmul($0,$11,$4);
 STACKTOP = sp;return;
}
function _fmul($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var $3 = 0, dest = 0, label = 0, sp = 0, src = 0, stop = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 160|0;
 $3 = sp;
 _fproduct($3,$1,$2);
 _freduce_degree($3);
 _freduce_coefficients($3);
 dest=$0; src=$3; stop=dest+80|0; do { HEAP32[dest>>2]=HEAP32[src>>2]|0; dest=dest+4|0; src=src+4|0; } while ((dest|0) < (stop|0));
 STACKTOP = sp;return;
}
function _fcontract($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $$0135154 = 0, $$1136 = 0, $$3155 = 0, $$promoted = 0, $$promoted168 = 0, $$promoted170 = 0, $$promoted172 = 0, $$promoted174 = 0, $$promoted176 = 0, $$promoted178 = 0, $$promoted180 = 0, $$promoted182 = 0, $$promoted184 = 0, $$sink149 = 0, $$sink149$1 = 0, $$sink149$1$1 = 0, $$sink149$1204 = 0, $$sink149$2 = 0, $$sink149$2$1 = 0, $$sink149$3 = 0;
 var $$sink149$3$1 = 0, $$sink149$4 = 0, $$sink149$4$1 = 0, $$sink149$5 = 0, $$sink149$5$1 = 0, $$sink149$6 = 0, $$sink149$6$1 = 0, $$sink149$7 = 0, $$sink149$7$1 = 0, $$sink149$8 = 0, $$sink149$8$1 = 0, $$sink3 = 0, $$sink3$1 = 0, $$sink3$2 = 0, $$sink3$3 = 0, $$sink3$4 = 0, $$sink3$5 = 0, $$sink3$6 = 0, $$sink3$7 = 0, $$sink3$8 = 0;
 var $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0, $113 = 0, $114 = 0, $115 = 0, $116 = 0, $117 = 0;
 var $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0, $133 = 0, $134 = 0, $135 = 0;
 var $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0, $15 = 0, $150 = 0, $151 = 0, $152 = 0, $153 = 0;
 var $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $159 = 0, $16 = 0, $160 = 0, $161 = 0, $162 = 0, $163 = 0, $164 = 0, $165 = 0, $166 = 0, $167 = 0, $168 = 0, $169 = 0, $17 = 0, $170 = 0, $171 = 0;
 var $172 = 0, $173 = 0, $174 = 0, $175 = 0, $176 = 0, $177 = 0, $178 = 0, $179 = 0, $18 = 0, $180 = 0, $181 = 0, $182 = 0, $183 = 0, $184 = 0, $185 = 0, $186 = 0, $187 = 0, $188 = 0, $189 = 0, $19 = 0;
 var $190 = 0, $191 = 0, $192 = 0, $193 = 0, $194 = 0, $195 = 0, $196 = 0, $197 = 0, $198 = 0, $199 = 0, $2 = 0, $20 = 0, $200 = 0, $201 = 0, $202 = 0, $203 = 0, $204 = 0, $205 = 0, $206 = 0, $207 = 0;
 var $208 = 0, $209 = 0, $21 = 0, $210 = 0, $211 = 0, $212 = 0, $213 = 0, $214 = 0, $215 = 0, $216 = 0, $217 = 0, $218 = 0, $219 = 0, $22 = 0, $220 = 0, $221 = 0, $222 = 0, $223 = 0, $224 = 0, $225 = 0;
 var $226 = 0, $227 = 0, $228 = 0, $229 = 0, $23 = 0, $230 = 0, $231 = 0, $232 = 0, $233 = 0, $234 = 0, $235 = 0, $236 = 0, $237 = 0, $238 = 0, $239 = 0, $24 = 0, $240 = 0, $241 = 0, $242 = 0, $243 = 0;
 var $244 = 0, $245 = 0, $246 = 0, $247 = 0, $248 = 0, $249 = 0, $25 = 0, $250 = 0, $251 = 0, $252 = 0, $253 = 0, $254 = 0, $255 = 0, $256 = 0, $257 = 0, $258 = 0, $259 = 0, $26 = 0, $260 = 0, $261 = 0;
 var $262 = 0, $263 = 0, $264 = 0, $265 = 0, $266 = 0, $267 = 0, $268 = 0, $269 = 0, $27 = 0, $270 = 0, $271 = 0, $272 = 0, $273 = 0, $274 = 0, $275 = 0, $276 = 0, $277 = 0, $278 = 0, $279 = 0, $28 = 0;
 var $280 = 0, $281 = 0, $282 = 0, $283 = 0, $284 = 0, $285 = 0, $286 = 0, $287 = 0, $288 = 0, $289 = 0, $29 = 0, $290 = 0, $291 = 0, $292 = 0, $293 = 0, $294 = 0, $295 = 0, $296 = 0, $297 = 0, $298 = 0;
 var $299 = 0, $3 = 0, $30 = 0, $300 = 0, $301 = 0, $302 = 0, $303 = 0, $304 = 0, $305 = 0, $306 = 0, $307 = 0, $308 = 0, $309 = 0, $31 = 0, $310 = 0, $311 = 0, $312 = 0, $313 = 0, $314 = 0, $315 = 0;
 var $316 = 0, $317 = 0, $318 = 0, $319 = 0, $32 = 0, $320 = 0, $321 = 0, $322 = 0, $323 = 0, $324 = 0, $325 = 0, $326 = 0, $327 = 0, $328 = 0, $329 = 0, $33 = 0, $330 = 0, $331 = 0, $332 = 0, $333 = 0;
 var $334 = 0, $335 = 0, $336 = 0, $337 = 0, $338 = 0, $339 = 0, $34 = 0, $340 = 0, $341 = 0, $342 = 0, $343 = 0, $344 = 0, $345 = 0, $346 = 0, $347 = 0, $348 = 0, $349 = 0, $35 = 0, $350 = 0, $351 = 0;
 var $352 = 0, $353 = 0, $354 = 0, $355 = 0, $356 = 0, $357 = 0, $358 = 0, $359 = 0, $36 = 0, $360 = 0, $361 = 0, $362 = 0, $363 = 0, $364 = 0, $365 = 0, $366 = 0, $367 = 0, $368 = 0, $369 = 0, $37 = 0;
 var $370 = 0, $371 = 0, $372 = 0, $373 = 0, $374 = 0, $375 = 0, $376 = 0, $377 = 0, $378 = 0, $379 = 0, $38 = 0, $380 = 0, $381 = 0, $382 = 0, $383 = 0, $384 = 0, $385 = 0, $386 = 0, $387 = 0, $388 = 0;
 var $389 = 0, $39 = 0, $390 = 0, $391 = 0, $392 = 0, $393 = 0, $394 = 0, $395 = 0, $396 = 0, $397 = 0, $398 = 0, $399 = 0, $4 = 0, $40 = 0, $400 = 0, $401 = 0, $402 = 0, $403 = 0, $404 = 0, $405 = 0;
 var $406 = 0, $407 = 0, $408 = 0, $409 = 0, $41 = 0, $410 = 0, $411 = 0, $412 = 0, $413 = 0, $414 = 0, $415 = 0, $416 = 0, $417 = 0, $418 = 0, $419 = 0, $42 = 0, $420 = 0, $421 = 0, $422 = 0, $423 = 0;
 var $424 = 0, $425 = 0, $426 = 0, $427 = 0, $428 = 0, $429 = 0, $43 = 0, $430 = 0, $431 = 0, $432 = 0, $433 = 0, $434 = 0, $435 = 0, $436 = 0, $437 = 0, $438 = 0, $439 = 0, $44 = 0, $440 = 0, $441 = 0;
 var $442 = 0, $443 = 0, $444 = 0, $445 = 0, $446 = 0, $447 = 0, $448 = 0, $449 = 0, $45 = 0, $450 = 0, $451 = 0, $452 = 0, $453 = 0, $454 = 0, $455 = 0, $456 = 0, $457 = 0, $458 = 0, $459 = 0, $46 = 0;
 var $460 = 0, $461 = 0, $462 = 0, $463 = 0, $464 = 0, $465 = 0, $466 = 0, $467 = 0, $468 = 0, $469 = 0, $47 = 0, $470 = 0, $471 = 0, $472 = 0, $473 = 0, $474 = 0, $475 = 0, $476 = 0, $477 = 0, $478 = 0;
 var $479 = 0, $48 = 0, $480 = 0, $481 = 0, $482 = 0, $483 = 0, $484 = 0, $485 = 0, $486 = 0, $487 = 0, $488 = 0, $489 = 0, $49 = 0, $490 = 0, $491 = 0, $492 = 0, $493 = 0, $494 = 0, $495 = 0, $496 = 0;
 var $497 = 0, $498 = 0, $499 = 0, $5 = 0, $50 = 0, $500 = 0, $501 = 0, $502 = 0, $503 = 0, $504 = 0, $505 = 0, $506 = 0, $507 = 0, $508 = 0, $509 = 0, $51 = 0, $510 = 0, $511 = 0, $512 = 0, $513 = 0;
 var $514 = 0, $515 = 0, $516 = 0, $517 = 0, $518 = 0, $519 = 0, $52 = 0, $520 = 0, $521 = 0, $522 = 0, $523 = 0, $524 = 0, $53 = 0, $54 = 0, $55 = 0, $56 = 0, $57 = 0, $58 = 0, $59 = 0, $6 = 0;
 var $60 = 0, $61 = 0, $62 = 0, $63 = 0, $64 = 0, $65 = 0, $66 = 0, $67 = 0, $68 = 0, $69 = 0, $7 = 0, $70 = 0, $71 = 0, $72 = 0, $73 = 0, $74 = 0, $75 = 0, $76 = 0, $77 = 0, $78 = 0;
 var $79 = 0, $8 = 0, $80 = 0, $81 = 0, $82 = 0, $83 = 0, $84 = 0, $85 = 0, $86 = 0, $87 = 0, $88 = 0, $89 = 0, $9 = 0, $90 = 0, $91 = 0, $92 = 0, $93 = 0, $94 = 0, $95 = 0, $96 = 0;
 var $97 = 0, $98 = 0, $99 = 0, $exitcond = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 48|0;
 $2 = sp;
 $3 = $1;
 $4 = $3;
 $5 = HEAP32[$4>>2]|0;
 $6 = (($3) + 4)|0;
 $7 = $6;
 $8 = HEAP32[$7>>2]|0;
 HEAP32[$2>>2] = $5;
 $9 = ((($1)) + 8|0);
 $10 = $9;
 $11 = $10;
 $12 = HEAP32[$11>>2]|0;
 $13 = (($10) + 4)|0;
 $14 = $13;
 $15 = HEAP32[$14>>2]|0;
 $16 = ((($2)) + 4|0);
 HEAP32[$16>>2] = $12;
 $17 = ((($1)) + 16|0);
 $18 = $17;
 $19 = $18;
 $20 = HEAP32[$19>>2]|0;
 $21 = (($18) + 4)|0;
 $22 = $21;
 $23 = HEAP32[$22>>2]|0;
 $24 = ((($2)) + 8|0);
 HEAP32[$24>>2] = $20;
 $25 = ((($1)) + 24|0);
 $26 = $25;
 $27 = $26;
 $28 = HEAP32[$27>>2]|0;
 $29 = (($26) + 4)|0;
 $30 = $29;
 $31 = HEAP32[$30>>2]|0;
 $32 = ((($2)) + 12|0);
 HEAP32[$32>>2] = $28;
 $33 = ((($1)) + 32|0);
 $34 = $33;
 $35 = $34;
 $36 = HEAP32[$35>>2]|0;
 $37 = (($34) + 4)|0;
 $38 = $37;
 $39 = HEAP32[$38>>2]|0;
 $40 = ((($2)) + 16|0);
 HEAP32[$40>>2] = $36;
 $41 = ((($1)) + 40|0);
 $42 = $41;
 $43 = $42;
 $44 = HEAP32[$43>>2]|0;
 $45 = (($42) + 4)|0;
 $46 = $45;
 $47 = HEAP32[$46>>2]|0;
 $48 = ((($2)) + 20|0);
 HEAP32[$48>>2] = $44;
 $49 = ((($1)) + 48|0);
 $50 = $49;
 $51 = $50;
 $52 = HEAP32[$51>>2]|0;
 $53 = (($50) + 4)|0;
 $54 = $53;
 $55 = HEAP32[$54>>2]|0;
 $56 = ((($2)) + 24|0);
 HEAP32[$56>>2] = $52;
 $57 = ((($1)) + 56|0);
 $58 = $57;
 $59 = $58;
 $60 = HEAP32[$59>>2]|0;
 $61 = (($58) + 4)|0;
 $62 = $61;
 $63 = HEAP32[$62>>2]|0;
 $64 = ((($2)) + 28|0);
 HEAP32[$64>>2] = $60;
 $65 = ((($1)) + 64|0);
 $66 = $65;
 $67 = $66;
 $68 = HEAP32[$67>>2]|0;
 $69 = (($66) + 4)|0;
 $70 = $69;
 $71 = HEAP32[$70>>2]|0;
 $72 = ((($2)) + 32|0);
 HEAP32[$72>>2] = $68;
 $73 = ((($1)) + 72|0);
 $74 = $73;
 $75 = $74;
 $76 = HEAP32[$75>>2]|0;
 $77 = (($74) + 4)|0;
 $78 = $77;
 $79 = HEAP32[$78>>2]|0;
 $80 = ((($2)) + 36|0);
 HEAP32[$80>>2] = $76;
 $81 = ((($2)) + 4|0);
 $82 = ((($2)) + 8|0);
 $83 = ((($2)) + 12|0);
 $84 = ((($2)) + 16|0);
 $85 = ((($2)) + 20|0);
 $86 = ((($2)) + 24|0);
 $87 = ((($2)) + 28|0);
 $88 = ((($2)) + 32|0);
 $89 = ((($2)) + 36|0);
 $$promoted = HEAP32[$2>>2]|0;
 $$promoted184 = HEAP32[$89>>2]|0;
 $$promoted182 = HEAP32[$88>>2]|0;
 $$promoted180 = HEAP32[$87>>2]|0;
 $$promoted178 = HEAP32[$86>>2]|0;
 $$promoted176 = HEAP32[$85>>2]|0;
 $$promoted174 = HEAP32[$84>>2]|0;
 $$promoted172 = HEAP32[$83>>2]|0;
 $$promoted170 = HEAP32[$82>>2]|0;
 $$promoted168 = HEAP32[$81>>2]|0;
 $90 = $$promoted >> 31;
 $91 = $90 & $$promoted;
 $$sink149 = $91 >> 26;
 $92 = (0 - ($$sink149))|0;
 $93 = $92 << 26;
 $94 = (($93) + ($$promoted))|0;
 $95 = (($$sink149) + ($$promoted168))|0;
 $96 = $95 >> 31;
 $97 = $96 & $95;
 $$sink149$1 = $97 >> 25;
 $98 = (0 - ($$sink149$1))|0;
 $99 = $98 << 25;
 $100 = (($99) + ($95))|0;
 $101 = (($$sink149$1) + ($$promoted170))|0;
 $102 = $101 >> 31;
 $103 = $102 & $101;
 $$sink149$2 = $103 >> 26;
 $104 = (0 - ($$sink149$2))|0;
 $105 = $104 << 26;
 $106 = (($105) + ($101))|0;
 $107 = (($$sink149$2) + ($$promoted172))|0;
 $108 = $107 >> 31;
 $109 = $108 & $107;
 $$sink149$3 = $109 >> 25;
 $110 = (0 - ($$sink149$3))|0;
 $111 = $110 << 25;
 $112 = (($111) + ($107))|0;
 $113 = (($$sink149$3) + ($$promoted174))|0;
 $114 = $113 >> 31;
 $115 = $114 & $113;
 $$sink149$4 = $115 >> 26;
 $116 = (0 - ($$sink149$4))|0;
 $117 = $116 << 26;
 $118 = (($117) + ($113))|0;
 $119 = (($$sink149$4) + ($$promoted176))|0;
 $120 = $119 >> 31;
 $121 = $120 & $119;
 $$sink149$5 = $121 >> 25;
 $122 = (0 - ($$sink149$5))|0;
 $123 = $122 << 25;
 $124 = (($123) + ($119))|0;
 $125 = (($$sink149$5) + ($$promoted178))|0;
 $126 = $125 >> 31;
 $127 = $126 & $125;
 $$sink149$6 = $127 >> 26;
 $128 = (0 - ($$sink149$6))|0;
 $129 = $128 << 26;
 $130 = (($129) + ($125))|0;
 $131 = (($$sink149$6) + ($$promoted180))|0;
 $132 = $131 >> 31;
 $133 = $132 & $131;
 $$sink149$7 = $133 >> 25;
 $134 = (0 - ($$sink149$7))|0;
 $135 = $134 << 25;
 $136 = (($135) + ($131))|0;
 $137 = (($$sink149$7) + ($$promoted182))|0;
 $138 = $137 >> 31;
 $139 = $138 & $137;
 $$sink149$8 = $139 >> 26;
 $140 = (0 - ($$sink149$8))|0;
 $141 = $140 << 26;
 $142 = (($141) + ($137))|0;
 $143 = (($$sink149$8) + ($$promoted184))|0;
 $144 = $143 >> 31;
 $145 = $144 & $143;
 $146 = $145 >> 25;
 $147 = Math_imul($146, -33554432)|0;
 $148 = (($147) + ($143))|0;
 $149 = ($146*19)|0;
 $150 = (($149) + ($94))|0;
 $151 = $150 >> 31;
 $152 = $151 & $150;
 $$sink149$1204 = $152 >> 26;
 $153 = (0 - ($$sink149$1204))|0;
 $154 = $153 << 26;
 $155 = (($154) + ($150))|0;
 $156 = (($$sink149$1204) + ($100))|0;
 $157 = $156 >> 31;
 $158 = $157 & $156;
 $$sink149$1$1 = $158 >> 25;
 $159 = (0 - ($$sink149$1$1))|0;
 $160 = $159 << 25;
 $161 = (($160) + ($156))|0;
 $162 = (($$sink149$1$1) + ($106))|0;
 $163 = $162 >> 31;
 $164 = $163 & $162;
 $$sink149$2$1 = $164 >> 26;
 $165 = (0 - ($$sink149$2$1))|0;
 $166 = $165 << 26;
 $167 = (($166) + ($162))|0;
 $168 = (($$sink149$2$1) + ($112))|0;
 $169 = $168 >> 31;
 $170 = $169 & $168;
 $$sink149$3$1 = $170 >> 25;
 $171 = (0 - ($$sink149$3$1))|0;
 $172 = $171 << 25;
 $173 = (($172) + ($168))|0;
 $174 = (($$sink149$3$1) + ($118))|0;
 $175 = $174 >> 31;
 $176 = $175 & $174;
 $$sink149$4$1 = $176 >> 26;
 $177 = (0 - ($$sink149$4$1))|0;
 $178 = $177 << 26;
 $179 = (($178) + ($174))|0;
 $180 = (($$sink149$4$1) + ($124))|0;
 $181 = $180 >> 31;
 $182 = $181 & $180;
 $$sink149$5$1 = $182 >> 25;
 $183 = (0 - ($$sink149$5$1))|0;
 $184 = $183 << 25;
 $185 = (($184) + ($180))|0;
 $186 = (($$sink149$5$1) + ($130))|0;
 $187 = $186 >> 31;
 $188 = $187 & $186;
 $$sink149$6$1 = $188 >> 26;
 $189 = (0 - ($$sink149$6$1))|0;
 $190 = $189 << 26;
 $191 = (($190) + ($186))|0;
 $192 = (($$sink149$6$1) + ($136))|0;
 $193 = $192 >> 31;
 $194 = $193 & $192;
 $$sink149$7$1 = $194 >> 25;
 $195 = (0 - ($$sink149$7$1))|0;
 $196 = $195 << 25;
 $197 = (($196) + ($192))|0;
 $198 = (($$sink149$7$1) + ($142))|0;
 $199 = $198 >> 31;
 $200 = $199 & $198;
 $$sink149$8$1 = $200 >> 26;
 $201 = (0 - ($$sink149$8$1))|0;
 $202 = $201 << 26;
 $203 = (($202) + ($198))|0;
 $204 = (($$sink149$8$1) + ($148))|0;
 $205 = $204 >> 31;
 $206 = $205 & $204;
 $207 = $206 >> 25;
 $208 = Math_imul($207, -33554432)|0;
 $209 = (($208) + ($204))|0;
 $210 = ($207*19)|0;
 $211 = (($210) + ($155))|0;
 HEAP32[$2>>2] = $211;
 HEAP32[$81>>2] = $161;
 HEAP32[$82>>2] = $167;
 HEAP32[$83>>2] = $173;
 HEAP32[$84>>2] = $179;
 HEAP32[$85>>2] = $185;
 HEAP32[$86>>2] = $191;
 HEAP32[$87>>2] = $197;
 HEAP32[$88>>2] = $203;
 HEAP32[$89>>2] = $209;
 $212 = HEAP32[$2>>2]|0;
 $213 = $212 >> 31;
 $214 = $213 & $212;
 $215 = $214 >> 26;
 $216 = Math_imul($215, -67108864)|0;
 $217 = (($216) + ($212))|0;
 HEAP32[$2>>2] = $217;
 $218 = ((($2)) + 4|0);
 $219 = HEAP32[$218>>2]|0;
 $220 = (($215) + ($219))|0;
 HEAP32[$218>>2] = $220;
 $221 = ((($2)) + 36|0);
 $222 = HEAP32[$2>>2]|0;
 $223 = $222 >> 26;
 $224 = $222 & 67108863;
 HEAP32[$2>>2] = $224;
 $225 = ((($2)) + 4|0);
 $226 = HEAP32[$225>>2]|0;
 $227 = (($226) + ($223))|0;
 $228 = ((($2)) + 4|0);
 $229 = $227 >> 25;
 $230 = $227 & 33554431;
 HEAP32[$228>>2] = $230;
 $231 = ((($2)) + 8|0);
 $232 = HEAP32[$231>>2]|0;
 $233 = (($232) + ($229))|0;
 $234 = ((($2)) + 8|0);
 $235 = $233 >> 26;
 $236 = $233 & 67108863;
 HEAP32[$234>>2] = $236;
 $237 = ((($2)) + 12|0);
 $238 = HEAP32[$237>>2]|0;
 $239 = (($238) + ($235))|0;
 $240 = ((($2)) + 12|0);
 $241 = $239 >> 25;
 $242 = $239 & 33554431;
 HEAP32[$240>>2] = $242;
 $243 = ((($2)) + 16|0);
 $244 = HEAP32[$243>>2]|0;
 $245 = (($244) + ($241))|0;
 $246 = ((($2)) + 16|0);
 $247 = $245 >> 26;
 $248 = $245 & 67108863;
 HEAP32[$246>>2] = $248;
 $249 = ((($2)) + 20|0);
 $250 = HEAP32[$249>>2]|0;
 $251 = (($250) + ($247))|0;
 $252 = ((($2)) + 20|0);
 $253 = $251 >> 25;
 $254 = $251 & 33554431;
 HEAP32[$252>>2] = $254;
 $255 = ((($2)) + 24|0);
 $256 = HEAP32[$255>>2]|0;
 $257 = (($256) + ($253))|0;
 $258 = ((($2)) + 24|0);
 $259 = $257 >> 26;
 $260 = $257 & 67108863;
 HEAP32[$258>>2] = $260;
 $261 = ((($2)) + 28|0);
 $262 = HEAP32[$261>>2]|0;
 $263 = (($262) + ($259))|0;
 $264 = ((($2)) + 28|0);
 $265 = $263 >> 25;
 $266 = $263 & 33554431;
 HEAP32[$264>>2] = $266;
 $267 = ((($2)) + 32|0);
 $268 = HEAP32[$267>>2]|0;
 $269 = (($268) + ($265))|0;
 $270 = ((($2)) + 32|0);
 $271 = $269 >> 26;
 $272 = $269 & 67108863;
 HEAP32[$270>>2] = $272;
 $273 = ((($2)) + 36|0);
 $274 = HEAP32[$273>>2]|0;
 $275 = (($274) + ($271))|0;
 $276 = $275 >> 25;
 $277 = $275 & 33554431;
 HEAP32[$221>>2] = $277;
 $278 = ($276*19)|0;
 $279 = HEAP32[$2>>2]|0;
 $280 = (($279) + ($278))|0;
 $281 = $280 >> 26;
 $282 = $280 & 67108863;
 HEAP32[$2>>2] = $282;
 $283 = ((($2)) + 4|0);
 $284 = HEAP32[$283>>2]|0;
 $285 = (($284) + ($281))|0;
 $286 = ((($2)) + 4|0);
 $287 = $285 >> 25;
 $288 = $285 & 33554431;
 HEAP32[$286>>2] = $288;
 $289 = ((($2)) + 8|0);
 $290 = HEAP32[$289>>2]|0;
 $291 = (($290) + ($287))|0;
 $292 = ((($2)) + 8|0);
 $293 = $291 >> 26;
 $294 = $291 & 67108863;
 HEAP32[$292>>2] = $294;
 $295 = ((($2)) + 12|0);
 $296 = HEAP32[$295>>2]|0;
 $297 = (($296) + ($293))|0;
 $298 = ((($2)) + 12|0);
 $299 = $297 >> 25;
 $300 = $297 & 33554431;
 HEAP32[$298>>2] = $300;
 $301 = ((($2)) + 16|0);
 $302 = HEAP32[$301>>2]|0;
 $303 = (($302) + ($299))|0;
 $304 = ((($2)) + 16|0);
 $305 = $303 >> 26;
 $306 = $303 & 67108863;
 HEAP32[$304>>2] = $306;
 $307 = ((($2)) + 20|0);
 $308 = HEAP32[$307>>2]|0;
 $309 = (($308) + ($305))|0;
 $310 = ((($2)) + 20|0);
 $311 = $309 >> 25;
 $312 = $309 & 33554431;
 HEAP32[$310>>2] = $312;
 $313 = ((($2)) + 24|0);
 $314 = HEAP32[$313>>2]|0;
 $315 = (($314) + ($311))|0;
 $316 = ((($2)) + 24|0);
 $317 = $315 >> 26;
 $318 = $315 & 67108863;
 HEAP32[$316>>2] = $318;
 $319 = ((($2)) + 28|0);
 $320 = HEAP32[$319>>2]|0;
 $321 = (($320) + ($317))|0;
 $322 = ((($2)) + 28|0);
 $323 = $321 >> 25;
 $324 = $321 & 33554431;
 HEAP32[$322>>2] = $324;
 $325 = ((($2)) + 32|0);
 $326 = HEAP32[$325>>2]|0;
 $327 = (($326) + ($323))|0;
 $328 = ((($2)) + 32|0);
 $329 = $327 >> 26;
 $330 = $327 & 67108863;
 HEAP32[$328>>2] = $330;
 $331 = ((($2)) + 36|0);
 $332 = HEAP32[$331>>2]|0;
 $333 = (($332) + ($329))|0;
 $334 = $333 >> 25;
 $335 = $333 & 33554431;
 HEAP32[$221>>2] = $335;
 $336 = ($334*19)|0;
 $337 = HEAP32[$2>>2]|0;
 $338 = (($337) + ($336))|0;
 HEAP32[$2>>2] = $338;
 $339 = (_s32_gte($338)|0);
 $$0135154 = $339;$$3155 = 1;
 while(1) {
  $340 = (($2) + ($$3155<<2)|0);
  $341 = HEAP32[$340>>2]|0;
  $342 = $$3155 << 25;
  $343 = $342 & 33554432;
  $344 = $343 ^ 67108863;
  $345 = (_s32_eq($341,$344)|0);
  $$1136 = $345 & $$0135154;
  $346 = (($$3155) + 1)|0;
  $exitcond = ($346|0)==(10);
  if ($exitcond) {
   break;
  } else {
   $$0135154 = $$1136;$$3155 = $346;
  }
 }
 $347 = $$1136 & 67108845;
 $348 = HEAP32[$2>>2]|0;
 $349 = (($348) - ($347))|0;
 HEAP32[$2>>2] = $349;
 $$sink3 = $$1136 & 33554431;
 $350 = ((($2)) + 4|0);
 $351 = HEAP32[$350>>2]|0;
 $352 = (($351) - ($$sink3))|0;
 HEAP32[$350>>2] = $352;
 $$sink3$1 = $$1136 & 67108863;
 $353 = ((($2)) + 8|0);
 $354 = HEAP32[$353>>2]|0;
 $355 = (($354) - ($$sink3$1))|0;
 HEAP32[$353>>2] = $355;
 $$sink3$2 = $$1136 & 33554431;
 $356 = ((($2)) + 12|0);
 $357 = HEAP32[$356>>2]|0;
 $358 = (($357) - ($$sink3$2))|0;
 HEAP32[$356>>2] = $358;
 $$sink3$3 = $$1136 & 67108863;
 $359 = ((($2)) + 16|0);
 $360 = HEAP32[$359>>2]|0;
 $361 = (($360) - ($$sink3$3))|0;
 HEAP32[$359>>2] = $361;
 $$sink3$4 = $$1136 & 33554431;
 $362 = ((($2)) + 20|0);
 $363 = HEAP32[$362>>2]|0;
 $364 = (($363) - ($$sink3$4))|0;
 HEAP32[$362>>2] = $364;
 $$sink3$5 = $$1136 & 67108863;
 $365 = ((($2)) + 24|0);
 $366 = HEAP32[$365>>2]|0;
 $367 = (($366) - ($$sink3$5))|0;
 HEAP32[$365>>2] = $367;
 $$sink3$6 = $$1136 & 33554431;
 $368 = ((($2)) + 28|0);
 $369 = HEAP32[$368>>2]|0;
 $370 = (($369) - ($$sink3$6))|0;
 HEAP32[$368>>2] = $370;
 $$sink3$7 = $$1136 & 67108863;
 $371 = ((($2)) + 32|0);
 $372 = HEAP32[$371>>2]|0;
 $373 = (($372) - ($$sink3$7))|0;
 HEAP32[$371>>2] = $373;
 $$sink3$8 = $$1136 & 33554431;
 $374 = ((($2)) + 36|0);
 $375 = HEAP32[$374>>2]|0;
 $376 = (($375) - ($$sink3$8))|0;
 HEAP32[$374>>2] = $376;
 $377 = HEAP32[$218>>2]|0;
 $378 = $377 << 2;
 HEAP32[$218>>2] = $378;
 $379 = ((($2)) + 8|0);
 $380 = HEAP32[$379>>2]|0;
 $381 = $380 << 3;
 HEAP32[$379>>2] = $381;
 $382 = ((($2)) + 12|0);
 $383 = HEAP32[$382>>2]|0;
 $384 = $383 << 5;
 HEAP32[$382>>2] = $384;
 $385 = ((($2)) + 16|0);
 $386 = HEAP32[$385>>2]|0;
 $387 = $386 << 6;
 HEAP32[$385>>2] = $387;
 $388 = ((($2)) + 24|0);
 $389 = HEAP32[$388>>2]|0;
 $390 = $389 << 1;
 HEAP32[$388>>2] = $390;
 $391 = ((($2)) + 28|0);
 $392 = HEAP32[$391>>2]|0;
 $393 = $392 << 3;
 HEAP32[$391>>2] = $393;
 $394 = ((($2)) + 32|0);
 $395 = HEAP32[$394>>2]|0;
 $396 = $395 << 4;
 HEAP32[$394>>2] = $396;
 $397 = ((($2)) + 36|0);
 $398 = HEAP32[$397>>2]|0;
 $399 = $398 << 6;
 HEAP32[$397>>2] = $399;
 $400 = ((($0)) + 16|0);
 HEAP8[$400>>0] = 0;
 $401 = HEAP32[$2>>2]|0;
 $402 = $401&255;
 HEAP8[$0>>0] = $402;
 $403 = $401 >>> 8;
 $404 = $403&255;
 $405 = ((($0)) + 1|0);
 HEAP8[$405>>0] = $404;
 $406 = HEAP32[$2>>2]|0;
 $407 = $406 >>> 16;
 $408 = $407&255;
 $409 = ((($0)) + 2|0);
 HEAP8[$409>>0] = $408;
 $410 = $406 >>> 24;
 $411 = ((($0)) + 3|0);
 $412 = HEAP32[$218>>2]|0;
 $413 = $412 | $410;
 $414 = $413&255;
 HEAP8[$411>>0] = $414;
 $415 = $412 >>> 8;
 $416 = $415&255;
 $417 = ((($0)) + 4|0);
 HEAP8[$417>>0] = $416;
 $418 = HEAP32[$218>>2]|0;
 $419 = $418 >>> 16;
 $420 = $419&255;
 $421 = ((($0)) + 5|0);
 HEAP8[$421>>0] = $420;
 $422 = $418 >>> 24;
 $423 = ((($0)) + 6|0);
 $424 = HEAP32[$379>>2]|0;
 $425 = $424 | $422;
 $426 = $425&255;
 HEAP8[$423>>0] = $426;
 $427 = $424 >>> 8;
 $428 = $427&255;
 $429 = ((($0)) + 7|0);
 HEAP8[$429>>0] = $428;
 $430 = HEAP32[$379>>2]|0;
 $431 = $430 >>> 16;
 $432 = $431&255;
 $433 = ((($0)) + 8|0);
 HEAP8[$433>>0] = $432;
 $434 = $430 >>> 24;
 $435 = ((($0)) + 9|0);
 $436 = HEAP32[$382>>2]|0;
 $437 = $436 | $434;
 $438 = $437&255;
 HEAP8[$435>>0] = $438;
 $439 = $436 >>> 8;
 $440 = $439&255;
 $441 = ((($0)) + 10|0);
 HEAP8[$441>>0] = $440;
 $442 = HEAP32[$382>>2]|0;
 $443 = $442 >>> 16;
 $444 = $443&255;
 $445 = ((($0)) + 11|0);
 HEAP8[$445>>0] = $444;
 $446 = $442 >>> 24;
 $447 = ((($0)) + 12|0);
 $448 = HEAP32[$385>>2]|0;
 $449 = $448 | $446;
 $450 = $449&255;
 HEAP8[$447>>0] = $450;
 $451 = $448 >>> 8;
 $452 = $451&255;
 $453 = ((($0)) + 13|0);
 HEAP8[$453>>0] = $452;
 $454 = HEAP32[$385>>2]|0;
 $455 = $454 >>> 16;
 $456 = $455&255;
 $457 = ((($0)) + 14|0);
 HEAP8[$457>>0] = $456;
 $458 = $454 >>> 24;
 $459 = $458&255;
 $460 = ((($0)) + 15|0);
 HEAP8[$460>>0] = $459;
 $461 = ((($2)) + 20|0);
 $462 = HEAP32[$461>>2]|0;
 $463 = HEAP8[$400>>0]|0;
 $464 = $463&255;
 $465 = $462 | $464;
 $466 = $465&255;
 HEAP8[$400>>0] = $466;
 $467 = $462 >>> 8;
 $468 = $467&255;
 $469 = ((($0)) + 17|0);
 HEAP8[$469>>0] = $468;
 $470 = HEAP32[$461>>2]|0;
 $471 = $470 >>> 16;
 $472 = $471&255;
 $473 = ((($0)) + 18|0);
 HEAP8[$473>>0] = $472;
 $474 = $470 >>> 24;
 $475 = ((($0)) + 19|0);
 $476 = HEAP32[$388>>2]|0;
 $477 = $476 | $474;
 $478 = $477&255;
 HEAP8[$475>>0] = $478;
 $479 = $476 >>> 8;
 $480 = $479&255;
 $481 = ((($0)) + 20|0);
 HEAP8[$481>>0] = $480;
 $482 = HEAP32[$388>>2]|0;
 $483 = $482 >>> 16;
 $484 = $483&255;
 $485 = ((($0)) + 21|0);
 HEAP8[$485>>0] = $484;
 $486 = $482 >>> 24;
 $487 = ((($0)) + 22|0);
 $488 = HEAP32[$391>>2]|0;
 $489 = $488 | $486;
 $490 = $489&255;
 HEAP8[$487>>0] = $490;
 $491 = $488 >>> 8;
 $492 = $491&255;
 $493 = ((($0)) + 23|0);
 HEAP8[$493>>0] = $492;
 $494 = HEAP32[$391>>2]|0;
 $495 = $494 >>> 16;
 $496 = $495&255;
 $497 = ((($0)) + 24|0);
 HEAP8[$497>>0] = $496;
 $498 = $494 >>> 24;
 $499 = ((($0)) + 25|0);
 $500 = HEAP32[$394>>2]|0;
 $501 = $500 | $498;
 $502 = $501&255;
 HEAP8[$499>>0] = $502;
 $503 = $500 >>> 8;
 $504 = $503&255;
 $505 = ((($0)) + 26|0);
 HEAP8[$505>>0] = $504;
 $506 = HEAP32[$394>>2]|0;
 $507 = $506 >>> 16;
 $508 = $507&255;
 $509 = ((($0)) + 27|0);
 HEAP8[$509>>0] = $508;
 $510 = $506 >>> 24;
 $511 = ((($0)) + 28|0);
 $512 = HEAP32[$397>>2]|0;
 $513 = $512 | $510;
 $514 = $513&255;
 HEAP8[$511>>0] = $514;
 $515 = $512 >>> 8;
 $516 = $515&255;
 $517 = ((($0)) + 29|0);
 HEAP8[$517>>0] = $516;
 $518 = HEAP32[$397>>2]|0;
 $519 = $518 >>> 16;
 $520 = $519&255;
 $521 = ((($0)) + 30|0);
 HEAP8[$521>>0] = $520;
 $522 = $518 >>> 24;
 $523 = $522&255;
 $524 = ((($0)) + 31|0);
 HEAP8[$524>>0] = $523;
 STACKTOP = sp;return;
}
function _s32_gte($0) {
 $0 = $0|0;
 var $1 = 0, $2 = 0, $3 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $1 = (($0) + -67108845)|0;
 $2 = $1 >> 31;
 $3 = $2 ^ -1;
 return ($3|0);
}
function _s32_eq($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = $0 ^ -1;
 $3 = $2 ^ $1;
 $4 = $3 << 16;
 $5 = $4 & $3;
 $6 = $5 << 8;
 $7 = $6 & $5;
 $8 = $7 << 4;
 $9 = $8 & $7;
 $10 = $9 << 2;
 $11 = $10 & $9;
 $12 = $11 << 1;
 $13 = $12 & $11;
 $14 = $13 >> 31;
 return ($14|0);
}
function _fproduct($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var $10 = 0, $100 = 0, $1000 = 0, $1001 = 0, $1002 = 0, $1003 = 0, $1004 = 0, $1005 = 0, $1006 = 0, $1007 = 0, $1008 = 0, $1009 = 0, $101 = 0, $1010 = 0, $1011 = 0, $1012 = 0, $1013 = 0, $1014 = 0, $1015 = 0, $1016 = 0;
 var $1017 = 0, $1018 = 0, $1019 = 0, $102 = 0, $1020 = 0, $1021 = 0, $1022 = 0, $1023 = 0, $1024 = 0, $1025 = 0, $1026 = 0, $1027 = 0, $1028 = 0, $1029 = 0, $103 = 0, $1030 = 0, $1031 = 0, $1032 = 0, $1033 = 0, $1034 = 0;
 var $1035 = 0, $1036 = 0, $1037 = 0, $1038 = 0, $1039 = 0, $104 = 0, $1040 = 0, $1041 = 0, $1042 = 0, $1043 = 0, $1044 = 0, $1045 = 0, $1046 = 0, $1047 = 0, $1048 = 0, $1049 = 0, $105 = 0, $1050 = 0, $1051 = 0, $1052 = 0;
 var $1053 = 0, $1054 = 0, $1055 = 0, $1056 = 0, $1057 = 0, $1058 = 0, $1059 = 0, $106 = 0, $1060 = 0, $1061 = 0, $1062 = 0, $1063 = 0, $1064 = 0, $1065 = 0, $1066 = 0, $1067 = 0, $1068 = 0, $1069 = 0, $107 = 0, $1070 = 0;
 var $1071 = 0, $1072 = 0, $1073 = 0, $1074 = 0, $1075 = 0, $1076 = 0, $1077 = 0, $1078 = 0, $1079 = 0, $108 = 0, $1080 = 0, $1081 = 0, $1082 = 0, $1083 = 0, $1084 = 0, $1085 = 0, $1086 = 0, $1087 = 0, $1088 = 0, $1089 = 0;
 var $109 = 0, $1090 = 0, $1091 = 0, $1092 = 0, $1093 = 0, $1094 = 0, $1095 = 0, $1096 = 0, $1097 = 0, $1098 = 0, $1099 = 0, $11 = 0, $110 = 0, $1100 = 0, $1101 = 0, $1102 = 0, $1103 = 0, $1104 = 0, $1105 = 0, $1106 = 0;
 var $1107 = 0, $1108 = 0, $1109 = 0, $111 = 0, $1110 = 0, $1111 = 0, $1112 = 0, $1113 = 0, $1114 = 0, $1115 = 0, $1116 = 0, $1117 = 0, $1118 = 0, $1119 = 0, $112 = 0, $1120 = 0, $1121 = 0, $1122 = 0, $1123 = 0, $1124 = 0;
 var $1125 = 0, $1126 = 0, $1127 = 0, $1128 = 0, $1129 = 0, $113 = 0, $1130 = 0, $1131 = 0, $1132 = 0, $1133 = 0, $1134 = 0, $1135 = 0, $1136 = 0, $1137 = 0, $1138 = 0, $1139 = 0, $114 = 0, $1140 = 0, $1141 = 0, $1142 = 0;
 var $1143 = 0, $1144 = 0, $1145 = 0, $1146 = 0, $1147 = 0, $1148 = 0, $1149 = 0, $115 = 0, $1150 = 0, $1151 = 0, $1152 = 0, $1153 = 0, $1154 = 0, $1155 = 0, $1156 = 0, $1157 = 0, $1158 = 0, $1159 = 0, $116 = 0, $1160 = 0;
 var $1161 = 0, $1162 = 0, $1163 = 0, $1164 = 0, $1165 = 0, $1166 = 0, $1167 = 0, $1168 = 0, $1169 = 0, $117 = 0, $1170 = 0, $1171 = 0, $1172 = 0, $1173 = 0, $1174 = 0, $1175 = 0, $1176 = 0, $1177 = 0, $1178 = 0, $1179 = 0;
 var $118 = 0, $1180 = 0, $1181 = 0, $1182 = 0, $1183 = 0, $1184 = 0, $1185 = 0, $1186 = 0, $1187 = 0, $1188 = 0, $1189 = 0, $119 = 0, $1190 = 0, $1191 = 0, $1192 = 0, $1193 = 0, $1194 = 0, $1195 = 0, $1196 = 0, $1197 = 0;
 var $1198 = 0, $1199 = 0, $12 = 0, $120 = 0, $1200 = 0, $1201 = 0, $1202 = 0, $1203 = 0, $1204 = 0, $1205 = 0, $1206 = 0, $1207 = 0, $1208 = 0, $1209 = 0, $121 = 0, $1210 = 0, $1211 = 0, $1212 = 0, $1213 = 0, $1214 = 0;
 var $1215 = 0, $1216 = 0, $1217 = 0, $1218 = 0, $1219 = 0, $122 = 0, $1220 = 0, $1221 = 0, $1222 = 0, $1223 = 0, $1224 = 0, $1225 = 0, $1226 = 0, $1227 = 0, $1228 = 0, $1229 = 0, $123 = 0, $1230 = 0, $1231 = 0, $1232 = 0;
 var $1233 = 0, $1234 = 0, $1235 = 0, $1236 = 0, $1237 = 0, $1238 = 0, $1239 = 0, $124 = 0, $1240 = 0, $1241 = 0, $1242 = 0, $1243 = 0, $1244 = 0, $1245 = 0, $1246 = 0, $1247 = 0, $1248 = 0, $1249 = 0, $125 = 0, $1250 = 0;
 var $1251 = 0, $1252 = 0, $1253 = 0, $1254 = 0, $1255 = 0, $1256 = 0, $1257 = 0, $1258 = 0, $1259 = 0, $126 = 0, $1260 = 0, $1261 = 0, $1262 = 0, $1263 = 0, $1264 = 0, $1265 = 0, $1266 = 0, $1267 = 0, $1268 = 0, $1269 = 0;
 var $127 = 0, $1270 = 0, $1271 = 0, $1272 = 0, $1273 = 0, $1274 = 0, $1275 = 0, $1276 = 0, $1277 = 0, $1278 = 0, $1279 = 0, $128 = 0, $1280 = 0, $1281 = 0, $1282 = 0, $1283 = 0, $1284 = 0, $1285 = 0, $1286 = 0, $1287 = 0;
 var $1288 = 0, $1289 = 0, $129 = 0, $1290 = 0, $1291 = 0, $1292 = 0, $1293 = 0, $1294 = 0, $1295 = 0, $1296 = 0, $1297 = 0, $1298 = 0, $1299 = 0, $13 = 0, $130 = 0, $1300 = 0, $1301 = 0, $1302 = 0, $1303 = 0, $1304 = 0;
 var $1305 = 0, $1306 = 0, $1307 = 0, $1308 = 0, $1309 = 0, $131 = 0, $1310 = 0, $1311 = 0, $1312 = 0, $1313 = 0, $1314 = 0, $1315 = 0, $1316 = 0, $1317 = 0, $1318 = 0, $1319 = 0, $132 = 0, $1320 = 0, $1321 = 0, $1322 = 0;
 var $1323 = 0, $1324 = 0, $1325 = 0, $1326 = 0, $1327 = 0, $1328 = 0, $1329 = 0, $133 = 0, $1330 = 0, $1331 = 0, $1332 = 0, $1333 = 0, $1334 = 0, $1335 = 0, $1336 = 0, $1337 = 0, $1338 = 0, $1339 = 0, $134 = 0, $1340 = 0;
 var $1341 = 0, $1342 = 0, $1343 = 0, $1344 = 0, $1345 = 0, $1346 = 0, $1347 = 0, $1348 = 0, $1349 = 0, $135 = 0, $1350 = 0, $1351 = 0, $1352 = 0, $1353 = 0, $1354 = 0, $1355 = 0, $1356 = 0, $1357 = 0, $1358 = 0, $1359 = 0;
 var $136 = 0, $1360 = 0, $1361 = 0, $1362 = 0, $1363 = 0, $1364 = 0, $1365 = 0, $1366 = 0, $1367 = 0, $1368 = 0, $1369 = 0, $137 = 0, $1370 = 0, $1371 = 0, $1372 = 0, $1373 = 0, $1374 = 0, $1375 = 0, $1376 = 0, $1377 = 0;
 var $1378 = 0, $1379 = 0, $138 = 0, $1380 = 0, $1381 = 0, $1382 = 0, $1383 = 0, $1384 = 0, $1385 = 0, $1386 = 0, $1387 = 0, $1388 = 0, $1389 = 0, $139 = 0, $1390 = 0, $1391 = 0, $1392 = 0, $1393 = 0, $1394 = 0, $1395 = 0;
 var $1396 = 0, $1397 = 0, $1398 = 0, $1399 = 0, $14 = 0, $140 = 0, $1400 = 0, $1401 = 0, $1402 = 0, $1403 = 0, $1404 = 0, $1405 = 0, $1406 = 0, $1407 = 0, $1408 = 0, $1409 = 0, $141 = 0, $1410 = 0, $1411 = 0, $1412 = 0;
 var $1413 = 0, $1414 = 0, $1415 = 0, $1416 = 0, $1417 = 0, $1418 = 0, $1419 = 0, $142 = 0, $1420 = 0, $1421 = 0, $1422 = 0, $1423 = 0, $1424 = 0, $1425 = 0, $1426 = 0, $1427 = 0, $1428 = 0, $1429 = 0, $143 = 0, $1430 = 0;
 var $1431 = 0, $1432 = 0, $1433 = 0, $1434 = 0, $1435 = 0, $1436 = 0, $1437 = 0, $1438 = 0, $1439 = 0, $144 = 0, $1440 = 0, $1441 = 0, $1442 = 0, $1443 = 0, $1444 = 0, $1445 = 0, $1446 = 0, $1447 = 0, $1448 = 0, $1449 = 0;
 var $145 = 0, $1450 = 0, $1451 = 0, $1452 = 0, $1453 = 0, $1454 = 0, $1455 = 0, $1456 = 0, $1457 = 0, $1458 = 0, $1459 = 0, $146 = 0, $1460 = 0, $1461 = 0, $1462 = 0, $1463 = 0, $1464 = 0, $1465 = 0, $1466 = 0, $1467 = 0;
 var $1468 = 0, $1469 = 0, $147 = 0, $1470 = 0, $1471 = 0, $1472 = 0, $1473 = 0, $1474 = 0, $1475 = 0, $1476 = 0, $1477 = 0, $1478 = 0, $1479 = 0, $148 = 0, $1480 = 0, $1481 = 0, $1482 = 0, $1483 = 0, $1484 = 0, $1485 = 0;
 var $1486 = 0, $1487 = 0, $1488 = 0, $1489 = 0, $149 = 0, $1490 = 0, $1491 = 0, $1492 = 0, $1493 = 0, $1494 = 0, $1495 = 0, $1496 = 0, $1497 = 0, $1498 = 0, $1499 = 0, $15 = 0, $150 = 0, $1500 = 0, $1501 = 0, $1502 = 0;
 var $1503 = 0, $1504 = 0, $1505 = 0, $1506 = 0, $1507 = 0, $1508 = 0, $1509 = 0, $151 = 0, $1510 = 0, $1511 = 0, $1512 = 0, $1513 = 0, $1514 = 0, $1515 = 0, $1516 = 0, $1517 = 0, $1518 = 0, $1519 = 0, $152 = 0, $1520 = 0;
 var $1521 = 0, $1522 = 0, $1523 = 0, $1524 = 0, $1525 = 0, $1526 = 0, $1527 = 0, $1528 = 0, $1529 = 0, $153 = 0, $1530 = 0, $1531 = 0, $1532 = 0, $1533 = 0, $1534 = 0, $1535 = 0, $1536 = 0, $1537 = 0, $1538 = 0, $1539 = 0;
 var $154 = 0, $1540 = 0, $1541 = 0, $1542 = 0, $1543 = 0, $1544 = 0, $1545 = 0, $1546 = 0, $1547 = 0, $1548 = 0, $1549 = 0, $155 = 0, $1550 = 0, $1551 = 0, $1552 = 0, $1553 = 0, $1554 = 0, $1555 = 0, $1556 = 0, $1557 = 0;
 var $1558 = 0, $1559 = 0, $156 = 0, $1560 = 0, $1561 = 0, $1562 = 0, $1563 = 0, $1564 = 0, $1565 = 0, $1566 = 0, $1567 = 0, $1568 = 0, $1569 = 0, $157 = 0, $1570 = 0, $1571 = 0, $1572 = 0, $1573 = 0, $1574 = 0, $1575 = 0;
 var $1576 = 0, $1577 = 0, $1578 = 0, $1579 = 0, $158 = 0, $1580 = 0, $1581 = 0, $1582 = 0, $1583 = 0, $1584 = 0, $1585 = 0, $1586 = 0, $1587 = 0, $1588 = 0, $1589 = 0, $159 = 0, $1590 = 0, $1591 = 0, $1592 = 0, $1593 = 0;
 var $1594 = 0, $1595 = 0, $1596 = 0, $1597 = 0, $1598 = 0, $1599 = 0, $16 = 0, $160 = 0, $1600 = 0, $1601 = 0, $1602 = 0, $1603 = 0, $1604 = 0, $1605 = 0, $1606 = 0, $1607 = 0, $1608 = 0, $1609 = 0, $161 = 0, $1610 = 0;
 var $1611 = 0, $1612 = 0, $1613 = 0, $1614 = 0, $1615 = 0, $1616 = 0, $1617 = 0, $1618 = 0, $1619 = 0, $162 = 0, $1620 = 0, $1621 = 0, $1622 = 0, $1623 = 0, $1624 = 0, $1625 = 0, $1626 = 0, $1627 = 0, $1628 = 0, $1629 = 0;
 var $163 = 0, $1630 = 0, $1631 = 0, $1632 = 0, $1633 = 0, $1634 = 0, $1635 = 0, $1636 = 0, $1637 = 0, $1638 = 0, $1639 = 0, $164 = 0, $1640 = 0, $1641 = 0, $1642 = 0, $1643 = 0, $1644 = 0, $1645 = 0, $1646 = 0, $1647 = 0;
 var $1648 = 0, $1649 = 0, $165 = 0, $1650 = 0, $1651 = 0, $1652 = 0, $1653 = 0, $1654 = 0, $1655 = 0, $1656 = 0, $1657 = 0, $1658 = 0, $1659 = 0, $166 = 0, $1660 = 0, $1661 = 0, $1662 = 0, $1663 = 0, $1664 = 0, $1665 = 0;
 var $1666 = 0, $1667 = 0, $1668 = 0, $1669 = 0, $167 = 0, $1670 = 0, $1671 = 0, $1672 = 0, $1673 = 0, $1674 = 0, $1675 = 0, $1676 = 0, $1677 = 0, $1678 = 0, $1679 = 0, $168 = 0, $1680 = 0, $1681 = 0, $1682 = 0, $1683 = 0;
 var $1684 = 0, $1685 = 0, $1686 = 0, $1687 = 0, $1688 = 0, $1689 = 0, $169 = 0, $1690 = 0, $1691 = 0, $1692 = 0, $1693 = 0, $1694 = 0, $1695 = 0, $1696 = 0, $1697 = 0, $1698 = 0, $1699 = 0, $17 = 0, $170 = 0, $1700 = 0;
 var $1701 = 0, $1702 = 0, $1703 = 0, $1704 = 0, $1705 = 0, $1706 = 0, $1707 = 0, $1708 = 0, $1709 = 0, $171 = 0, $1710 = 0, $1711 = 0, $1712 = 0, $1713 = 0, $1714 = 0, $1715 = 0, $1716 = 0, $1717 = 0, $1718 = 0, $1719 = 0;
 var $172 = 0, $1720 = 0, $1721 = 0, $1722 = 0, $1723 = 0, $1724 = 0, $1725 = 0, $1726 = 0, $1727 = 0, $1728 = 0, $1729 = 0, $173 = 0, $1730 = 0, $1731 = 0, $1732 = 0, $1733 = 0, $1734 = 0, $1735 = 0, $1736 = 0, $1737 = 0;
 var $1738 = 0, $1739 = 0, $174 = 0, $1740 = 0, $1741 = 0, $1742 = 0, $1743 = 0, $1744 = 0, $1745 = 0, $1746 = 0, $1747 = 0, $1748 = 0, $1749 = 0, $175 = 0, $1750 = 0, $1751 = 0, $1752 = 0, $1753 = 0, $1754 = 0, $1755 = 0;
 var $1756 = 0, $1757 = 0, $1758 = 0, $1759 = 0, $176 = 0, $1760 = 0, $1761 = 0, $1762 = 0, $1763 = 0, $1764 = 0, $1765 = 0, $1766 = 0, $1767 = 0, $1768 = 0, $1769 = 0, $177 = 0, $1770 = 0, $1771 = 0, $1772 = 0, $1773 = 0;
 var $1774 = 0, $1775 = 0, $1776 = 0, $1777 = 0, $1778 = 0, $1779 = 0, $178 = 0, $1780 = 0, $1781 = 0, $1782 = 0, $1783 = 0, $1784 = 0, $1785 = 0, $1786 = 0, $1787 = 0, $1788 = 0, $1789 = 0, $179 = 0, $1790 = 0, $1791 = 0;
 var $1792 = 0, $1793 = 0, $1794 = 0, $1795 = 0, $1796 = 0, $1797 = 0, $1798 = 0, $1799 = 0, $18 = 0, $180 = 0, $1800 = 0, $1801 = 0, $1802 = 0, $1803 = 0, $1804 = 0, $1805 = 0, $1806 = 0, $1807 = 0, $1808 = 0, $1809 = 0;
 var $181 = 0, $1810 = 0, $1811 = 0, $1812 = 0, $1813 = 0, $1814 = 0, $1815 = 0, $1816 = 0, $1817 = 0, $1818 = 0, $1819 = 0, $182 = 0, $1820 = 0, $1821 = 0, $1822 = 0, $1823 = 0, $1824 = 0, $1825 = 0, $1826 = 0, $1827 = 0;
 var $1828 = 0, $1829 = 0, $183 = 0, $1830 = 0, $1831 = 0, $1832 = 0, $1833 = 0, $1834 = 0, $1835 = 0, $1836 = 0, $1837 = 0, $1838 = 0, $1839 = 0, $184 = 0, $1840 = 0, $1841 = 0, $1842 = 0, $1843 = 0, $1844 = 0, $1845 = 0;
 var $1846 = 0, $1847 = 0, $1848 = 0, $1849 = 0, $185 = 0, $1850 = 0, $1851 = 0, $1852 = 0, $1853 = 0, $1854 = 0, $1855 = 0, $1856 = 0, $1857 = 0, $1858 = 0, $1859 = 0, $186 = 0, $1860 = 0, $1861 = 0, $1862 = 0, $1863 = 0;
 var $1864 = 0, $1865 = 0, $1866 = 0, $1867 = 0, $1868 = 0, $1869 = 0, $187 = 0, $1870 = 0, $1871 = 0, $1872 = 0, $1873 = 0, $1874 = 0, $1875 = 0, $1876 = 0, $1877 = 0, $1878 = 0, $1879 = 0, $188 = 0, $1880 = 0, $1881 = 0;
 var $1882 = 0, $1883 = 0, $1884 = 0, $1885 = 0, $1886 = 0, $1887 = 0, $1888 = 0, $1889 = 0, $189 = 0, $1890 = 0, $1891 = 0, $1892 = 0, $1893 = 0, $1894 = 0, $1895 = 0, $1896 = 0, $1897 = 0, $1898 = 0, $1899 = 0, $19 = 0;
 var $190 = 0, $1900 = 0, $1901 = 0, $1902 = 0, $1903 = 0, $1904 = 0, $1905 = 0, $1906 = 0, $1907 = 0, $1908 = 0, $1909 = 0, $191 = 0, $1910 = 0, $1911 = 0, $1912 = 0, $1913 = 0, $1914 = 0, $1915 = 0, $1916 = 0, $1917 = 0;
 var $1918 = 0, $1919 = 0, $192 = 0, $1920 = 0, $1921 = 0, $1922 = 0, $1923 = 0, $1924 = 0, $1925 = 0, $1926 = 0, $1927 = 0, $1928 = 0, $1929 = 0, $193 = 0, $1930 = 0, $1931 = 0, $1932 = 0, $1933 = 0, $1934 = 0, $1935 = 0;
 var $1936 = 0, $1937 = 0, $1938 = 0, $1939 = 0, $194 = 0, $1940 = 0, $1941 = 0, $1942 = 0, $1943 = 0, $1944 = 0, $1945 = 0, $1946 = 0, $1947 = 0, $1948 = 0, $1949 = 0, $195 = 0, $1950 = 0, $1951 = 0, $1952 = 0, $1953 = 0;
 var $1954 = 0, $1955 = 0, $1956 = 0, $1957 = 0, $1958 = 0, $1959 = 0, $196 = 0, $1960 = 0, $1961 = 0, $1962 = 0, $1963 = 0, $1964 = 0, $1965 = 0, $1966 = 0, $1967 = 0, $1968 = 0, $1969 = 0, $197 = 0, $1970 = 0, $1971 = 0;
 var $1972 = 0, $1973 = 0, $1974 = 0, $1975 = 0, $1976 = 0, $1977 = 0, $1978 = 0, $1979 = 0, $198 = 0, $1980 = 0, $1981 = 0, $1982 = 0, $1983 = 0, $1984 = 0, $1985 = 0, $1986 = 0, $1987 = 0, $1988 = 0, $1989 = 0, $199 = 0;
 var $1990 = 0, $1991 = 0, $1992 = 0, $1993 = 0, $1994 = 0, $1995 = 0, $1996 = 0, $1997 = 0, $1998 = 0, $1999 = 0, $20 = 0, $200 = 0, $2000 = 0, $2001 = 0, $2002 = 0, $2003 = 0, $2004 = 0, $2005 = 0, $2006 = 0, $2007 = 0;
 var $2008 = 0, $2009 = 0, $201 = 0, $2010 = 0, $2011 = 0, $2012 = 0, $2013 = 0, $2014 = 0, $2015 = 0, $2016 = 0, $2017 = 0, $2018 = 0, $2019 = 0, $202 = 0, $2020 = 0, $2021 = 0, $2022 = 0, $2023 = 0, $2024 = 0, $2025 = 0;
 var $2026 = 0, $2027 = 0, $2028 = 0, $2029 = 0, $203 = 0, $2030 = 0, $2031 = 0, $2032 = 0, $2033 = 0, $2034 = 0, $2035 = 0, $2036 = 0, $2037 = 0, $2038 = 0, $2039 = 0, $204 = 0, $2040 = 0, $2041 = 0, $2042 = 0, $2043 = 0;
 var $2044 = 0, $2045 = 0, $2046 = 0, $2047 = 0, $2048 = 0, $2049 = 0, $205 = 0, $2050 = 0, $2051 = 0, $2052 = 0, $2053 = 0, $2054 = 0, $2055 = 0, $2056 = 0, $2057 = 0, $2058 = 0, $2059 = 0, $206 = 0, $2060 = 0, $2061 = 0;
 var $2062 = 0, $2063 = 0, $2064 = 0, $2065 = 0, $2066 = 0, $2067 = 0, $2068 = 0, $2069 = 0, $207 = 0, $2070 = 0, $2071 = 0, $2072 = 0, $2073 = 0, $2074 = 0, $2075 = 0, $2076 = 0, $2077 = 0, $2078 = 0, $2079 = 0, $208 = 0;
 var $2080 = 0, $2081 = 0, $2082 = 0, $2083 = 0, $2084 = 0, $2085 = 0, $2086 = 0, $2087 = 0, $2088 = 0, $2089 = 0, $209 = 0, $2090 = 0, $21 = 0, $210 = 0, $211 = 0, $212 = 0, $213 = 0, $214 = 0, $215 = 0, $216 = 0;
 var $217 = 0, $218 = 0, $219 = 0, $22 = 0, $220 = 0, $221 = 0, $222 = 0, $223 = 0, $224 = 0, $225 = 0, $226 = 0, $227 = 0, $228 = 0, $229 = 0, $23 = 0, $230 = 0, $231 = 0, $232 = 0, $233 = 0, $234 = 0;
 var $235 = 0, $236 = 0, $237 = 0, $238 = 0, $239 = 0, $24 = 0, $240 = 0, $241 = 0, $242 = 0, $243 = 0, $244 = 0, $245 = 0, $246 = 0, $247 = 0, $248 = 0, $249 = 0, $25 = 0, $250 = 0, $251 = 0, $252 = 0;
 var $253 = 0, $254 = 0, $255 = 0, $256 = 0, $257 = 0, $258 = 0, $259 = 0, $26 = 0, $260 = 0, $261 = 0, $262 = 0, $263 = 0, $264 = 0, $265 = 0, $266 = 0, $267 = 0, $268 = 0, $269 = 0, $27 = 0, $270 = 0;
 var $271 = 0, $272 = 0, $273 = 0, $274 = 0, $275 = 0, $276 = 0, $277 = 0, $278 = 0, $279 = 0, $28 = 0, $280 = 0, $281 = 0, $282 = 0, $283 = 0, $284 = 0, $285 = 0, $286 = 0, $287 = 0, $288 = 0, $289 = 0;
 var $29 = 0, $290 = 0, $291 = 0, $292 = 0, $293 = 0, $294 = 0, $295 = 0, $296 = 0, $297 = 0, $298 = 0, $299 = 0, $3 = 0, $30 = 0, $300 = 0, $301 = 0, $302 = 0, $303 = 0, $304 = 0, $305 = 0, $306 = 0;
 var $307 = 0, $308 = 0, $309 = 0, $31 = 0, $310 = 0, $311 = 0, $312 = 0, $313 = 0, $314 = 0, $315 = 0, $316 = 0, $317 = 0, $318 = 0, $319 = 0, $32 = 0, $320 = 0, $321 = 0, $322 = 0, $323 = 0, $324 = 0;
 var $325 = 0, $326 = 0, $327 = 0, $328 = 0, $329 = 0, $33 = 0, $330 = 0, $331 = 0, $332 = 0, $333 = 0, $334 = 0, $335 = 0, $336 = 0, $337 = 0, $338 = 0, $339 = 0, $34 = 0, $340 = 0, $341 = 0, $342 = 0;
 var $343 = 0, $344 = 0, $345 = 0, $346 = 0, $347 = 0, $348 = 0, $349 = 0, $35 = 0, $350 = 0, $351 = 0, $352 = 0, $353 = 0, $354 = 0, $355 = 0, $356 = 0, $357 = 0, $358 = 0, $359 = 0, $36 = 0, $360 = 0;
 var $361 = 0, $362 = 0, $363 = 0, $364 = 0, $365 = 0, $366 = 0, $367 = 0, $368 = 0, $369 = 0, $37 = 0, $370 = 0, $371 = 0, $372 = 0, $373 = 0, $374 = 0, $375 = 0, $376 = 0, $377 = 0, $378 = 0, $379 = 0;
 var $38 = 0, $380 = 0, $381 = 0, $382 = 0, $383 = 0, $384 = 0, $385 = 0, $386 = 0, $387 = 0, $388 = 0, $389 = 0, $39 = 0, $390 = 0, $391 = 0, $392 = 0, $393 = 0, $394 = 0, $395 = 0, $396 = 0, $397 = 0;
 var $398 = 0, $399 = 0, $4 = 0, $40 = 0, $400 = 0, $401 = 0, $402 = 0, $403 = 0, $404 = 0, $405 = 0, $406 = 0, $407 = 0, $408 = 0, $409 = 0, $41 = 0, $410 = 0, $411 = 0, $412 = 0, $413 = 0, $414 = 0;
 var $415 = 0, $416 = 0, $417 = 0, $418 = 0, $419 = 0, $42 = 0, $420 = 0, $421 = 0, $422 = 0, $423 = 0, $424 = 0, $425 = 0, $426 = 0, $427 = 0, $428 = 0, $429 = 0, $43 = 0, $430 = 0, $431 = 0, $432 = 0;
 var $433 = 0, $434 = 0, $435 = 0, $436 = 0, $437 = 0, $438 = 0, $439 = 0, $44 = 0, $440 = 0, $441 = 0, $442 = 0, $443 = 0, $444 = 0, $445 = 0, $446 = 0, $447 = 0, $448 = 0, $449 = 0, $45 = 0, $450 = 0;
 var $451 = 0, $452 = 0, $453 = 0, $454 = 0, $455 = 0, $456 = 0, $457 = 0, $458 = 0, $459 = 0, $46 = 0, $460 = 0, $461 = 0, $462 = 0, $463 = 0, $464 = 0, $465 = 0, $466 = 0, $467 = 0, $468 = 0, $469 = 0;
 var $47 = 0, $470 = 0, $471 = 0, $472 = 0, $473 = 0, $474 = 0, $475 = 0, $476 = 0, $477 = 0, $478 = 0, $479 = 0, $48 = 0, $480 = 0, $481 = 0, $482 = 0, $483 = 0, $484 = 0, $485 = 0, $486 = 0, $487 = 0;
 var $488 = 0, $489 = 0, $49 = 0, $490 = 0, $491 = 0, $492 = 0, $493 = 0, $494 = 0, $495 = 0, $496 = 0, $497 = 0, $498 = 0, $499 = 0, $5 = 0, $50 = 0, $500 = 0, $501 = 0, $502 = 0, $503 = 0, $504 = 0;
 var $505 = 0, $506 = 0, $507 = 0, $508 = 0, $509 = 0, $51 = 0, $510 = 0, $511 = 0, $512 = 0, $513 = 0, $514 = 0, $515 = 0, $516 = 0, $517 = 0, $518 = 0, $519 = 0, $52 = 0, $520 = 0, $521 = 0, $522 = 0;
 var $523 = 0, $524 = 0, $525 = 0, $526 = 0, $527 = 0, $528 = 0, $529 = 0, $53 = 0, $530 = 0, $531 = 0, $532 = 0, $533 = 0, $534 = 0, $535 = 0, $536 = 0, $537 = 0, $538 = 0, $539 = 0, $54 = 0, $540 = 0;
 var $541 = 0, $542 = 0, $543 = 0, $544 = 0, $545 = 0, $546 = 0, $547 = 0, $548 = 0, $549 = 0, $55 = 0, $550 = 0, $551 = 0, $552 = 0, $553 = 0, $554 = 0, $555 = 0, $556 = 0, $557 = 0, $558 = 0, $559 = 0;
 var $56 = 0, $560 = 0, $561 = 0, $562 = 0, $563 = 0, $564 = 0, $565 = 0, $566 = 0, $567 = 0, $568 = 0, $569 = 0, $57 = 0, $570 = 0, $571 = 0, $572 = 0, $573 = 0, $574 = 0, $575 = 0, $576 = 0, $577 = 0;
 var $578 = 0, $579 = 0, $58 = 0, $580 = 0, $581 = 0, $582 = 0, $583 = 0, $584 = 0, $585 = 0, $586 = 0, $587 = 0, $588 = 0, $589 = 0, $59 = 0, $590 = 0, $591 = 0, $592 = 0, $593 = 0, $594 = 0, $595 = 0;
 var $596 = 0, $597 = 0, $598 = 0, $599 = 0, $6 = 0, $60 = 0, $600 = 0, $601 = 0, $602 = 0, $603 = 0, $604 = 0, $605 = 0, $606 = 0, $607 = 0, $608 = 0, $609 = 0, $61 = 0, $610 = 0, $611 = 0, $612 = 0;
 var $613 = 0, $614 = 0, $615 = 0, $616 = 0, $617 = 0, $618 = 0, $619 = 0, $62 = 0, $620 = 0, $621 = 0, $622 = 0, $623 = 0, $624 = 0, $625 = 0, $626 = 0, $627 = 0, $628 = 0, $629 = 0, $63 = 0, $630 = 0;
 var $631 = 0, $632 = 0, $633 = 0, $634 = 0, $635 = 0, $636 = 0, $637 = 0, $638 = 0, $639 = 0, $64 = 0, $640 = 0, $641 = 0, $642 = 0, $643 = 0, $644 = 0, $645 = 0, $646 = 0, $647 = 0, $648 = 0, $649 = 0;
 var $65 = 0, $650 = 0, $651 = 0, $652 = 0, $653 = 0, $654 = 0, $655 = 0, $656 = 0, $657 = 0, $658 = 0, $659 = 0, $66 = 0, $660 = 0, $661 = 0, $662 = 0, $663 = 0, $664 = 0, $665 = 0, $666 = 0, $667 = 0;
 var $668 = 0, $669 = 0, $67 = 0, $670 = 0, $671 = 0, $672 = 0, $673 = 0, $674 = 0, $675 = 0, $676 = 0, $677 = 0, $678 = 0, $679 = 0, $68 = 0, $680 = 0, $681 = 0, $682 = 0, $683 = 0, $684 = 0, $685 = 0;
 var $686 = 0, $687 = 0, $688 = 0, $689 = 0, $69 = 0, $690 = 0, $691 = 0, $692 = 0, $693 = 0, $694 = 0, $695 = 0, $696 = 0, $697 = 0, $698 = 0, $699 = 0, $7 = 0, $70 = 0, $700 = 0, $701 = 0, $702 = 0;
 var $703 = 0, $704 = 0, $705 = 0, $706 = 0, $707 = 0, $708 = 0, $709 = 0, $71 = 0, $710 = 0, $711 = 0, $712 = 0, $713 = 0, $714 = 0, $715 = 0, $716 = 0, $717 = 0, $718 = 0, $719 = 0, $72 = 0, $720 = 0;
 var $721 = 0, $722 = 0, $723 = 0, $724 = 0, $725 = 0, $726 = 0, $727 = 0, $728 = 0, $729 = 0, $73 = 0, $730 = 0, $731 = 0, $732 = 0, $733 = 0, $734 = 0, $735 = 0, $736 = 0, $737 = 0, $738 = 0, $739 = 0;
 var $74 = 0, $740 = 0, $741 = 0, $742 = 0, $743 = 0, $744 = 0, $745 = 0, $746 = 0, $747 = 0, $748 = 0, $749 = 0, $75 = 0, $750 = 0, $751 = 0, $752 = 0, $753 = 0, $754 = 0, $755 = 0, $756 = 0, $757 = 0;
 var $758 = 0, $759 = 0, $76 = 0, $760 = 0, $761 = 0, $762 = 0, $763 = 0, $764 = 0, $765 = 0, $766 = 0, $767 = 0, $768 = 0, $769 = 0, $77 = 0, $770 = 0, $771 = 0, $772 = 0, $773 = 0, $774 = 0, $775 = 0;
 var $776 = 0, $777 = 0, $778 = 0, $779 = 0, $78 = 0, $780 = 0, $781 = 0, $782 = 0, $783 = 0, $784 = 0, $785 = 0, $786 = 0, $787 = 0, $788 = 0, $789 = 0, $79 = 0, $790 = 0, $791 = 0, $792 = 0, $793 = 0;
 var $794 = 0, $795 = 0, $796 = 0, $797 = 0, $798 = 0, $799 = 0, $8 = 0, $80 = 0, $800 = 0, $801 = 0, $802 = 0, $803 = 0, $804 = 0, $805 = 0, $806 = 0, $807 = 0, $808 = 0, $809 = 0, $81 = 0, $810 = 0;
 var $811 = 0, $812 = 0, $813 = 0, $814 = 0, $815 = 0, $816 = 0, $817 = 0, $818 = 0, $819 = 0, $82 = 0, $820 = 0, $821 = 0, $822 = 0, $823 = 0, $824 = 0, $825 = 0, $826 = 0, $827 = 0, $828 = 0, $829 = 0;
 var $83 = 0, $830 = 0, $831 = 0, $832 = 0, $833 = 0, $834 = 0, $835 = 0, $836 = 0, $837 = 0, $838 = 0, $839 = 0, $84 = 0, $840 = 0, $841 = 0, $842 = 0, $843 = 0, $844 = 0, $845 = 0, $846 = 0, $847 = 0;
 var $848 = 0, $849 = 0, $85 = 0, $850 = 0, $851 = 0, $852 = 0, $853 = 0, $854 = 0, $855 = 0, $856 = 0, $857 = 0, $858 = 0, $859 = 0, $86 = 0, $860 = 0, $861 = 0, $862 = 0, $863 = 0, $864 = 0, $865 = 0;
 var $866 = 0, $867 = 0, $868 = 0, $869 = 0, $87 = 0, $870 = 0, $871 = 0, $872 = 0, $873 = 0, $874 = 0, $875 = 0, $876 = 0, $877 = 0, $878 = 0, $879 = 0, $88 = 0, $880 = 0, $881 = 0, $882 = 0, $883 = 0;
 var $884 = 0, $885 = 0, $886 = 0, $887 = 0, $888 = 0, $889 = 0, $89 = 0, $890 = 0, $891 = 0, $892 = 0, $893 = 0, $894 = 0, $895 = 0, $896 = 0, $897 = 0, $898 = 0, $899 = 0, $9 = 0, $90 = 0, $900 = 0;
 var $901 = 0, $902 = 0, $903 = 0, $904 = 0, $905 = 0, $906 = 0, $907 = 0, $908 = 0, $909 = 0, $91 = 0, $910 = 0, $911 = 0, $912 = 0, $913 = 0, $914 = 0, $915 = 0, $916 = 0, $917 = 0, $918 = 0, $919 = 0;
 var $92 = 0, $920 = 0, $921 = 0, $922 = 0, $923 = 0, $924 = 0, $925 = 0, $926 = 0, $927 = 0, $928 = 0, $929 = 0, $93 = 0, $930 = 0, $931 = 0, $932 = 0, $933 = 0, $934 = 0, $935 = 0, $936 = 0, $937 = 0;
 var $938 = 0, $939 = 0, $94 = 0, $940 = 0, $941 = 0, $942 = 0, $943 = 0, $944 = 0, $945 = 0, $946 = 0, $947 = 0, $948 = 0, $949 = 0, $95 = 0, $950 = 0, $951 = 0, $952 = 0, $953 = 0, $954 = 0, $955 = 0;
 var $956 = 0, $957 = 0, $958 = 0, $959 = 0, $96 = 0, $960 = 0, $961 = 0, $962 = 0, $963 = 0, $964 = 0, $965 = 0, $966 = 0, $967 = 0, $968 = 0, $969 = 0, $97 = 0, $970 = 0, $971 = 0, $972 = 0, $973 = 0;
 var $974 = 0, $975 = 0, $976 = 0, $977 = 0, $978 = 0, $979 = 0, $98 = 0, $980 = 0, $981 = 0, $982 = 0, $983 = 0, $984 = 0, $985 = 0, $986 = 0, $987 = 0, $988 = 0, $989 = 0, $99 = 0, $990 = 0, $991 = 0;
 var $992 = 0, $993 = 0, $994 = 0, $995 = 0, $996 = 0, $997 = 0, $998 = 0, $999 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $3 = $1;
 $4 = $3;
 $5 = HEAP32[$4>>2]|0;
 $6 = (($3) + 4)|0;
 $7 = $6;
 $8 = HEAP32[$7>>2]|0;
 $9 = (_bitshift64Ashr(0,($5|0),32)|0);
 $10 = tempRet0;
 $11 = $2;
 $12 = $11;
 $13 = HEAP32[$12>>2]|0;
 $14 = (($11) + 4)|0;
 $15 = $14;
 $16 = HEAP32[$15>>2]|0;
 $17 = (_bitshift64Ashr(0,($13|0),32)|0);
 $18 = tempRet0;
 $19 = (___muldi3(($17|0),($18|0),($9|0),($10|0))|0);
 $20 = tempRet0;
 $21 = $0;
 $22 = $21;
 HEAP32[$22>>2] = $19;
 $23 = (($21) + 4)|0;
 $24 = $23;
 HEAP32[$24>>2] = $20;
 $25 = $1;
 $26 = $25;
 $27 = HEAP32[$26>>2]|0;
 $28 = (($25) + 4)|0;
 $29 = $28;
 $30 = HEAP32[$29>>2]|0;
 $31 = (_bitshift64Ashr(0,($27|0),32)|0);
 $32 = tempRet0;
 $33 = ((($2)) + 8|0);
 $34 = $33;
 $35 = $34;
 $36 = HEAP32[$35>>2]|0;
 $37 = (($34) + 4)|0;
 $38 = $37;
 $39 = HEAP32[$38>>2]|0;
 $40 = (_bitshift64Ashr(0,($36|0),32)|0);
 $41 = tempRet0;
 $42 = (___muldi3(($40|0),($41|0),($31|0),($32|0))|0);
 $43 = tempRet0;
 $44 = ((($1)) + 8|0);
 $45 = $44;
 $46 = $45;
 $47 = HEAP32[$46>>2]|0;
 $48 = (($45) + 4)|0;
 $49 = $48;
 $50 = HEAP32[$49>>2]|0;
 $51 = (_bitshift64Ashr(0,($47|0),32)|0);
 $52 = tempRet0;
 $53 = $2;
 $54 = $53;
 $55 = HEAP32[$54>>2]|0;
 $56 = (($53) + 4)|0;
 $57 = $56;
 $58 = HEAP32[$57>>2]|0;
 $59 = (_bitshift64Ashr(0,($55|0),32)|0);
 $60 = tempRet0;
 $61 = (___muldi3(($59|0),($60|0),($51|0),($52|0))|0);
 $62 = tempRet0;
 $63 = (_i64Add(($61|0),($62|0),($42|0),($43|0))|0);
 $64 = tempRet0;
 $65 = ((($0)) + 8|0);
 $66 = $65;
 $67 = $66;
 HEAP32[$67>>2] = $63;
 $68 = (($66) + 4)|0;
 $69 = $68;
 HEAP32[$69>>2] = $64;
 $70 = $44;
 $71 = $70;
 $72 = HEAP32[$71>>2]|0;
 $73 = (($70) + 4)|0;
 $74 = $73;
 $75 = HEAP32[$74>>2]|0;
 $76 = (_bitshift64Ashr(0,($72|0),31)|0);
 $77 = tempRet0;
 $78 = $33;
 $79 = $78;
 $80 = HEAP32[$79>>2]|0;
 $81 = (($78) + 4)|0;
 $82 = $81;
 $83 = HEAP32[$82>>2]|0;
 $84 = (_bitshift64Ashr(0,($80|0),32)|0);
 $85 = tempRet0;
 $86 = (___muldi3(($84|0),($85|0),($76|0),($77|0))|0);
 $87 = tempRet0;
 $88 = $1;
 $89 = $88;
 $90 = HEAP32[$89>>2]|0;
 $91 = (($88) + 4)|0;
 $92 = $91;
 $93 = HEAP32[$92>>2]|0;
 $94 = (_bitshift64Ashr(0,($90|0),32)|0);
 $95 = tempRet0;
 $96 = ((($2)) + 16|0);
 $97 = $96;
 $98 = $97;
 $99 = HEAP32[$98>>2]|0;
 $100 = (($97) + 4)|0;
 $101 = $100;
 $102 = HEAP32[$101>>2]|0;
 $103 = (_bitshift64Ashr(0,($99|0),32)|0);
 $104 = tempRet0;
 $105 = (___muldi3(($103|0),($104|0),($94|0),($95|0))|0);
 $106 = tempRet0;
 $107 = (_i64Add(($105|0),($106|0),($86|0),($87|0))|0);
 $108 = tempRet0;
 $109 = ((($1)) + 16|0);
 $110 = $109;
 $111 = $110;
 $112 = HEAP32[$111>>2]|0;
 $113 = (($110) + 4)|0;
 $114 = $113;
 $115 = HEAP32[$114>>2]|0;
 $116 = (_bitshift64Ashr(0,($112|0),32)|0);
 $117 = tempRet0;
 $118 = $2;
 $119 = $118;
 $120 = HEAP32[$119>>2]|0;
 $121 = (($118) + 4)|0;
 $122 = $121;
 $123 = HEAP32[$122>>2]|0;
 $124 = (_bitshift64Ashr(0,($120|0),32)|0);
 $125 = tempRet0;
 $126 = (___muldi3(($124|0),($125|0),($116|0),($117|0))|0);
 $127 = tempRet0;
 $128 = (_i64Add(($107|0),($108|0),($126|0),($127|0))|0);
 $129 = tempRet0;
 $130 = ((($0)) + 16|0);
 $131 = $130;
 $132 = $131;
 HEAP32[$132>>2] = $128;
 $133 = (($131) + 4)|0;
 $134 = $133;
 HEAP32[$134>>2] = $129;
 $135 = $44;
 $136 = $135;
 $137 = HEAP32[$136>>2]|0;
 $138 = (($135) + 4)|0;
 $139 = $138;
 $140 = HEAP32[$139>>2]|0;
 $141 = (_bitshift64Ashr(0,($137|0),32)|0);
 $142 = tempRet0;
 $143 = $96;
 $144 = $143;
 $145 = HEAP32[$144>>2]|0;
 $146 = (($143) + 4)|0;
 $147 = $146;
 $148 = HEAP32[$147>>2]|0;
 $149 = (_bitshift64Ashr(0,($145|0),32)|0);
 $150 = tempRet0;
 $151 = (___muldi3(($149|0),($150|0),($141|0),($142|0))|0);
 $152 = tempRet0;
 $153 = $109;
 $154 = $153;
 $155 = HEAP32[$154>>2]|0;
 $156 = (($153) + 4)|0;
 $157 = $156;
 $158 = HEAP32[$157>>2]|0;
 $159 = (_bitshift64Ashr(0,($155|0),32)|0);
 $160 = tempRet0;
 $161 = $33;
 $162 = $161;
 $163 = HEAP32[$162>>2]|0;
 $164 = (($161) + 4)|0;
 $165 = $164;
 $166 = HEAP32[$165>>2]|0;
 $167 = (_bitshift64Ashr(0,($163|0),32)|0);
 $168 = tempRet0;
 $169 = (___muldi3(($167|0),($168|0),($159|0),($160|0))|0);
 $170 = tempRet0;
 $171 = (_i64Add(($169|0),($170|0),($151|0),($152|0))|0);
 $172 = tempRet0;
 $173 = $1;
 $174 = $173;
 $175 = HEAP32[$174>>2]|0;
 $176 = (($173) + 4)|0;
 $177 = $176;
 $178 = HEAP32[$177>>2]|0;
 $179 = (_bitshift64Ashr(0,($175|0),32)|0);
 $180 = tempRet0;
 $181 = ((($2)) + 24|0);
 $182 = $181;
 $183 = $182;
 $184 = HEAP32[$183>>2]|0;
 $185 = (($182) + 4)|0;
 $186 = $185;
 $187 = HEAP32[$186>>2]|0;
 $188 = (_bitshift64Ashr(0,($184|0),32)|0);
 $189 = tempRet0;
 $190 = (___muldi3(($188|0),($189|0),($179|0),($180|0))|0);
 $191 = tempRet0;
 $192 = (_i64Add(($171|0),($172|0),($190|0),($191|0))|0);
 $193 = tempRet0;
 $194 = ((($1)) + 24|0);
 $195 = $194;
 $196 = $195;
 $197 = HEAP32[$196>>2]|0;
 $198 = (($195) + 4)|0;
 $199 = $198;
 $200 = HEAP32[$199>>2]|0;
 $201 = (_bitshift64Ashr(0,($197|0),32)|0);
 $202 = tempRet0;
 $203 = $2;
 $204 = $203;
 $205 = HEAP32[$204>>2]|0;
 $206 = (($203) + 4)|0;
 $207 = $206;
 $208 = HEAP32[$207>>2]|0;
 $209 = (_bitshift64Ashr(0,($205|0),32)|0);
 $210 = tempRet0;
 $211 = (___muldi3(($209|0),($210|0),($201|0),($202|0))|0);
 $212 = tempRet0;
 $213 = (_i64Add(($192|0),($193|0),($211|0),($212|0))|0);
 $214 = tempRet0;
 $215 = ((($0)) + 24|0);
 $216 = $215;
 $217 = $216;
 HEAP32[$217>>2] = $213;
 $218 = (($216) + 4)|0;
 $219 = $218;
 HEAP32[$219>>2] = $214;
 $220 = $109;
 $221 = $220;
 $222 = HEAP32[$221>>2]|0;
 $223 = (($220) + 4)|0;
 $224 = $223;
 $225 = HEAP32[$224>>2]|0;
 $226 = (_bitshift64Ashr(0,($222|0),32)|0);
 $227 = tempRet0;
 $228 = $96;
 $229 = $228;
 $230 = HEAP32[$229>>2]|0;
 $231 = (($228) + 4)|0;
 $232 = $231;
 $233 = HEAP32[$232>>2]|0;
 $234 = (_bitshift64Ashr(0,($230|0),32)|0);
 $235 = tempRet0;
 $236 = (___muldi3(($234|0),($235|0),($226|0),($227|0))|0);
 $237 = tempRet0;
 $238 = $44;
 $239 = $238;
 $240 = HEAP32[$239>>2]|0;
 $241 = (($238) + 4)|0;
 $242 = $241;
 $243 = HEAP32[$242>>2]|0;
 $244 = (_bitshift64Ashr(0,($240|0),32)|0);
 $245 = tempRet0;
 $246 = $181;
 $247 = $246;
 $248 = HEAP32[$247>>2]|0;
 $249 = (($246) + 4)|0;
 $250 = $249;
 $251 = HEAP32[$250>>2]|0;
 $252 = (_bitshift64Ashr(0,($248|0),32)|0);
 $253 = tempRet0;
 $254 = (___muldi3(($252|0),($253|0),($244|0),($245|0))|0);
 $255 = tempRet0;
 $256 = $194;
 $257 = $256;
 $258 = HEAP32[$257>>2]|0;
 $259 = (($256) + 4)|0;
 $260 = $259;
 $261 = HEAP32[$260>>2]|0;
 $262 = (_bitshift64Ashr(0,($258|0),32)|0);
 $263 = tempRet0;
 $264 = $33;
 $265 = $264;
 $266 = HEAP32[$265>>2]|0;
 $267 = (($264) + 4)|0;
 $268 = $267;
 $269 = HEAP32[$268>>2]|0;
 $270 = (_bitshift64Ashr(0,($266|0),32)|0);
 $271 = tempRet0;
 $272 = (___muldi3(($270|0),($271|0),($262|0),($263|0))|0);
 $273 = tempRet0;
 $274 = (_i64Add(($272|0),($273|0),($254|0),($255|0))|0);
 $275 = tempRet0;
 $276 = (_bitshift64Shl(($274|0),($275|0),1)|0);
 $277 = tempRet0;
 $278 = (_i64Add(($276|0),($277|0),($236|0),($237|0))|0);
 $279 = tempRet0;
 $280 = $1;
 $281 = $280;
 $282 = HEAP32[$281>>2]|0;
 $283 = (($280) + 4)|0;
 $284 = $283;
 $285 = HEAP32[$284>>2]|0;
 $286 = (_bitshift64Ashr(0,($282|0),32)|0);
 $287 = tempRet0;
 $288 = ((($2)) + 32|0);
 $289 = $288;
 $290 = $289;
 $291 = HEAP32[$290>>2]|0;
 $292 = (($289) + 4)|0;
 $293 = $292;
 $294 = HEAP32[$293>>2]|0;
 $295 = (_bitshift64Ashr(0,($291|0),32)|0);
 $296 = tempRet0;
 $297 = (___muldi3(($295|0),($296|0),($286|0),($287|0))|0);
 $298 = tempRet0;
 $299 = (_i64Add(($278|0),($279|0),($297|0),($298|0))|0);
 $300 = tempRet0;
 $301 = ((($1)) + 32|0);
 $302 = $301;
 $303 = $302;
 $304 = HEAP32[$303>>2]|0;
 $305 = (($302) + 4)|0;
 $306 = $305;
 $307 = HEAP32[$306>>2]|0;
 $308 = (_bitshift64Ashr(0,($304|0),32)|0);
 $309 = tempRet0;
 $310 = $2;
 $311 = $310;
 $312 = HEAP32[$311>>2]|0;
 $313 = (($310) + 4)|0;
 $314 = $313;
 $315 = HEAP32[$314>>2]|0;
 $316 = (_bitshift64Ashr(0,($312|0),32)|0);
 $317 = tempRet0;
 $318 = (___muldi3(($316|0),($317|0),($308|0),($309|0))|0);
 $319 = tempRet0;
 $320 = (_i64Add(($299|0),($300|0),($318|0),($319|0))|0);
 $321 = tempRet0;
 $322 = ((($0)) + 32|0);
 $323 = $322;
 $324 = $323;
 HEAP32[$324>>2] = $320;
 $325 = (($323) + 4)|0;
 $326 = $325;
 HEAP32[$326>>2] = $321;
 $327 = $109;
 $328 = $327;
 $329 = HEAP32[$328>>2]|0;
 $330 = (($327) + 4)|0;
 $331 = $330;
 $332 = HEAP32[$331>>2]|0;
 $333 = (_bitshift64Ashr(0,($329|0),32)|0);
 $334 = tempRet0;
 $335 = $181;
 $336 = $335;
 $337 = HEAP32[$336>>2]|0;
 $338 = (($335) + 4)|0;
 $339 = $338;
 $340 = HEAP32[$339>>2]|0;
 $341 = (_bitshift64Ashr(0,($337|0),32)|0);
 $342 = tempRet0;
 $343 = (___muldi3(($341|0),($342|0),($333|0),($334|0))|0);
 $344 = tempRet0;
 $345 = $194;
 $346 = $345;
 $347 = HEAP32[$346>>2]|0;
 $348 = (($345) + 4)|0;
 $349 = $348;
 $350 = HEAP32[$349>>2]|0;
 $351 = (_bitshift64Ashr(0,($347|0),32)|0);
 $352 = tempRet0;
 $353 = $96;
 $354 = $353;
 $355 = HEAP32[$354>>2]|0;
 $356 = (($353) + 4)|0;
 $357 = $356;
 $358 = HEAP32[$357>>2]|0;
 $359 = (_bitshift64Ashr(0,($355|0),32)|0);
 $360 = tempRet0;
 $361 = (___muldi3(($359|0),($360|0),($351|0),($352|0))|0);
 $362 = tempRet0;
 $363 = (_i64Add(($361|0),($362|0),($343|0),($344|0))|0);
 $364 = tempRet0;
 $365 = $44;
 $366 = $365;
 $367 = HEAP32[$366>>2]|0;
 $368 = (($365) + 4)|0;
 $369 = $368;
 $370 = HEAP32[$369>>2]|0;
 $371 = (_bitshift64Ashr(0,($367|0),32)|0);
 $372 = tempRet0;
 $373 = $288;
 $374 = $373;
 $375 = HEAP32[$374>>2]|0;
 $376 = (($373) + 4)|0;
 $377 = $376;
 $378 = HEAP32[$377>>2]|0;
 $379 = (_bitshift64Ashr(0,($375|0),32)|0);
 $380 = tempRet0;
 $381 = (___muldi3(($379|0),($380|0),($371|0),($372|0))|0);
 $382 = tempRet0;
 $383 = (_i64Add(($363|0),($364|0),($381|0),($382|0))|0);
 $384 = tempRet0;
 $385 = $301;
 $386 = $385;
 $387 = HEAP32[$386>>2]|0;
 $388 = (($385) + 4)|0;
 $389 = $388;
 $390 = HEAP32[$389>>2]|0;
 $391 = (_bitshift64Ashr(0,($387|0),32)|0);
 $392 = tempRet0;
 $393 = $33;
 $394 = $393;
 $395 = HEAP32[$394>>2]|0;
 $396 = (($393) + 4)|0;
 $397 = $396;
 $398 = HEAP32[$397>>2]|0;
 $399 = (_bitshift64Ashr(0,($395|0),32)|0);
 $400 = tempRet0;
 $401 = (___muldi3(($399|0),($400|0),($391|0),($392|0))|0);
 $402 = tempRet0;
 $403 = (_i64Add(($383|0),($384|0),($401|0),($402|0))|0);
 $404 = tempRet0;
 $405 = $1;
 $406 = $405;
 $407 = HEAP32[$406>>2]|0;
 $408 = (($405) + 4)|0;
 $409 = $408;
 $410 = HEAP32[$409>>2]|0;
 $411 = (_bitshift64Ashr(0,($407|0),32)|0);
 $412 = tempRet0;
 $413 = ((($2)) + 40|0);
 $414 = $413;
 $415 = $414;
 $416 = HEAP32[$415>>2]|0;
 $417 = (($414) + 4)|0;
 $418 = $417;
 $419 = HEAP32[$418>>2]|0;
 $420 = (_bitshift64Ashr(0,($416|0),32)|0);
 $421 = tempRet0;
 $422 = (___muldi3(($420|0),($421|0),($411|0),($412|0))|0);
 $423 = tempRet0;
 $424 = (_i64Add(($403|0),($404|0),($422|0),($423|0))|0);
 $425 = tempRet0;
 $426 = ((($1)) + 40|0);
 $427 = $426;
 $428 = $427;
 $429 = HEAP32[$428>>2]|0;
 $430 = (($427) + 4)|0;
 $431 = $430;
 $432 = HEAP32[$431>>2]|0;
 $433 = (_bitshift64Ashr(0,($429|0),32)|0);
 $434 = tempRet0;
 $435 = $2;
 $436 = $435;
 $437 = HEAP32[$436>>2]|0;
 $438 = (($435) + 4)|0;
 $439 = $438;
 $440 = HEAP32[$439>>2]|0;
 $441 = (_bitshift64Ashr(0,($437|0),32)|0);
 $442 = tempRet0;
 $443 = (___muldi3(($441|0),($442|0),($433|0),($434|0))|0);
 $444 = tempRet0;
 $445 = (_i64Add(($424|0),($425|0),($443|0),($444|0))|0);
 $446 = tempRet0;
 $447 = ((($0)) + 40|0);
 $448 = $447;
 $449 = $448;
 HEAP32[$449>>2] = $445;
 $450 = (($448) + 4)|0;
 $451 = $450;
 HEAP32[$451>>2] = $446;
 $452 = $194;
 $453 = $452;
 $454 = HEAP32[$453>>2]|0;
 $455 = (($452) + 4)|0;
 $456 = $455;
 $457 = HEAP32[$456>>2]|0;
 $458 = (_bitshift64Ashr(0,($454|0),32)|0);
 $459 = tempRet0;
 $460 = $181;
 $461 = $460;
 $462 = HEAP32[$461>>2]|0;
 $463 = (($460) + 4)|0;
 $464 = $463;
 $465 = HEAP32[$464>>2]|0;
 $466 = (_bitshift64Ashr(0,($462|0),32)|0);
 $467 = tempRet0;
 $468 = (___muldi3(($466|0),($467|0),($458|0),($459|0))|0);
 $469 = tempRet0;
 $470 = $44;
 $471 = $470;
 $472 = HEAP32[$471>>2]|0;
 $473 = (($470) + 4)|0;
 $474 = $473;
 $475 = HEAP32[$474>>2]|0;
 $476 = (_bitshift64Ashr(0,($472|0),32)|0);
 $477 = tempRet0;
 $478 = $413;
 $479 = $478;
 $480 = HEAP32[$479>>2]|0;
 $481 = (($478) + 4)|0;
 $482 = $481;
 $483 = HEAP32[$482>>2]|0;
 $484 = (_bitshift64Ashr(0,($480|0),32)|0);
 $485 = tempRet0;
 $486 = (___muldi3(($484|0),($485|0),($476|0),($477|0))|0);
 $487 = tempRet0;
 $488 = (_i64Add(($486|0),($487|0),($468|0),($469|0))|0);
 $489 = tempRet0;
 $490 = $426;
 $491 = $490;
 $492 = HEAP32[$491>>2]|0;
 $493 = (($490) + 4)|0;
 $494 = $493;
 $495 = HEAP32[$494>>2]|0;
 $496 = (_bitshift64Ashr(0,($492|0),32)|0);
 $497 = tempRet0;
 $498 = $33;
 $499 = $498;
 $500 = HEAP32[$499>>2]|0;
 $501 = (($498) + 4)|0;
 $502 = $501;
 $503 = HEAP32[$502>>2]|0;
 $504 = (_bitshift64Ashr(0,($500|0),32)|0);
 $505 = tempRet0;
 $506 = (___muldi3(($504|0),($505|0),($496|0),($497|0))|0);
 $507 = tempRet0;
 $508 = (_i64Add(($488|0),($489|0),($506|0),($507|0))|0);
 $509 = tempRet0;
 $510 = (_bitshift64Shl(($508|0),($509|0),1)|0);
 $511 = tempRet0;
 $512 = $109;
 $513 = $512;
 $514 = HEAP32[$513>>2]|0;
 $515 = (($512) + 4)|0;
 $516 = $515;
 $517 = HEAP32[$516>>2]|0;
 $518 = (_bitshift64Ashr(0,($514|0),32)|0);
 $519 = tempRet0;
 $520 = $288;
 $521 = $520;
 $522 = HEAP32[$521>>2]|0;
 $523 = (($520) + 4)|0;
 $524 = $523;
 $525 = HEAP32[$524>>2]|0;
 $526 = (_bitshift64Ashr(0,($522|0),32)|0);
 $527 = tempRet0;
 $528 = (___muldi3(($526|0),($527|0),($518|0),($519|0))|0);
 $529 = tempRet0;
 $530 = (_i64Add(($510|0),($511|0),($528|0),($529|0))|0);
 $531 = tempRet0;
 $532 = $301;
 $533 = $532;
 $534 = HEAP32[$533>>2]|0;
 $535 = (($532) + 4)|0;
 $536 = $535;
 $537 = HEAP32[$536>>2]|0;
 $538 = (_bitshift64Ashr(0,($534|0),32)|0);
 $539 = tempRet0;
 $540 = $96;
 $541 = $540;
 $542 = HEAP32[$541>>2]|0;
 $543 = (($540) + 4)|0;
 $544 = $543;
 $545 = HEAP32[$544>>2]|0;
 $546 = (_bitshift64Ashr(0,($542|0),32)|0);
 $547 = tempRet0;
 $548 = (___muldi3(($546|0),($547|0),($538|0),($539|0))|0);
 $549 = tempRet0;
 $550 = (_i64Add(($530|0),($531|0),($548|0),($549|0))|0);
 $551 = tempRet0;
 $552 = $1;
 $553 = $552;
 $554 = HEAP32[$553>>2]|0;
 $555 = (($552) + 4)|0;
 $556 = $555;
 $557 = HEAP32[$556>>2]|0;
 $558 = (_bitshift64Ashr(0,($554|0),32)|0);
 $559 = tempRet0;
 $560 = ((($2)) + 48|0);
 $561 = $560;
 $562 = $561;
 $563 = HEAP32[$562>>2]|0;
 $564 = (($561) + 4)|0;
 $565 = $564;
 $566 = HEAP32[$565>>2]|0;
 $567 = (_bitshift64Ashr(0,($563|0),32)|0);
 $568 = tempRet0;
 $569 = (___muldi3(($567|0),($568|0),($558|0),($559|0))|0);
 $570 = tempRet0;
 $571 = (_i64Add(($550|0),($551|0),($569|0),($570|0))|0);
 $572 = tempRet0;
 $573 = ((($1)) + 48|0);
 $574 = $573;
 $575 = $574;
 $576 = HEAP32[$575>>2]|0;
 $577 = (($574) + 4)|0;
 $578 = $577;
 $579 = HEAP32[$578>>2]|0;
 $580 = (_bitshift64Ashr(0,($576|0),32)|0);
 $581 = tempRet0;
 $582 = $2;
 $583 = $582;
 $584 = HEAP32[$583>>2]|0;
 $585 = (($582) + 4)|0;
 $586 = $585;
 $587 = HEAP32[$586>>2]|0;
 $588 = (_bitshift64Ashr(0,($584|0),32)|0);
 $589 = tempRet0;
 $590 = (___muldi3(($588|0),($589|0),($580|0),($581|0))|0);
 $591 = tempRet0;
 $592 = (_i64Add(($571|0),($572|0),($590|0),($591|0))|0);
 $593 = tempRet0;
 $594 = ((($0)) + 48|0);
 $595 = $594;
 $596 = $595;
 HEAP32[$596>>2] = $592;
 $597 = (($595) + 4)|0;
 $598 = $597;
 HEAP32[$598>>2] = $593;
 $599 = $194;
 $600 = $599;
 $601 = HEAP32[$600>>2]|0;
 $602 = (($599) + 4)|0;
 $603 = $602;
 $604 = HEAP32[$603>>2]|0;
 $605 = (_bitshift64Ashr(0,($601|0),32)|0);
 $606 = tempRet0;
 $607 = $288;
 $608 = $607;
 $609 = HEAP32[$608>>2]|0;
 $610 = (($607) + 4)|0;
 $611 = $610;
 $612 = HEAP32[$611>>2]|0;
 $613 = (_bitshift64Ashr(0,($609|0),32)|0);
 $614 = tempRet0;
 $615 = (___muldi3(($613|0),($614|0),($605|0),($606|0))|0);
 $616 = tempRet0;
 $617 = $301;
 $618 = $617;
 $619 = HEAP32[$618>>2]|0;
 $620 = (($617) + 4)|0;
 $621 = $620;
 $622 = HEAP32[$621>>2]|0;
 $623 = (_bitshift64Ashr(0,($619|0),32)|0);
 $624 = tempRet0;
 $625 = $181;
 $626 = $625;
 $627 = HEAP32[$626>>2]|0;
 $628 = (($625) + 4)|0;
 $629 = $628;
 $630 = HEAP32[$629>>2]|0;
 $631 = (_bitshift64Ashr(0,($627|0),32)|0);
 $632 = tempRet0;
 $633 = (___muldi3(($631|0),($632|0),($623|0),($624|0))|0);
 $634 = tempRet0;
 $635 = (_i64Add(($633|0),($634|0),($615|0),($616|0))|0);
 $636 = tempRet0;
 $637 = $109;
 $638 = $637;
 $639 = HEAP32[$638>>2]|0;
 $640 = (($637) + 4)|0;
 $641 = $640;
 $642 = HEAP32[$641>>2]|0;
 $643 = (_bitshift64Ashr(0,($639|0),32)|0);
 $644 = tempRet0;
 $645 = $413;
 $646 = $645;
 $647 = HEAP32[$646>>2]|0;
 $648 = (($645) + 4)|0;
 $649 = $648;
 $650 = HEAP32[$649>>2]|0;
 $651 = (_bitshift64Ashr(0,($647|0),32)|0);
 $652 = tempRet0;
 $653 = (___muldi3(($651|0),($652|0),($643|0),($644|0))|0);
 $654 = tempRet0;
 $655 = (_i64Add(($635|0),($636|0),($653|0),($654|0))|0);
 $656 = tempRet0;
 $657 = $426;
 $658 = $657;
 $659 = HEAP32[$658>>2]|0;
 $660 = (($657) + 4)|0;
 $661 = $660;
 $662 = HEAP32[$661>>2]|0;
 $663 = (_bitshift64Ashr(0,($659|0),32)|0);
 $664 = tempRet0;
 $665 = $96;
 $666 = $665;
 $667 = HEAP32[$666>>2]|0;
 $668 = (($665) + 4)|0;
 $669 = $668;
 $670 = HEAP32[$669>>2]|0;
 $671 = (_bitshift64Ashr(0,($667|0),32)|0);
 $672 = tempRet0;
 $673 = (___muldi3(($671|0),($672|0),($663|0),($664|0))|0);
 $674 = tempRet0;
 $675 = (_i64Add(($655|0),($656|0),($673|0),($674|0))|0);
 $676 = tempRet0;
 $677 = $44;
 $678 = $677;
 $679 = HEAP32[$678>>2]|0;
 $680 = (($677) + 4)|0;
 $681 = $680;
 $682 = HEAP32[$681>>2]|0;
 $683 = (_bitshift64Ashr(0,($679|0),32)|0);
 $684 = tempRet0;
 $685 = $560;
 $686 = $685;
 $687 = HEAP32[$686>>2]|0;
 $688 = (($685) + 4)|0;
 $689 = $688;
 $690 = HEAP32[$689>>2]|0;
 $691 = (_bitshift64Ashr(0,($687|0),32)|0);
 $692 = tempRet0;
 $693 = (___muldi3(($691|0),($692|0),($683|0),($684|0))|0);
 $694 = tempRet0;
 $695 = (_i64Add(($675|0),($676|0),($693|0),($694|0))|0);
 $696 = tempRet0;
 $697 = $573;
 $698 = $697;
 $699 = HEAP32[$698>>2]|0;
 $700 = (($697) + 4)|0;
 $701 = $700;
 $702 = HEAP32[$701>>2]|0;
 $703 = (_bitshift64Ashr(0,($699|0),32)|0);
 $704 = tempRet0;
 $705 = $33;
 $706 = $705;
 $707 = HEAP32[$706>>2]|0;
 $708 = (($705) + 4)|0;
 $709 = $708;
 $710 = HEAP32[$709>>2]|0;
 $711 = (_bitshift64Ashr(0,($707|0),32)|0);
 $712 = tempRet0;
 $713 = (___muldi3(($711|0),($712|0),($703|0),($704|0))|0);
 $714 = tempRet0;
 $715 = (_i64Add(($695|0),($696|0),($713|0),($714|0))|0);
 $716 = tempRet0;
 $717 = $1;
 $718 = $717;
 $719 = HEAP32[$718>>2]|0;
 $720 = (($717) + 4)|0;
 $721 = $720;
 $722 = HEAP32[$721>>2]|0;
 $723 = (_bitshift64Ashr(0,($719|0),32)|0);
 $724 = tempRet0;
 $725 = ((($2)) + 56|0);
 $726 = $725;
 $727 = $726;
 $728 = HEAP32[$727>>2]|0;
 $729 = (($726) + 4)|0;
 $730 = $729;
 $731 = HEAP32[$730>>2]|0;
 $732 = (_bitshift64Ashr(0,($728|0),32)|0);
 $733 = tempRet0;
 $734 = (___muldi3(($732|0),($733|0),($723|0),($724|0))|0);
 $735 = tempRet0;
 $736 = (_i64Add(($715|0),($716|0),($734|0),($735|0))|0);
 $737 = tempRet0;
 $738 = ((($1)) + 56|0);
 $739 = $738;
 $740 = $739;
 $741 = HEAP32[$740>>2]|0;
 $742 = (($739) + 4)|0;
 $743 = $742;
 $744 = HEAP32[$743>>2]|0;
 $745 = (_bitshift64Ashr(0,($741|0),32)|0);
 $746 = tempRet0;
 $747 = $2;
 $748 = $747;
 $749 = HEAP32[$748>>2]|0;
 $750 = (($747) + 4)|0;
 $751 = $750;
 $752 = HEAP32[$751>>2]|0;
 $753 = (_bitshift64Ashr(0,($749|0),32)|0);
 $754 = tempRet0;
 $755 = (___muldi3(($753|0),($754|0),($745|0),($746|0))|0);
 $756 = tempRet0;
 $757 = (_i64Add(($736|0),($737|0),($755|0),($756|0))|0);
 $758 = tempRet0;
 $759 = ((($0)) + 56|0);
 $760 = $759;
 $761 = $760;
 HEAP32[$761>>2] = $757;
 $762 = (($760) + 4)|0;
 $763 = $762;
 HEAP32[$763>>2] = $758;
 $764 = $301;
 $765 = $764;
 $766 = HEAP32[$765>>2]|0;
 $767 = (($764) + 4)|0;
 $768 = $767;
 $769 = HEAP32[$768>>2]|0;
 $770 = (_bitshift64Ashr(0,($766|0),32)|0);
 $771 = tempRet0;
 $772 = $288;
 $773 = $772;
 $774 = HEAP32[$773>>2]|0;
 $775 = (($772) + 4)|0;
 $776 = $775;
 $777 = HEAP32[$776>>2]|0;
 $778 = (_bitshift64Ashr(0,($774|0),32)|0);
 $779 = tempRet0;
 $780 = (___muldi3(($778|0),($779|0),($770|0),($771|0))|0);
 $781 = tempRet0;
 $782 = $194;
 $783 = $782;
 $784 = HEAP32[$783>>2]|0;
 $785 = (($782) + 4)|0;
 $786 = $785;
 $787 = HEAP32[$786>>2]|0;
 $788 = (_bitshift64Ashr(0,($784|0),32)|0);
 $789 = tempRet0;
 $790 = $413;
 $791 = $790;
 $792 = HEAP32[$791>>2]|0;
 $793 = (($790) + 4)|0;
 $794 = $793;
 $795 = HEAP32[$794>>2]|0;
 $796 = (_bitshift64Ashr(0,($792|0),32)|0);
 $797 = tempRet0;
 $798 = (___muldi3(($796|0),($797|0),($788|0),($789|0))|0);
 $799 = tempRet0;
 $800 = $426;
 $801 = $800;
 $802 = HEAP32[$801>>2]|0;
 $803 = (($800) + 4)|0;
 $804 = $803;
 $805 = HEAP32[$804>>2]|0;
 $806 = (_bitshift64Ashr(0,($802|0),32)|0);
 $807 = tempRet0;
 $808 = $181;
 $809 = $808;
 $810 = HEAP32[$809>>2]|0;
 $811 = (($808) + 4)|0;
 $812 = $811;
 $813 = HEAP32[$812>>2]|0;
 $814 = (_bitshift64Ashr(0,($810|0),32)|0);
 $815 = tempRet0;
 $816 = (___muldi3(($814|0),($815|0),($806|0),($807|0))|0);
 $817 = tempRet0;
 $818 = (_i64Add(($816|0),($817|0),($798|0),($799|0))|0);
 $819 = tempRet0;
 $820 = $44;
 $821 = $820;
 $822 = HEAP32[$821>>2]|0;
 $823 = (($820) + 4)|0;
 $824 = $823;
 $825 = HEAP32[$824>>2]|0;
 $826 = (_bitshift64Ashr(0,($822|0),32)|0);
 $827 = tempRet0;
 $828 = $725;
 $829 = $828;
 $830 = HEAP32[$829>>2]|0;
 $831 = (($828) + 4)|0;
 $832 = $831;
 $833 = HEAP32[$832>>2]|0;
 $834 = (_bitshift64Ashr(0,($830|0),32)|0);
 $835 = tempRet0;
 $836 = (___muldi3(($834|0),($835|0),($826|0),($827|0))|0);
 $837 = tempRet0;
 $838 = (_i64Add(($818|0),($819|0),($836|0),($837|0))|0);
 $839 = tempRet0;
 $840 = $738;
 $841 = $840;
 $842 = HEAP32[$841>>2]|0;
 $843 = (($840) + 4)|0;
 $844 = $843;
 $845 = HEAP32[$844>>2]|0;
 $846 = (_bitshift64Ashr(0,($842|0),32)|0);
 $847 = tempRet0;
 $848 = $33;
 $849 = $848;
 $850 = HEAP32[$849>>2]|0;
 $851 = (($848) + 4)|0;
 $852 = $851;
 $853 = HEAP32[$852>>2]|0;
 $854 = (_bitshift64Ashr(0,($850|0),32)|0);
 $855 = tempRet0;
 $856 = (___muldi3(($854|0),($855|0),($846|0),($847|0))|0);
 $857 = tempRet0;
 $858 = (_i64Add(($838|0),($839|0),($856|0),($857|0))|0);
 $859 = tempRet0;
 $860 = (_bitshift64Shl(($858|0),($859|0),1)|0);
 $861 = tempRet0;
 $862 = (_i64Add(($860|0),($861|0),($780|0),($781|0))|0);
 $863 = tempRet0;
 $864 = $109;
 $865 = $864;
 $866 = HEAP32[$865>>2]|0;
 $867 = (($864) + 4)|0;
 $868 = $867;
 $869 = HEAP32[$868>>2]|0;
 $870 = (_bitshift64Ashr(0,($866|0),32)|0);
 $871 = tempRet0;
 $872 = $560;
 $873 = $872;
 $874 = HEAP32[$873>>2]|0;
 $875 = (($872) + 4)|0;
 $876 = $875;
 $877 = HEAP32[$876>>2]|0;
 $878 = (_bitshift64Ashr(0,($874|0),32)|0);
 $879 = tempRet0;
 $880 = (___muldi3(($878|0),($879|0),($870|0),($871|0))|0);
 $881 = tempRet0;
 $882 = (_i64Add(($862|0),($863|0),($880|0),($881|0))|0);
 $883 = tempRet0;
 $884 = $573;
 $885 = $884;
 $886 = HEAP32[$885>>2]|0;
 $887 = (($884) + 4)|0;
 $888 = $887;
 $889 = HEAP32[$888>>2]|0;
 $890 = (_bitshift64Ashr(0,($886|0),32)|0);
 $891 = tempRet0;
 $892 = $96;
 $893 = $892;
 $894 = HEAP32[$893>>2]|0;
 $895 = (($892) + 4)|0;
 $896 = $895;
 $897 = HEAP32[$896>>2]|0;
 $898 = (_bitshift64Ashr(0,($894|0),32)|0);
 $899 = tempRet0;
 $900 = (___muldi3(($898|0),($899|0),($890|0),($891|0))|0);
 $901 = tempRet0;
 $902 = (_i64Add(($882|0),($883|0),($900|0),($901|0))|0);
 $903 = tempRet0;
 $904 = $1;
 $905 = $904;
 $906 = HEAP32[$905>>2]|0;
 $907 = (($904) + 4)|0;
 $908 = $907;
 $909 = HEAP32[$908>>2]|0;
 $910 = (_bitshift64Ashr(0,($906|0),32)|0);
 $911 = tempRet0;
 $912 = ((($2)) + 64|0);
 $913 = $912;
 $914 = $913;
 $915 = HEAP32[$914>>2]|0;
 $916 = (($913) + 4)|0;
 $917 = $916;
 $918 = HEAP32[$917>>2]|0;
 $919 = (_bitshift64Ashr(0,($915|0),32)|0);
 $920 = tempRet0;
 $921 = (___muldi3(($919|0),($920|0),($910|0),($911|0))|0);
 $922 = tempRet0;
 $923 = (_i64Add(($902|0),($903|0),($921|0),($922|0))|0);
 $924 = tempRet0;
 $925 = ((($1)) + 64|0);
 $926 = $925;
 $927 = $926;
 $928 = HEAP32[$927>>2]|0;
 $929 = (($926) + 4)|0;
 $930 = $929;
 $931 = HEAP32[$930>>2]|0;
 $932 = (_bitshift64Ashr(0,($928|0),32)|0);
 $933 = tempRet0;
 $934 = $2;
 $935 = $934;
 $936 = HEAP32[$935>>2]|0;
 $937 = (($934) + 4)|0;
 $938 = $937;
 $939 = HEAP32[$938>>2]|0;
 $940 = (_bitshift64Ashr(0,($936|0),32)|0);
 $941 = tempRet0;
 $942 = (___muldi3(($940|0),($941|0),($932|0),($933|0))|0);
 $943 = tempRet0;
 $944 = (_i64Add(($923|0),($924|0),($942|0),($943|0))|0);
 $945 = tempRet0;
 $946 = ((($0)) + 64|0);
 $947 = $946;
 $948 = $947;
 HEAP32[$948>>2] = $944;
 $949 = (($947) + 4)|0;
 $950 = $949;
 HEAP32[$950>>2] = $945;
 $951 = $301;
 $952 = $951;
 $953 = HEAP32[$952>>2]|0;
 $954 = (($951) + 4)|0;
 $955 = $954;
 $956 = HEAP32[$955>>2]|0;
 $957 = (_bitshift64Ashr(0,($953|0),32)|0);
 $958 = tempRet0;
 $959 = $413;
 $960 = $959;
 $961 = HEAP32[$960>>2]|0;
 $962 = (($959) + 4)|0;
 $963 = $962;
 $964 = HEAP32[$963>>2]|0;
 $965 = (_bitshift64Ashr(0,($961|0),32)|0);
 $966 = tempRet0;
 $967 = (___muldi3(($965|0),($966|0),($957|0),($958|0))|0);
 $968 = tempRet0;
 $969 = $426;
 $970 = $969;
 $971 = HEAP32[$970>>2]|0;
 $972 = (($969) + 4)|0;
 $973 = $972;
 $974 = HEAP32[$973>>2]|0;
 $975 = (_bitshift64Ashr(0,($971|0),32)|0);
 $976 = tempRet0;
 $977 = $288;
 $978 = $977;
 $979 = HEAP32[$978>>2]|0;
 $980 = (($977) + 4)|0;
 $981 = $980;
 $982 = HEAP32[$981>>2]|0;
 $983 = (_bitshift64Ashr(0,($979|0),32)|0);
 $984 = tempRet0;
 $985 = (___muldi3(($983|0),($984|0),($975|0),($976|0))|0);
 $986 = tempRet0;
 $987 = (_i64Add(($985|0),($986|0),($967|0),($968|0))|0);
 $988 = tempRet0;
 $989 = $194;
 $990 = $989;
 $991 = HEAP32[$990>>2]|0;
 $992 = (($989) + 4)|0;
 $993 = $992;
 $994 = HEAP32[$993>>2]|0;
 $995 = (_bitshift64Ashr(0,($991|0),32)|0);
 $996 = tempRet0;
 $997 = $560;
 $998 = $997;
 $999 = HEAP32[$998>>2]|0;
 $1000 = (($997) + 4)|0;
 $1001 = $1000;
 $1002 = HEAP32[$1001>>2]|0;
 $1003 = (_bitshift64Ashr(0,($999|0),32)|0);
 $1004 = tempRet0;
 $1005 = (___muldi3(($1003|0),($1004|0),($995|0),($996|0))|0);
 $1006 = tempRet0;
 $1007 = (_i64Add(($987|0),($988|0),($1005|0),($1006|0))|0);
 $1008 = tempRet0;
 $1009 = $573;
 $1010 = $1009;
 $1011 = HEAP32[$1010>>2]|0;
 $1012 = (($1009) + 4)|0;
 $1013 = $1012;
 $1014 = HEAP32[$1013>>2]|0;
 $1015 = (_bitshift64Ashr(0,($1011|0),32)|0);
 $1016 = tempRet0;
 $1017 = $181;
 $1018 = $1017;
 $1019 = HEAP32[$1018>>2]|0;
 $1020 = (($1017) + 4)|0;
 $1021 = $1020;
 $1022 = HEAP32[$1021>>2]|0;
 $1023 = (_bitshift64Ashr(0,($1019|0),32)|0);
 $1024 = tempRet0;
 $1025 = (___muldi3(($1023|0),($1024|0),($1015|0),($1016|0))|0);
 $1026 = tempRet0;
 $1027 = (_i64Add(($1007|0),($1008|0),($1025|0),($1026|0))|0);
 $1028 = tempRet0;
 $1029 = $109;
 $1030 = $1029;
 $1031 = HEAP32[$1030>>2]|0;
 $1032 = (($1029) + 4)|0;
 $1033 = $1032;
 $1034 = HEAP32[$1033>>2]|0;
 $1035 = (_bitshift64Ashr(0,($1031|0),32)|0);
 $1036 = tempRet0;
 $1037 = $725;
 $1038 = $1037;
 $1039 = HEAP32[$1038>>2]|0;
 $1040 = (($1037) + 4)|0;
 $1041 = $1040;
 $1042 = HEAP32[$1041>>2]|0;
 $1043 = (_bitshift64Ashr(0,($1039|0),32)|0);
 $1044 = tempRet0;
 $1045 = (___muldi3(($1043|0),($1044|0),($1035|0),($1036|0))|0);
 $1046 = tempRet0;
 $1047 = (_i64Add(($1027|0),($1028|0),($1045|0),($1046|0))|0);
 $1048 = tempRet0;
 $1049 = $738;
 $1050 = $1049;
 $1051 = HEAP32[$1050>>2]|0;
 $1052 = (($1049) + 4)|0;
 $1053 = $1052;
 $1054 = HEAP32[$1053>>2]|0;
 $1055 = (_bitshift64Ashr(0,($1051|0),32)|0);
 $1056 = tempRet0;
 $1057 = $96;
 $1058 = $1057;
 $1059 = HEAP32[$1058>>2]|0;
 $1060 = (($1057) + 4)|0;
 $1061 = $1060;
 $1062 = HEAP32[$1061>>2]|0;
 $1063 = (_bitshift64Ashr(0,($1059|0),32)|0);
 $1064 = tempRet0;
 $1065 = (___muldi3(($1063|0),($1064|0),($1055|0),($1056|0))|0);
 $1066 = tempRet0;
 $1067 = (_i64Add(($1047|0),($1048|0),($1065|0),($1066|0))|0);
 $1068 = tempRet0;
 $1069 = $44;
 $1070 = $1069;
 $1071 = HEAP32[$1070>>2]|0;
 $1072 = (($1069) + 4)|0;
 $1073 = $1072;
 $1074 = HEAP32[$1073>>2]|0;
 $1075 = (_bitshift64Ashr(0,($1071|0),32)|0);
 $1076 = tempRet0;
 $1077 = $912;
 $1078 = $1077;
 $1079 = HEAP32[$1078>>2]|0;
 $1080 = (($1077) + 4)|0;
 $1081 = $1080;
 $1082 = HEAP32[$1081>>2]|0;
 $1083 = (_bitshift64Ashr(0,($1079|0),32)|0);
 $1084 = tempRet0;
 $1085 = (___muldi3(($1083|0),($1084|0),($1075|0),($1076|0))|0);
 $1086 = tempRet0;
 $1087 = (_i64Add(($1067|0),($1068|0),($1085|0),($1086|0))|0);
 $1088 = tempRet0;
 $1089 = $925;
 $1090 = $1089;
 $1091 = HEAP32[$1090>>2]|0;
 $1092 = (($1089) + 4)|0;
 $1093 = $1092;
 $1094 = HEAP32[$1093>>2]|0;
 $1095 = (_bitshift64Ashr(0,($1091|0),32)|0);
 $1096 = tempRet0;
 $1097 = $33;
 $1098 = $1097;
 $1099 = HEAP32[$1098>>2]|0;
 $1100 = (($1097) + 4)|0;
 $1101 = $1100;
 $1102 = HEAP32[$1101>>2]|0;
 $1103 = (_bitshift64Ashr(0,($1099|0),32)|0);
 $1104 = tempRet0;
 $1105 = (___muldi3(($1103|0),($1104|0),($1095|0),($1096|0))|0);
 $1106 = tempRet0;
 $1107 = (_i64Add(($1087|0),($1088|0),($1105|0),($1106|0))|0);
 $1108 = tempRet0;
 $1109 = $1;
 $1110 = $1109;
 $1111 = HEAP32[$1110>>2]|0;
 $1112 = (($1109) + 4)|0;
 $1113 = $1112;
 $1114 = HEAP32[$1113>>2]|0;
 $1115 = (_bitshift64Ashr(0,($1111|0),32)|0);
 $1116 = tempRet0;
 $1117 = ((($2)) + 72|0);
 $1118 = $1117;
 $1119 = $1118;
 $1120 = HEAP32[$1119>>2]|0;
 $1121 = (($1118) + 4)|0;
 $1122 = $1121;
 $1123 = HEAP32[$1122>>2]|0;
 $1124 = (_bitshift64Ashr(0,($1120|0),32)|0);
 $1125 = tempRet0;
 $1126 = (___muldi3(($1124|0),($1125|0),($1115|0),($1116|0))|0);
 $1127 = tempRet0;
 $1128 = (_i64Add(($1107|0),($1108|0),($1126|0),($1127|0))|0);
 $1129 = tempRet0;
 $1130 = ((($1)) + 72|0);
 $1131 = $1130;
 $1132 = $1131;
 $1133 = HEAP32[$1132>>2]|0;
 $1134 = (($1131) + 4)|0;
 $1135 = $1134;
 $1136 = HEAP32[$1135>>2]|0;
 $1137 = (_bitshift64Ashr(0,($1133|0),32)|0);
 $1138 = tempRet0;
 $1139 = $2;
 $1140 = $1139;
 $1141 = HEAP32[$1140>>2]|0;
 $1142 = (($1139) + 4)|0;
 $1143 = $1142;
 $1144 = HEAP32[$1143>>2]|0;
 $1145 = (_bitshift64Ashr(0,($1141|0),32)|0);
 $1146 = tempRet0;
 $1147 = (___muldi3(($1145|0),($1146|0),($1137|0),($1138|0))|0);
 $1148 = tempRet0;
 $1149 = (_i64Add(($1128|0),($1129|0),($1147|0),($1148|0))|0);
 $1150 = tempRet0;
 $1151 = ((($0)) + 72|0);
 $1152 = $1151;
 $1153 = $1152;
 HEAP32[$1153>>2] = $1149;
 $1154 = (($1152) + 4)|0;
 $1155 = $1154;
 HEAP32[$1155>>2] = $1150;
 $1156 = $426;
 $1157 = $1156;
 $1158 = HEAP32[$1157>>2]|0;
 $1159 = (($1156) + 4)|0;
 $1160 = $1159;
 $1161 = HEAP32[$1160>>2]|0;
 $1162 = (_bitshift64Ashr(0,($1158|0),32)|0);
 $1163 = tempRet0;
 $1164 = $413;
 $1165 = $1164;
 $1166 = HEAP32[$1165>>2]|0;
 $1167 = (($1164) + 4)|0;
 $1168 = $1167;
 $1169 = HEAP32[$1168>>2]|0;
 $1170 = (_bitshift64Ashr(0,($1166|0),32)|0);
 $1171 = tempRet0;
 $1172 = (___muldi3(($1170|0),($1171|0),($1162|0),($1163|0))|0);
 $1173 = tempRet0;
 $1174 = $194;
 $1175 = $1174;
 $1176 = HEAP32[$1175>>2]|0;
 $1177 = (($1174) + 4)|0;
 $1178 = $1177;
 $1179 = HEAP32[$1178>>2]|0;
 $1180 = (_bitshift64Ashr(0,($1176|0),32)|0);
 $1181 = tempRet0;
 $1182 = $725;
 $1183 = $1182;
 $1184 = HEAP32[$1183>>2]|0;
 $1185 = (($1182) + 4)|0;
 $1186 = $1185;
 $1187 = HEAP32[$1186>>2]|0;
 $1188 = (_bitshift64Ashr(0,($1184|0),32)|0);
 $1189 = tempRet0;
 $1190 = (___muldi3(($1188|0),($1189|0),($1180|0),($1181|0))|0);
 $1191 = tempRet0;
 $1192 = (_i64Add(($1190|0),($1191|0),($1172|0),($1173|0))|0);
 $1193 = tempRet0;
 $1194 = $738;
 $1195 = $1194;
 $1196 = HEAP32[$1195>>2]|0;
 $1197 = (($1194) + 4)|0;
 $1198 = $1197;
 $1199 = HEAP32[$1198>>2]|0;
 $1200 = (_bitshift64Ashr(0,($1196|0),32)|0);
 $1201 = tempRet0;
 $1202 = $181;
 $1203 = $1202;
 $1204 = HEAP32[$1203>>2]|0;
 $1205 = (($1202) + 4)|0;
 $1206 = $1205;
 $1207 = HEAP32[$1206>>2]|0;
 $1208 = (_bitshift64Ashr(0,($1204|0),32)|0);
 $1209 = tempRet0;
 $1210 = (___muldi3(($1208|0),($1209|0),($1200|0),($1201|0))|0);
 $1211 = tempRet0;
 $1212 = (_i64Add(($1192|0),($1193|0),($1210|0),($1211|0))|0);
 $1213 = tempRet0;
 $1214 = $44;
 $1215 = $1214;
 $1216 = HEAP32[$1215>>2]|0;
 $1217 = (($1214) + 4)|0;
 $1218 = $1217;
 $1219 = HEAP32[$1218>>2]|0;
 $1220 = (_bitshift64Ashr(0,($1216|0),32)|0);
 $1221 = tempRet0;
 $1222 = $1117;
 $1223 = $1222;
 $1224 = HEAP32[$1223>>2]|0;
 $1225 = (($1222) + 4)|0;
 $1226 = $1225;
 $1227 = HEAP32[$1226>>2]|0;
 $1228 = (_bitshift64Ashr(0,($1224|0),32)|0);
 $1229 = tempRet0;
 $1230 = (___muldi3(($1228|0),($1229|0),($1220|0),($1221|0))|0);
 $1231 = tempRet0;
 $1232 = (_i64Add(($1212|0),($1213|0),($1230|0),($1231|0))|0);
 $1233 = tempRet0;
 $1234 = $1130;
 $1235 = $1234;
 $1236 = HEAP32[$1235>>2]|0;
 $1237 = (($1234) + 4)|0;
 $1238 = $1237;
 $1239 = HEAP32[$1238>>2]|0;
 $1240 = (_bitshift64Ashr(0,($1236|0),32)|0);
 $1241 = tempRet0;
 $1242 = $33;
 $1243 = $1242;
 $1244 = HEAP32[$1243>>2]|0;
 $1245 = (($1242) + 4)|0;
 $1246 = $1245;
 $1247 = HEAP32[$1246>>2]|0;
 $1248 = (_bitshift64Ashr(0,($1244|0),32)|0);
 $1249 = tempRet0;
 $1250 = (___muldi3(($1248|0),($1249|0),($1240|0),($1241|0))|0);
 $1251 = tempRet0;
 $1252 = (_i64Add(($1232|0),($1233|0),($1250|0),($1251|0))|0);
 $1253 = tempRet0;
 $1254 = (_bitshift64Shl(($1252|0),($1253|0),1)|0);
 $1255 = tempRet0;
 $1256 = $301;
 $1257 = $1256;
 $1258 = HEAP32[$1257>>2]|0;
 $1259 = (($1256) + 4)|0;
 $1260 = $1259;
 $1261 = HEAP32[$1260>>2]|0;
 $1262 = (_bitshift64Ashr(0,($1258|0),32)|0);
 $1263 = tempRet0;
 $1264 = $560;
 $1265 = $1264;
 $1266 = HEAP32[$1265>>2]|0;
 $1267 = (($1264) + 4)|0;
 $1268 = $1267;
 $1269 = HEAP32[$1268>>2]|0;
 $1270 = (_bitshift64Ashr(0,($1266|0),32)|0);
 $1271 = tempRet0;
 $1272 = (___muldi3(($1270|0),($1271|0),($1262|0),($1263|0))|0);
 $1273 = tempRet0;
 $1274 = (_i64Add(($1254|0),($1255|0),($1272|0),($1273|0))|0);
 $1275 = tempRet0;
 $1276 = $573;
 $1277 = $1276;
 $1278 = HEAP32[$1277>>2]|0;
 $1279 = (($1276) + 4)|0;
 $1280 = $1279;
 $1281 = HEAP32[$1280>>2]|0;
 $1282 = (_bitshift64Ashr(0,($1278|0),32)|0);
 $1283 = tempRet0;
 $1284 = $288;
 $1285 = $1284;
 $1286 = HEAP32[$1285>>2]|0;
 $1287 = (($1284) + 4)|0;
 $1288 = $1287;
 $1289 = HEAP32[$1288>>2]|0;
 $1290 = (_bitshift64Ashr(0,($1286|0),32)|0);
 $1291 = tempRet0;
 $1292 = (___muldi3(($1290|0),($1291|0),($1282|0),($1283|0))|0);
 $1293 = tempRet0;
 $1294 = (_i64Add(($1274|0),($1275|0),($1292|0),($1293|0))|0);
 $1295 = tempRet0;
 $1296 = $109;
 $1297 = $1296;
 $1298 = HEAP32[$1297>>2]|0;
 $1299 = (($1296) + 4)|0;
 $1300 = $1299;
 $1301 = HEAP32[$1300>>2]|0;
 $1302 = (_bitshift64Ashr(0,($1298|0),32)|0);
 $1303 = tempRet0;
 $1304 = $912;
 $1305 = $1304;
 $1306 = HEAP32[$1305>>2]|0;
 $1307 = (($1304) + 4)|0;
 $1308 = $1307;
 $1309 = HEAP32[$1308>>2]|0;
 $1310 = (_bitshift64Ashr(0,($1306|0),32)|0);
 $1311 = tempRet0;
 $1312 = (___muldi3(($1310|0),($1311|0),($1302|0),($1303|0))|0);
 $1313 = tempRet0;
 $1314 = (_i64Add(($1294|0),($1295|0),($1312|0),($1313|0))|0);
 $1315 = tempRet0;
 $1316 = $925;
 $1317 = $1316;
 $1318 = HEAP32[$1317>>2]|0;
 $1319 = (($1316) + 4)|0;
 $1320 = $1319;
 $1321 = HEAP32[$1320>>2]|0;
 $1322 = (_bitshift64Ashr(0,($1318|0),32)|0);
 $1323 = tempRet0;
 $1324 = $96;
 $1325 = $1324;
 $1326 = HEAP32[$1325>>2]|0;
 $1327 = (($1324) + 4)|0;
 $1328 = $1327;
 $1329 = HEAP32[$1328>>2]|0;
 $1330 = (_bitshift64Ashr(0,($1326|0),32)|0);
 $1331 = tempRet0;
 $1332 = (___muldi3(($1330|0),($1331|0),($1322|0),($1323|0))|0);
 $1333 = tempRet0;
 $1334 = (_i64Add(($1314|0),($1315|0),($1332|0),($1333|0))|0);
 $1335 = tempRet0;
 $1336 = ((($0)) + 80|0);
 $1337 = $1336;
 $1338 = $1337;
 HEAP32[$1338>>2] = $1334;
 $1339 = (($1337) + 4)|0;
 $1340 = $1339;
 HEAP32[$1340>>2] = $1335;
 $1341 = $426;
 $1342 = $1341;
 $1343 = HEAP32[$1342>>2]|0;
 $1344 = (($1341) + 4)|0;
 $1345 = $1344;
 $1346 = HEAP32[$1345>>2]|0;
 $1347 = (_bitshift64Ashr(0,($1343|0),32)|0);
 $1348 = tempRet0;
 $1349 = $560;
 $1350 = $1349;
 $1351 = HEAP32[$1350>>2]|0;
 $1352 = (($1349) + 4)|0;
 $1353 = $1352;
 $1354 = HEAP32[$1353>>2]|0;
 $1355 = (_bitshift64Ashr(0,($1351|0),32)|0);
 $1356 = tempRet0;
 $1357 = (___muldi3(($1355|0),($1356|0),($1347|0),($1348|0))|0);
 $1358 = tempRet0;
 $1359 = $573;
 $1360 = $1359;
 $1361 = HEAP32[$1360>>2]|0;
 $1362 = (($1359) + 4)|0;
 $1363 = $1362;
 $1364 = HEAP32[$1363>>2]|0;
 $1365 = (_bitshift64Ashr(0,($1361|0),32)|0);
 $1366 = tempRet0;
 $1367 = $413;
 $1368 = $1367;
 $1369 = HEAP32[$1368>>2]|0;
 $1370 = (($1367) + 4)|0;
 $1371 = $1370;
 $1372 = HEAP32[$1371>>2]|0;
 $1373 = (_bitshift64Ashr(0,($1369|0),32)|0);
 $1374 = tempRet0;
 $1375 = (___muldi3(($1373|0),($1374|0),($1365|0),($1366|0))|0);
 $1376 = tempRet0;
 $1377 = (_i64Add(($1375|0),($1376|0),($1357|0),($1358|0))|0);
 $1378 = tempRet0;
 $1379 = $301;
 $1380 = $1379;
 $1381 = HEAP32[$1380>>2]|0;
 $1382 = (($1379) + 4)|0;
 $1383 = $1382;
 $1384 = HEAP32[$1383>>2]|0;
 $1385 = (_bitshift64Ashr(0,($1381|0),32)|0);
 $1386 = tempRet0;
 $1387 = $725;
 $1388 = $1387;
 $1389 = HEAP32[$1388>>2]|0;
 $1390 = (($1387) + 4)|0;
 $1391 = $1390;
 $1392 = HEAP32[$1391>>2]|0;
 $1393 = (_bitshift64Ashr(0,($1389|0),32)|0);
 $1394 = tempRet0;
 $1395 = (___muldi3(($1393|0),($1394|0),($1385|0),($1386|0))|0);
 $1396 = tempRet0;
 $1397 = (_i64Add(($1377|0),($1378|0),($1395|0),($1396|0))|0);
 $1398 = tempRet0;
 $1399 = $738;
 $1400 = $1399;
 $1401 = HEAP32[$1400>>2]|0;
 $1402 = (($1399) + 4)|0;
 $1403 = $1402;
 $1404 = HEAP32[$1403>>2]|0;
 $1405 = (_bitshift64Ashr(0,($1401|0),32)|0);
 $1406 = tempRet0;
 $1407 = $288;
 $1408 = $1407;
 $1409 = HEAP32[$1408>>2]|0;
 $1410 = (($1407) + 4)|0;
 $1411 = $1410;
 $1412 = HEAP32[$1411>>2]|0;
 $1413 = (_bitshift64Ashr(0,($1409|0),32)|0);
 $1414 = tempRet0;
 $1415 = (___muldi3(($1413|0),($1414|0),($1405|0),($1406|0))|0);
 $1416 = tempRet0;
 $1417 = (_i64Add(($1397|0),($1398|0),($1415|0),($1416|0))|0);
 $1418 = tempRet0;
 $1419 = $194;
 $1420 = $1419;
 $1421 = HEAP32[$1420>>2]|0;
 $1422 = (($1419) + 4)|0;
 $1423 = $1422;
 $1424 = HEAP32[$1423>>2]|0;
 $1425 = (_bitshift64Ashr(0,($1421|0),32)|0);
 $1426 = tempRet0;
 $1427 = $912;
 $1428 = $1427;
 $1429 = HEAP32[$1428>>2]|0;
 $1430 = (($1427) + 4)|0;
 $1431 = $1430;
 $1432 = HEAP32[$1431>>2]|0;
 $1433 = (_bitshift64Ashr(0,($1429|0),32)|0);
 $1434 = tempRet0;
 $1435 = (___muldi3(($1433|0),($1434|0),($1425|0),($1426|0))|0);
 $1436 = tempRet0;
 $1437 = (_i64Add(($1417|0),($1418|0),($1435|0),($1436|0))|0);
 $1438 = tempRet0;
 $1439 = $925;
 $1440 = $1439;
 $1441 = HEAP32[$1440>>2]|0;
 $1442 = (($1439) + 4)|0;
 $1443 = $1442;
 $1444 = HEAP32[$1443>>2]|0;
 $1445 = (_bitshift64Ashr(0,($1441|0),32)|0);
 $1446 = tempRet0;
 $1447 = $181;
 $1448 = $1447;
 $1449 = HEAP32[$1448>>2]|0;
 $1450 = (($1447) + 4)|0;
 $1451 = $1450;
 $1452 = HEAP32[$1451>>2]|0;
 $1453 = (_bitshift64Ashr(0,($1449|0),32)|0);
 $1454 = tempRet0;
 $1455 = (___muldi3(($1453|0),($1454|0),($1445|0),($1446|0))|0);
 $1456 = tempRet0;
 $1457 = (_i64Add(($1437|0),($1438|0),($1455|0),($1456|0))|0);
 $1458 = tempRet0;
 $1459 = $109;
 $1460 = $1459;
 $1461 = HEAP32[$1460>>2]|0;
 $1462 = (($1459) + 4)|0;
 $1463 = $1462;
 $1464 = HEAP32[$1463>>2]|0;
 $1465 = (_bitshift64Ashr(0,($1461|0),32)|0);
 $1466 = tempRet0;
 $1467 = $1117;
 $1468 = $1467;
 $1469 = HEAP32[$1468>>2]|0;
 $1470 = (($1467) + 4)|0;
 $1471 = $1470;
 $1472 = HEAP32[$1471>>2]|0;
 $1473 = (_bitshift64Ashr(0,($1469|0),32)|0);
 $1474 = tempRet0;
 $1475 = (___muldi3(($1473|0),($1474|0),($1465|0),($1466|0))|0);
 $1476 = tempRet0;
 $1477 = (_i64Add(($1457|0),($1458|0),($1475|0),($1476|0))|0);
 $1478 = tempRet0;
 $1479 = $1130;
 $1480 = $1479;
 $1481 = HEAP32[$1480>>2]|0;
 $1482 = (($1479) + 4)|0;
 $1483 = $1482;
 $1484 = HEAP32[$1483>>2]|0;
 $1485 = (_bitshift64Ashr(0,($1481|0),32)|0);
 $1486 = tempRet0;
 $1487 = $96;
 $1488 = $1487;
 $1489 = HEAP32[$1488>>2]|0;
 $1490 = (($1487) + 4)|0;
 $1491 = $1490;
 $1492 = HEAP32[$1491>>2]|0;
 $1493 = (_bitshift64Ashr(0,($1489|0),32)|0);
 $1494 = tempRet0;
 $1495 = (___muldi3(($1493|0),($1494|0),($1485|0),($1486|0))|0);
 $1496 = tempRet0;
 $1497 = (_i64Add(($1477|0),($1478|0),($1495|0),($1496|0))|0);
 $1498 = tempRet0;
 $1499 = ((($0)) + 88|0);
 $1500 = $1499;
 $1501 = $1500;
 HEAP32[$1501>>2] = $1497;
 $1502 = (($1500) + 4)|0;
 $1503 = $1502;
 HEAP32[$1503>>2] = $1498;
 $1504 = $573;
 $1505 = $1504;
 $1506 = HEAP32[$1505>>2]|0;
 $1507 = (($1504) + 4)|0;
 $1508 = $1507;
 $1509 = HEAP32[$1508>>2]|0;
 $1510 = (_bitshift64Ashr(0,($1506|0),32)|0);
 $1511 = tempRet0;
 $1512 = $560;
 $1513 = $1512;
 $1514 = HEAP32[$1513>>2]|0;
 $1515 = (($1512) + 4)|0;
 $1516 = $1515;
 $1517 = HEAP32[$1516>>2]|0;
 $1518 = (_bitshift64Ashr(0,($1514|0),32)|0);
 $1519 = tempRet0;
 $1520 = (___muldi3(($1518|0),($1519|0),($1510|0),($1511|0))|0);
 $1521 = tempRet0;
 $1522 = $426;
 $1523 = $1522;
 $1524 = HEAP32[$1523>>2]|0;
 $1525 = (($1522) + 4)|0;
 $1526 = $1525;
 $1527 = HEAP32[$1526>>2]|0;
 $1528 = (_bitshift64Ashr(0,($1524|0),32)|0);
 $1529 = tempRet0;
 $1530 = $725;
 $1531 = $1530;
 $1532 = HEAP32[$1531>>2]|0;
 $1533 = (($1530) + 4)|0;
 $1534 = $1533;
 $1535 = HEAP32[$1534>>2]|0;
 $1536 = (_bitshift64Ashr(0,($1532|0),32)|0);
 $1537 = tempRet0;
 $1538 = (___muldi3(($1536|0),($1537|0),($1528|0),($1529|0))|0);
 $1539 = tempRet0;
 $1540 = $738;
 $1541 = $1540;
 $1542 = HEAP32[$1541>>2]|0;
 $1543 = (($1540) + 4)|0;
 $1544 = $1543;
 $1545 = HEAP32[$1544>>2]|0;
 $1546 = (_bitshift64Ashr(0,($1542|0),32)|0);
 $1547 = tempRet0;
 $1548 = $413;
 $1549 = $1548;
 $1550 = HEAP32[$1549>>2]|0;
 $1551 = (($1548) + 4)|0;
 $1552 = $1551;
 $1553 = HEAP32[$1552>>2]|0;
 $1554 = (_bitshift64Ashr(0,($1550|0),32)|0);
 $1555 = tempRet0;
 $1556 = (___muldi3(($1554|0),($1555|0),($1546|0),($1547|0))|0);
 $1557 = tempRet0;
 $1558 = (_i64Add(($1556|0),($1557|0),($1538|0),($1539|0))|0);
 $1559 = tempRet0;
 $1560 = $194;
 $1561 = $1560;
 $1562 = HEAP32[$1561>>2]|0;
 $1563 = (($1560) + 4)|0;
 $1564 = $1563;
 $1565 = HEAP32[$1564>>2]|0;
 $1566 = (_bitshift64Ashr(0,($1562|0),32)|0);
 $1567 = tempRet0;
 $1568 = $1117;
 $1569 = $1568;
 $1570 = HEAP32[$1569>>2]|0;
 $1571 = (($1568) + 4)|0;
 $1572 = $1571;
 $1573 = HEAP32[$1572>>2]|0;
 $1574 = (_bitshift64Ashr(0,($1570|0),32)|0);
 $1575 = tempRet0;
 $1576 = (___muldi3(($1574|0),($1575|0),($1566|0),($1567|0))|0);
 $1577 = tempRet0;
 $1578 = (_i64Add(($1558|0),($1559|0),($1576|0),($1577|0))|0);
 $1579 = tempRet0;
 $1580 = $1130;
 $1581 = $1580;
 $1582 = HEAP32[$1581>>2]|0;
 $1583 = (($1580) + 4)|0;
 $1584 = $1583;
 $1585 = HEAP32[$1584>>2]|0;
 $1586 = (_bitshift64Ashr(0,($1582|0),32)|0);
 $1587 = tempRet0;
 $1588 = $181;
 $1589 = $1588;
 $1590 = HEAP32[$1589>>2]|0;
 $1591 = (($1588) + 4)|0;
 $1592 = $1591;
 $1593 = HEAP32[$1592>>2]|0;
 $1594 = (_bitshift64Ashr(0,($1590|0),32)|0);
 $1595 = tempRet0;
 $1596 = (___muldi3(($1594|0),($1595|0),($1586|0),($1587|0))|0);
 $1597 = tempRet0;
 $1598 = (_i64Add(($1578|0),($1579|0),($1596|0),($1597|0))|0);
 $1599 = tempRet0;
 $1600 = (_bitshift64Shl(($1598|0),($1599|0),1)|0);
 $1601 = tempRet0;
 $1602 = (_i64Add(($1600|0),($1601|0),($1520|0),($1521|0))|0);
 $1603 = tempRet0;
 $1604 = $301;
 $1605 = $1604;
 $1606 = HEAP32[$1605>>2]|0;
 $1607 = (($1604) + 4)|0;
 $1608 = $1607;
 $1609 = HEAP32[$1608>>2]|0;
 $1610 = (_bitshift64Ashr(0,($1606|0),32)|0);
 $1611 = tempRet0;
 $1612 = $912;
 $1613 = $1612;
 $1614 = HEAP32[$1613>>2]|0;
 $1615 = (($1612) + 4)|0;
 $1616 = $1615;
 $1617 = HEAP32[$1616>>2]|0;
 $1618 = (_bitshift64Ashr(0,($1614|0),32)|0);
 $1619 = tempRet0;
 $1620 = (___muldi3(($1618|0),($1619|0),($1610|0),($1611|0))|0);
 $1621 = tempRet0;
 $1622 = (_i64Add(($1602|0),($1603|0),($1620|0),($1621|0))|0);
 $1623 = tempRet0;
 $1624 = $925;
 $1625 = $1624;
 $1626 = HEAP32[$1625>>2]|0;
 $1627 = (($1624) + 4)|0;
 $1628 = $1627;
 $1629 = HEAP32[$1628>>2]|0;
 $1630 = (_bitshift64Ashr(0,($1626|0),32)|0);
 $1631 = tempRet0;
 $1632 = $288;
 $1633 = $1632;
 $1634 = HEAP32[$1633>>2]|0;
 $1635 = (($1632) + 4)|0;
 $1636 = $1635;
 $1637 = HEAP32[$1636>>2]|0;
 $1638 = (_bitshift64Ashr(0,($1634|0),32)|0);
 $1639 = tempRet0;
 $1640 = (___muldi3(($1638|0),($1639|0),($1630|0),($1631|0))|0);
 $1641 = tempRet0;
 $1642 = (_i64Add(($1622|0),($1623|0),($1640|0),($1641|0))|0);
 $1643 = tempRet0;
 $1644 = ((($0)) + 96|0);
 $1645 = $1644;
 $1646 = $1645;
 HEAP32[$1646>>2] = $1642;
 $1647 = (($1645) + 4)|0;
 $1648 = $1647;
 HEAP32[$1648>>2] = $1643;
 $1649 = $573;
 $1650 = $1649;
 $1651 = HEAP32[$1650>>2]|0;
 $1652 = (($1649) + 4)|0;
 $1653 = $1652;
 $1654 = HEAP32[$1653>>2]|0;
 $1655 = (_bitshift64Ashr(0,($1651|0),32)|0);
 $1656 = tempRet0;
 $1657 = $725;
 $1658 = $1657;
 $1659 = HEAP32[$1658>>2]|0;
 $1660 = (($1657) + 4)|0;
 $1661 = $1660;
 $1662 = HEAP32[$1661>>2]|0;
 $1663 = (_bitshift64Ashr(0,($1659|0),32)|0);
 $1664 = tempRet0;
 $1665 = (___muldi3(($1663|0),($1664|0),($1655|0),($1656|0))|0);
 $1666 = tempRet0;
 $1667 = $738;
 $1668 = $1667;
 $1669 = HEAP32[$1668>>2]|0;
 $1670 = (($1667) + 4)|0;
 $1671 = $1670;
 $1672 = HEAP32[$1671>>2]|0;
 $1673 = (_bitshift64Ashr(0,($1669|0),32)|0);
 $1674 = tempRet0;
 $1675 = $560;
 $1676 = $1675;
 $1677 = HEAP32[$1676>>2]|0;
 $1678 = (($1675) + 4)|0;
 $1679 = $1678;
 $1680 = HEAP32[$1679>>2]|0;
 $1681 = (_bitshift64Ashr(0,($1677|0),32)|0);
 $1682 = tempRet0;
 $1683 = (___muldi3(($1681|0),($1682|0),($1673|0),($1674|0))|0);
 $1684 = tempRet0;
 $1685 = (_i64Add(($1683|0),($1684|0),($1665|0),($1666|0))|0);
 $1686 = tempRet0;
 $1687 = $426;
 $1688 = $1687;
 $1689 = HEAP32[$1688>>2]|0;
 $1690 = (($1687) + 4)|0;
 $1691 = $1690;
 $1692 = HEAP32[$1691>>2]|0;
 $1693 = (_bitshift64Ashr(0,($1689|0),32)|0);
 $1694 = tempRet0;
 $1695 = $912;
 $1696 = $1695;
 $1697 = HEAP32[$1696>>2]|0;
 $1698 = (($1695) + 4)|0;
 $1699 = $1698;
 $1700 = HEAP32[$1699>>2]|0;
 $1701 = (_bitshift64Ashr(0,($1697|0),32)|0);
 $1702 = tempRet0;
 $1703 = (___muldi3(($1701|0),($1702|0),($1693|0),($1694|0))|0);
 $1704 = tempRet0;
 $1705 = (_i64Add(($1685|0),($1686|0),($1703|0),($1704|0))|0);
 $1706 = tempRet0;
 $1707 = $925;
 $1708 = $1707;
 $1709 = HEAP32[$1708>>2]|0;
 $1710 = (($1707) + 4)|0;
 $1711 = $1710;
 $1712 = HEAP32[$1711>>2]|0;
 $1713 = (_bitshift64Ashr(0,($1709|0),32)|0);
 $1714 = tempRet0;
 $1715 = $413;
 $1716 = $1715;
 $1717 = HEAP32[$1716>>2]|0;
 $1718 = (($1715) + 4)|0;
 $1719 = $1718;
 $1720 = HEAP32[$1719>>2]|0;
 $1721 = (_bitshift64Ashr(0,($1717|0),32)|0);
 $1722 = tempRet0;
 $1723 = (___muldi3(($1721|0),($1722|0),($1713|0),($1714|0))|0);
 $1724 = tempRet0;
 $1725 = (_i64Add(($1705|0),($1706|0),($1723|0),($1724|0))|0);
 $1726 = tempRet0;
 $1727 = $301;
 $1728 = $1727;
 $1729 = HEAP32[$1728>>2]|0;
 $1730 = (($1727) + 4)|0;
 $1731 = $1730;
 $1732 = HEAP32[$1731>>2]|0;
 $1733 = (_bitshift64Ashr(0,($1729|0),32)|0);
 $1734 = tempRet0;
 $1735 = $1117;
 $1736 = $1735;
 $1737 = HEAP32[$1736>>2]|0;
 $1738 = (($1735) + 4)|0;
 $1739 = $1738;
 $1740 = HEAP32[$1739>>2]|0;
 $1741 = (_bitshift64Ashr(0,($1737|0),32)|0);
 $1742 = tempRet0;
 $1743 = (___muldi3(($1741|0),($1742|0),($1733|0),($1734|0))|0);
 $1744 = tempRet0;
 $1745 = (_i64Add(($1725|0),($1726|0),($1743|0),($1744|0))|0);
 $1746 = tempRet0;
 $1747 = $1130;
 $1748 = $1747;
 $1749 = HEAP32[$1748>>2]|0;
 $1750 = (($1747) + 4)|0;
 $1751 = $1750;
 $1752 = HEAP32[$1751>>2]|0;
 $1753 = (_bitshift64Ashr(0,($1749|0),32)|0);
 $1754 = tempRet0;
 $1755 = $288;
 $1756 = $1755;
 $1757 = HEAP32[$1756>>2]|0;
 $1758 = (($1755) + 4)|0;
 $1759 = $1758;
 $1760 = HEAP32[$1759>>2]|0;
 $1761 = (_bitshift64Ashr(0,($1757|0),32)|0);
 $1762 = tempRet0;
 $1763 = (___muldi3(($1761|0),($1762|0),($1753|0),($1754|0))|0);
 $1764 = tempRet0;
 $1765 = (_i64Add(($1745|0),($1746|0),($1763|0),($1764|0))|0);
 $1766 = tempRet0;
 $1767 = ((($0)) + 104|0);
 $1768 = $1767;
 $1769 = $1768;
 HEAP32[$1769>>2] = $1765;
 $1770 = (($1768) + 4)|0;
 $1771 = $1770;
 HEAP32[$1771>>2] = $1766;
 $1772 = $738;
 $1773 = $1772;
 $1774 = HEAP32[$1773>>2]|0;
 $1775 = (($1772) + 4)|0;
 $1776 = $1775;
 $1777 = HEAP32[$1776>>2]|0;
 $1778 = (_bitshift64Ashr(0,($1774|0),32)|0);
 $1779 = tempRet0;
 $1780 = $725;
 $1781 = $1780;
 $1782 = HEAP32[$1781>>2]|0;
 $1783 = (($1780) + 4)|0;
 $1784 = $1783;
 $1785 = HEAP32[$1784>>2]|0;
 $1786 = (_bitshift64Ashr(0,($1782|0),32)|0);
 $1787 = tempRet0;
 $1788 = (___muldi3(($1786|0),($1787|0),($1778|0),($1779|0))|0);
 $1789 = tempRet0;
 $1790 = $426;
 $1791 = $1790;
 $1792 = HEAP32[$1791>>2]|0;
 $1793 = (($1790) + 4)|0;
 $1794 = $1793;
 $1795 = HEAP32[$1794>>2]|0;
 $1796 = (_bitshift64Ashr(0,($1792|0),32)|0);
 $1797 = tempRet0;
 $1798 = $1117;
 $1799 = $1798;
 $1800 = HEAP32[$1799>>2]|0;
 $1801 = (($1798) + 4)|0;
 $1802 = $1801;
 $1803 = HEAP32[$1802>>2]|0;
 $1804 = (_bitshift64Ashr(0,($1800|0),32)|0);
 $1805 = tempRet0;
 $1806 = (___muldi3(($1804|0),($1805|0),($1796|0),($1797|0))|0);
 $1807 = tempRet0;
 $1808 = (_i64Add(($1806|0),($1807|0),($1788|0),($1789|0))|0);
 $1809 = tempRet0;
 $1810 = $1130;
 $1811 = $1810;
 $1812 = HEAP32[$1811>>2]|0;
 $1813 = (($1810) + 4)|0;
 $1814 = $1813;
 $1815 = HEAP32[$1814>>2]|0;
 $1816 = (_bitshift64Ashr(0,($1812|0),32)|0);
 $1817 = tempRet0;
 $1818 = $413;
 $1819 = $1818;
 $1820 = HEAP32[$1819>>2]|0;
 $1821 = (($1818) + 4)|0;
 $1822 = $1821;
 $1823 = HEAP32[$1822>>2]|0;
 $1824 = (_bitshift64Ashr(0,($1820|0),32)|0);
 $1825 = tempRet0;
 $1826 = (___muldi3(($1824|0),($1825|0),($1816|0),($1817|0))|0);
 $1827 = tempRet0;
 $1828 = (_i64Add(($1808|0),($1809|0),($1826|0),($1827|0))|0);
 $1829 = tempRet0;
 $1830 = (_bitshift64Shl(($1828|0),($1829|0),1)|0);
 $1831 = tempRet0;
 $1832 = $573;
 $1833 = $1832;
 $1834 = HEAP32[$1833>>2]|0;
 $1835 = (($1832) + 4)|0;
 $1836 = $1835;
 $1837 = HEAP32[$1836>>2]|0;
 $1838 = (_bitshift64Ashr(0,($1834|0),32)|0);
 $1839 = tempRet0;
 $1840 = $912;
 $1841 = $1840;
 $1842 = HEAP32[$1841>>2]|0;
 $1843 = (($1840) + 4)|0;
 $1844 = $1843;
 $1845 = HEAP32[$1844>>2]|0;
 $1846 = (_bitshift64Ashr(0,($1842|0),32)|0);
 $1847 = tempRet0;
 $1848 = (___muldi3(($1846|0),($1847|0),($1838|0),($1839|0))|0);
 $1849 = tempRet0;
 $1850 = (_i64Add(($1830|0),($1831|0),($1848|0),($1849|0))|0);
 $1851 = tempRet0;
 $1852 = $925;
 $1853 = $1852;
 $1854 = HEAP32[$1853>>2]|0;
 $1855 = (($1852) + 4)|0;
 $1856 = $1855;
 $1857 = HEAP32[$1856>>2]|0;
 $1858 = (_bitshift64Ashr(0,($1854|0),32)|0);
 $1859 = tempRet0;
 $1860 = $560;
 $1861 = $1860;
 $1862 = HEAP32[$1861>>2]|0;
 $1863 = (($1860) + 4)|0;
 $1864 = $1863;
 $1865 = HEAP32[$1864>>2]|0;
 $1866 = (_bitshift64Ashr(0,($1862|0),32)|0);
 $1867 = tempRet0;
 $1868 = (___muldi3(($1866|0),($1867|0),($1858|0),($1859|0))|0);
 $1869 = tempRet0;
 $1870 = (_i64Add(($1850|0),($1851|0),($1868|0),($1869|0))|0);
 $1871 = tempRet0;
 $1872 = ((($0)) + 112|0);
 $1873 = $1872;
 $1874 = $1873;
 HEAP32[$1874>>2] = $1870;
 $1875 = (($1873) + 4)|0;
 $1876 = $1875;
 HEAP32[$1876>>2] = $1871;
 $1877 = $738;
 $1878 = $1877;
 $1879 = HEAP32[$1878>>2]|0;
 $1880 = (($1877) + 4)|0;
 $1881 = $1880;
 $1882 = HEAP32[$1881>>2]|0;
 $1883 = (_bitshift64Ashr(0,($1879|0),32)|0);
 $1884 = tempRet0;
 $1885 = $912;
 $1886 = $1885;
 $1887 = HEAP32[$1886>>2]|0;
 $1888 = (($1885) + 4)|0;
 $1889 = $1888;
 $1890 = HEAP32[$1889>>2]|0;
 $1891 = (_bitshift64Ashr(0,($1887|0),32)|0);
 $1892 = tempRet0;
 $1893 = (___muldi3(($1891|0),($1892|0),($1883|0),($1884|0))|0);
 $1894 = tempRet0;
 $1895 = $925;
 $1896 = $1895;
 $1897 = HEAP32[$1896>>2]|0;
 $1898 = (($1895) + 4)|0;
 $1899 = $1898;
 $1900 = HEAP32[$1899>>2]|0;
 $1901 = (_bitshift64Ashr(0,($1897|0),32)|0);
 $1902 = tempRet0;
 $1903 = $725;
 $1904 = $1903;
 $1905 = HEAP32[$1904>>2]|0;
 $1906 = (($1903) + 4)|0;
 $1907 = $1906;
 $1908 = HEAP32[$1907>>2]|0;
 $1909 = (_bitshift64Ashr(0,($1905|0),32)|0);
 $1910 = tempRet0;
 $1911 = (___muldi3(($1909|0),($1910|0),($1901|0),($1902|0))|0);
 $1912 = tempRet0;
 $1913 = (_i64Add(($1911|0),($1912|0),($1893|0),($1894|0))|0);
 $1914 = tempRet0;
 $1915 = $573;
 $1916 = $1915;
 $1917 = HEAP32[$1916>>2]|0;
 $1918 = (($1915) + 4)|0;
 $1919 = $1918;
 $1920 = HEAP32[$1919>>2]|0;
 $1921 = (_bitshift64Ashr(0,($1917|0),32)|0);
 $1922 = tempRet0;
 $1923 = $1117;
 $1924 = $1923;
 $1925 = HEAP32[$1924>>2]|0;
 $1926 = (($1923) + 4)|0;
 $1927 = $1926;
 $1928 = HEAP32[$1927>>2]|0;
 $1929 = (_bitshift64Ashr(0,($1925|0),32)|0);
 $1930 = tempRet0;
 $1931 = (___muldi3(($1929|0),($1930|0),($1921|0),($1922|0))|0);
 $1932 = tempRet0;
 $1933 = (_i64Add(($1913|0),($1914|0),($1931|0),($1932|0))|0);
 $1934 = tempRet0;
 $1935 = $1130;
 $1936 = $1935;
 $1937 = HEAP32[$1936>>2]|0;
 $1938 = (($1935) + 4)|0;
 $1939 = $1938;
 $1940 = HEAP32[$1939>>2]|0;
 $1941 = (_bitshift64Ashr(0,($1937|0),32)|0);
 $1942 = tempRet0;
 $1943 = $560;
 $1944 = $1943;
 $1945 = HEAP32[$1944>>2]|0;
 $1946 = (($1943) + 4)|0;
 $1947 = $1946;
 $1948 = HEAP32[$1947>>2]|0;
 $1949 = (_bitshift64Ashr(0,($1945|0),32)|0);
 $1950 = tempRet0;
 $1951 = (___muldi3(($1949|0),($1950|0),($1941|0),($1942|0))|0);
 $1952 = tempRet0;
 $1953 = (_i64Add(($1933|0),($1934|0),($1951|0),($1952|0))|0);
 $1954 = tempRet0;
 $1955 = ((($0)) + 120|0);
 $1956 = $1955;
 $1957 = $1956;
 HEAP32[$1957>>2] = $1953;
 $1958 = (($1956) + 4)|0;
 $1959 = $1958;
 HEAP32[$1959>>2] = $1954;
 $1960 = $925;
 $1961 = $1960;
 $1962 = HEAP32[$1961>>2]|0;
 $1963 = (($1960) + 4)|0;
 $1964 = $1963;
 $1965 = HEAP32[$1964>>2]|0;
 $1966 = (_bitshift64Ashr(0,($1962|0),32)|0);
 $1967 = tempRet0;
 $1968 = $912;
 $1969 = $1968;
 $1970 = HEAP32[$1969>>2]|0;
 $1971 = (($1968) + 4)|0;
 $1972 = $1971;
 $1973 = HEAP32[$1972>>2]|0;
 $1974 = (_bitshift64Ashr(0,($1970|0),32)|0);
 $1975 = tempRet0;
 $1976 = (___muldi3(($1974|0),($1975|0),($1966|0),($1967|0))|0);
 $1977 = tempRet0;
 $1978 = $738;
 $1979 = $1978;
 $1980 = HEAP32[$1979>>2]|0;
 $1981 = (($1978) + 4)|0;
 $1982 = $1981;
 $1983 = HEAP32[$1982>>2]|0;
 $1984 = (_bitshift64Ashr(0,($1980|0),32)|0);
 $1985 = tempRet0;
 $1986 = $1117;
 $1987 = $1986;
 $1988 = HEAP32[$1987>>2]|0;
 $1989 = (($1986) + 4)|0;
 $1990 = $1989;
 $1991 = HEAP32[$1990>>2]|0;
 $1992 = (_bitshift64Ashr(0,($1988|0),32)|0);
 $1993 = tempRet0;
 $1994 = (___muldi3(($1992|0),($1993|0),($1984|0),($1985|0))|0);
 $1995 = tempRet0;
 $1996 = $1130;
 $1997 = $1996;
 $1998 = HEAP32[$1997>>2]|0;
 $1999 = (($1996) + 4)|0;
 $2000 = $1999;
 $2001 = HEAP32[$2000>>2]|0;
 $2002 = (_bitshift64Ashr(0,($1998|0),32)|0);
 $2003 = tempRet0;
 $2004 = $725;
 $2005 = $2004;
 $2006 = HEAP32[$2005>>2]|0;
 $2007 = (($2004) + 4)|0;
 $2008 = $2007;
 $2009 = HEAP32[$2008>>2]|0;
 $2010 = (_bitshift64Ashr(0,($2006|0),32)|0);
 $2011 = tempRet0;
 $2012 = (___muldi3(($2010|0),($2011|0),($2002|0),($2003|0))|0);
 $2013 = tempRet0;
 $2014 = (_i64Add(($2012|0),($2013|0),($1994|0),($1995|0))|0);
 $2015 = tempRet0;
 $2016 = (_bitshift64Shl(($2014|0),($2015|0),1)|0);
 $2017 = tempRet0;
 $2018 = (_i64Add(($2016|0),($2017|0),($1976|0),($1977|0))|0);
 $2019 = tempRet0;
 $2020 = ((($0)) + 128|0);
 $2021 = $2020;
 $2022 = $2021;
 HEAP32[$2022>>2] = $2018;
 $2023 = (($2021) + 4)|0;
 $2024 = $2023;
 HEAP32[$2024>>2] = $2019;
 $2025 = $925;
 $2026 = $2025;
 $2027 = HEAP32[$2026>>2]|0;
 $2028 = (($2025) + 4)|0;
 $2029 = $2028;
 $2030 = HEAP32[$2029>>2]|0;
 $2031 = (_bitshift64Ashr(0,($2027|0),32)|0);
 $2032 = tempRet0;
 $2033 = $1117;
 $2034 = $2033;
 $2035 = HEAP32[$2034>>2]|0;
 $2036 = (($2033) + 4)|0;
 $2037 = $2036;
 $2038 = HEAP32[$2037>>2]|0;
 $2039 = (_bitshift64Ashr(0,($2035|0),32)|0);
 $2040 = tempRet0;
 $2041 = (___muldi3(($2039|0),($2040|0),($2031|0),($2032|0))|0);
 $2042 = tempRet0;
 $2043 = $1130;
 $2044 = $2043;
 $2045 = HEAP32[$2044>>2]|0;
 $2046 = (($2043) + 4)|0;
 $2047 = $2046;
 $2048 = HEAP32[$2047>>2]|0;
 $2049 = (_bitshift64Ashr(0,($2045|0),32)|0);
 $2050 = tempRet0;
 $2051 = $912;
 $2052 = $2051;
 $2053 = HEAP32[$2052>>2]|0;
 $2054 = (($2051) + 4)|0;
 $2055 = $2054;
 $2056 = HEAP32[$2055>>2]|0;
 $2057 = (_bitshift64Ashr(0,($2053|0),32)|0);
 $2058 = tempRet0;
 $2059 = (___muldi3(($2057|0),($2058|0),($2049|0),($2050|0))|0);
 $2060 = tempRet0;
 $2061 = (_i64Add(($2059|0),($2060|0),($2041|0),($2042|0))|0);
 $2062 = tempRet0;
 $2063 = ((($0)) + 136|0);
 $2064 = $2063;
 $2065 = $2064;
 HEAP32[$2065>>2] = $2061;
 $2066 = (($2064) + 4)|0;
 $2067 = $2066;
 HEAP32[$2067>>2] = $2062;
 $2068 = $1130;
 $2069 = $2068;
 $2070 = HEAP32[$2069>>2]|0;
 $2071 = (($2068) + 4)|0;
 $2072 = $2071;
 $2073 = HEAP32[$2072>>2]|0;
 $2074 = (_bitshift64Ashr(0,($2070|0),31)|0);
 $2075 = tempRet0;
 $2076 = $1117;
 $2077 = $2076;
 $2078 = HEAP32[$2077>>2]|0;
 $2079 = (($2076) + 4)|0;
 $2080 = $2079;
 $2081 = HEAP32[$2080>>2]|0;
 $2082 = (_bitshift64Ashr(0,($2078|0),32)|0);
 $2083 = tempRet0;
 $2084 = (___muldi3(($2082|0),($2083|0),($2074|0),($2075|0))|0);
 $2085 = tempRet0;
 $2086 = ((($0)) + 144|0);
 $2087 = $2086;
 $2088 = $2087;
 HEAP32[$2088>>2] = $2084;
 $2089 = (($2087) + 4)|0;
 $2090 = $2089;
 HEAP32[$2090>>2] = $2085;
 return;
}
function _freduce_degree($0) {
 $0 = $0|0;
 var $1 = 0, $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0, $113 = 0, $114 = 0, $115 = 0, $116 = 0;
 var $117 = 0, $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0, $133 = 0, $134 = 0;
 var $135 = 0, $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0, $15 = 0, $150 = 0, $151 = 0, $152 = 0;
 var $153 = 0, $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $159 = 0, $16 = 0, $160 = 0, $161 = 0, $162 = 0, $163 = 0, $164 = 0, $165 = 0, $166 = 0, $167 = 0, $168 = 0, $169 = 0, $17 = 0, $170 = 0;
 var $171 = 0, $172 = 0, $173 = 0, $174 = 0, $175 = 0, $176 = 0, $177 = 0, $178 = 0, $179 = 0, $18 = 0, $180 = 0, $181 = 0, $182 = 0, $183 = 0, $184 = 0, $185 = 0, $186 = 0, $187 = 0, $188 = 0, $189 = 0;
 var $19 = 0, $190 = 0, $191 = 0, $192 = 0, $193 = 0, $194 = 0, $195 = 0, $196 = 0, $197 = 0, $198 = 0, $199 = 0, $2 = 0, $20 = 0, $200 = 0, $201 = 0, $202 = 0, $203 = 0, $204 = 0, $205 = 0, $206 = 0;
 var $207 = 0, $208 = 0, $209 = 0, $21 = 0, $210 = 0, $211 = 0, $212 = 0, $213 = 0, $214 = 0, $215 = 0, $216 = 0, $217 = 0, $218 = 0, $219 = 0, $22 = 0, $220 = 0, $221 = 0, $222 = 0, $223 = 0, $224 = 0;
 var $225 = 0, $226 = 0, $227 = 0, $228 = 0, $229 = 0, $23 = 0, $230 = 0, $231 = 0, $232 = 0, $233 = 0, $234 = 0, $235 = 0, $236 = 0, $237 = 0, $238 = 0, $239 = 0, $24 = 0, $240 = 0, $241 = 0, $242 = 0;
 var $243 = 0, $244 = 0, $245 = 0, $246 = 0, $247 = 0, $248 = 0, $249 = 0, $25 = 0, $250 = 0, $251 = 0, $252 = 0, $253 = 0, $254 = 0, $255 = 0, $256 = 0, $257 = 0, $258 = 0, $259 = 0, $26 = 0, $260 = 0;
 var $261 = 0, $262 = 0, $263 = 0, $264 = 0, $265 = 0, $266 = 0, $267 = 0, $268 = 0, $269 = 0, $27 = 0, $270 = 0, $271 = 0, $272 = 0, $273 = 0, $274 = 0, $275 = 0, $276 = 0, $277 = 0, $278 = 0, $279 = 0;
 var $28 = 0, $280 = 0, $281 = 0, $282 = 0, $283 = 0, $284 = 0, $285 = 0, $286 = 0, $287 = 0, $288 = 0, $289 = 0, $29 = 0, $290 = 0, $291 = 0, $292 = 0, $293 = 0, $294 = 0, $295 = 0, $296 = 0, $297 = 0;
 var $298 = 0, $299 = 0, $3 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $4 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0;
 var $46 = 0, $47 = 0, $48 = 0, $49 = 0, $5 = 0, $50 = 0, $51 = 0, $52 = 0, $53 = 0, $54 = 0, $55 = 0, $56 = 0, $57 = 0, $58 = 0, $59 = 0, $6 = 0, $60 = 0, $61 = 0, $62 = 0, $63 = 0;
 var $64 = 0, $65 = 0, $66 = 0, $67 = 0, $68 = 0, $69 = 0, $7 = 0, $70 = 0, $71 = 0, $72 = 0, $73 = 0, $74 = 0, $75 = 0, $76 = 0, $77 = 0, $78 = 0, $79 = 0, $8 = 0, $80 = 0, $81 = 0;
 var $82 = 0, $83 = 0, $84 = 0, $85 = 0, $86 = 0, $87 = 0, $88 = 0, $89 = 0, $9 = 0, $90 = 0, $91 = 0, $92 = 0, $93 = 0, $94 = 0, $95 = 0, $96 = 0, $97 = 0, $98 = 0, $99 = 0, label = 0;
 var sp = 0;
 sp = STACKTOP;
 $1 = ((($0)) + 144|0);
 $2 = $1;
 $3 = $2;
 $4 = HEAP32[$3>>2]|0;
 $5 = (($2) + 4)|0;
 $6 = $5;
 $7 = HEAP32[$6>>2]|0;
 $8 = (_bitshift64Shl(($4|0),($7|0),4)|0);
 $9 = tempRet0;
 $10 = ((($0)) + 64|0);
 $11 = $10;
 $12 = $11;
 $13 = HEAP32[$12>>2]|0;
 $14 = (($11) + 4)|0;
 $15 = $14;
 $16 = HEAP32[$15>>2]|0;
 $17 = (_i64Add(($13|0),($16|0),($8|0),($9|0))|0);
 $18 = tempRet0;
 $19 = (_bitshift64Shl(($4|0),($7|0),1)|0);
 $20 = tempRet0;
 $21 = (_i64Add(($17|0),($18|0),($19|0),($20|0))|0);
 $22 = tempRet0;
 $23 = $1;
 $24 = $23;
 $25 = HEAP32[$24>>2]|0;
 $26 = (($23) + 4)|0;
 $27 = $26;
 $28 = HEAP32[$27>>2]|0;
 $29 = (_i64Add(($21|0),($22|0),($25|0),($28|0))|0);
 $30 = tempRet0;
 $31 = $10;
 $32 = $31;
 HEAP32[$32>>2] = $29;
 $33 = (($31) + 4)|0;
 $34 = $33;
 HEAP32[$34>>2] = $30;
 $35 = ((($0)) + 136|0);
 $36 = $35;
 $37 = $36;
 $38 = HEAP32[$37>>2]|0;
 $39 = (($36) + 4)|0;
 $40 = $39;
 $41 = HEAP32[$40>>2]|0;
 $42 = (_bitshift64Shl(($38|0),($41|0),4)|0);
 $43 = tempRet0;
 $44 = ((($0)) + 56|0);
 $45 = $44;
 $46 = $45;
 $47 = HEAP32[$46>>2]|0;
 $48 = (($45) + 4)|0;
 $49 = $48;
 $50 = HEAP32[$49>>2]|0;
 $51 = (_i64Add(($47|0),($50|0),($42|0),($43|0))|0);
 $52 = tempRet0;
 $53 = (_bitshift64Shl(($38|0),($41|0),1)|0);
 $54 = tempRet0;
 $55 = (_i64Add(($51|0),($52|0),($53|0),($54|0))|0);
 $56 = tempRet0;
 $57 = $35;
 $58 = $57;
 $59 = HEAP32[$58>>2]|0;
 $60 = (($57) + 4)|0;
 $61 = $60;
 $62 = HEAP32[$61>>2]|0;
 $63 = (_i64Add(($55|0),($56|0),($59|0),($62|0))|0);
 $64 = tempRet0;
 $65 = $44;
 $66 = $65;
 HEAP32[$66>>2] = $63;
 $67 = (($65) + 4)|0;
 $68 = $67;
 HEAP32[$68>>2] = $64;
 $69 = ((($0)) + 128|0);
 $70 = $69;
 $71 = $70;
 $72 = HEAP32[$71>>2]|0;
 $73 = (($70) + 4)|0;
 $74 = $73;
 $75 = HEAP32[$74>>2]|0;
 $76 = (_bitshift64Shl(($72|0),($75|0),4)|0);
 $77 = tempRet0;
 $78 = ((($0)) + 48|0);
 $79 = $78;
 $80 = $79;
 $81 = HEAP32[$80>>2]|0;
 $82 = (($79) + 4)|0;
 $83 = $82;
 $84 = HEAP32[$83>>2]|0;
 $85 = (_i64Add(($81|0),($84|0),($76|0),($77|0))|0);
 $86 = tempRet0;
 $87 = (_bitshift64Shl(($72|0),($75|0),1)|0);
 $88 = tempRet0;
 $89 = (_i64Add(($85|0),($86|0),($87|0),($88|0))|0);
 $90 = tempRet0;
 $91 = $69;
 $92 = $91;
 $93 = HEAP32[$92>>2]|0;
 $94 = (($91) + 4)|0;
 $95 = $94;
 $96 = HEAP32[$95>>2]|0;
 $97 = (_i64Add(($89|0),($90|0),($93|0),($96|0))|0);
 $98 = tempRet0;
 $99 = $78;
 $100 = $99;
 HEAP32[$100>>2] = $97;
 $101 = (($99) + 4)|0;
 $102 = $101;
 HEAP32[$102>>2] = $98;
 $103 = ((($0)) + 120|0);
 $104 = $103;
 $105 = $104;
 $106 = HEAP32[$105>>2]|0;
 $107 = (($104) + 4)|0;
 $108 = $107;
 $109 = HEAP32[$108>>2]|0;
 $110 = (_bitshift64Shl(($106|0),($109|0),4)|0);
 $111 = tempRet0;
 $112 = ((($0)) + 40|0);
 $113 = $112;
 $114 = $113;
 $115 = HEAP32[$114>>2]|0;
 $116 = (($113) + 4)|0;
 $117 = $116;
 $118 = HEAP32[$117>>2]|0;
 $119 = (_i64Add(($115|0),($118|0),($110|0),($111|0))|0);
 $120 = tempRet0;
 $121 = (_bitshift64Shl(($106|0),($109|0),1)|0);
 $122 = tempRet0;
 $123 = (_i64Add(($119|0),($120|0),($121|0),($122|0))|0);
 $124 = tempRet0;
 $125 = $103;
 $126 = $125;
 $127 = HEAP32[$126>>2]|0;
 $128 = (($125) + 4)|0;
 $129 = $128;
 $130 = HEAP32[$129>>2]|0;
 $131 = (_i64Add(($123|0),($124|0),($127|0),($130|0))|0);
 $132 = tempRet0;
 $133 = $112;
 $134 = $133;
 HEAP32[$134>>2] = $131;
 $135 = (($133) + 4)|0;
 $136 = $135;
 HEAP32[$136>>2] = $132;
 $137 = ((($0)) + 112|0);
 $138 = $137;
 $139 = $138;
 $140 = HEAP32[$139>>2]|0;
 $141 = (($138) + 4)|0;
 $142 = $141;
 $143 = HEAP32[$142>>2]|0;
 $144 = (_bitshift64Shl(($140|0),($143|0),4)|0);
 $145 = tempRet0;
 $146 = ((($0)) + 32|0);
 $147 = $146;
 $148 = $147;
 $149 = HEAP32[$148>>2]|0;
 $150 = (($147) + 4)|0;
 $151 = $150;
 $152 = HEAP32[$151>>2]|0;
 $153 = (_i64Add(($149|0),($152|0),($144|0),($145|0))|0);
 $154 = tempRet0;
 $155 = (_bitshift64Shl(($140|0),($143|0),1)|0);
 $156 = tempRet0;
 $157 = (_i64Add(($153|0),($154|0),($155|0),($156|0))|0);
 $158 = tempRet0;
 $159 = $137;
 $160 = $159;
 $161 = HEAP32[$160>>2]|0;
 $162 = (($159) + 4)|0;
 $163 = $162;
 $164 = HEAP32[$163>>2]|0;
 $165 = (_i64Add(($157|0),($158|0),($161|0),($164|0))|0);
 $166 = tempRet0;
 $167 = $146;
 $168 = $167;
 HEAP32[$168>>2] = $165;
 $169 = (($167) + 4)|0;
 $170 = $169;
 HEAP32[$170>>2] = $166;
 $171 = ((($0)) + 104|0);
 $172 = $171;
 $173 = $172;
 $174 = HEAP32[$173>>2]|0;
 $175 = (($172) + 4)|0;
 $176 = $175;
 $177 = HEAP32[$176>>2]|0;
 $178 = (_bitshift64Shl(($174|0),($177|0),4)|0);
 $179 = tempRet0;
 $180 = ((($0)) + 24|0);
 $181 = $180;
 $182 = $181;
 $183 = HEAP32[$182>>2]|0;
 $184 = (($181) + 4)|0;
 $185 = $184;
 $186 = HEAP32[$185>>2]|0;
 $187 = (_i64Add(($183|0),($186|0),($178|0),($179|0))|0);
 $188 = tempRet0;
 $189 = (_bitshift64Shl(($174|0),($177|0),1)|0);
 $190 = tempRet0;
 $191 = (_i64Add(($187|0),($188|0),($189|0),($190|0))|0);
 $192 = tempRet0;
 $193 = $171;
 $194 = $193;
 $195 = HEAP32[$194>>2]|0;
 $196 = (($193) + 4)|0;
 $197 = $196;
 $198 = HEAP32[$197>>2]|0;
 $199 = (_i64Add(($191|0),($192|0),($195|0),($198|0))|0);
 $200 = tempRet0;
 $201 = $180;
 $202 = $201;
 HEAP32[$202>>2] = $199;
 $203 = (($201) + 4)|0;
 $204 = $203;
 HEAP32[$204>>2] = $200;
 $205 = ((($0)) + 96|0);
 $206 = $205;
 $207 = $206;
 $208 = HEAP32[$207>>2]|0;
 $209 = (($206) + 4)|0;
 $210 = $209;
 $211 = HEAP32[$210>>2]|0;
 $212 = (_bitshift64Shl(($208|0),($211|0),4)|0);
 $213 = tempRet0;
 $214 = ((($0)) + 16|0);
 $215 = $214;
 $216 = $215;
 $217 = HEAP32[$216>>2]|0;
 $218 = (($215) + 4)|0;
 $219 = $218;
 $220 = HEAP32[$219>>2]|0;
 $221 = (_i64Add(($217|0),($220|0),($212|0),($213|0))|0);
 $222 = tempRet0;
 $223 = (_bitshift64Shl(($208|0),($211|0),1)|0);
 $224 = tempRet0;
 $225 = (_i64Add(($221|0),($222|0),($223|0),($224|0))|0);
 $226 = tempRet0;
 $227 = $205;
 $228 = $227;
 $229 = HEAP32[$228>>2]|0;
 $230 = (($227) + 4)|0;
 $231 = $230;
 $232 = HEAP32[$231>>2]|0;
 $233 = (_i64Add(($225|0),($226|0),($229|0),($232|0))|0);
 $234 = tempRet0;
 $235 = $214;
 $236 = $235;
 HEAP32[$236>>2] = $233;
 $237 = (($235) + 4)|0;
 $238 = $237;
 HEAP32[$238>>2] = $234;
 $239 = ((($0)) + 88|0);
 $240 = $239;
 $241 = $240;
 $242 = HEAP32[$241>>2]|0;
 $243 = (($240) + 4)|0;
 $244 = $243;
 $245 = HEAP32[$244>>2]|0;
 $246 = (_bitshift64Shl(($242|0),($245|0),4)|0);
 $247 = tempRet0;
 $248 = ((($0)) + 8|0);
 $249 = $248;
 $250 = $249;
 $251 = HEAP32[$250>>2]|0;
 $252 = (($249) + 4)|0;
 $253 = $252;
 $254 = HEAP32[$253>>2]|0;
 $255 = (_i64Add(($251|0),($254|0),($246|0),($247|0))|0);
 $256 = tempRet0;
 $257 = (_bitshift64Shl(($242|0),($245|0),1)|0);
 $258 = tempRet0;
 $259 = (_i64Add(($255|0),($256|0),($257|0),($258|0))|0);
 $260 = tempRet0;
 $261 = $239;
 $262 = $261;
 $263 = HEAP32[$262>>2]|0;
 $264 = (($261) + 4)|0;
 $265 = $264;
 $266 = HEAP32[$265>>2]|0;
 $267 = (_i64Add(($259|0),($260|0),($263|0),($266|0))|0);
 $268 = tempRet0;
 $269 = $248;
 $270 = $269;
 HEAP32[$270>>2] = $267;
 $271 = (($269) + 4)|0;
 $272 = $271;
 HEAP32[$272>>2] = $268;
 $273 = ((($0)) + 80|0);
 $274 = $273;
 $275 = $274;
 $276 = HEAP32[$275>>2]|0;
 $277 = (($274) + 4)|0;
 $278 = $277;
 $279 = HEAP32[$278>>2]|0;
 $280 = (_bitshift64Shl(($276|0),($279|0),4)|0);
 $281 = tempRet0;
 $282 = $0;
 $283 = $282;
 $284 = HEAP32[$283>>2]|0;
 $285 = (($282) + 4)|0;
 $286 = $285;
 $287 = HEAP32[$286>>2]|0;
 $288 = (_i64Add(($284|0),($287|0),($280|0),($281|0))|0);
 $289 = tempRet0;
 $290 = (_bitshift64Shl(($276|0),($279|0),1)|0);
 $291 = tempRet0;
 $292 = (_i64Add(($288|0),($289|0),($290|0),($291|0))|0);
 $293 = tempRet0;
 $294 = (_i64Add(($292|0),($293|0),($276|0),($279|0))|0);
 $295 = tempRet0;
 $296 = $0;
 $297 = $296;
 HEAP32[$297>>2] = $294;
 $298 = (($296) + 4)|0;
 $299 = $298;
 HEAP32[$299>>2] = $295;
 return;
}
function _freduce_coefficients($0) {
 $0 = $0|0;
 var $$035 = 0, $1 = 0, $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $2 = 0;
 var $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0, $29 = 0, $3 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0;
 var $39 = 0, $4 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0, $46 = 0, $47 = 0, $48 = 0, $49 = 0, $5 = 0, $50 = 0, $51 = 0, $52 = 0, $53 = 0, $54 = 0, $55 = 0, $56 = 0;
 var $57 = 0, $58 = 0, $59 = 0, $6 = 0, $60 = 0, $61 = 0, $62 = 0, $63 = 0, $64 = 0, $65 = 0, $66 = 0, $67 = 0, $68 = 0, $69 = 0, $7 = 0, $70 = 0, $71 = 0, $72 = 0, $73 = 0, $74 = 0;
 var $75 = 0, $76 = 0, $77 = 0, $78 = 0, $79 = 0, $8 = 0, $80 = 0, $81 = 0, $82 = 0, $83 = 0, $84 = 0, $85 = 0, $86 = 0, $87 = 0, $88 = 0, $89 = 0, $9 = 0, $90 = 0, $91 = 0, $92 = 0;
 var $93 = 0, $94 = 0, $95 = 0, $96 = 0, $97 = 0, $98 = 0, $99 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $1 = ((($0)) + 80|0);
 $2 = $1;
 $3 = $2;
 HEAP32[$3>>2] = 0;
 $4 = (($2) + 4)|0;
 $5 = $4;
 HEAP32[$5>>2] = 0;
 $$035 = 0;
 while(1) {
  $6 = (($0) + ($$035<<3)|0);
  $7 = $6;
  $8 = $7;
  $9 = HEAP32[$8>>2]|0;
  $10 = (($7) + 4)|0;
  $11 = $10;
  $12 = HEAP32[$11>>2]|0;
  $13 = (_div_by_2_26($9,$12)|0);
  $14 = tempRet0;
  $15 = (_bitshift64Shl(($13|0),($14|0),26)|0);
  $16 = tempRet0;
  $17 = (_i64Subtract(($9|0),($12|0),($15|0),($16|0))|0);
  $18 = tempRet0;
  $19 = $6;
  $20 = $19;
  HEAP32[$20>>2] = $17;
  $21 = (($19) + 4)|0;
  $22 = $21;
  HEAP32[$22>>2] = $18;
  $23 = $$035 | 1;
  $24 = (($0) + ($23<<3)|0);
  $25 = $24;
  $26 = $25;
  $27 = HEAP32[$26>>2]|0;
  $28 = (($25) + 4)|0;
  $29 = $28;
  $30 = HEAP32[$29>>2]|0;
  $31 = (_i64Add(($27|0),($30|0),($13|0),($14|0))|0);
  $32 = tempRet0;
  $33 = (_div_by_2_25($31,$32)|0);
  $34 = tempRet0;
  $35 = (_bitshift64Shl(($33|0),($34|0),25)|0);
  $36 = tempRet0;
  $37 = (_i64Subtract(($31|0),($32|0),($35|0),($36|0))|0);
  $38 = tempRet0;
  $39 = $24;
  $40 = $39;
  HEAP32[$40>>2] = $37;
  $41 = (($39) + 4)|0;
  $42 = $41;
  HEAP32[$42>>2] = $38;
  $43 = (($$035) + 2)|0;
  $44 = (($0) + ($43<<3)|0);
  $45 = $44;
  $46 = $45;
  $47 = HEAP32[$46>>2]|0;
  $48 = (($45) + 4)|0;
  $49 = $48;
  $50 = HEAP32[$49>>2]|0;
  $51 = (_i64Add(($47|0),($50|0),($33|0),($34|0))|0);
  $52 = tempRet0;
  $53 = $44;
  $54 = $53;
  HEAP32[$54>>2] = $51;
  $55 = (($53) + 4)|0;
  $56 = $55;
  HEAP32[$56>>2] = $52;
  $57 = ($43>>>0)<(10);
  if ($57) {
   $$035 = $43;
  } else {
   break;
  }
 }
 $58 = $1;
 $59 = $58;
 $60 = HEAP32[$59>>2]|0;
 $61 = (($58) + 4)|0;
 $62 = $61;
 $63 = HEAP32[$62>>2]|0;
 $64 = (_bitshift64Shl(($60|0),($63|0),4)|0);
 $65 = tempRet0;
 $66 = $0;
 $67 = $66;
 $68 = HEAP32[$67>>2]|0;
 $69 = (($66) + 4)|0;
 $70 = $69;
 $71 = HEAP32[$70>>2]|0;
 $72 = (_i64Add(($68|0),($71|0),($64|0),($65|0))|0);
 $73 = tempRet0;
 $74 = (_bitshift64Shl(($60|0),($63|0),1)|0);
 $75 = tempRet0;
 $76 = (_i64Add(($72|0),($73|0),($74|0),($75|0))|0);
 $77 = tempRet0;
 $78 = (_i64Add(($76|0),($77|0),($60|0),($63|0))|0);
 $79 = tempRet0;
 $80 = $1;
 $81 = $80;
 HEAP32[$81>>2] = 0;
 $82 = (($80) + 4)|0;
 $83 = $82;
 HEAP32[$83>>2] = 0;
 $84 = (_div_by_2_26($78,$79)|0);
 $85 = tempRet0;
 $86 = (_bitshift64Shl(($84|0),($85|0),26)|0);
 $87 = tempRet0;
 $88 = (_i64Subtract(($78|0),($79|0),($86|0),($87|0))|0);
 $89 = tempRet0;
 $90 = $0;
 $91 = $90;
 HEAP32[$91>>2] = $88;
 $92 = (($90) + 4)|0;
 $93 = $92;
 HEAP32[$93>>2] = $89;
 $94 = ((($0)) + 8|0);
 $95 = $94;
 $96 = $95;
 $97 = HEAP32[$96>>2]|0;
 $98 = (($95) + 4)|0;
 $99 = $98;
 $100 = HEAP32[$99>>2]|0;
 $101 = (_i64Add(($97|0),($100|0),($84|0),($85|0))|0);
 $102 = tempRet0;
 $103 = $94;
 $104 = $103;
 HEAP32[$104>>2] = $101;
 $105 = (($103) + 4)|0;
 $106 = $105;
 HEAP32[$106>>2] = $102;
 return;
}
function _div_by_2_26($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = $1 >> 31;
 $3 = $2 >>> 6;
 $4 = (_i64Add(($3|0),0,($0|0),($1|0))|0);
 $5 = tempRet0;
 $6 = (_bitshift64Ashr(($4|0),($5|0),26)|0);
 $7 = tempRet0;
 tempRet0 = ($7);
 return ($6|0);
}
function _div_by_2_25($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = $1 >> 31;
 $3 = $2 >>> 7;
 $4 = (_i64Add(($3|0),0,($0|0),($1|0))|0);
 $5 = tempRet0;
 $6 = (_bitshift64Ashr(($4|0),($5|0),25)|0);
 $7 = tempRet0;
 tempRet0 = ($7);
 return ($6|0);
}
function _fsquare($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $2 = 0, dest = 0, label = 0, sp = 0, src = 0, stop = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 160|0;
 $2 = sp;
 _fsquare_inner($2,$1);
 _freduce_degree($2);
 _freduce_coefficients($2);
 dest=$0; src=$2; stop=dest+80|0; do { HEAP32[dest>>2]=HEAP32[src>>2]|0; dest=dest+4|0; src=src+4|0; } while ((dest|0) < (stop|0));
 STACKTOP = sp;return;
}
function _fsquare_inner($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $10 = 0, $100 = 0, $1000 = 0, $1001 = 0, $1002 = 0, $1003 = 0, $1004 = 0, $1005 = 0, $1006 = 0, $1007 = 0, $1008 = 0, $1009 = 0, $101 = 0, $1010 = 0, $1011 = 0, $1012 = 0, $1013 = 0, $1014 = 0, $1015 = 0, $1016 = 0;
 var $1017 = 0, $1018 = 0, $1019 = 0, $102 = 0, $1020 = 0, $1021 = 0, $1022 = 0, $1023 = 0, $1024 = 0, $1025 = 0, $1026 = 0, $1027 = 0, $1028 = 0, $1029 = 0, $103 = 0, $1030 = 0, $1031 = 0, $1032 = 0, $1033 = 0, $1034 = 0;
 var $1035 = 0, $1036 = 0, $1037 = 0, $1038 = 0, $1039 = 0, $104 = 0, $1040 = 0, $1041 = 0, $1042 = 0, $1043 = 0, $1044 = 0, $1045 = 0, $1046 = 0, $1047 = 0, $1048 = 0, $1049 = 0, $105 = 0, $1050 = 0, $1051 = 0, $1052 = 0;
 var $1053 = 0, $1054 = 0, $1055 = 0, $1056 = 0, $1057 = 0, $1058 = 0, $1059 = 0, $106 = 0, $1060 = 0, $1061 = 0, $1062 = 0, $1063 = 0, $1064 = 0, $1065 = 0, $1066 = 0, $1067 = 0, $1068 = 0, $1069 = 0, $107 = 0, $1070 = 0;
 var $1071 = 0, $1072 = 0, $1073 = 0, $1074 = 0, $1075 = 0, $1076 = 0, $1077 = 0, $1078 = 0, $1079 = 0, $108 = 0, $1080 = 0, $1081 = 0, $1082 = 0, $1083 = 0, $1084 = 0, $1085 = 0, $1086 = 0, $1087 = 0, $1088 = 0, $1089 = 0;
 var $109 = 0, $1090 = 0, $1091 = 0, $1092 = 0, $1093 = 0, $1094 = 0, $1095 = 0, $1096 = 0, $1097 = 0, $1098 = 0, $1099 = 0, $11 = 0, $110 = 0, $1100 = 0, $1101 = 0, $1102 = 0, $1103 = 0, $1104 = 0, $1105 = 0, $1106 = 0;
 var $1107 = 0, $1108 = 0, $1109 = 0, $111 = 0, $1110 = 0, $1111 = 0, $1112 = 0, $1113 = 0, $1114 = 0, $1115 = 0, $1116 = 0, $1117 = 0, $1118 = 0, $1119 = 0, $112 = 0, $1120 = 0, $113 = 0, $114 = 0, $115 = 0, $116 = 0;
 var $117 = 0, $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0, $133 = 0, $134 = 0;
 var $135 = 0, $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0, $15 = 0, $150 = 0, $151 = 0, $152 = 0;
 var $153 = 0, $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $159 = 0, $16 = 0, $160 = 0, $161 = 0, $162 = 0, $163 = 0, $164 = 0, $165 = 0, $166 = 0, $167 = 0, $168 = 0, $169 = 0, $17 = 0, $170 = 0;
 var $171 = 0, $172 = 0, $173 = 0, $174 = 0, $175 = 0, $176 = 0, $177 = 0, $178 = 0, $179 = 0, $18 = 0, $180 = 0, $181 = 0, $182 = 0, $183 = 0, $184 = 0, $185 = 0, $186 = 0, $187 = 0, $188 = 0, $189 = 0;
 var $19 = 0, $190 = 0, $191 = 0, $192 = 0, $193 = 0, $194 = 0, $195 = 0, $196 = 0, $197 = 0, $198 = 0, $199 = 0, $2 = 0, $20 = 0, $200 = 0, $201 = 0, $202 = 0, $203 = 0, $204 = 0, $205 = 0, $206 = 0;
 var $207 = 0, $208 = 0, $209 = 0, $21 = 0, $210 = 0, $211 = 0, $212 = 0, $213 = 0, $214 = 0, $215 = 0, $216 = 0, $217 = 0, $218 = 0, $219 = 0, $22 = 0, $220 = 0, $221 = 0, $222 = 0, $223 = 0, $224 = 0;
 var $225 = 0, $226 = 0, $227 = 0, $228 = 0, $229 = 0, $23 = 0, $230 = 0, $231 = 0, $232 = 0, $233 = 0, $234 = 0, $235 = 0, $236 = 0, $237 = 0, $238 = 0, $239 = 0, $24 = 0, $240 = 0, $241 = 0, $242 = 0;
 var $243 = 0, $244 = 0, $245 = 0, $246 = 0, $247 = 0, $248 = 0, $249 = 0, $25 = 0, $250 = 0, $251 = 0, $252 = 0, $253 = 0, $254 = 0, $255 = 0, $256 = 0, $257 = 0, $258 = 0, $259 = 0, $26 = 0, $260 = 0;
 var $261 = 0, $262 = 0, $263 = 0, $264 = 0, $265 = 0, $266 = 0, $267 = 0, $268 = 0, $269 = 0, $27 = 0, $270 = 0, $271 = 0, $272 = 0, $273 = 0, $274 = 0, $275 = 0, $276 = 0, $277 = 0, $278 = 0, $279 = 0;
 var $28 = 0, $280 = 0, $281 = 0, $282 = 0, $283 = 0, $284 = 0, $285 = 0, $286 = 0, $287 = 0, $288 = 0, $289 = 0, $29 = 0, $290 = 0, $291 = 0, $292 = 0, $293 = 0, $294 = 0, $295 = 0, $296 = 0, $297 = 0;
 var $298 = 0, $299 = 0, $3 = 0, $30 = 0, $300 = 0, $301 = 0, $302 = 0, $303 = 0, $304 = 0, $305 = 0, $306 = 0, $307 = 0, $308 = 0, $309 = 0, $31 = 0, $310 = 0, $311 = 0, $312 = 0, $313 = 0, $314 = 0;
 var $315 = 0, $316 = 0, $317 = 0, $318 = 0, $319 = 0, $32 = 0, $320 = 0, $321 = 0, $322 = 0, $323 = 0, $324 = 0, $325 = 0, $326 = 0, $327 = 0, $328 = 0, $329 = 0, $33 = 0, $330 = 0, $331 = 0, $332 = 0;
 var $333 = 0, $334 = 0, $335 = 0, $336 = 0, $337 = 0, $338 = 0, $339 = 0, $34 = 0, $340 = 0, $341 = 0, $342 = 0, $343 = 0, $344 = 0, $345 = 0, $346 = 0, $347 = 0, $348 = 0, $349 = 0, $35 = 0, $350 = 0;
 var $351 = 0, $352 = 0, $353 = 0, $354 = 0, $355 = 0, $356 = 0, $357 = 0, $358 = 0, $359 = 0, $36 = 0, $360 = 0, $361 = 0, $362 = 0, $363 = 0, $364 = 0, $365 = 0, $366 = 0, $367 = 0, $368 = 0, $369 = 0;
 var $37 = 0, $370 = 0, $371 = 0, $372 = 0, $373 = 0, $374 = 0, $375 = 0, $376 = 0, $377 = 0, $378 = 0, $379 = 0, $38 = 0, $380 = 0, $381 = 0, $382 = 0, $383 = 0, $384 = 0, $385 = 0, $386 = 0, $387 = 0;
 var $388 = 0, $389 = 0, $39 = 0, $390 = 0, $391 = 0, $392 = 0, $393 = 0, $394 = 0, $395 = 0, $396 = 0, $397 = 0, $398 = 0, $399 = 0, $4 = 0, $40 = 0, $400 = 0, $401 = 0, $402 = 0, $403 = 0, $404 = 0;
 var $405 = 0, $406 = 0, $407 = 0, $408 = 0, $409 = 0, $41 = 0, $410 = 0, $411 = 0, $412 = 0, $413 = 0, $414 = 0, $415 = 0, $416 = 0, $417 = 0, $418 = 0, $419 = 0, $42 = 0, $420 = 0, $421 = 0, $422 = 0;
 var $423 = 0, $424 = 0, $425 = 0, $426 = 0, $427 = 0, $428 = 0, $429 = 0, $43 = 0, $430 = 0, $431 = 0, $432 = 0, $433 = 0, $434 = 0, $435 = 0, $436 = 0, $437 = 0, $438 = 0, $439 = 0, $44 = 0, $440 = 0;
 var $441 = 0, $442 = 0, $443 = 0, $444 = 0, $445 = 0, $446 = 0, $447 = 0, $448 = 0, $449 = 0, $45 = 0, $450 = 0, $451 = 0, $452 = 0, $453 = 0, $454 = 0, $455 = 0, $456 = 0, $457 = 0, $458 = 0, $459 = 0;
 var $46 = 0, $460 = 0, $461 = 0, $462 = 0, $463 = 0, $464 = 0, $465 = 0, $466 = 0, $467 = 0, $468 = 0, $469 = 0, $47 = 0, $470 = 0, $471 = 0, $472 = 0, $473 = 0, $474 = 0, $475 = 0, $476 = 0, $477 = 0;
 var $478 = 0, $479 = 0, $48 = 0, $480 = 0, $481 = 0, $482 = 0, $483 = 0, $484 = 0, $485 = 0, $486 = 0, $487 = 0, $488 = 0, $489 = 0, $49 = 0, $490 = 0, $491 = 0, $492 = 0, $493 = 0, $494 = 0, $495 = 0;
 var $496 = 0, $497 = 0, $498 = 0, $499 = 0, $5 = 0, $50 = 0, $500 = 0, $501 = 0, $502 = 0, $503 = 0, $504 = 0, $505 = 0, $506 = 0, $507 = 0, $508 = 0, $509 = 0, $51 = 0, $510 = 0, $511 = 0, $512 = 0;
 var $513 = 0, $514 = 0, $515 = 0, $516 = 0, $517 = 0, $518 = 0, $519 = 0, $52 = 0, $520 = 0, $521 = 0, $522 = 0, $523 = 0, $524 = 0, $525 = 0, $526 = 0, $527 = 0, $528 = 0, $529 = 0, $53 = 0, $530 = 0;
 var $531 = 0, $532 = 0, $533 = 0, $534 = 0, $535 = 0, $536 = 0, $537 = 0, $538 = 0, $539 = 0, $54 = 0, $540 = 0, $541 = 0, $542 = 0, $543 = 0, $544 = 0, $545 = 0, $546 = 0, $547 = 0, $548 = 0, $549 = 0;
 var $55 = 0, $550 = 0, $551 = 0, $552 = 0, $553 = 0, $554 = 0, $555 = 0, $556 = 0, $557 = 0, $558 = 0, $559 = 0, $56 = 0, $560 = 0, $561 = 0, $562 = 0, $563 = 0, $564 = 0, $565 = 0, $566 = 0, $567 = 0;
 var $568 = 0, $569 = 0, $57 = 0, $570 = 0, $571 = 0, $572 = 0, $573 = 0, $574 = 0, $575 = 0, $576 = 0, $577 = 0, $578 = 0, $579 = 0, $58 = 0, $580 = 0, $581 = 0, $582 = 0, $583 = 0, $584 = 0, $585 = 0;
 var $586 = 0, $587 = 0, $588 = 0, $589 = 0, $59 = 0, $590 = 0, $591 = 0, $592 = 0, $593 = 0, $594 = 0, $595 = 0, $596 = 0, $597 = 0, $598 = 0, $599 = 0, $6 = 0, $60 = 0, $600 = 0, $601 = 0, $602 = 0;
 var $603 = 0, $604 = 0, $605 = 0, $606 = 0, $607 = 0, $608 = 0, $609 = 0, $61 = 0, $610 = 0, $611 = 0, $612 = 0, $613 = 0, $614 = 0, $615 = 0, $616 = 0, $617 = 0, $618 = 0, $619 = 0, $62 = 0, $620 = 0;
 var $621 = 0, $622 = 0, $623 = 0, $624 = 0, $625 = 0, $626 = 0, $627 = 0, $628 = 0, $629 = 0, $63 = 0, $630 = 0, $631 = 0, $632 = 0, $633 = 0, $634 = 0, $635 = 0, $636 = 0, $637 = 0, $638 = 0, $639 = 0;
 var $64 = 0, $640 = 0, $641 = 0, $642 = 0, $643 = 0, $644 = 0, $645 = 0, $646 = 0, $647 = 0, $648 = 0, $649 = 0, $65 = 0, $650 = 0, $651 = 0, $652 = 0, $653 = 0, $654 = 0, $655 = 0, $656 = 0, $657 = 0;
 var $658 = 0, $659 = 0, $66 = 0, $660 = 0, $661 = 0, $662 = 0, $663 = 0, $664 = 0, $665 = 0, $666 = 0, $667 = 0, $668 = 0, $669 = 0, $67 = 0, $670 = 0, $671 = 0, $672 = 0, $673 = 0, $674 = 0, $675 = 0;
 var $676 = 0, $677 = 0, $678 = 0, $679 = 0, $68 = 0, $680 = 0, $681 = 0, $682 = 0, $683 = 0, $684 = 0, $685 = 0, $686 = 0, $687 = 0, $688 = 0, $689 = 0, $69 = 0, $690 = 0, $691 = 0, $692 = 0, $693 = 0;
 var $694 = 0, $695 = 0, $696 = 0, $697 = 0, $698 = 0, $699 = 0, $7 = 0, $70 = 0, $700 = 0, $701 = 0, $702 = 0, $703 = 0, $704 = 0, $705 = 0, $706 = 0, $707 = 0, $708 = 0, $709 = 0, $71 = 0, $710 = 0;
 var $711 = 0, $712 = 0, $713 = 0, $714 = 0, $715 = 0, $716 = 0, $717 = 0, $718 = 0, $719 = 0, $72 = 0, $720 = 0, $721 = 0, $722 = 0, $723 = 0, $724 = 0, $725 = 0, $726 = 0, $727 = 0, $728 = 0, $729 = 0;
 var $73 = 0, $730 = 0, $731 = 0, $732 = 0, $733 = 0, $734 = 0, $735 = 0, $736 = 0, $737 = 0, $738 = 0, $739 = 0, $74 = 0, $740 = 0, $741 = 0, $742 = 0, $743 = 0, $744 = 0, $745 = 0, $746 = 0, $747 = 0;
 var $748 = 0, $749 = 0, $75 = 0, $750 = 0, $751 = 0, $752 = 0, $753 = 0, $754 = 0, $755 = 0, $756 = 0, $757 = 0, $758 = 0, $759 = 0, $76 = 0, $760 = 0, $761 = 0, $762 = 0, $763 = 0, $764 = 0, $765 = 0;
 var $766 = 0, $767 = 0, $768 = 0, $769 = 0, $77 = 0, $770 = 0, $771 = 0, $772 = 0, $773 = 0, $774 = 0, $775 = 0, $776 = 0, $777 = 0, $778 = 0, $779 = 0, $78 = 0, $780 = 0, $781 = 0, $782 = 0, $783 = 0;
 var $784 = 0, $785 = 0, $786 = 0, $787 = 0, $788 = 0, $789 = 0, $79 = 0, $790 = 0, $791 = 0, $792 = 0, $793 = 0, $794 = 0, $795 = 0, $796 = 0, $797 = 0, $798 = 0, $799 = 0, $8 = 0, $80 = 0, $800 = 0;
 var $801 = 0, $802 = 0, $803 = 0, $804 = 0, $805 = 0, $806 = 0, $807 = 0, $808 = 0, $809 = 0, $81 = 0, $810 = 0, $811 = 0, $812 = 0, $813 = 0, $814 = 0, $815 = 0, $816 = 0, $817 = 0, $818 = 0, $819 = 0;
 var $82 = 0, $820 = 0, $821 = 0, $822 = 0, $823 = 0, $824 = 0, $825 = 0, $826 = 0, $827 = 0, $828 = 0, $829 = 0, $83 = 0, $830 = 0, $831 = 0, $832 = 0, $833 = 0, $834 = 0, $835 = 0, $836 = 0, $837 = 0;
 var $838 = 0, $839 = 0, $84 = 0, $840 = 0, $841 = 0, $842 = 0, $843 = 0, $844 = 0, $845 = 0, $846 = 0, $847 = 0, $848 = 0, $849 = 0, $85 = 0, $850 = 0, $851 = 0, $852 = 0, $853 = 0, $854 = 0, $855 = 0;
 var $856 = 0, $857 = 0, $858 = 0, $859 = 0, $86 = 0, $860 = 0, $861 = 0, $862 = 0, $863 = 0, $864 = 0, $865 = 0, $866 = 0, $867 = 0, $868 = 0, $869 = 0, $87 = 0, $870 = 0, $871 = 0, $872 = 0, $873 = 0;
 var $874 = 0, $875 = 0, $876 = 0, $877 = 0, $878 = 0, $879 = 0, $88 = 0, $880 = 0, $881 = 0, $882 = 0, $883 = 0, $884 = 0, $885 = 0, $886 = 0, $887 = 0, $888 = 0, $889 = 0, $89 = 0, $890 = 0, $891 = 0;
 var $892 = 0, $893 = 0, $894 = 0, $895 = 0, $896 = 0, $897 = 0, $898 = 0, $899 = 0, $9 = 0, $90 = 0, $900 = 0, $901 = 0, $902 = 0, $903 = 0, $904 = 0, $905 = 0, $906 = 0, $907 = 0, $908 = 0, $909 = 0;
 var $91 = 0, $910 = 0, $911 = 0, $912 = 0, $913 = 0, $914 = 0, $915 = 0, $916 = 0, $917 = 0, $918 = 0, $919 = 0, $92 = 0, $920 = 0, $921 = 0, $922 = 0, $923 = 0, $924 = 0, $925 = 0, $926 = 0, $927 = 0;
 var $928 = 0, $929 = 0, $93 = 0, $930 = 0, $931 = 0, $932 = 0, $933 = 0, $934 = 0, $935 = 0, $936 = 0, $937 = 0, $938 = 0, $939 = 0, $94 = 0, $940 = 0, $941 = 0, $942 = 0, $943 = 0, $944 = 0, $945 = 0;
 var $946 = 0, $947 = 0, $948 = 0, $949 = 0, $95 = 0, $950 = 0, $951 = 0, $952 = 0, $953 = 0, $954 = 0, $955 = 0, $956 = 0, $957 = 0, $958 = 0, $959 = 0, $96 = 0, $960 = 0, $961 = 0, $962 = 0, $963 = 0;
 var $964 = 0, $965 = 0, $966 = 0, $967 = 0, $968 = 0, $969 = 0, $97 = 0, $970 = 0, $971 = 0, $972 = 0, $973 = 0, $974 = 0, $975 = 0, $976 = 0, $977 = 0, $978 = 0, $979 = 0, $98 = 0, $980 = 0, $981 = 0;
 var $982 = 0, $983 = 0, $984 = 0, $985 = 0, $986 = 0, $987 = 0, $988 = 0, $989 = 0, $99 = 0, $990 = 0, $991 = 0, $992 = 0, $993 = 0, $994 = 0, $995 = 0, $996 = 0, $997 = 0, $998 = 0, $999 = 0, label = 0;
 var sp = 0;
 sp = STACKTOP;
 $2 = $1;
 $3 = $2;
 $4 = HEAP32[$3>>2]|0;
 $5 = (($2) + 4)|0;
 $6 = $5;
 $7 = HEAP32[$6>>2]|0;
 $8 = (_bitshift64Ashr(0,($4|0),32)|0);
 $9 = tempRet0;
 $10 = (___muldi3(($8|0),($9|0),($8|0),($9|0))|0);
 $11 = tempRet0;
 $12 = $0;
 $13 = $12;
 HEAP32[$13>>2] = $10;
 $14 = (($12) + 4)|0;
 $15 = $14;
 HEAP32[$15>>2] = $11;
 $16 = $1;
 $17 = $16;
 $18 = HEAP32[$17>>2]|0;
 $19 = (($16) + 4)|0;
 $20 = $19;
 $21 = HEAP32[$20>>2]|0;
 $22 = (_bitshift64Ashr(0,($18|0),31)|0);
 $23 = tempRet0;
 $24 = ((($1)) + 8|0);
 $25 = $24;
 $26 = $25;
 $27 = HEAP32[$26>>2]|0;
 $28 = (($25) + 4)|0;
 $29 = $28;
 $30 = HEAP32[$29>>2]|0;
 $31 = (_bitshift64Ashr(0,($27|0),32)|0);
 $32 = tempRet0;
 $33 = (___muldi3(($31|0),($32|0),($22|0),($23|0))|0);
 $34 = tempRet0;
 $35 = ((($0)) + 8|0);
 $36 = $35;
 $37 = $36;
 HEAP32[$37>>2] = $33;
 $38 = (($36) + 4)|0;
 $39 = $38;
 HEAP32[$39>>2] = $34;
 $40 = $24;
 $41 = $40;
 $42 = HEAP32[$41>>2]|0;
 $43 = (($40) + 4)|0;
 $44 = $43;
 $45 = HEAP32[$44>>2]|0;
 $46 = (_bitshift64Ashr(0,($42|0),32)|0);
 $47 = tempRet0;
 $48 = (___muldi3(($46|0),($47|0),($46|0),($47|0))|0);
 $49 = tempRet0;
 $50 = $1;
 $51 = $50;
 $52 = HEAP32[$51>>2]|0;
 $53 = (($50) + 4)|0;
 $54 = $53;
 $55 = HEAP32[$54>>2]|0;
 $56 = (_bitshift64Ashr(0,($52|0),32)|0);
 $57 = tempRet0;
 $58 = ((($1)) + 16|0);
 $59 = $58;
 $60 = $59;
 $61 = HEAP32[$60>>2]|0;
 $62 = (($59) + 4)|0;
 $63 = $62;
 $64 = HEAP32[$63>>2]|0;
 $65 = (_bitshift64Ashr(0,($61|0),32)|0);
 $66 = tempRet0;
 $67 = (___muldi3(($65|0),($66|0),($56|0),($57|0))|0);
 $68 = tempRet0;
 $69 = (_i64Add(($67|0),($68|0),($48|0),($49|0))|0);
 $70 = tempRet0;
 $71 = (_bitshift64Shl(($69|0),($70|0),1)|0);
 $72 = tempRet0;
 $73 = ((($0)) + 16|0);
 $74 = $73;
 $75 = $74;
 HEAP32[$75>>2] = $71;
 $76 = (($74) + 4)|0;
 $77 = $76;
 HEAP32[$77>>2] = $72;
 $78 = $24;
 $79 = $78;
 $80 = HEAP32[$79>>2]|0;
 $81 = (($78) + 4)|0;
 $82 = $81;
 $83 = HEAP32[$82>>2]|0;
 $84 = (_bitshift64Ashr(0,($80|0),32)|0);
 $85 = tempRet0;
 $86 = $58;
 $87 = $86;
 $88 = HEAP32[$87>>2]|0;
 $89 = (($86) + 4)|0;
 $90 = $89;
 $91 = HEAP32[$90>>2]|0;
 $92 = (_bitshift64Ashr(0,($88|0),32)|0);
 $93 = tempRet0;
 $94 = (___muldi3(($92|0),($93|0),($84|0),($85|0))|0);
 $95 = tempRet0;
 $96 = $1;
 $97 = $96;
 $98 = HEAP32[$97>>2]|0;
 $99 = (($96) + 4)|0;
 $100 = $99;
 $101 = HEAP32[$100>>2]|0;
 $102 = (_bitshift64Ashr(0,($98|0),32)|0);
 $103 = tempRet0;
 $104 = ((($1)) + 24|0);
 $105 = $104;
 $106 = $105;
 $107 = HEAP32[$106>>2]|0;
 $108 = (($105) + 4)|0;
 $109 = $108;
 $110 = HEAP32[$109>>2]|0;
 $111 = (_bitshift64Ashr(0,($107|0),32)|0);
 $112 = tempRet0;
 $113 = (___muldi3(($111|0),($112|0),($102|0),($103|0))|0);
 $114 = tempRet0;
 $115 = (_i64Add(($113|0),($114|0),($94|0),($95|0))|0);
 $116 = tempRet0;
 $117 = (_bitshift64Shl(($115|0),($116|0),1)|0);
 $118 = tempRet0;
 $119 = ((($0)) + 24|0);
 $120 = $119;
 $121 = $120;
 HEAP32[$121>>2] = $117;
 $122 = (($120) + 4)|0;
 $123 = $122;
 HEAP32[$123>>2] = $118;
 $124 = $58;
 $125 = $124;
 $126 = HEAP32[$125>>2]|0;
 $127 = (($124) + 4)|0;
 $128 = $127;
 $129 = HEAP32[$128>>2]|0;
 $130 = (_bitshift64Ashr(0,($126|0),32)|0);
 $131 = tempRet0;
 $132 = (___muldi3(($130|0),($131|0),($130|0),($131|0))|0);
 $133 = tempRet0;
 $134 = $24;
 $135 = $134;
 $136 = HEAP32[$135>>2]|0;
 $137 = (($134) + 4)|0;
 $138 = $137;
 $139 = HEAP32[$138>>2]|0;
 $140 = (_bitshift64Ashr(0,($136|0),30)|0);
 $141 = tempRet0;
 $142 = $104;
 $143 = $142;
 $144 = HEAP32[$143>>2]|0;
 $145 = (($142) + 4)|0;
 $146 = $145;
 $147 = HEAP32[$146>>2]|0;
 $148 = (_bitshift64Ashr(0,($144|0),32)|0);
 $149 = tempRet0;
 $150 = (___muldi3(($148|0),($149|0),($140|0),($141|0))|0);
 $151 = tempRet0;
 $152 = (_i64Add(($150|0),($151|0),($132|0),($133|0))|0);
 $153 = tempRet0;
 $154 = $1;
 $155 = $154;
 $156 = HEAP32[$155>>2]|0;
 $157 = (($154) + 4)|0;
 $158 = $157;
 $159 = HEAP32[$158>>2]|0;
 $160 = (_bitshift64Ashr(0,($156|0),31)|0);
 $161 = tempRet0;
 $162 = ((($1)) + 32|0);
 $163 = $162;
 $164 = $163;
 $165 = HEAP32[$164>>2]|0;
 $166 = (($163) + 4)|0;
 $167 = $166;
 $168 = HEAP32[$167>>2]|0;
 $169 = (_bitshift64Ashr(0,($165|0),32)|0);
 $170 = tempRet0;
 $171 = (___muldi3(($169|0),($170|0),($160|0),($161|0))|0);
 $172 = tempRet0;
 $173 = (_i64Add(($152|0),($153|0),($171|0),($172|0))|0);
 $174 = tempRet0;
 $175 = ((($0)) + 32|0);
 $176 = $175;
 $177 = $176;
 HEAP32[$177>>2] = $173;
 $178 = (($176) + 4)|0;
 $179 = $178;
 HEAP32[$179>>2] = $174;
 $180 = $58;
 $181 = $180;
 $182 = HEAP32[$181>>2]|0;
 $183 = (($180) + 4)|0;
 $184 = $183;
 $185 = HEAP32[$184>>2]|0;
 $186 = (_bitshift64Ashr(0,($182|0),32)|0);
 $187 = tempRet0;
 $188 = $104;
 $189 = $188;
 $190 = HEAP32[$189>>2]|0;
 $191 = (($188) + 4)|0;
 $192 = $191;
 $193 = HEAP32[$192>>2]|0;
 $194 = (_bitshift64Ashr(0,($190|0),32)|0);
 $195 = tempRet0;
 $196 = (___muldi3(($194|0),($195|0),($186|0),($187|0))|0);
 $197 = tempRet0;
 $198 = $24;
 $199 = $198;
 $200 = HEAP32[$199>>2]|0;
 $201 = (($198) + 4)|0;
 $202 = $201;
 $203 = HEAP32[$202>>2]|0;
 $204 = (_bitshift64Ashr(0,($200|0),32)|0);
 $205 = tempRet0;
 $206 = $162;
 $207 = $206;
 $208 = HEAP32[$207>>2]|0;
 $209 = (($206) + 4)|0;
 $210 = $209;
 $211 = HEAP32[$210>>2]|0;
 $212 = (_bitshift64Ashr(0,($208|0),32)|0);
 $213 = tempRet0;
 $214 = (___muldi3(($212|0),($213|0),($204|0),($205|0))|0);
 $215 = tempRet0;
 $216 = (_i64Add(($214|0),($215|0),($196|0),($197|0))|0);
 $217 = tempRet0;
 $218 = $1;
 $219 = $218;
 $220 = HEAP32[$219>>2]|0;
 $221 = (($218) + 4)|0;
 $222 = $221;
 $223 = HEAP32[$222>>2]|0;
 $224 = (_bitshift64Ashr(0,($220|0),32)|0);
 $225 = tempRet0;
 $226 = ((($1)) + 40|0);
 $227 = $226;
 $228 = $227;
 $229 = HEAP32[$228>>2]|0;
 $230 = (($227) + 4)|0;
 $231 = $230;
 $232 = HEAP32[$231>>2]|0;
 $233 = (_bitshift64Ashr(0,($229|0),32)|0);
 $234 = tempRet0;
 $235 = (___muldi3(($233|0),($234|0),($224|0),($225|0))|0);
 $236 = tempRet0;
 $237 = (_i64Add(($216|0),($217|0),($235|0),($236|0))|0);
 $238 = tempRet0;
 $239 = (_bitshift64Shl(($237|0),($238|0),1)|0);
 $240 = tempRet0;
 $241 = ((($0)) + 40|0);
 $242 = $241;
 $243 = $242;
 HEAP32[$243>>2] = $239;
 $244 = (($242) + 4)|0;
 $245 = $244;
 HEAP32[$245>>2] = $240;
 $246 = $104;
 $247 = $246;
 $248 = HEAP32[$247>>2]|0;
 $249 = (($246) + 4)|0;
 $250 = $249;
 $251 = HEAP32[$250>>2]|0;
 $252 = (_bitshift64Ashr(0,($248|0),32)|0);
 $253 = tempRet0;
 $254 = (___muldi3(($252|0),($253|0),($252|0),($253|0))|0);
 $255 = tempRet0;
 $256 = $58;
 $257 = $256;
 $258 = HEAP32[$257>>2]|0;
 $259 = (($256) + 4)|0;
 $260 = $259;
 $261 = HEAP32[$260>>2]|0;
 $262 = (_bitshift64Ashr(0,($258|0),32)|0);
 $263 = tempRet0;
 $264 = $162;
 $265 = $264;
 $266 = HEAP32[$265>>2]|0;
 $267 = (($264) + 4)|0;
 $268 = $267;
 $269 = HEAP32[$268>>2]|0;
 $270 = (_bitshift64Ashr(0,($266|0),32)|0);
 $271 = tempRet0;
 $272 = (___muldi3(($270|0),($271|0),($262|0),($263|0))|0);
 $273 = tempRet0;
 $274 = (_i64Add(($272|0),($273|0),($254|0),($255|0))|0);
 $275 = tempRet0;
 $276 = $1;
 $277 = $276;
 $278 = HEAP32[$277>>2]|0;
 $279 = (($276) + 4)|0;
 $280 = $279;
 $281 = HEAP32[$280>>2]|0;
 $282 = (_bitshift64Ashr(0,($278|0),32)|0);
 $283 = tempRet0;
 $284 = ((($1)) + 48|0);
 $285 = $284;
 $286 = $285;
 $287 = HEAP32[$286>>2]|0;
 $288 = (($285) + 4)|0;
 $289 = $288;
 $290 = HEAP32[$289>>2]|0;
 $291 = (_bitshift64Ashr(0,($287|0),32)|0);
 $292 = tempRet0;
 $293 = (___muldi3(($291|0),($292|0),($282|0),($283|0))|0);
 $294 = tempRet0;
 $295 = (_i64Add(($274|0),($275|0),($293|0),($294|0))|0);
 $296 = tempRet0;
 $297 = $24;
 $298 = $297;
 $299 = HEAP32[$298>>2]|0;
 $300 = (($297) + 4)|0;
 $301 = $300;
 $302 = HEAP32[$301>>2]|0;
 $303 = (_bitshift64Ashr(0,($299|0),31)|0);
 $304 = tempRet0;
 $305 = $226;
 $306 = $305;
 $307 = HEAP32[$306>>2]|0;
 $308 = (($305) + 4)|0;
 $309 = $308;
 $310 = HEAP32[$309>>2]|0;
 $311 = (_bitshift64Ashr(0,($307|0),32)|0);
 $312 = tempRet0;
 $313 = (___muldi3(($311|0),($312|0),($303|0),($304|0))|0);
 $314 = tempRet0;
 $315 = (_i64Add(($295|0),($296|0),($313|0),($314|0))|0);
 $316 = tempRet0;
 $317 = (_bitshift64Shl(($315|0),($316|0),1)|0);
 $318 = tempRet0;
 $319 = ((($0)) + 48|0);
 $320 = $319;
 $321 = $320;
 HEAP32[$321>>2] = $317;
 $322 = (($320) + 4)|0;
 $323 = $322;
 HEAP32[$323>>2] = $318;
 $324 = $104;
 $325 = $324;
 $326 = HEAP32[$325>>2]|0;
 $327 = (($324) + 4)|0;
 $328 = $327;
 $329 = HEAP32[$328>>2]|0;
 $330 = (_bitshift64Ashr(0,($326|0),32)|0);
 $331 = tempRet0;
 $332 = $162;
 $333 = $332;
 $334 = HEAP32[$333>>2]|0;
 $335 = (($332) + 4)|0;
 $336 = $335;
 $337 = HEAP32[$336>>2]|0;
 $338 = (_bitshift64Ashr(0,($334|0),32)|0);
 $339 = tempRet0;
 $340 = (___muldi3(($338|0),($339|0),($330|0),($331|0))|0);
 $341 = tempRet0;
 $342 = $58;
 $343 = $342;
 $344 = HEAP32[$343>>2]|0;
 $345 = (($342) + 4)|0;
 $346 = $345;
 $347 = HEAP32[$346>>2]|0;
 $348 = (_bitshift64Ashr(0,($344|0),32)|0);
 $349 = tempRet0;
 $350 = $226;
 $351 = $350;
 $352 = HEAP32[$351>>2]|0;
 $353 = (($350) + 4)|0;
 $354 = $353;
 $355 = HEAP32[$354>>2]|0;
 $356 = (_bitshift64Ashr(0,($352|0),32)|0);
 $357 = tempRet0;
 $358 = (___muldi3(($356|0),($357|0),($348|0),($349|0))|0);
 $359 = tempRet0;
 $360 = (_i64Add(($358|0),($359|0),($340|0),($341|0))|0);
 $361 = tempRet0;
 $362 = $24;
 $363 = $362;
 $364 = HEAP32[$363>>2]|0;
 $365 = (($362) + 4)|0;
 $366 = $365;
 $367 = HEAP32[$366>>2]|0;
 $368 = (_bitshift64Ashr(0,($364|0),32)|0);
 $369 = tempRet0;
 $370 = $284;
 $371 = $370;
 $372 = HEAP32[$371>>2]|0;
 $373 = (($370) + 4)|0;
 $374 = $373;
 $375 = HEAP32[$374>>2]|0;
 $376 = (_bitshift64Ashr(0,($372|0),32)|0);
 $377 = tempRet0;
 $378 = (___muldi3(($376|0),($377|0),($368|0),($369|0))|0);
 $379 = tempRet0;
 $380 = (_i64Add(($360|0),($361|0),($378|0),($379|0))|0);
 $381 = tempRet0;
 $382 = $1;
 $383 = $382;
 $384 = HEAP32[$383>>2]|0;
 $385 = (($382) + 4)|0;
 $386 = $385;
 $387 = HEAP32[$386>>2]|0;
 $388 = (_bitshift64Ashr(0,($384|0),32)|0);
 $389 = tempRet0;
 $390 = ((($1)) + 56|0);
 $391 = $390;
 $392 = $391;
 $393 = HEAP32[$392>>2]|0;
 $394 = (($391) + 4)|0;
 $395 = $394;
 $396 = HEAP32[$395>>2]|0;
 $397 = (_bitshift64Ashr(0,($393|0),32)|0);
 $398 = tempRet0;
 $399 = (___muldi3(($397|0),($398|0),($388|0),($389|0))|0);
 $400 = tempRet0;
 $401 = (_i64Add(($380|0),($381|0),($399|0),($400|0))|0);
 $402 = tempRet0;
 $403 = (_bitshift64Shl(($401|0),($402|0),1)|0);
 $404 = tempRet0;
 $405 = ((($0)) + 56|0);
 $406 = $405;
 $407 = $406;
 HEAP32[$407>>2] = $403;
 $408 = (($406) + 4)|0;
 $409 = $408;
 HEAP32[$409>>2] = $404;
 $410 = $162;
 $411 = $410;
 $412 = HEAP32[$411>>2]|0;
 $413 = (($410) + 4)|0;
 $414 = $413;
 $415 = HEAP32[$414>>2]|0;
 $416 = (_bitshift64Ashr(0,($412|0),32)|0);
 $417 = tempRet0;
 $418 = (___muldi3(($416|0),($417|0),($416|0),($417|0))|0);
 $419 = tempRet0;
 $420 = $58;
 $421 = $420;
 $422 = HEAP32[$421>>2]|0;
 $423 = (($420) + 4)|0;
 $424 = $423;
 $425 = HEAP32[$424>>2]|0;
 $426 = (_bitshift64Ashr(0,($422|0),32)|0);
 $427 = tempRet0;
 $428 = $284;
 $429 = $428;
 $430 = HEAP32[$429>>2]|0;
 $431 = (($428) + 4)|0;
 $432 = $431;
 $433 = HEAP32[$432>>2]|0;
 $434 = (_bitshift64Ashr(0,($430|0),32)|0);
 $435 = tempRet0;
 $436 = (___muldi3(($434|0),($435|0),($426|0),($427|0))|0);
 $437 = tempRet0;
 $438 = $1;
 $439 = $438;
 $440 = HEAP32[$439>>2]|0;
 $441 = (($438) + 4)|0;
 $442 = $441;
 $443 = HEAP32[$442>>2]|0;
 $444 = (_bitshift64Ashr(0,($440|0),32)|0);
 $445 = tempRet0;
 $446 = ((($1)) + 64|0);
 $447 = $446;
 $448 = $447;
 $449 = HEAP32[$448>>2]|0;
 $450 = (($447) + 4)|0;
 $451 = $450;
 $452 = HEAP32[$451>>2]|0;
 $453 = (_bitshift64Ashr(0,($449|0),32)|0);
 $454 = tempRet0;
 $455 = (___muldi3(($453|0),($454|0),($444|0),($445|0))|0);
 $456 = tempRet0;
 $457 = (_i64Add(($455|0),($456|0),($436|0),($437|0))|0);
 $458 = tempRet0;
 $459 = $24;
 $460 = $459;
 $461 = HEAP32[$460>>2]|0;
 $462 = (($459) + 4)|0;
 $463 = $462;
 $464 = HEAP32[$463>>2]|0;
 $465 = (_bitshift64Ashr(0,($461|0),32)|0);
 $466 = tempRet0;
 $467 = $390;
 $468 = $467;
 $469 = HEAP32[$468>>2]|0;
 $470 = (($467) + 4)|0;
 $471 = $470;
 $472 = HEAP32[$471>>2]|0;
 $473 = (_bitshift64Ashr(0,($469|0),32)|0);
 $474 = tempRet0;
 $475 = (___muldi3(($473|0),($474|0),($465|0),($466|0))|0);
 $476 = tempRet0;
 $477 = $104;
 $478 = $477;
 $479 = HEAP32[$478>>2]|0;
 $480 = (($477) + 4)|0;
 $481 = $480;
 $482 = HEAP32[$481>>2]|0;
 $483 = (_bitshift64Ashr(0,($479|0),32)|0);
 $484 = tempRet0;
 $485 = $226;
 $486 = $485;
 $487 = HEAP32[$486>>2]|0;
 $488 = (($485) + 4)|0;
 $489 = $488;
 $490 = HEAP32[$489>>2]|0;
 $491 = (_bitshift64Ashr(0,($487|0),32)|0);
 $492 = tempRet0;
 $493 = (___muldi3(($491|0),($492|0),($483|0),($484|0))|0);
 $494 = tempRet0;
 $495 = (_i64Add(($493|0),($494|0),($475|0),($476|0))|0);
 $496 = tempRet0;
 $497 = (_bitshift64Shl(($495|0),($496|0),1)|0);
 $498 = tempRet0;
 $499 = (_i64Add(($457|0),($458|0),($497|0),($498|0))|0);
 $500 = tempRet0;
 $501 = (_bitshift64Shl(($499|0),($500|0),1)|0);
 $502 = tempRet0;
 $503 = (_i64Add(($501|0),($502|0),($418|0),($419|0))|0);
 $504 = tempRet0;
 $505 = ((($0)) + 64|0);
 $506 = $505;
 $507 = $506;
 HEAP32[$507>>2] = $503;
 $508 = (($506) + 4)|0;
 $509 = $508;
 HEAP32[$509>>2] = $504;
 $510 = $162;
 $511 = $510;
 $512 = HEAP32[$511>>2]|0;
 $513 = (($510) + 4)|0;
 $514 = $513;
 $515 = HEAP32[$514>>2]|0;
 $516 = (_bitshift64Ashr(0,($512|0),32)|0);
 $517 = tempRet0;
 $518 = $226;
 $519 = $518;
 $520 = HEAP32[$519>>2]|0;
 $521 = (($518) + 4)|0;
 $522 = $521;
 $523 = HEAP32[$522>>2]|0;
 $524 = (_bitshift64Ashr(0,($520|0),32)|0);
 $525 = tempRet0;
 $526 = (___muldi3(($524|0),($525|0),($516|0),($517|0))|0);
 $527 = tempRet0;
 $528 = $104;
 $529 = $528;
 $530 = HEAP32[$529>>2]|0;
 $531 = (($528) + 4)|0;
 $532 = $531;
 $533 = HEAP32[$532>>2]|0;
 $534 = (_bitshift64Ashr(0,($530|0),32)|0);
 $535 = tempRet0;
 $536 = $284;
 $537 = $536;
 $538 = HEAP32[$537>>2]|0;
 $539 = (($536) + 4)|0;
 $540 = $539;
 $541 = HEAP32[$540>>2]|0;
 $542 = (_bitshift64Ashr(0,($538|0),32)|0);
 $543 = tempRet0;
 $544 = (___muldi3(($542|0),($543|0),($534|0),($535|0))|0);
 $545 = tempRet0;
 $546 = (_i64Add(($544|0),($545|0),($526|0),($527|0))|0);
 $547 = tempRet0;
 $548 = $58;
 $549 = $548;
 $550 = HEAP32[$549>>2]|0;
 $551 = (($548) + 4)|0;
 $552 = $551;
 $553 = HEAP32[$552>>2]|0;
 $554 = (_bitshift64Ashr(0,($550|0),32)|0);
 $555 = tempRet0;
 $556 = $390;
 $557 = $556;
 $558 = HEAP32[$557>>2]|0;
 $559 = (($556) + 4)|0;
 $560 = $559;
 $561 = HEAP32[$560>>2]|0;
 $562 = (_bitshift64Ashr(0,($558|0),32)|0);
 $563 = tempRet0;
 $564 = (___muldi3(($562|0),($563|0),($554|0),($555|0))|0);
 $565 = tempRet0;
 $566 = (_i64Add(($546|0),($547|0),($564|0),($565|0))|0);
 $567 = tempRet0;
 $568 = $24;
 $569 = $568;
 $570 = HEAP32[$569>>2]|0;
 $571 = (($568) + 4)|0;
 $572 = $571;
 $573 = HEAP32[$572>>2]|0;
 $574 = (_bitshift64Ashr(0,($570|0),32)|0);
 $575 = tempRet0;
 $576 = $446;
 $577 = $576;
 $578 = HEAP32[$577>>2]|0;
 $579 = (($576) + 4)|0;
 $580 = $579;
 $581 = HEAP32[$580>>2]|0;
 $582 = (_bitshift64Ashr(0,($578|0),32)|0);
 $583 = tempRet0;
 $584 = (___muldi3(($582|0),($583|0),($574|0),($575|0))|0);
 $585 = tempRet0;
 $586 = (_i64Add(($566|0),($567|0),($584|0),($585|0))|0);
 $587 = tempRet0;
 $588 = $1;
 $589 = $588;
 $590 = HEAP32[$589>>2]|0;
 $591 = (($588) + 4)|0;
 $592 = $591;
 $593 = HEAP32[$592>>2]|0;
 $594 = (_bitshift64Ashr(0,($590|0),32)|0);
 $595 = tempRet0;
 $596 = ((($1)) + 72|0);
 $597 = $596;
 $598 = $597;
 $599 = HEAP32[$598>>2]|0;
 $600 = (($597) + 4)|0;
 $601 = $600;
 $602 = HEAP32[$601>>2]|0;
 $603 = (_bitshift64Ashr(0,($599|0),32)|0);
 $604 = tempRet0;
 $605 = (___muldi3(($603|0),($604|0),($594|0),($595|0))|0);
 $606 = tempRet0;
 $607 = (_i64Add(($586|0),($587|0),($605|0),($606|0))|0);
 $608 = tempRet0;
 $609 = (_bitshift64Shl(($607|0),($608|0),1)|0);
 $610 = tempRet0;
 $611 = ((($0)) + 72|0);
 $612 = $611;
 $613 = $612;
 HEAP32[$613>>2] = $609;
 $614 = (($612) + 4)|0;
 $615 = $614;
 HEAP32[$615>>2] = $610;
 $616 = $226;
 $617 = $616;
 $618 = HEAP32[$617>>2]|0;
 $619 = (($616) + 4)|0;
 $620 = $619;
 $621 = HEAP32[$620>>2]|0;
 $622 = (_bitshift64Ashr(0,($618|0),32)|0);
 $623 = tempRet0;
 $624 = (___muldi3(($622|0),($623|0),($622|0),($623|0))|0);
 $625 = tempRet0;
 $626 = $162;
 $627 = $626;
 $628 = HEAP32[$627>>2]|0;
 $629 = (($626) + 4)|0;
 $630 = $629;
 $631 = HEAP32[$630>>2]|0;
 $632 = (_bitshift64Ashr(0,($628|0),32)|0);
 $633 = tempRet0;
 $634 = $284;
 $635 = $634;
 $636 = HEAP32[$635>>2]|0;
 $637 = (($634) + 4)|0;
 $638 = $637;
 $639 = HEAP32[$638>>2]|0;
 $640 = (_bitshift64Ashr(0,($636|0),32)|0);
 $641 = tempRet0;
 $642 = (___muldi3(($640|0),($641|0),($632|0),($633|0))|0);
 $643 = tempRet0;
 $644 = (_i64Add(($642|0),($643|0),($624|0),($625|0))|0);
 $645 = tempRet0;
 $646 = $58;
 $647 = $646;
 $648 = HEAP32[$647>>2]|0;
 $649 = (($646) + 4)|0;
 $650 = $649;
 $651 = HEAP32[$650>>2]|0;
 $652 = (_bitshift64Ashr(0,($648|0),32)|0);
 $653 = tempRet0;
 $654 = $446;
 $655 = $654;
 $656 = HEAP32[$655>>2]|0;
 $657 = (($654) + 4)|0;
 $658 = $657;
 $659 = HEAP32[$658>>2]|0;
 $660 = (_bitshift64Ashr(0,($656|0),32)|0);
 $661 = tempRet0;
 $662 = (___muldi3(($660|0),($661|0),($652|0),($653|0))|0);
 $663 = tempRet0;
 $664 = (_i64Add(($644|0),($645|0),($662|0),($663|0))|0);
 $665 = tempRet0;
 $666 = $104;
 $667 = $666;
 $668 = HEAP32[$667>>2]|0;
 $669 = (($666) + 4)|0;
 $670 = $669;
 $671 = HEAP32[$670>>2]|0;
 $672 = (_bitshift64Ashr(0,($668|0),32)|0);
 $673 = tempRet0;
 $674 = $390;
 $675 = $674;
 $676 = HEAP32[$675>>2]|0;
 $677 = (($674) + 4)|0;
 $678 = $677;
 $679 = HEAP32[$678>>2]|0;
 $680 = (_bitshift64Ashr(0,($676|0),32)|0);
 $681 = tempRet0;
 $682 = (___muldi3(($680|0),($681|0),($672|0),($673|0))|0);
 $683 = tempRet0;
 $684 = $24;
 $685 = $684;
 $686 = HEAP32[$685>>2]|0;
 $687 = (($684) + 4)|0;
 $688 = $687;
 $689 = HEAP32[$688>>2]|0;
 $690 = (_bitshift64Ashr(0,($686|0),32)|0);
 $691 = tempRet0;
 $692 = $596;
 $693 = $692;
 $694 = HEAP32[$693>>2]|0;
 $695 = (($692) + 4)|0;
 $696 = $695;
 $697 = HEAP32[$696>>2]|0;
 $698 = (_bitshift64Ashr(0,($694|0),32)|0);
 $699 = tempRet0;
 $700 = (___muldi3(($698|0),($699|0),($690|0),($691|0))|0);
 $701 = tempRet0;
 $702 = (_i64Add(($700|0),($701|0),($682|0),($683|0))|0);
 $703 = tempRet0;
 $704 = (_bitshift64Shl(($702|0),($703|0),1)|0);
 $705 = tempRet0;
 $706 = (_i64Add(($664|0),($665|0),($704|0),($705|0))|0);
 $707 = tempRet0;
 $708 = (_bitshift64Shl(($706|0),($707|0),1)|0);
 $709 = tempRet0;
 $710 = ((($0)) + 80|0);
 $711 = $710;
 $712 = $711;
 HEAP32[$712>>2] = $708;
 $713 = (($711) + 4)|0;
 $714 = $713;
 HEAP32[$714>>2] = $709;
 $715 = $226;
 $716 = $715;
 $717 = HEAP32[$716>>2]|0;
 $718 = (($715) + 4)|0;
 $719 = $718;
 $720 = HEAP32[$719>>2]|0;
 $721 = (_bitshift64Ashr(0,($717|0),32)|0);
 $722 = tempRet0;
 $723 = $284;
 $724 = $723;
 $725 = HEAP32[$724>>2]|0;
 $726 = (($723) + 4)|0;
 $727 = $726;
 $728 = HEAP32[$727>>2]|0;
 $729 = (_bitshift64Ashr(0,($725|0),32)|0);
 $730 = tempRet0;
 $731 = (___muldi3(($729|0),($730|0),($721|0),($722|0))|0);
 $732 = tempRet0;
 $733 = $162;
 $734 = $733;
 $735 = HEAP32[$734>>2]|0;
 $736 = (($733) + 4)|0;
 $737 = $736;
 $738 = HEAP32[$737>>2]|0;
 $739 = (_bitshift64Ashr(0,($735|0),32)|0);
 $740 = tempRet0;
 $741 = $390;
 $742 = $741;
 $743 = HEAP32[$742>>2]|0;
 $744 = (($741) + 4)|0;
 $745 = $744;
 $746 = HEAP32[$745>>2]|0;
 $747 = (_bitshift64Ashr(0,($743|0),32)|0);
 $748 = tempRet0;
 $749 = (___muldi3(($747|0),($748|0),($739|0),($740|0))|0);
 $750 = tempRet0;
 $751 = (_i64Add(($749|0),($750|0),($731|0),($732|0))|0);
 $752 = tempRet0;
 $753 = $104;
 $754 = $753;
 $755 = HEAP32[$754>>2]|0;
 $756 = (($753) + 4)|0;
 $757 = $756;
 $758 = HEAP32[$757>>2]|0;
 $759 = (_bitshift64Ashr(0,($755|0),32)|0);
 $760 = tempRet0;
 $761 = $446;
 $762 = $761;
 $763 = HEAP32[$762>>2]|0;
 $764 = (($761) + 4)|0;
 $765 = $764;
 $766 = HEAP32[$765>>2]|0;
 $767 = (_bitshift64Ashr(0,($763|0),32)|0);
 $768 = tempRet0;
 $769 = (___muldi3(($767|0),($768|0),($759|0),($760|0))|0);
 $770 = tempRet0;
 $771 = (_i64Add(($751|0),($752|0),($769|0),($770|0))|0);
 $772 = tempRet0;
 $773 = $58;
 $774 = $773;
 $775 = HEAP32[$774>>2]|0;
 $776 = (($773) + 4)|0;
 $777 = $776;
 $778 = HEAP32[$777>>2]|0;
 $779 = (_bitshift64Ashr(0,($775|0),32)|0);
 $780 = tempRet0;
 $781 = $596;
 $782 = $781;
 $783 = HEAP32[$782>>2]|0;
 $784 = (($781) + 4)|0;
 $785 = $784;
 $786 = HEAP32[$785>>2]|0;
 $787 = (_bitshift64Ashr(0,($783|0),32)|0);
 $788 = tempRet0;
 $789 = (___muldi3(($787|0),($788|0),($779|0),($780|0))|0);
 $790 = tempRet0;
 $791 = (_i64Add(($771|0),($772|0),($789|0),($790|0))|0);
 $792 = tempRet0;
 $793 = (_bitshift64Shl(($791|0),($792|0),1)|0);
 $794 = tempRet0;
 $795 = ((($0)) + 88|0);
 $796 = $795;
 $797 = $796;
 HEAP32[$797>>2] = $793;
 $798 = (($796) + 4)|0;
 $799 = $798;
 HEAP32[$799>>2] = $794;
 $800 = $284;
 $801 = $800;
 $802 = HEAP32[$801>>2]|0;
 $803 = (($800) + 4)|0;
 $804 = $803;
 $805 = HEAP32[$804>>2]|0;
 $806 = (_bitshift64Ashr(0,($802|0),32)|0);
 $807 = tempRet0;
 $808 = (___muldi3(($806|0),($807|0),($806|0),($807|0))|0);
 $809 = tempRet0;
 $810 = $162;
 $811 = $810;
 $812 = HEAP32[$811>>2]|0;
 $813 = (($810) + 4)|0;
 $814 = $813;
 $815 = HEAP32[$814>>2]|0;
 $816 = (_bitshift64Ashr(0,($812|0),32)|0);
 $817 = tempRet0;
 $818 = $446;
 $819 = $818;
 $820 = HEAP32[$819>>2]|0;
 $821 = (($818) + 4)|0;
 $822 = $821;
 $823 = HEAP32[$822>>2]|0;
 $824 = (_bitshift64Ashr(0,($820|0),32)|0);
 $825 = tempRet0;
 $826 = (___muldi3(($824|0),($825|0),($816|0),($817|0))|0);
 $827 = tempRet0;
 $828 = $226;
 $829 = $828;
 $830 = HEAP32[$829>>2]|0;
 $831 = (($828) + 4)|0;
 $832 = $831;
 $833 = HEAP32[$832>>2]|0;
 $834 = (_bitshift64Ashr(0,($830|0),32)|0);
 $835 = tempRet0;
 $836 = $390;
 $837 = $836;
 $838 = HEAP32[$837>>2]|0;
 $839 = (($836) + 4)|0;
 $840 = $839;
 $841 = HEAP32[$840>>2]|0;
 $842 = (_bitshift64Ashr(0,($838|0),32)|0);
 $843 = tempRet0;
 $844 = (___muldi3(($842|0),($843|0),($834|0),($835|0))|0);
 $845 = tempRet0;
 $846 = $104;
 $847 = $846;
 $848 = HEAP32[$847>>2]|0;
 $849 = (($846) + 4)|0;
 $850 = $849;
 $851 = HEAP32[$850>>2]|0;
 $852 = (_bitshift64Ashr(0,($848|0),32)|0);
 $853 = tempRet0;
 $854 = $596;
 $855 = $854;
 $856 = HEAP32[$855>>2]|0;
 $857 = (($854) + 4)|0;
 $858 = $857;
 $859 = HEAP32[$858>>2]|0;
 $860 = (_bitshift64Ashr(0,($856|0),32)|0);
 $861 = tempRet0;
 $862 = (___muldi3(($860|0),($861|0),($852|0),($853|0))|0);
 $863 = tempRet0;
 $864 = (_i64Add(($862|0),($863|0),($844|0),($845|0))|0);
 $865 = tempRet0;
 $866 = (_bitshift64Shl(($864|0),($865|0),1)|0);
 $867 = tempRet0;
 $868 = (_i64Add(($866|0),($867|0),($826|0),($827|0))|0);
 $869 = tempRet0;
 $870 = (_bitshift64Shl(($868|0),($869|0),1)|0);
 $871 = tempRet0;
 $872 = (_i64Add(($870|0),($871|0),($808|0),($809|0))|0);
 $873 = tempRet0;
 $874 = ((($0)) + 96|0);
 $875 = $874;
 $876 = $875;
 HEAP32[$876>>2] = $872;
 $877 = (($875) + 4)|0;
 $878 = $877;
 HEAP32[$878>>2] = $873;
 $879 = $284;
 $880 = $879;
 $881 = HEAP32[$880>>2]|0;
 $882 = (($879) + 4)|0;
 $883 = $882;
 $884 = HEAP32[$883>>2]|0;
 $885 = (_bitshift64Ashr(0,($881|0),32)|0);
 $886 = tempRet0;
 $887 = $390;
 $888 = $887;
 $889 = HEAP32[$888>>2]|0;
 $890 = (($887) + 4)|0;
 $891 = $890;
 $892 = HEAP32[$891>>2]|0;
 $893 = (_bitshift64Ashr(0,($889|0),32)|0);
 $894 = tempRet0;
 $895 = (___muldi3(($893|0),($894|0),($885|0),($886|0))|0);
 $896 = tempRet0;
 $897 = $226;
 $898 = $897;
 $899 = HEAP32[$898>>2]|0;
 $900 = (($897) + 4)|0;
 $901 = $900;
 $902 = HEAP32[$901>>2]|0;
 $903 = (_bitshift64Ashr(0,($899|0),32)|0);
 $904 = tempRet0;
 $905 = $446;
 $906 = $905;
 $907 = HEAP32[$906>>2]|0;
 $908 = (($905) + 4)|0;
 $909 = $908;
 $910 = HEAP32[$909>>2]|0;
 $911 = (_bitshift64Ashr(0,($907|0),32)|0);
 $912 = tempRet0;
 $913 = (___muldi3(($911|0),($912|0),($903|0),($904|0))|0);
 $914 = tempRet0;
 $915 = (_i64Add(($913|0),($914|0),($895|0),($896|0))|0);
 $916 = tempRet0;
 $917 = $162;
 $918 = $917;
 $919 = HEAP32[$918>>2]|0;
 $920 = (($917) + 4)|0;
 $921 = $920;
 $922 = HEAP32[$921>>2]|0;
 $923 = (_bitshift64Ashr(0,($919|0),32)|0);
 $924 = tempRet0;
 $925 = $596;
 $926 = $925;
 $927 = HEAP32[$926>>2]|0;
 $928 = (($925) + 4)|0;
 $929 = $928;
 $930 = HEAP32[$929>>2]|0;
 $931 = (_bitshift64Ashr(0,($927|0),32)|0);
 $932 = tempRet0;
 $933 = (___muldi3(($931|0),($932|0),($923|0),($924|0))|0);
 $934 = tempRet0;
 $935 = (_i64Add(($915|0),($916|0),($933|0),($934|0))|0);
 $936 = tempRet0;
 $937 = (_bitshift64Shl(($935|0),($936|0),1)|0);
 $938 = tempRet0;
 $939 = ((($0)) + 104|0);
 $940 = $939;
 $941 = $940;
 HEAP32[$941>>2] = $937;
 $942 = (($940) + 4)|0;
 $943 = $942;
 HEAP32[$943>>2] = $938;
 $944 = $390;
 $945 = $944;
 $946 = HEAP32[$945>>2]|0;
 $947 = (($944) + 4)|0;
 $948 = $947;
 $949 = HEAP32[$948>>2]|0;
 $950 = (_bitshift64Ashr(0,($946|0),32)|0);
 $951 = tempRet0;
 $952 = (___muldi3(($950|0),($951|0),($950|0),($951|0))|0);
 $953 = tempRet0;
 $954 = $284;
 $955 = $954;
 $956 = HEAP32[$955>>2]|0;
 $957 = (($954) + 4)|0;
 $958 = $957;
 $959 = HEAP32[$958>>2]|0;
 $960 = (_bitshift64Ashr(0,($956|0),32)|0);
 $961 = tempRet0;
 $962 = $446;
 $963 = $962;
 $964 = HEAP32[$963>>2]|0;
 $965 = (($962) + 4)|0;
 $966 = $965;
 $967 = HEAP32[$966>>2]|0;
 $968 = (_bitshift64Ashr(0,($964|0),32)|0);
 $969 = tempRet0;
 $970 = (___muldi3(($968|0),($969|0),($960|0),($961|0))|0);
 $971 = tempRet0;
 $972 = (_i64Add(($970|0),($971|0),($952|0),($953|0))|0);
 $973 = tempRet0;
 $974 = $226;
 $975 = $974;
 $976 = HEAP32[$975>>2]|0;
 $977 = (($974) + 4)|0;
 $978 = $977;
 $979 = HEAP32[$978>>2]|0;
 $980 = (_bitshift64Ashr(0,($976|0),31)|0);
 $981 = tempRet0;
 $982 = $596;
 $983 = $982;
 $984 = HEAP32[$983>>2]|0;
 $985 = (($982) + 4)|0;
 $986 = $985;
 $987 = HEAP32[$986>>2]|0;
 $988 = (_bitshift64Ashr(0,($984|0),32)|0);
 $989 = tempRet0;
 $990 = (___muldi3(($988|0),($989|0),($980|0),($981|0))|0);
 $991 = tempRet0;
 $992 = (_i64Add(($972|0),($973|0),($990|0),($991|0))|0);
 $993 = tempRet0;
 $994 = (_bitshift64Shl(($992|0),($993|0),1)|0);
 $995 = tempRet0;
 $996 = ((($0)) + 112|0);
 $997 = $996;
 $998 = $997;
 HEAP32[$998>>2] = $994;
 $999 = (($997) + 4)|0;
 $1000 = $999;
 HEAP32[$1000>>2] = $995;
 $1001 = $390;
 $1002 = $1001;
 $1003 = HEAP32[$1002>>2]|0;
 $1004 = (($1001) + 4)|0;
 $1005 = $1004;
 $1006 = HEAP32[$1005>>2]|0;
 $1007 = (_bitshift64Ashr(0,($1003|0),32)|0);
 $1008 = tempRet0;
 $1009 = $446;
 $1010 = $1009;
 $1011 = HEAP32[$1010>>2]|0;
 $1012 = (($1009) + 4)|0;
 $1013 = $1012;
 $1014 = HEAP32[$1013>>2]|0;
 $1015 = (_bitshift64Ashr(0,($1011|0),32)|0);
 $1016 = tempRet0;
 $1017 = (___muldi3(($1015|0),($1016|0),($1007|0),($1008|0))|0);
 $1018 = tempRet0;
 $1019 = $284;
 $1020 = $1019;
 $1021 = HEAP32[$1020>>2]|0;
 $1022 = (($1019) + 4)|0;
 $1023 = $1022;
 $1024 = HEAP32[$1023>>2]|0;
 $1025 = (_bitshift64Ashr(0,($1021|0),32)|0);
 $1026 = tempRet0;
 $1027 = $596;
 $1028 = $1027;
 $1029 = HEAP32[$1028>>2]|0;
 $1030 = (($1027) + 4)|0;
 $1031 = $1030;
 $1032 = HEAP32[$1031>>2]|0;
 $1033 = (_bitshift64Ashr(0,($1029|0),32)|0);
 $1034 = tempRet0;
 $1035 = (___muldi3(($1033|0),($1034|0),($1025|0),($1026|0))|0);
 $1036 = tempRet0;
 $1037 = (_i64Add(($1035|0),($1036|0),($1017|0),($1018|0))|0);
 $1038 = tempRet0;
 $1039 = (_bitshift64Shl(($1037|0),($1038|0),1)|0);
 $1040 = tempRet0;
 $1041 = ((($0)) + 120|0);
 $1042 = $1041;
 $1043 = $1042;
 HEAP32[$1043>>2] = $1039;
 $1044 = (($1042) + 4)|0;
 $1045 = $1044;
 HEAP32[$1045>>2] = $1040;
 $1046 = $446;
 $1047 = $1046;
 $1048 = HEAP32[$1047>>2]|0;
 $1049 = (($1046) + 4)|0;
 $1050 = $1049;
 $1051 = HEAP32[$1050>>2]|0;
 $1052 = (_bitshift64Ashr(0,($1048|0),32)|0);
 $1053 = tempRet0;
 $1054 = (___muldi3(($1052|0),($1053|0),($1052|0),($1053|0))|0);
 $1055 = tempRet0;
 $1056 = $390;
 $1057 = $1056;
 $1058 = HEAP32[$1057>>2]|0;
 $1059 = (($1056) + 4)|0;
 $1060 = $1059;
 $1061 = HEAP32[$1060>>2]|0;
 $1062 = (_bitshift64Ashr(0,($1058|0),30)|0);
 $1063 = tempRet0;
 $1064 = $596;
 $1065 = $1064;
 $1066 = HEAP32[$1065>>2]|0;
 $1067 = (($1064) + 4)|0;
 $1068 = $1067;
 $1069 = HEAP32[$1068>>2]|0;
 $1070 = (_bitshift64Ashr(0,($1066|0),32)|0);
 $1071 = tempRet0;
 $1072 = (___muldi3(($1070|0),($1071|0),($1062|0),($1063|0))|0);
 $1073 = tempRet0;
 $1074 = (_i64Add(($1072|0),($1073|0),($1054|0),($1055|0))|0);
 $1075 = tempRet0;
 $1076 = ((($0)) + 128|0);
 $1077 = $1076;
 $1078 = $1077;
 HEAP32[$1078>>2] = $1074;
 $1079 = (($1077) + 4)|0;
 $1080 = $1079;
 HEAP32[$1080>>2] = $1075;
 $1081 = $446;
 $1082 = $1081;
 $1083 = HEAP32[$1082>>2]|0;
 $1084 = (($1081) + 4)|0;
 $1085 = $1084;
 $1086 = HEAP32[$1085>>2]|0;
 $1087 = (_bitshift64Ashr(0,($1083|0),31)|0);
 $1088 = tempRet0;
 $1089 = $596;
 $1090 = $1089;
 $1091 = HEAP32[$1090>>2]|0;
 $1092 = (($1089) + 4)|0;
 $1093 = $1092;
 $1094 = HEAP32[$1093>>2]|0;
 $1095 = (_bitshift64Ashr(0,($1091|0),32)|0);
 $1096 = tempRet0;
 $1097 = (___muldi3(($1095|0),($1096|0),($1087|0),($1088|0))|0);
 $1098 = tempRet0;
 $1099 = ((($0)) + 136|0);
 $1100 = $1099;
 $1101 = $1100;
 HEAP32[$1101>>2] = $1097;
 $1102 = (($1100) + 4)|0;
 $1103 = $1102;
 HEAP32[$1103>>2] = $1098;
 $1104 = $596;
 $1105 = $1104;
 $1106 = HEAP32[$1105>>2]|0;
 $1107 = (($1104) + 4)|0;
 $1108 = $1107;
 $1109 = HEAP32[$1108>>2]|0;
 $1110 = (_bitshift64Ashr(0,($1106|0),32)|0);
 $1111 = tempRet0;
 $1112 = (_bitshift64Ashr(0,($1106|0),31)|0);
 $1113 = tempRet0;
 $1114 = (___muldi3(($1112|0),($1113|0),($1110|0),($1111|0))|0);
 $1115 = tempRet0;
 $1116 = ((($0)) + 144|0);
 $1117 = $1116;
 $1118 = $1117;
 HEAP32[$1118>>2] = $1114;
 $1119 = (($1117) + 4)|0;
 $1120 = $1119;
 HEAP32[$1120>>2] = $1115;
 return;
}
function _swap_conditional($0,$1,$2,$3) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 $3 = $3|0;
 var $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0, $113 = 0, $114 = 0, $115 = 0, $116 = 0, $117 = 0;
 var $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0, $133 = 0, $134 = 0, $135 = 0;
 var $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0, $15 = 0, $150 = 0, $151 = 0, $152 = 0, $153 = 0;
 var $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $159 = 0, $16 = 0, $160 = 0, $161 = 0, $162 = 0, $163 = 0, $164 = 0, $165 = 0, $166 = 0, $167 = 0, $168 = 0, $169 = 0, $17 = 0, $170 = 0, $171 = 0;
 var $172 = 0, $173 = 0, $174 = 0, $175 = 0, $176 = 0, $177 = 0, $178 = 0, $179 = 0, $18 = 0, $180 = 0, $181 = 0, $182 = 0, $183 = 0, $184 = 0, $185 = 0, $186 = 0, $187 = 0, $188 = 0, $189 = 0, $19 = 0;
 var $190 = 0, $191 = 0, $192 = 0, $193 = 0, $194 = 0, $195 = 0, $196 = 0, $197 = 0, $198 = 0, $199 = 0, $20 = 0, $200 = 0, $201 = 0, $202 = 0, $203 = 0, $204 = 0, $205 = 0, $206 = 0, $207 = 0, $208 = 0;
 var $209 = 0, $21 = 0, $210 = 0, $211 = 0, $212 = 0, $213 = 0, $214 = 0, $215 = 0, $216 = 0, $217 = 0, $218 = 0, $219 = 0, $22 = 0, $220 = 0, $221 = 0, $222 = 0, $223 = 0, $224 = 0, $225 = 0, $226 = 0;
 var $227 = 0, $228 = 0, $229 = 0, $23 = 0, $230 = 0, $231 = 0, $232 = 0, $233 = 0, $234 = 0, $235 = 0, $236 = 0, $237 = 0, $238 = 0, $239 = 0, $24 = 0, $240 = 0, $241 = 0, $242 = 0, $243 = 0, $244 = 0;
 var $245 = 0, $246 = 0, $247 = 0, $248 = 0, $249 = 0, $25 = 0, $250 = 0, $251 = 0, $252 = 0, $253 = 0, $254 = 0, $255 = 0, $256 = 0, $257 = 0, $258 = 0, $259 = 0, $26 = 0, $260 = 0, $261 = 0, $262 = 0;
 var $263 = 0, $264 = 0, $265 = 0, $266 = 0, $267 = 0, $268 = 0, $269 = 0, $27 = 0, $270 = 0, $271 = 0, $272 = 0, $273 = 0, $274 = 0, $275 = 0, $276 = 0, $277 = 0, $278 = 0, $279 = 0, $28 = 0, $280 = 0;
 var $281 = 0, $282 = 0, $283 = 0, $284 = 0, $285 = 0, $286 = 0, $287 = 0, $288 = 0, $289 = 0, $29 = 0, $290 = 0, $291 = 0, $292 = 0, $293 = 0, $294 = 0, $295 = 0, $296 = 0, $297 = 0, $298 = 0, $299 = 0;
 var $30 = 0, $300 = 0, $301 = 0, $302 = 0, $303 = 0, $304 = 0, $305 = 0, $306 = 0, $307 = 0, $308 = 0, $309 = 0, $31 = 0, $310 = 0, $311 = 0, $312 = 0, $313 = 0, $314 = 0, $315 = 0, $316 = 0, $317 = 0;
 var $318 = 0, $319 = 0, $32 = 0, $320 = 0, $321 = 0, $322 = 0, $323 = 0, $324 = 0, $325 = 0, $326 = 0, $327 = 0, $328 = 0, $329 = 0, $33 = 0, $330 = 0, $331 = 0, $332 = 0, $333 = 0, $334 = 0, $335 = 0;
 var $336 = 0, $337 = 0, $338 = 0, $339 = 0, $34 = 0, $340 = 0, $341 = 0, $342 = 0, $343 = 0, $344 = 0, $345 = 0, $346 = 0, $347 = 0, $348 = 0, $349 = 0, $35 = 0, $350 = 0, $351 = 0, $352 = 0, $353 = 0;
 var $354 = 0, $355 = 0, $356 = 0, $357 = 0, $358 = 0, $359 = 0, $36 = 0, $360 = 0, $361 = 0, $362 = 0, $363 = 0, $364 = 0, $365 = 0, $366 = 0, $367 = 0, $368 = 0, $369 = 0, $37 = 0, $370 = 0, $371 = 0;
 var $372 = 0, $373 = 0, $374 = 0, $375 = 0, $376 = 0, $377 = 0, $378 = 0, $379 = 0, $38 = 0, $380 = 0, $381 = 0, $382 = 0, $383 = 0, $39 = 0, $4 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0;
 var $45 = 0, $46 = 0, $47 = 0, $48 = 0, $49 = 0, $5 = 0, $50 = 0, $51 = 0, $52 = 0, $53 = 0, $54 = 0, $55 = 0, $56 = 0, $57 = 0, $58 = 0, $59 = 0, $6 = 0, $60 = 0, $61 = 0, $62 = 0;
 var $63 = 0, $64 = 0, $65 = 0, $66 = 0, $67 = 0, $68 = 0, $69 = 0, $7 = 0, $70 = 0, $71 = 0, $72 = 0, $73 = 0, $74 = 0, $75 = 0, $76 = 0, $77 = 0, $78 = 0, $79 = 0, $8 = 0, $80 = 0;
 var $81 = 0, $82 = 0, $83 = 0, $84 = 0, $85 = 0, $86 = 0, $87 = 0, $88 = 0, $89 = 0, $9 = 0, $90 = 0, $91 = 0, $92 = 0, $93 = 0, $94 = 0, $95 = 0, $96 = 0, $97 = 0, $98 = 0, $99 = 0;
 var label = 0, sp = 0;
 sp = STACKTOP;
 $4 = (_i64Subtract(0,0,($2|0),($3|0))|0);
 $5 = tempRet0;
 $6 = $0;
 $7 = $6;
 $8 = HEAP32[$7>>2]|0;
 $9 = (($6) + 4)|0;
 $10 = $9;
 $11 = HEAP32[$10>>2]|0;
 $12 = $1;
 $13 = $12;
 $14 = HEAP32[$13>>2]|0;
 $15 = (($12) + 4)|0;
 $16 = $15;
 $17 = HEAP32[$16>>2]|0;
 $18 = $14 ^ $8;
 $19 = $17 ^ $11;
 $20 = $18 & $4;
 $21 = $19 & $5;
 $22 = $20 ^ $8;
 $21 ^ $11;
 $23 = (_bitshift64Ashr(0,($22|0),32)|0);
 $24 = tempRet0;
 $25 = $0;
 $26 = $25;
 HEAP32[$26>>2] = $23;
 $27 = (($25) + 4)|0;
 $28 = $27;
 HEAP32[$28>>2] = $24;
 $29 = $1;
 $30 = $29;
 $31 = HEAP32[$30>>2]|0;
 $32 = (($29) + 4)|0;
 $33 = $32;
 $34 = HEAP32[$33>>2]|0;
 $35 = $31 ^ $20;
 $34 ^ $21;
 $36 = (_bitshift64Ashr(0,($35|0),32)|0);
 $37 = tempRet0;
 $38 = $1;
 $39 = $38;
 HEAP32[$39>>2] = $36;
 $40 = (($38) + 4)|0;
 $41 = $40;
 HEAP32[$41>>2] = $37;
 $42 = ((($0)) + 8|0);
 $43 = $42;
 $44 = $43;
 $45 = HEAP32[$44>>2]|0;
 $46 = (($43) + 4)|0;
 $47 = $46;
 $48 = HEAP32[$47>>2]|0;
 $49 = ((($1)) + 8|0);
 $50 = $49;
 $51 = $50;
 $52 = HEAP32[$51>>2]|0;
 $53 = (($50) + 4)|0;
 $54 = $53;
 $55 = HEAP32[$54>>2]|0;
 $56 = $52 ^ $45;
 $57 = $55 ^ $48;
 $58 = $56 & $4;
 $59 = $57 & $5;
 $60 = $58 ^ $45;
 $59 ^ $48;
 $61 = (_bitshift64Ashr(0,($60|0),32)|0);
 $62 = tempRet0;
 $63 = $42;
 $64 = $63;
 HEAP32[$64>>2] = $61;
 $65 = (($63) + 4)|0;
 $66 = $65;
 HEAP32[$66>>2] = $62;
 $67 = $49;
 $68 = $67;
 $69 = HEAP32[$68>>2]|0;
 $70 = (($67) + 4)|0;
 $71 = $70;
 $72 = HEAP32[$71>>2]|0;
 $73 = $69 ^ $58;
 $72 ^ $59;
 $74 = (_bitshift64Ashr(0,($73|0),32)|0);
 $75 = tempRet0;
 $76 = $49;
 $77 = $76;
 HEAP32[$77>>2] = $74;
 $78 = (($76) + 4)|0;
 $79 = $78;
 HEAP32[$79>>2] = $75;
 $80 = ((($0)) + 16|0);
 $81 = $80;
 $82 = $81;
 $83 = HEAP32[$82>>2]|0;
 $84 = (($81) + 4)|0;
 $85 = $84;
 $86 = HEAP32[$85>>2]|0;
 $87 = ((($1)) + 16|0);
 $88 = $87;
 $89 = $88;
 $90 = HEAP32[$89>>2]|0;
 $91 = (($88) + 4)|0;
 $92 = $91;
 $93 = HEAP32[$92>>2]|0;
 $94 = $90 ^ $83;
 $95 = $93 ^ $86;
 $96 = $94 & $4;
 $97 = $95 & $5;
 $98 = $96 ^ $83;
 $97 ^ $86;
 $99 = (_bitshift64Ashr(0,($98|0),32)|0);
 $100 = tempRet0;
 $101 = $80;
 $102 = $101;
 HEAP32[$102>>2] = $99;
 $103 = (($101) + 4)|0;
 $104 = $103;
 HEAP32[$104>>2] = $100;
 $105 = $87;
 $106 = $105;
 $107 = HEAP32[$106>>2]|0;
 $108 = (($105) + 4)|0;
 $109 = $108;
 $110 = HEAP32[$109>>2]|0;
 $111 = $107 ^ $96;
 $110 ^ $97;
 $112 = (_bitshift64Ashr(0,($111|0),32)|0);
 $113 = tempRet0;
 $114 = $87;
 $115 = $114;
 HEAP32[$115>>2] = $112;
 $116 = (($114) + 4)|0;
 $117 = $116;
 HEAP32[$117>>2] = $113;
 $118 = ((($0)) + 24|0);
 $119 = $118;
 $120 = $119;
 $121 = HEAP32[$120>>2]|0;
 $122 = (($119) + 4)|0;
 $123 = $122;
 $124 = HEAP32[$123>>2]|0;
 $125 = ((($1)) + 24|0);
 $126 = $125;
 $127 = $126;
 $128 = HEAP32[$127>>2]|0;
 $129 = (($126) + 4)|0;
 $130 = $129;
 $131 = HEAP32[$130>>2]|0;
 $132 = $128 ^ $121;
 $133 = $131 ^ $124;
 $134 = $132 & $4;
 $135 = $133 & $5;
 $136 = $134 ^ $121;
 $135 ^ $124;
 $137 = (_bitshift64Ashr(0,($136|0),32)|0);
 $138 = tempRet0;
 $139 = $118;
 $140 = $139;
 HEAP32[$140>>2] = $137;
 $141 = (($139) + 4)|0;
 $142 = $141;
 HEAP32[$142>>2] = $138;
 $143 = $125;
 $144 = $143;
 $145 = HEAP32[$144>>2]|0;
 $146 = (($143) + 4)|0;
 $147 = $146;
 $148 = HEAP32[$147>>2]|0;
 $149 = $145 ^ $134;
 $148 ^ $135;
 $150 = (_bitshift64Ashr(0,($149|0),32)|0);
 $151 = tempRet0;
 $152 = $125;
 $153 = $152;
 HEAP32[$153>>2] = $150;
 $154 = (($152) + 4)|0;
 $155 = $154;
 HEAP32[$155>>2] = $151;
 $156 = ((($0)) + 32|0);
 $157 = $156;
 $158 = $157;
 $159 = HEAP32[$158>>2]|0;
 $160 = (($157) + 4)|0;
 $161 = $160;
 $162 = HEAP32[$161>>2]|0;
 $163 = ((($1)) + 32|0);
 $164 = $163;
 $165 = $164;
 $166 = HEAP32[$165>>2]|0;
 $167 = (($164) + 4)|0;
 $168 = $167;
 $169 = HEAP32[$168>>2]|0;
 $170 = $166 ^ $159;
 $171 = $169 ^ $162;
 $172 = $170 & $4;
 $173 = $171 & $5;
 $174 = $172 ^ $159;
 $173 ^ $162;
 $175 = (_bitshift64Ashr(0,($174|0),32)|0);
 $176 = tempRet0;
 $177 = $156;
 $178 = $177;
 HEAP32[$178>>2] = $175;
 $179 = (($177) + 4)|0;
 $180 = $179;
 HEAP32[$180>>2] = $176;
 $181 = $163;
 $182 = $181;
 $183 = HEAP32[$182>>2]|0;
 $184 = (($181) + 4)|0;
 $185 = $184;
 $186 = HEAP32[$185>>2]|0;
 $187 = $183 ^ $172;
 $186 ^ $173;
 $188 = (_bitshift64Ashr(0,($187|0),32)|0);
 $189 = tempRet0;
 $190 = $163;
 $191 = $190;
 HEAP32[$191>>2] = $188;
 $192 = (($190) + 4)|0;
 $193 = $192;
 HEAP32[$193>>2] = $189;
 $194 = ((($0)) + 40|0);
 $195 = $194;
 $196 = $195;
 $197 = HEAP32[$196>>2]|0;
 $198 = (($195) + 4)|0;
 $199 = $198;
 $200 = HEAP32[$199>>2]|0;
 $201 = ((($1)) + 40|0);
 $202 = $201;
 $203 = $202;
 $204 = HEAP32[$203>>2]|0;
 $205 = (($202) + 4)|0;
 $206 = $205;
 $207 = HEAP32[$206>>2]|0;
 $208 = $204 ^ $197;
 $209 = $207 ^ $200;
 $210 = $208 & $4;
 $211 = $209 & $5;
 $212 = $210 ^ $197;
 $211 ^ $200;
 $213 = (_bitshift64Ashr(0,($212|0),32)|0);
 $214 = tempRet0;
 $215 = $194;
 $216 = $215;
 HEAP32[$216>>2] = $213;
 $217 = (($215) + 4)|0;
 $218 = $217;
 HEAP32[$218>>2] = $214;
 $219 = $201;
 $220 = $219;
 $221 = HEAP32[$220>>2]|0;
 $222 = (($219) + 4)|0;
 $223 = $222;
 $224 = HEAP32[$223>>2]|0;
 $225 = $221 ^ $210;
 $224 ^ $211;
 $226 = (_bitshift64Ashr(0,($225|0),32)|0);
 $227 = tempRet0;
 $228 = $201;
 $229 = $228;
 HEAP32[$229>>2] = $226;
 $230 = (($228) + 4)|0;
 $231 = $230;
 HEAP32[$231>>2] = $227;
 $232 = ((($0)) + 48|0);
 $233 = $232;
 $234 = $233;
 $235 = HEAP32[$234>>2]|0;
 $236 = (($233) + 4)|0;
 $237 = $236;
 $238 = HEAP32[$237>>2]|0;
 $239 = ((($1)) + 48|0);
 $240 = $239;
 $241 = $240;
 $242 = HEAP32[$241>>2]|0;
 $243 = (($240) + 4)|0;
 $244 = $243;
 $245 = HEAP32[$244>>2]|0;
 $246 = $242 ^ $235;
 $247 = $245 ^ $238;
 $248 = $246 & $4;
 $249 = $247 & $5;
 $250 = $248 ^ $235;
 $249 ^ $238;
 $251 = (_bitshift64Ashr(0,($250|0),32)|0);
 $252 = tempRet0;
 $253 = $232;
 $254 = $253;
 HEAP32[$254>>2] = $251;
 $255 = (($253) + 4)|0;
 $256 = $255;
 HEAP32[$256>>2] = $252;
 $257 = $239;
 $258 = $257;
 $259 = HEAP32[$258>>2]|0;
 $260 = (($257) + 4)|0;
 $261 = $260;
 $262 = HEAP32[$261>>2]|0;
 $263 = $259 ^ $248;
 $262 ^ $249;
 $264 = (_bitshift64Ashr(0,($263|0),32)|0);
 $265 = tempRet0;
 $266 = $239;
 $267 = $266;
 HEAP32[$267>>2] = $264;
 $268 = (($266) + 4)|0;
 $269 = $268;
 HEAP32[$269>>2] = $265;
 $270 = ((($0)) + 56|0);
 $271 = $270;
 $272 = $271;
 $273 = HEAP32[$272>>2]|0;
 $274 = (($271) + 4)|0;
 $275 = $274;
 $276 = HEAP32[$275>>2]|0;
 $277 = ((($1)) + 56|0);
 $278 = $277;
 $279 = $278;
 $280 = HEAP32[$279>>2]|0;
 $281 = (($278) + 4)|0;
 $282 = $281;
 $283 = HEAP32[$282>>2]|0;
 $284 = $280 ^ $273;
 $285 = $283 ^ $276;
 $286 = $284 & $4;
 $287 = $285 & $5;
 $288 = $286 ^ $273;
 $287 ^ $276;
 $289 = (_bitshift64Ashr(0,($288|0),32)|0);
 $290 = tempRet0;
 $291 = $270;
 $292 = $291;
 HEAP32[$292>>2] = $289;
 $293 = (($291) + 4)|0;
 $294 = $293;
 HEAP32[$294>>2] = $290;
 $295 = $277;
 $296 = $295;
 $297 = HEAP32[$296>>2]|0;
 $298 = (($295) + 4)|0;
 $299 = $298;
 $300 = HEAP32[$299>>2]|0;
 $301 = $297 ^ $286;
 $300 ^ $287;
 $302 = (_bitshift64Ashr(0,($301|0),32)|0);
 $303 = tempRet0;
 $304 = $277;
 $305 = $304;
 HEAP32[$305>>2] = $302;
 $306 = (($304) + 4)|0;
 $307 = $306;
 HEAP32[$307>>2] = $303;
 $308 = ((($0)) + 64|0);
 $309 = $308;
 $310 = $309;
 $311 = HEAP32[$310>>2]|0;
 $312 = (($309) + 4)|0;
 $313 = $312;
 $314 = HEAP32[$313>>2]|0;
 $315 = ((($1)) + 64|0);
 $316 = $315;
 $317 = $316;
 $318 = HEAP32[$317>>2]|0;
 $319 = (($316) + 4)|0;
 $320 = $319;
 $321 = HEAP32[$320>>2]|0;
 $322 = $318 ^ $311;
 $323 = $321 ^ $314;
 $324 = $322 & $4;
 $325 = $323 & $5;
 $326 = $324 ^ $311;
 $325 ^ $314;
 $327 = (_bitshift64Ashr(0,($326|0),32)|0);
 $328 = tempRet0;
 $329 = $308;
 $330 = $329;
 HEAP32[$330>>2] = $327;
 $331 = (($329) + 4)|0;
 $332 = $331;
 HEAP32[$332>>2] = $328;
 $333 = $315;
 $334 = $333;
 $335 = HEAP32[$334>>2]|0;
 $336 = (($333) + 4)|0;
 $337 = $336;
 $338 = HEAP32[$337>>2]|0;
 $339 = $335 ^ $324;
 $338 ^ $325;
 $340 = (_bitshift64Ashr(0,($339|0),32)|0);
 $341 = tempRet0;
 $342 = $315;
 $343 = $342;
 HEAP32[$343>>2] = $340;
 $344 = (($342) + 4)|0;
 $345 = $344;
 HEAP32[$345>>2] = $341;
 $346 = ((($0)) + 72|0);
 $347 = $346;
 $348 = $347;
 $349 = HEAP32[$348>>2]|0;
 $350 = (($347) + 4)|0;
 $351 = $350;
 $352 = HEAP32[$351>>2]|0;
 $353 = ((($1)) + 72|0);
 $354 = $353;
 $355 = $354;
 $356 = HEAP32[$355>>2]|0;
 $357 = (($354) + 4)|0;
 $358 = $357;
 $359 = HEAP32[$358>>2]|0;
 $360 = $356 ^ $349;
 $361 = $359 ^ $352;
 $362 = $360 & $4;
 $363 = $361 & $5;
 $364 = $362 ^ $349;
 $363 ^ $352;
 $365 = (_bitshift64Ashr(0,($364|0),32)|0);
 $366 = tempRet0;
 $367 = $346;
 $368 = $367;
 HEAP32[$368>>2] = $365;
 $369 = (($367) + 4)|0;
 $370 = $369;
 HEAP32[$370>>2] = $366;
 $371 = $353;
 $372 = $371;
 $373 = HEAP32[$372>>2]|0;
 $374 = (($371) + 4)|0;
 $375 = $374;
 $376 = HEAP32[$375>>2]|0;
 $377 = $373 ^ $362;
 $376 ^ $363;
 $378 = (_bitshift64Ashr(0,($377|0),32)|0);
 $379 = tempRet0;
 $380 = $353;
 $381 = $380;
 HEAP32[$381>>2] = $378;
 $382 = (($380) + 4)|0;
 $383 = $382;
 HEAP32[$383>>2] = $379;
 return;
}
function _fmonty($0,$1,$2,$3,$4,$5,$6,$7,$8) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 $3 = $3|0;
 $4 = $4|0;
 $5 = $5|0;
 $6 = $6|0;
 $7 = $7|0;
 $8 = $8|0;
 var $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $9 = 0, dest = 0, label = 0, sp = 0, src = 0, stop = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 1232|0;
 $9 = sp + 1144|0;
 $10 = sp + 1064|0;
 $11 = sp + 912|0;
 $12 = sp + 760|0;
 $13 = sp + 608|0;
 $14 = sp + 456|0;
 $15 = sp + 304|0;
 $16 = sp + 152|0;
 $17 = sp;
 dest=$9; src=$4; stop=dest+80|0; do { HEAP32[dest>>2]=HEAP32[src>>2]|0; dest=dest+4|0; src=src+4|0; } while ((dest|0) < (stop|0));
 _fsum($4,$5);
 _fdifference($5,$9);
 dest=$10; src=$6; stop=dest+80|0; do { HEAP32[dest>>2]=HEAP32[src>>2]|0; dest=dest+4|0; src=src+4|0; } while ((dest|0) < (stop|0));
 _fsum($6,$7);
 _fdifference($7,$10);
 _fproduct($14,$6,$5);
 _fproduct($15,$4,$7);
 _freduce_degree($14);
 _freduce_coefficients($14);
 _freduce_degree($15);
 _freduce_coefficients($15);
 dest=$10; src=$14; stop=dest+80|0; do { HEAP32[dest>>2]=HEAP32[src>>2]|0; dest=dest+4|0; src=src+4|0; } while ((dest|0) < (stop|0));
 _fsum($14,$15);
 _fdifference($15,$10);
 _fsquare($17,$14);
 _fsquare($16,$15);
 _fproduct($15,$16,$8);
 _freduce_degree($15);
 _freduce_coefficients($15);
 dest=$2; src=$17; stop=dest+80|0; do { HEAP32[dest>>2]=HEAP32[src>>2]|0; dest=dest+4|0; src=src+4|0; } while ((dest|0) < (stop|0));
 dest=$3; src=$15; stop=dest+80|0; do { HEAP32[dest>>2]=HEAP32[src>>2]|0; dest=dest+4|0; src=src+4|0; } while ((dest|0) < (stop|0));
 _fsquare($12,$4);
 _fsquare($13,$5);
 _fproduct($0,$12,$13);
 _freduce_degree($0);
 _freduce_coefficients($0);
 _fdifference($13,$12);
 $18 = ((($11)) + 80|0);
 dest=$18; stop=dest+72|0; do { HEAP32[dest>>2]=0|0; dest=dest+4|0; } while ((dest|0) < (stop|0));
 _fscalar_product($11,$13);
 _freduce_coefficients($11);
 _fsum($11,$12);
 _fproduct($1,$13,$11);
 _freduce_degree($1);
 _freduce_coefficients($1);
 STACKTOP = sp;return;
}
function _fsum($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0, $113 = 0, $114 = 0, $115 = 0, $116 = 0, $117 = 0;
 var $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0, $133 = 0, $134 = 0, $135 = 0;
 var $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0, $15 = 0, $150 = 0, $151 = 0, $152 = 0, $153 = 0;
 var $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $159 = 0, $16 = 0, $160 = 0, $161 = 0, $162 = 0, $163 = 0, $164 = 0, $165 = 0, $166 = 0, $167 = 0, $168 = 0, $169 = 0, $17 = 0, $170 = 0, $171 = 0;
 var $172 = 0, $173 = 0, $174 = 0, $175 = 0, $176 = 0, $177 = 0, $178 = 0, $179 = 0, $18 = 0, $180 = 0, $181 = 0, $182 = 0, $183 = 0, $184 = 0, $185 = 0, $186 = 0, $187 = 0, $188 = 0, $189 = 0, $19 = 0;
 var $190 = 0, $191 = 0, $192 = 0, $193 = 0, $194 = 0, $195 = 0, $196 = 0, $197 = 0, $198 = 0, $199 = 0, $2 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0;
 var $29 = 0, $3 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $4 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0, $46 = 0;
 var $47 = 0, $48 = 0, $49 = 0, $5 = 0, $50 = 0, $51 = 0, $52 = 0, $53 = 0, $54 = 0, $55 = 0, $56 = 0, $57 = 0, $58 = 0, $59 = 0, $6 = 0, $60 = 0, $61 = 0, $62 = 0, $63 = 0, $64 = 0;
 var $65 = 0, $66 = 0, $67 = 0, $68 = 0, $69 = 0, $7 = 0, $70 = 0, $71 = 0, $72 = 0, $73 = 0, $74 = 0, $75 = 0, $76 = 0, $77 = 0, $78 = 0, $79 = 0, $8 = 0, $80 = 0, $81 = 0, $82 = 0;
 var $83 = 0, $84 = 0, $85 = 0, $86 = 0, $87 = 0, $88 = 0, $89 = 0, $9 = 0, $90 = 0, $91 = 0, $92 = 0, $93 = 0, $94 = 0, $95 = 0, $96 = 0, $97 = 0, $98 = 0, $99 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = $0;
 $3 = $2;
 $4 = HEAP32[$3>>2]|0;
 $5 = (($2) + 4)|0;
 $6 = $5;
 $7 = HEAP32[$6>>2]|0;
 $8 = $1;
 $9 = $8;
 $10 = HEAP32[$9>>2]|0;
 $11 = (($8) + 4)|0;
 $12 = $11;
 $13 = HEAP32[$12>>2]|0;
 $14 = (_i64Add(($10|0),($13|0),($4|0),($7|0))|0);
 $15 = tempRet0;
 $16 = $0;
 $17 = $16;
 HEAP32[$17>>2] = $14;
 $18 = (($16) + 4)|0;
 $19 = $18;
 HEAP32[$19>>2] = $15;
 $20 = ((($0)) + 8|0);
 $21 = $20;
 $22 = $21;
 $23 = HEAP32[$22>>2]|0;
 $24 = (($21) + 4)|0;
 $25 = $24;
 $26 = HEAP32[$25>>2]|0;
 $27 = ((($1)) + 8|0);
 $28 = $27;
 $29 = $28;
 $30 = HEAP32[$29>>2]|0;
 $31 = (($28) + 4)|0;
 $32 = $31;
 $33 = HEAP32[$32>>2]|0;
 $34 = (_i64Add(($30|0),($33|0),($23|0),($26|0))|0);
 $35 = tempRet0;
 $36 = $20;
 $37 = $36;
 HEAP32[$37>>2] = $34;
 $38 = (($36) + 4)|0;
 $39 = $38;
 HEAP32[$39>>2] = $35;
 $40 = ((($0)) + 16|0);
 $41 = $40;
 $42 = $41;
 $43 = HEAP32[$42>>2]|0;
 $44 = (($41) + 4)|0;
 $45 = $44;
 $46 = HEAP32[$45>>2]|0;
 $47 = ((($1)) + 16|0);
 $48 = $47;
 $49 = $48;
 $50 = HEAP32[$49>>2]|0;
 $51 = (($48) + 4)|0;
 $52 = $51;
 $53 = HEAP32[$52>>2]|0;
 $54 = (_i64Add(($50|0),($53|0),($43|0),($46|0))|0);
 $55 = tempRet0;
 $56 = $40;
 $57 = $56;
 HEAP32[$57>>2] = $54;
 $58 = (($56) + 4)|0;
 $59 = $58;
 HEAP32[$59>>2] = $55;
 $60 = ((($0)) + 24|0);
 $61 = $60;
 $62 = $61;
 $63 = HEAP32[$62>>2]|0;
 $64 = (($61) + 4)|0;
 $65 = $64;
 $66 = HEAP32[$65>>2]|0;
 $67 = ((($1)) + 24|0);
 $68 = $67;
 $69 = $68;
 $70 = HEAP32[$69>>2]|0;
 $71 = (($68) + 4)|0;
 $72 = $71;
 $73 = HEAP32[$72>>2]|0;
 $74 = (_i64Add(($70|0),($73|0),($63|0),($66|0))|0);
 $75 = tempRet0;
 $76 = $60;
 $77 = $76;
 HEAP32[$77>>2] = $74;
 $78 = (($76) + 4)|0;
 $79 = $78;
 HEAP32[$79>>2] = $75;
 $80 = ((($0)) + 32|0);
 $81 = $80;
 $82 = $81;
 $83 = HEAP32[$82>>2]|0;
 $84 = (($81) + 4)|0;
 $85 = $84;
 $86 = HEAP32[$85>>2]|0;
 $87 = ((($1)) + 32|0);
 $88 = $87;
 $89 = $88;
 $90 = HEAP32[$89>>2]|0;
 $91 = (($88) + 4)|0;
 $92 = $91;
 $93 = HEAP32[$92>>2]|0;
 $94 = (_i64Add(($90|0),($93|0),($83|0),($86|0))|0);
 $95 = tempRet0;
 $96 = $80;
 $97 = $96;
 HEAP32[$97>>2] = $94;
 $98 = (($96) + 4)|0;
 $99 = $98;
 HEAP32[$99>>2] = $95;
 $100 = ((($0)) + 40|0);
 $101 = $100;
 $102 = $101;
 $103 = HEAP32[$102>>2]|0;
 $104 = (($101) + 4)|0;
 $105 = $104;
 $106 = HEAP32[$105>>2]|0;
 $107 = ((($1)) + 40|0);
 $108 = $107;
 $109 = $108;
 $110 = HEAP32[$109>>2]|0;
 $111 = (($108) + 4)|0;
 $112 = $111;
 $113 = HEAP32[$112>>2]|0;
 $114 = (_i64Add(($110|0),($113|0),($103|0),($106|0))|0);
 $115 = tempRet0;
 $116 = $100;
 $117 = $116;
 HEAP32[$117>>2] = $114;
 $118 = (($116) + 4)|0;
 $119 = $118;
 HEAP32[$119>>2] = $115;
 $120 = ((($0)) + 48|0);
 $121 = $120;
 $122 = $121;
 $123 = HEAP32[$122>>2]|0;
 $124 = (($121) + 4)|0;
 $125 = $124;
 $126 = HEAP32[$125>>2]|0;
 $127 = ((($1)) + 48|0);
 $128 = $127;
 $129 = $128;
 $130 = HEAP32[$129>>2]|0;
 $131 = (($128) + 4)|0;
 $132 = $131;
 $133 = HEAP32[$132>>2]|0;
 $134 = (_i64Add(($130|0),($133|0),($123|0),($126|0))|0);
 $135 = tempRet0;
 $136 = $120;
 $137 = $136;
 HEAP32[$137>>2] = $134;
 $138 = (($136) + 4)|0;
 $139 = $138;
 HEAP32[$139>>2] = $135;
 $140 = ((($0)) + 56|0);
 $141 = $140;
 $142 = $141;
 $143 = HEAP32[$142>>2]|0;
 $144 = (($141) + 4)|0;
 $145 = $144;
 $146 = HEAP32[$145>>2]|0;
 $147 = ((($1)) + 56|0);
 $148 = $147;
 $149 = $148;
 $150 = HEAP32[$149>>2]|0;
 $151 = (($148) + 4)|0;
 $152 = $151;
 $153 = HEAP32[$152>>2]|0;
 $154 = (_i64Add(($150|0),($153|0),($143|0),($146|0))|0);
 $155 = tempRet0;
 $156 = $140;
 $157 = $156;
 HEAP32[$157>>2] = $154;
 $158 = (($156) + 4)|0;
 $159 = $158;
 HEAP32[$159>>2] = $155;
 $160 = ((($0)) + 64|0);
 $161 = $160;
 $162 = $161;
 $163 = HEAP32[$162>>2]|0;
 $164 = (($161) + 4)|0;
 $165 = $164;
 $166 = HEAP32[$165>>2]|0;
 $167 = ((($1)) + 64|0);
 $168 = $167;
 $169 = $168;
 $170 = HEAP32[$169>>2]|0;
 $171 = (($168) + 4)|0;
 $172 = $171;
 $173 = HEAP32[$172>>2]|0;
 $174 = (_i64Add(($170|0),($173|0),($163|0),($166|0))|0);
 $175 = tempRet0;
 $176 = $160;
 $177 = $176;
 HEAP32[$177>>2] = $174;
 $178 = (($176) + 4)|0;
 $179 = $178;
 HEAP32[$179>>2] = $175;
 $180 = ((($0)) + 72|0);
 $181 = $180;
 $182 = $181;
 $183 = HEAP32[$182>>2]|0;
 $184 = (($181) + 4)|0;
 $185 = $184;
 $186 = HEAP32[$185>>2]|0;
 $187 = ((($1)) + 72|0);
 $188 = $187;
 $189 = $188;
 $190 = HEAP32[$189>>2]|0;
 $191 = (($188) + 4)|0;
 $192 = $191;
 $193 = HEAP32[$192>>2]|0;
 $194 = (_i64Add(($190|0),($193|0),($183|0),($186|0))|0);
 $195 = tempRet0;
 $196 = $180;
 $197 = $196;
 HEAP32[$197>>2] = $194;
 $198 = (($196) + 4)|0;
 $199 = $198;
 HEAP32[$199>>2] = $195;
 return;
}
function _fdifference($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0, $113 = 0, $114 = 0, $115 = 0, $116 = 0, $117 = 0;
 var $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0, $133 = 0, $134 = 0, $135 = 0;
 var $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0, $15 = 0, $150 = 0, $151 = 0, $152 = 0, $153 = 0;
 var $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $159 = 0, $16 = 0, $160 = 0, $161 = 0, $162 = 0, $163 = 0, $164 = 0, $165 = 0, $166 = 0, $167 = 0, $168 = 0, $169 = 0, $17 = 0, $170 = 0, $171 = 0;
 var $172 = 0, $173 = 0, $174 = 0, $175 = 0, $176 = 0, $177 = 0, $178 = 0, $179 = 0, $18 = 0, $180 = 0, $181 = 0, $182 = 0, $183 = 0, $184 = 0, $185 = 0, $186 = 0, $187 = 0, $188 = 0, $189 = 0, $19 = 0;
 var $190 = 0, $191 = 0, $192 = 0, $193 = 0, $194 = 0, $195 = 0, $196 = 0, $197 = 0, $198 = 0, $199 = 0, $2 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0;
 var $29 = 0, $3 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $4 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0, $46 = 0;
 var $47 = 0, $48 = 0, $49 = 0, $5 = 0, $50 = 0, $51 = 0, $52 = 0, $53 = 0, $54 = 0, $55 = 0, $56 = 0, $57 = 0, $58 = 0, $59 = 0, $6 = 0, $60 = 0, $61 = 0, $62 = 0, $63 = 0, $64 = 0;
 var $65 = 0, $66 = 0, $67 = 0, $68 = 0, $69 = 0, $7 = 0, $70 = 0, $71 = 0, $72 = 0, $73 = 0, $74 = 0, $75 = 0, $76 = 0, $77 = 0, $78 = 0, $79 = 0, $8 = 0, $80 = 0, $81 = 0, $82 = 0;
 var $83 = 0, $84 = 0, $85 = 0, $86 = 0, $87 = 0, $88 = 0, $89 = 0, $9 = 0, $90 = 0, $91 = 0, $92 = 0, $93 = 0, $94 = 0, $95 = 0, $96 = 0, $97 = 0, $98 = 0, $99 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = $1;
 $3 = $2;
 $4 = HEAP32[$3>>2]|0;
 $5 = (($2) + 4)|0;
 $6 = $5;
 $7 = HEAP32[$6>>2]|0;
 $8 = $0;
 $9 = $8;
 $10 = HEAP32[$9>>2]|0;
 $11 = (($8) + 4)|0;
 $12 = $11;
 $13 = HEAP32[$12>>2]|0;
 $14 = (_i64Subtract(($4|0),($7|0),($10|0),($13|0))|0);
 $15 = tempRet0;
 $16 = $0;
 $17 = $16;
 HEAP32[$17>>2] = $14;
 $18 = (($16) + 4)|0;
 $19 = $18;
 HEAP32[$19>>2] = $15;
 $20 = ((($1)) + 8|0);
 $21 = $20;
 $22 = $21;
 $23 = HEAP32[$22>>2]|0;
 $24 = (($21) + 4)|0;
 $25 = $24;
 $26 = HEAP32[$25>>2]|0;
 $27 = ((($0)) + 8|0);
 $28 = $27;
 $29 = $28;
 $30 = HEAP32[$29>>2]|0;
 $31 = (($28) + 4)|0;
 $32 = $31;
 $33 = HEAP32[$32>>2]|0;
 $34 = (_i64Subtract(($23|0),($26|0),($30|0),($33|0))|0);
 $35 = tempRet0;
 $36 = $27;
 $37 = $36;
 HEAP32[$37>>2] = $34;
 $38 = (($36) + 4)|0;
 $39 = $38;
 HEAP32[$39>>2] = $35;
 $40 = ((($1)) + 16|0);
 $41 = $40;
 $42 = $41;
 $43 = HEAP32[$42>>2]|0;
 $44 = (($41) + 4)|0;
 $45 = $44;
 $46 = HEAP32[$45>>2]|0;
 $47 = ((($0)) + 16|0);
 $48 = $47;
 $49 = $48;
 $50 = HEAP32[$49>>2]|0;
 $51 = (($48) + 4)|0;
 $52 = $51;
 $53 = HEAP32[$52>>2]|0;
 $54 = (_i64Subtract(($43|0),($46|0),($50|0),($53|0))|0);
 $55 = tempRet0;
 $56 = $47;
 $57 = $56;
 HEAP32[$57>>2] = $54;
 $58 = (($56) + 4)|0;
 $59 = $58;
 HEAP32[$59>>2] = $55;
 $60 = ((($1)) + 24|0);
 $61 = $60;
 $62 = $61;
 $63 = HEAP32[$62>>2]|0;
 $64 = (($61) + 4)|0;
 $65 = $64;
 $66 = HEAP32[$65>>2]|0;
 $67 = ((($0)) + 24|0);
 $68 = $67;
 $69 = $68;
 $70 = HEAP32[$69>>2]|0;
 $71 = (($68) + 4)|0;
 $72 = $71;
 $73 = HEAP32[$72>>2]|0;
 $74 = (_i64Subtract(($63|0),($66|0),($70|0),($73|0))|0);
 $75 = tempRet0;
 $76 = $67;
 $77 = $76;
 HEAP32[$77>>2] = $74;
 $78 = (($76) + 4)|0;
 $79 = $78;
 HEAP32[$79>>2] = $75;
 $80 = ((($1)) + 32|0);
 $81 = $80;
 $82 = $81;
 $83 = HEAP32[$82>>2]|0;
 $84 = (($81) + 4)|0;
 $85 = $84;
 $86 = HEAP32[$85>>2]|0;
 $87 = ((($0)) + 32|0);
 $88 = $87;
 $89 = $88;
 $90 = HEAP32[$89>>2]|0;
 $91 = (($88) + 4)|0;
 $92 = $91;
 $93 = HEAP32[$92>>2]|0;
 $94 = (_i64Subtract(($83|0),($86|0),($90|0),($93|0))|0);
 $95 = tempRet0;
 $96 = $87;
 $97 = $96;
 HEAP32[$97>>2] = $94;
 $98 = (($96) + 4)|0;
 $99 = $98;
 HEAP32[$99>>2] = $95;
 $100 = ((($1)) + 40|0);
 $101 = $100;
 $102 = $101;
 $103 = HEAP32[$102>>2]|0;
 $104 = (($101) + 4)|0;
 $105 = $104;
 $106 = HEAP32[$105>>2]|0;
 $107 = ((($0)) + 40|0);
 $108 = $107;
 $109 = $108;
 $110 = HEAP32[$109>>2]|0;
 $111 = (($108) + 4)|0;
 $112 = $111;
 $113 = HEAP32[$112>>2]|0;
 $114 = (_i64Subtract(($103|0),($106|0),($110|0),($113|0))|0);
 $115 = tempRet0;
 $116 = $107;
 $117 = $116;
 HEAP32[$117>>2] = $114;
 $118 = (($116) + 4)|0;
 $119 = $118;
 HEAP32[$119>>2] = $115;
 $120 = ((($1)) + 48|0);
 $121 = $120;
 $122 = $121;
 $123 = HEAP32[$122>>2]|0;
 $124 = (($121) + 4)|0;
 $125 = $124;
 $126 = HEAP32[$125>>2]|0;
 $127 = ((($0)) + 48|0);
 $128 = $127;
 $129 = $128;
 $130 = HEAP32[$129>>2]|0;
 $131 = (($128) + 4)|0;
 $132 = $131;
 $133 = HEAP32[$132>>2]|0;
 $134 = (_i64Subtract(($123|0),($126|0),($130|0),($133|0))|0);
 $135 = tempRet0;
 $136 = $127;
 $137 = $136;
 HEAP32[$137>>2] = $134;
 $138 = (($136) + 4)|0;
 $139 = $138;
 HEAP32[$139>>2] = $135;
 $140 = ((($1)) + 56|0);
 $141 = $140;
 $142 = $141;
 $143 = HEAP32[$142>>2]|0;
 $144 = (($141) + 4)|0;
 $145 = $144;
 $146 = HEAP32[$145>>2]|0;
 $147 = ((($0)) + 56|0);
 $148 = $147;
 $149 = $148;
 $150 = HEAP32[$149>>2]|0;
 $151 = (($148) + 4)|0;
 $152 = $151;
 $153 = HEAP32[$152>>2]|0;
 $154 = (_i64Subtract(($143|0),($146|0),($150|0),($153|0))|0);
 $155 = tempRet0;
 $156 = $147;
 $157 = $156;
 HEAP32[$157>>2] = $154;
 $158 = (($156) + 4)|0;
 $159 = $158;
 HEAP32[$159>>2] = $155;
 $160 = ((($1)) + 64|0);
 $161 = $160;
 $162 = $161;
 $163 = HEAP32[$162>>2]|0;
 $164 = (($161) + 4)|0;
 $165 = $164;
 $166 = HEAP32[$165>>2]|0;
 $167 = ((($0)) + 64|0);
 $168 = $167;
 $169 = $168;
 $170 = HEAP32[$169>>2]|0;
 $171 = (($168) + 4)|0;
 $172 = $171;
 $173 = HEAP32[$172>>2]|0;
 $174 = (_i64Subtract(($163|0),($166|0),($170|0),($173|0))|0);
 $175 = tempRet0;
 $176 = $167;
 $177 = $176;
 HEAP32[$177>>2] = $174;
 $178 = (($176) + 4)|0;
 $179 = $178;
 HEAP32[$179>>2] = $175;
 $180 = ((($1)) + 72|0);
 $181 = $180;
 $182 = $181;
 $183 = HEAP32[$182>>2]|0;
 $184 = (($181) + 4)|0;
 $185 = $184;
 $186 = HEAP32[$185>>2]|0;
 $187 = ((($0)) + 72|0);
 $188 = $187;
 $189 = $188;
 $190 = HEAP32[$189>>2]|0;
 $191 = (($188) + 4)|0;
 $192 = $191;
 $193 = HEAP32[$192>>2]|0;
 $194 = (_i64Subtract(($183|0),($186|0),($190|0),($193|0))|0);
 $195 = tempRet0;
 $196 = $187;
 $197 = $196;
 HEAP32[$197>>2] = $194;
 $198 = (($196) + 4)|0;
 $199 = $198;
 HEAP32[$199>>2] = $195;
 return;
}
function _fscalar_product($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0, $113 = 0, $114 = 0, $115 = 0, $116 = 0, $117 = 0;
 var $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0, $133 = 0, $134 = 0, $135 = 0;
 var $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $2 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0;
 var $29 = 0, $3 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $4 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0, $46 = 0;
 var $47 = 0, $48 = 0, $49 = 0, $5 = 0, $50 = 0, $51 = 0, $52 = 0, $53 = 0, $54 = 0, $55 = 0, $56 = 0, $57 = 0, $58 = 0, $59 = 0, $6 = 0, $60 = 0, $61 = 0, $62 = 0, $63 = 0, $64 = 0;
 var $65 = 0, $66 = 0, $67 = 0, $68 = 0, $69 = 0, $7 = 0, $70 = 0, $71 = 0, $72 = 0, $73 = 0, $74 = 0, $75 = 0, $76 = 0, $77 = 0, $78 = 0, $79 = 0, $8 = 0, $80 = 0, $81 = 0, $82 = 0;
 var $83 = 0, $84 = 0, $85 = 0, $86 = 0, $87 = 0, $88 = 0, $89 = 0, $9 = 0, $90 = 0, $91 = 0, $92 = 0, $93 = 0, $94 = 0, $95 = 0, $96 = 0, $97 = 0, $98 = 0, $99 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = $1;
 $3 = $2;
 $4 = HEAP32[$3>>2]|0;
 $5 = (($2) + 4)|0;
 $6 = $5;
 $7 = HEAP32[$6>>2]|0;
 $8 = (___muldi3(($4|0),($7|0),121665,0)|0);
 $9 = tempRet0;
 $10 = $0;
 $11 = $10;
 HEAP32[$11>>2] = $8;
 $12 = (($10) + 4)|0;
 $13 = $12;
 HEAP32[$13>>2] = $9;
 $14 = ((($1)) + 8|0);
 $15 = $14;
 $16 = $15;
 $17 = HEAP32[$16>>2]|0;
 $18 = (($15) + 4)|0;
 $19 = $18;
 $20 = HEAP32[$19>>2]|0;
 $21 = (___muldi3(($17|0),($20|0),121665,0)|0);
 $22 = tempRet0;
 $23 = ((($0)) + 8|0);
 $24 = $23;
 $25 = $24;
 HEAP32[$25>>2] = $21;
 $26 = (($24) + 4)|0;
 $27 = $26;
 HEAP32[$27>>2] = $22;
 $28 = ((($1)) + 16|0);
 $29 = $28;
 $30 = $29;
 $31 = HEAP32[$30>>2]|0;
 $32 = (($29) + 4)|0;
 $33 = $32;
 $34 = HEAP32[$33>>2]|0;
 $35 = (___muldi3(($31|0),($34|0),121665,0)|0);
 $36 = tempRet0;
 $37 = ((($0)) + 16|0);
 $38 = $37;
 $39 = $38;
 HEAP32[$39>>2] = $35;
 $40 = (($38) + 4)|0;
 $41 = $40;
 HEAP32[$41>>2] = $36;
 $42 = ((($1)) + 24|0);
 $43 = $42;
 $44 = $43;
 $45 = HEAP32[$44>>2]|0;
 $46 = (($43) + 4)|0;
 $47 = $46;
 $48 = HEAP32[$47>>2]|0;
 $49 = (___muldi3(($45|0),($48|0),121665,0)|0);
 $50 = tempRet0;
 $51 = ((($0)) + 24|0);
 $52 = $51;
 $53 = $52;
 HEAP32[$53>>2] = $49;
 $54 = (($52) + 4)|0;
 $55 = $54;
 HEAP32[$55>>2] = $50;
 $56 = ((($1)) + 32|0);
 $57 = $56;
 $58 = $57;
 $59 = HEAP32[$58>>2]|0;
 $60 = (($57) + 4)|0;
 $61 = $60;
 $62 = HEAP32[$61>>2]|0;
 $63 = (___muldi3(($59|0),($62|0),121665,0)|0);
 $64 = tempRet0;
 $65 = ((($0)) + 32|0);
 $66 = $65;
 $67 = $66;
 HEAP32[$67>>2] = $63;
 $68 = (($66) + 4)|0;
 $69 = $68;
 HEAP32[$69>>2] = $64;
 $70 = ((($1)) + 40|0);
 $71 = $70;
 $72 = $71;
 $73 = HEAP32[$72>>2]|0;
 $74 = (($71) + 4)|0;
 $75 = $74;
 $76 = HEAP32[$75>>2]|0;
 $77 = (___muldi3(($73|0),($76|0),121665,0)|0);
 $78 = tempRet0;
 $79 = ((($0)) + 40|0);
 $80 = $79;
 $81 = $80;
 HEAP32[$81>>2] = $77;
 $82 = (($80) + 4)|0;
 $83 = $82;
 HEAP32[$83>>2] = $78;
 $84 = ((($1)) + 48|0);
 $85 = $84;
 $86 = $85;
 $87 = HEAP32[$86>>2]|0;
 $88 = (($85) + 4)|0;
 $89 = $88;
 $90 = HEAP32[$89>>2]|0;
 $91 = (___muldi3(($87|0),($90|0),121665,0)|0);
 $92 = tempRet0;
 $93 = ((($0)) + 48|0);
 $94 = $93;
 $95 = $94;
 HEAP32[$95>>2] = $91;
 $96 = (($94) + 4)|0;
 $97 = $96;
 HEAP32[$97>>2] = $92;
 $98 = ((($1)) + 56|0);
 $99 = $98;
 $100 = $99;
 $101 = HEAP32[$100>>2]|0;
 $102 = (($99) + 4)|0;
 $103 = $102;
 $104 = HEAP32[$103>>2]|0;
 $105 = (___muldi3(($101|0),($104|0),121665,0)|0);
 $106 = tempRet0;
 $107 = ((($0)) + 56|0);
 $108 = $107;
 $109 = $108;
 HEAP32[$109>>2] = $105;
 $110 = (($108) + 4)|0;
 $111 = $110;
 HEAP32[$111>>2] = $106;
 $112 = ((($1)) + 64|0);
 $113 = $112;
 $114 = $113;
 $115 = HEAP32[$114>>2]|0;
 $116 = (($113) + 4)|0;
 $117 = $116;
 $118 = HEAP32[$117>>2]|0;
 $119 = (___muldi3(($115|0),($118|0),121665,0)|0);
 $120 = tempRet0;
 $121 = ((($0)) + 64|0);
 $122 = $121;
 $123 = $122;
 HEAP32[$123>>2] = $119;
 $124 = (($122) + 4)|0;
 $125 = $124;
 HEAP32[$125>>2] = $120;
 $126 = ((($1)) + 72|0);
 $127 = $126;
 $128 = $127;
 $129 = HEAP32[$128>>2]|0;
 $130 = (($127) + 4)|0;
 $131 = $130;
 $132 = HEAP32[$131>>2]|0;
 $133 = (___muldi3(($129|0),($132|0),121665,0)|0);
 $134 = tempRet0;
 $135 = ((($0)) + 72|0);
 $136 = $135;
 $137 = $136;
 HEAP32[$137>>2] = $133;
 $138 = (($136) + 4)|0;
 $139 = $138;
 HEAP32[$139>>2] = $134;
 return;
}
function _crypto_sign_ed25519_ref10_fe_0($0) {
 $0 = $0|0;
 var dest = 0, label = 0, sp = 0, stop = 0;
 sp = STACKTOP;
 dest=$0; stop=dest+40|0; do { HEAP32[dest>>2]=0|0; dest=dest+4|0; } while ((dest|0) < (stop|0));
 return;
}
function _crypto_sign_ed25519_ref10_fe_1($0) {
 $0 = $0|0;
 var $1 = 0, dest = 0, label = 0, sp = 0, stop = 0;
 sp = STACKTOP;
 HEAP32[$0>>2] = 1;
 $1 = ((($0)) + 4|0);
 dest=$1; stop=dest+36|0; do { HEAP32[dest>>2]=0|0; dest=dest+4|0; } while ((dest|0) < (stop|0));
 return;
}
function _crypto_sign_ed25519_ref10_fe_add($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0, $29 = 0;
 var $3 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $4 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0, $46 = 0, $47 = 0;
 var $48 = 0, $49 = 0, $5 = 0, $50 = 0, $51 = 0, $52 = 0, $53 = 0, $54 = 0, $55 = 0, $56 = 0, $57 = 0, $58 = 0, $59 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $3 = HEAP32[$1>>2]|0;
 $4 = ((($1)) + 4|0);
 $5 = HEAP32[$4>>2]|0;
 $6 = ((($1)) + 8|0);
 $7 = HEAP32[$6>>2]|0;
 $8 = ((($1)) + 12|0);
 $9 = HEAP32[$8>>2]|0;
 $10 = ((($1)) + 16|0);
 $11 = HEAP32[$10>>2]|0;
 $12 = ((($1)) + 20|0);
 $13 = HEAP32[$12>>2]|0;
 $14 = ((($1)) + 24|0);
 $15 = HEAP32[$14>>2]|0;
 $16 = ((($1)) + 28|0);
 $17 = HEAP32[$16>>2]|0;
 $18 = ((($1)) + 32|0);
 $19 = HEAP32[$18>>2]|0;
 $20 = ((($1)) + 36|0);
 $21 = HEAP32[$20>>2]|0;
 $22 = HEAP32[$2>>2]|0;
 $23 = ((($2)) + 4|0);
 $24 = HEAP32[$23>>2]|0;
 $25 = ((($2)) + 8|0);
 $26 = HEAP32[$25>>2]|0;
 $27 = ((($2)) + 12|0);
 $28 = HEAP32[$27>>2]|0;
 $29 = ((($2)) + 16|0);
 $30 = HEAP32[$29>>2]|0;
 $31 = ((($2)) + 20|0);
 $32 = HEAP32[$31>>2]|0;
 $33 = ((($2)) + 24|0);
 $34 = HEAP32[$33>>2]|0;
 $35 = ((($2)) + 28|0);
 $36 = HEAP32[$35>>2]|0;
 $37 = ((($2)) + 32|0);
 $38 = HEAP32[$37>>2]|0;
 $39 = ((($2)) + 36|0);
 $40 = HEAP32[$39>>2]|0;
 $41 = (($22) + ($3))|0;
 $42 = (($24) + ($5))|0;
 $43 = (($26) + ($7))|0;
 $44 = (($28) + ($9))|0;
 $45 = (($30) + ($11))|0;
 $46 = (($32) + ($13))|0;
 $47 = (($34) + ($15))|0;
 $48 = (($36) + ($17))|0;
 $49 = (($38) + ($19))|0;
 $50 = (($40) + ($21))|0;
 HEAP32[$0>>2] = $41;
 $51 = ((($0)) + 4|0);
 HEAP32[$51>>2] = $42;
 $52 = ((($0)) + 8|0);
 HEAP32[$52>>2] = $43;
 $53 = ((($0)) + 12|0);
 HEAP32[$53>>2] = $44;
 $54 = ((($0)) + 16|0);
 HEAP32[$54>>2] = $45;
 $55 = ((($0)) + 20|0);
 HEAP32[$55>>2] = $46;
 $56 = ((($0)) + 24|0);
 HEAP32[$56>>2] = $47;
 $57 = ((($0)) + 28|0);
 HEAP32[$57>>2] = $48;
 $58 = ((($0)) + 32|0);
 HEAP32[$58>>2] = $49;
 $59 = ((($0)) + 36|0);
 HEAP32[$59>>2] = $50;
 return;
}
function _crypto_sign_ed25519_ref10_fe_cmov($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0, $29 = 0;
 var $3 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $4 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0, $46 = 0, $47 = 0;
 var $48 = 0, $49 = 0, $5 = 0, $50 = 0, $51 = 0, $52 = 0, $53 = 0, $54 = 0, $55 = 0, $56 = 0, $57 = 0, $58 = 0, $59 = 0, $6 = 0, $60 = 0, $61 = 0, $62 = 0, $63 = 0, $64 = 0, $65 = 0;
 var $66 = 0, $67 = 0, $68 = 0, $69 = 0, $7 = 0, $70 = 0, $71 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $3 = HEAP32[$0>>2]|0;
 $4 = ((($0)) + 4|0);
 $5 = HEAP32[$4>>2]|0;
 $6 = ((($0)) + 8|0);
 $7 = HEAP32[$6>>2]|0;
 $8 = ((($0)) + 12|0);
 $9 = HEAP32[$8>>2]|0;
 $10 = ((($0)) + 16|0);
 $11 = HEAP32[$10>>2]|0;
 $12 = ((($0)) + 20|0);
 $13 = HEAP32[$12>>2]|0;
 $14 = ((($0)) + 24|0);
 $15 = HEAP32[$14>>2]|0;
 $16 = ((($0)) + 28|0);
 $17 = HEAP32[$16>>2]|0;
 $18 = ((($0)) + 32|0);
 $19 = HEAP32[$18>>2]|0;
 $20 = ((($0)) + 36|0);
 $21 = HEAP32[$20>>2]|0;
 $22 = HEAP32[$1>>2]|0;
 $23 = ((($1)) + 4|0);
 $24 = HEAP32[$23>>2]|0;
 $25 = ((($1)) + 8|0);
 $26 = HEAP32[$25>>2]|0;
 $27 = ((($1)) + 12|0);
 $28 = HEAP32[$27>>2]|0;
 $29 = ((($1)) + 16|0);
 $30 = HEAP32[$29>>2]|0;
 $31 = ((($1)) + 20|0);
 $32 = HEAP32[$31>>2]|0;
 $33 = ((($1)) + 24|0);
 $34 = HEAP32[$33>>2]|0;
 $35 = ((($1)) + 28|0);
 $36 = HEAP32[$35>>2]|0;
 $37 = ((($1)) + 32|0);
 $38 = HEAP32[$37>>2]|0;
 $39 = ((($1)) + 36|0);
 $40 = HEAP32[$39>>2]|0;
 $41 = $22 ^ $3;
 $42 = $24 ^ $5;
 $43 = $26 ^ $7;
 $44 = $28 ^ $9;
 $45 = $30 ^ $11;
 $46 = $32 ^ $13;
 $47 = $34 ^ $15;
 $48 = $36 ^ $17;
 $49 = $38 ^ $19;
 $50 = $40 ^ $21;
 $51 = (0 - ($2))|0;
 $52 = $41 & $51;
 $53 = $42 & $51;
 $54 = $43 & $51;
 $55 = $44 & $51;
 $56 = $45 & $51;
 $57 = $46 & $51;
 $58 = $47 & $51;
 $59 = $48 & $51;
 $60 = $49 & $51;
 $61 = $50 & $51;
 $62 = $52 ^ $3;
 HEAP32[$0>>2] = $62;
 $63 = $53 ^ $5;
 HEAP32[$4>>2] = $63;
 $64 = $54 ^ $7;
 HEAP32[$6>>2] = $64;
 $65 = $55 ^ $9;
 HEAP32[$8>>2] = $65;
 $66 = $56 ^ $11;
 HEAP32[$10>>2] = $66;
 $67 = $57 ^ $13;
 HEAP32[$12>>2] = $67;
 $68 = $58 ^ $15;
 HEAP32[$14>>2] = $68;
 $69 = $59 ^ $17;
 HEAP32[$16>>2] = $69;
 $70 = $60 ^ $19;
 HEAP32[$18>>2] = $70;
 $71 = $61 ^ $21;
 HEAP32[$20>>2] = $71;
 return;
}
function _crypto_sign_ed25519_ref10_fe_copy($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $2 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0;
 var $29 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = HEAP32[$1>>2]|0;
 $3 = ((($1)) + 4|0);
 $4 = HEAP32[$3>>2]|0;
 $5 = ((($1)) + 8|0);
 $6 = HEAP32[$5>>2]|0;
 $7 = ((($1)) + 12|0);
 $8 = HEAP32[$7>>2]|0;
 $9 = ((($1)) + 16|0);
 $10 = HEAP32[$9>>2]|0;
 $11 = ((($1)) + 20|0);
 $12 = HEAP32[$11>>2]|0;
 $13 = ((($1)) + 24|0);
 $14 = HEAP32[$13>>2]|0;
 $15 = ((($1)) + 28|0);
 $16 = HEAP32[$15>>2]|0;
 $17 = ((($1)) + 32|0);
 $18 = HEAP32[$17>>2]|0;
 $19 = ((($1)) + 36|0);
 $20 = HEAP32[$19>>2]|0;
 HEAP32[$0>>2] = $2;
 $21 = ((($0)) + 4|0);
 HEAP32[$21>>2] = $4;
 $22 = ((($0)) + 8|0);
 HEAP32[$22>>2] = $6;
 $23 = ((($0)) + 12|0);
 HEAP32[$23>>2] = $8;
 $24 = ((($0)) + 16|0);
 HEAP32[$24>>2] = $10;
 $25 = ((($0)) + 20|0);
 HEAP32[$25>>2] = $12;
 $26 = ((($0)) + 24|0);
 HEAP32[$26>>2] = $14;
 $27 = ((($0)) + 28|0);
 HEAP32[$27>>2] = $16;
 $28 = ((($0)) + 32|0);
 HEAP32[$28>>2] = $18;
 $29 = ((($0)) + 36|0);
 HEAP32[$29>>2] = $20;
 return;
}
function _crypto_sign_ed25519_ref10_fe_frombytes($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0, $113 = 0, $114 = 0, $115 = 0, $116 = 0, $117 = 0;
 var $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0, $133 = 0, $134 = 0, $135 = 0;
 var $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0, $15 = 0, $150 = 0, $151 = 0, $152 = 0, $153 = 0;
 var $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $2 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0, $29 = 0;
 var $3 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $4 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0, $46 = 0, $47 = 0;
 var $48 = 0, $49 = 0, $5 = 0, $50 = 0, $51 = 0, $52 = 0, $53 = 0, $54 = 0, $55 = 0, $56 = 0, $57 = 0, $58 = 0, $59 = 0, $6 = 0, $60 = 0, $61 = 0, $62 = 0, $63 = 0, $64 = 0, $65 = 0;
 var $66 = 0, $67 = 0, $68 = 0, $69 = 0, $7 = 0, $70 = 0, $71 = 0, $72 = 0, $73 = 0, $74 = 0, $75 = 0, $76 = 0, $77 = 0, $78 = 0, $79 = 0, $8 = 0, $80 = 0, $81 = 0, $82 = 0, $83 = 0;
 var $84 = 0, $85 = 0, $86 = 0, $87 = 0, $88 = 0, $89 = 0, $9 = 0, $90 = 0, $91 = 0, $92 = 0, $93 = 0, $94 = 0, $95 = 0, $96 = 0, $97 = 0, $98 = 0, $99 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = (_load_4($1)|0);
 $3 = tempRet0;
 $4 = ((($1)) + 4|0);
 $5 = (_load_3($4)|0);
 $6 = tempRet0;
 $7 = (_bitshift64Shl(($5|0),($6|0),6)|0);
 $8 = tempRet0;
 $9 = ((($1)) + 7|0);
 $10 = (_load_3($9)|0);
 $11 = tempRet0;
 $12 = (_bitshift64Shl(($10|0),($11|0),5)|0);
 $13 = tempRet0;
 $14 = ((($1)) + 10|0);
 $15 = (_load_3($14)|0);
 $16 = tempRet0;
 $17 = (_bitshift64Shl(($15|0),($16|0),3)|0);
 $18 = tempRet0;
 $19 = ((($1)) + 13|0);
 $20 = (_load_3($19)|0);
 $21 = tempRet0;
 $22 = (_bitshift64Shl(($20|0),($21|0),2)|0);
 $23 = tempRet0;
 $24 = ((($1)) + 16|0);
 $25 = (_load_4($24)|0);
 $26 = tempRet0;
 $27 = ((($1)) + 20|0);
 $28 = (_load_3($27)|0);
 $29 = tempRet0;
 $30 = (_bitshift64Shl(($28|0),($29|0),7)|0);
 $31 = tempRet0;
 $32 = ((($1)) + 23|0);
 $33 = (_load_3($32)|0);
 $34 = tempRet0;
 $35 = (_bitshift64Shl(($33|0),($34|0),5)|0);
 $36 = tempRet0;
 $37 = ((($1)) + 26|0);
 $38 = (_load_3($37)|0);
 $39 = tempRet0;
 $40 = (_bitshift64Shl(($38|0),($39|0),4)|0);
 $41 = tempRet0;
 $42 = ((($1)) + 29|0);
 $43 = (_load_3($42)|0);
 $44 = tempRet0;
 $45 = (_bitshift64Shl(($43|0),($44|0),2)|0);
 $46 = tempRet0;
 $47 = $45 & 33554428;
 $48 = (_i64Add(($47|0),0,16777216,0)|0);
 $49 = tempRet0;
 $50 = (_bitshift64Lshr(($48|0),($49|0),25)|0);
 $51 = tempRet0;
 $52 = (_i64Subtract(0,0,($50|0),($51|0))|0);
 $53 = tempRet0;
 $54 = $52 & 19;
 $55 = (_i64Add(($54|0),0,($2|0),($3|0))|0);
 $56 = tempRet0;
 $57 = $48 & 33554432;
 $58 = (_i64Subtract(($47|0),0,($57|0),0)|0);
 $59 = tempRet0;
 $60 = (_i64Add(($7|0),($8|0),16777216,0)|0);
 $61 = tempRet0;
 $62 = (_bitshift64Ashr(($60|0),($61|0),25)|0);
 $63 = tempRet0;
 $64 = (_i64Add(($62|0),($63|0),($12|0),($13|0))|0);
 $65 = tempRet0;
 $66 = (_bitshift64Shl(($62|0),($63|0),25)|0);
 $67 = tempRet0;
 $68 = (_i64Subtract(($7|0),($8|0),($66|0),($67|0))|0);
 $69 = tempRet0;
 $70 = (_i64Add(($17|0),($18|0),16777216,0)|0);
 $71 = tempRet0;
 $72 = (_bitshift64Ashr(($70|0),($71|0),25)|0);
 $73 = tempRet0;
 $74 = (_i64Add(($72|0),($73|0),($22|0),($23|0))|0);
 $75 = tempRet0;
 $76 = (_bitshift64Shl(($72|0),($73|0),25)|0);
 $77 = tempRet0;
 $78 = (_i64Subtract(($17|0),($18|0),($76|0),($77|0))|0);
 $79 = tempRet0;
 $80 = (_i64Add(($25|0),($26|0),16777216,0)|0);
 $81 = tempRet0;
 $82 = (_bitshift64Ashr(($80|0),($81|0),25)|0);
 $83 = tempRet0;
 $84 = (_i64Add(($30|0),($31|0),($82|0),($83|0))|0);
 $85 = tempRet0;
 $86 = (_bitshift64Shl(($82|0),($83|0),25)|0);
 $87 = tempRet0;
 $88 = (_i64Subtract(($25|0),($26|0),($86|0),($87|0))|0);
 $89 = tempRet0;
 $90 = (_i64Add(($35|0),($36|0),16777216,0)|0);
 $91 = tempRet0;
 $92 = (_bitshift64Ashr(($90|0),($91|0),25)|0);
 $93 = tempRet0;
 $94 = (_i64Add(($92|0),($93|0),($40|0),($41|0))|0);
 $95 = tempRet0;
 $96 = (_bitshift64Shl(($92|0),($93|0),25)|0);
 $97 = tempRet0;
 $98 = (_i64Add(($55|0),($56|0),33554432,0)|0);
 $99 = tempRet0;
 $100 = (_bitshift64Ashr(($98|0),($99|0),26)|0);
 $101 = tempRet0;
 $102 = (_i64Add(($68|0),($69|0),($100|0),($101|0))|0);
 $103 = tempRet0;
 $104 = (_bitshift64Shl(($100|0),($101|0),26)|0);
 $105 = tempRet0;
 $106 = (_i64Subtract(($55|0),($56|0),($104|0),($105|0))|0);
 $107 = tempRet0;
 $108 = (_i64Add(($64|0),($65|0),33554432,0)|0);
 $109 = tempRet0;
 $110 = (_bitshift64Ashr(($108|0),($109|0),26)|0);
 $111 = tempRet0;
 $112 = (_i64Add(($78|0),($79|0),($110|0),($111|0))|0);
 $113 = tempRet0;
 $114 = (_bitshift64Shl(($110|0),($111|0),26)|0);
 $115 = tempRet0;
 $116 = (_i64Subtract(($64|0),($65|0),($114|0),($115|0))|0);
 $117 = tempRet0;
 $118 = (_i64Add(($74|0),($75|0),33554432,0)|0);
 $119 = tempRet0;
 $120 = (_bitshift64Ashr(($118|0),($119|0),26)|0);
 $121 = tempRet0;
 $122 = (_i64Add(($88|0),($89|0),($120|0),($121|0))|0);
 $123 = tempRet0;
 $124 = (_bitshift64Shl(($120|0),($121|0),26)|0);
 $125 = tempRet0;
 $126 = (_i64Subtract(($74|0),($75|0),($124|0),($125|0))|0);
 $127 = tempRet0;
 $128 = (_i64Add(($84|0),($85|0),33554432,0)|0);
 $129 = tempRet0;
 $130 = (_bitshift64Ashr(($128|0),($129|0),26)|0);
 $131 = tempRet0;
 $132 = (_i64Add(($130|0),($131|0),($35|0),($36|0))|0);
 $133 = tempRet0;
 $134 = (_i64Subtract(($132|0),($133|0),($96|0),($97|0))|0);
 $135 = tempRet0;
 $136 = (_bitshift64Shl(($130|0),($131|0),26)|0);
 $137 = tempRet0;
 $138 = (_i64Subtract(($84|0),($85|0),($136|0),($137|0))|0);
 $139 = tempRet0;
 $140 = (_i64Add(($94|0),($95|0),33554432,0)|0);
 $141 = tempRet0;
 $142 = (_bitshift64Ashr(($140|0),($141|0),26)|0);
 $143 = tempRet0;
 $144 = (_i64Add(($58|0),($59|0),($142|0),($143|0))|0);
 $145 = tempRet0;
 $146 = (_bitshift64Shl(($142|0),($143|0),26)|0);
 $147 = tempRet0;
 $148 = (_i64Subtract(($94|0),($95|0),($146|0),($147|0))|0);
 $149 = tempRet0;
 HEAP32[$0>>2] = $106;
 $150 = ((($0)) + 4|0);
 HEAP32[$150>>2] = $102;
 $151 = ((($0)) + 8|0);
 HEAP32[$151>>2] = $116;
 $152 = ((($0)) + 12|0);
 HEAP32[$152>>2] = $112;
 $153 = ((($0)) + 16|0);
 HEAP32[$153>>2] = $126;
 $154 = ((($0)) + 20|0);
 HEAP32[$154>>2] = $122;
 $155 = ((($0)) + 24|0);
 HEAP32[$155>>2] = $138;
 $156 = ((($0)) + 28|0);
 HEAP32[$156>>2] = $134;
 $157 = ((($0)) + 32|0);
 HEAP32[$157>>2] = $148;
 $158 = ((($0)) + 36|0);
 HEAP32[$158>>2] = $144;
 return;
}
function _load_4($0) {
 $0 = $0|0;
 var $1 = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $2 = 0, $20 = 0, $21 = 0, $22 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0;
 var $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $1 = HEAP8[$0>>0]|0;
 $2 = $1&255;
 $3 = ((($0)) + 1|0);
 $4 = HEAP8[$3>>0]|0;
 $5 = $4&255;
 $6 = (_bitshift64Shl(($5|0),0,8)|0);
 $7 = tempRet0;
 $8 = $6 | $2;
 $9 = ((($0)) + 2|0);
 $10 = HEAP8[$9>>0]|0;
 $11 = $10&255;
 $12 = (_bitshift64Shl(($11|0),0,16)|0);
 $13 = tempRet0;
 $14 = $8 | $12;
 $15 = $7 | $13;
 $16 = ((($0)) + 3|0);
 $17 = HEAP8[$16>>0]|0;
 $18 = $17&255;
 $19 = (_bitshift64Shl(($18|0),0,24)|0);
 $20 = tempRet0;
 $21 = $14 | $19;
 $22 = $15 | $20;
 tempRet0 = ($22);
 return ($21|0);
}
function _load_3($0) {
 $0 = $0|0;
 var $1 = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $1 = HEAP8[$0>>0]|0;
 $2 = $1&255;
 $3 = ((($0)) + 1|0);
 $4 = HEAP8[$3>>0]|0;
 $5 = $4&255;
 $6 = (_bitshift64Shl(($5|0),0,8)|0);
 $7 = tempRet0;
 $8 = $6 | $2;
 $9 = ((($0)) + 2|0);
 $10 = HEAP8[$9>>0]|0;
 $11 = $10&255;
 $12 = (_bitshift64Shl(($11|0),0,16)|0);
 $13 = tempRet0;
 $14 = $8 | $12;
 $15 = $7 | $13;
 tempRet0 = ($15);
 return ($14|0);
}
function _crypto_sign_ed25519_ref10_fe_invert($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $$728 = 0, $$827 = 0, $$926 = 0, $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $exitcond = 0, $exitcond34 = 0, $exitcond35 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 160|0;
 $2 = sp + 120|0;
 $3 = sp + 80|0;
 $4 = sp + 40|0;
 $5 = sp;
 _crypto_sign_ed25519_ref10_fe_sq($2,$1);
 _crypto_sign_ed25519_ref10_fe_sq($3,$2);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_mul($3,$1,$3);
 _crypto_sign_ed25519_ref10_fe_mul($2,$2,$3);
 _crypto_sign_ed25519_ref10_fe_sq($4,$2);
 _crypto_sign_ed25519_ref10_fe_mul($3,$3,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$3);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_mul($3,$4,$3);
 _crypto_sign_ed25519_ref10_fe_sq($4,$3);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_mul($4,$4,$3);
 _crypto_sign_ed25519_ref10_fe_sq($5,$4);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_sq($5,$5);
 _crypto_sign_ed25519_ref10_fe_mul($4,$5,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_mul($3,$4,$3);
 _crypto_sign_ed25519_ref10_fe_sq($4,$3);
 $$728 = 1;
 while(1) {
  _crypto_sign_ed25519_ref10_fe_sq($4,$4);
  $6 = (($$728) + 1)|0;
  $exitcond35 = ($6|0)==(50);
  if ($exitcond35) {
   break;
  } else {
   $$728 = $6;
  }
 }
 _crypto_sign_ed25519_ref10_fe_mul($4,$4,$3);
 _crypto_sign_ed25519_ref10_fe_sq($5,$4);
 $$827 = 1;
 while(1) {
  _crypto_sign_ed25519_ref10_fe_sq($5,$5);
  $7 = (($$827) + 1)|0;
  $exitcond34 = ($7|0)==(100);
  if ($exitcond34) {
   break;
  } else {
   $$827 = $7;
  }
 }
 _crypto_sign_ed25519_ref10_fe_mul($4,$5,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 $$926 = 1;
 while(1) {
  _crypto_sign_ed25519_ref10_fe_sq($4,$4);
  $8 = (($$926) + 1)|0;
  $exitcond = ($8|0)==(50);
  if ($exitcond) {
   break;
  } else {
   $$926 = $8;
  }
 }
 _crypto_sign_ed25519_ref10_fe_mul($3,$4,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_mul($0,$3,$2);
 STACKTOP = sp;return;
}
function _crypto_sign_ed25519_ref10_fe_isnegative($0) {
 $0 = $0|0;
 var $1 = 0, $2 = 0, $3 = 0, $4 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 32|0;
 $1 = sp;
 _crypto_sign_ed25519_ref10_fe_tobytes($1,$0);
 $2 = HEAP8[$1>>0]|0;
 $3 = $2 & 1;
 $4 = $3&255;
 STACKTOP = sp;return ($4|0);
}
function _crypto_sign_ed25519_ref10_fe_isnonzero($0) {
 $0 = $0|0;
 var $1 = 0, $2 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 32|0;
 $1 = sp;
 _crypto_sign_ed25519_ref10_fe_tobytes($1,$0);
 $2 = (_crypto_verify_32_ref($1,33012)|0);
 STACKTOP = sp;return ($2|0);
}
function _crypto_sign_ed25519_ref10_fe_mul($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0, $113 = 0, $114 = 0, $115 = 0, $116 = 0, $117 = 0;
 var $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0, $133 = 0, $134 = 0, $135 = 0;
 var $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0, $15 = 0, $150 = 0, $151 = 0, $152 = 0, $153 = 0;
 var $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $159 = 0, $16 = 0, $160 = 0, $161 = 0, $162 = 0, $163 = 0, $164 = 0, $165 = 0, $166 = 0, $167 = 0, $168 = 0, $169 = 0, $17 = 0, $170 = 0, $171 = 0;
 var $172 = 0, $173 = 0, $174 = 0, $175 = 0, $176 = 0, $177 = 0, $178 = 0, $179 = 0, $18 = 0, $180 = 0, $181 = 0, $182 = 0, $183 = 0, $184 = 0, $185 = 0, $186 = 0, $187 = 0, $188 = 0, $189 = 0, $19 = 0;
 var $190 = 0, $191 = 0, $192 = 0, $193 = 0, $194 = 0, $195 = 0, $196 = 0, $197 = 0, $198 = 0, $199 = 0, $20 = 0, $200 = 0, $201 = 0, $202 = 0, $203 = 0, $204 = 0, $205 = 0, $206 = 0, $207 = 0, $208 = 0;
 var $209 = 0, $21 = 0, $210 = 0, $211 = 0, $212 = 0, $213 = 0, $214 = 0, $215 = 0, $216 = 0, $217 = 0, $218 = 0, $219 = 0, $22 = 0, $220 = 0, $221 = 0, $222 = 0, $223 = 0, $224 = 0, $225 = 0, $226 = 0;
 var $227 = 0, $228 = 0, $229 = 0, $23 = 0, $230 = 0, $231 = 0, $232 = 0, $233 = 0, $234 = 0, $235 = 0, $236 = 0, $237 = 0, $238 = 0, $239 = 0, $24 = 0, $240 = 0, $241 = 0, $242 = 0, $243 = 0, $244 = 0;
 var $245 = 0, $246 = 0, $247 = 0, $248 = 0, $249 = 0, $25 = 0, $250 = 0, $251 = 0, $252 = 0, $253 = 0, $254 = 0, $255 = 0, $256 = 0, $257 = 0, $258 = 0, $259 = 0, $26 = 0, $260 = 0, $261 = 0, $262 = 0;
 var $263 = 0, $264 = 0, $265 = 0, $266 = 0, $267 = 0, $268 = 0, $269 = 0, $27 = 0, $270 = 0, $271 = 0, $272 = 0, $273 = 0, $274 = 0, $275 = 0, $276 = 0, $277 = 0, $278 = 0, $279 = 0, $28 = 0, $280 = 0;
 var $281 = 0, $282 = 0, $283 = 0, $284 = 0, $285 = 0, $286 = 0, $287 = 0, $288 = 0, $289 = 0, $29 = 0, $290 = 0, $291 = 0, $292 = 0, $293 = 0, $294 = 0, $295 = 0, $296 = 0, $297 = 0, $298 = 0, $299 = 0;
 var $3 = 0, $30 = 0, $300 = 0, $301 = 0, $302 = 0, $303 = 0, $304 = 0, $305 = 0, $306 = 0, $307 = 0, $308 = 0, $309 = 0, $31 = 0, $310 = 0, $311 = 0, $312 = 0, $313 = 0, $314 = 0, $315 = 0, $316 = 0;
 var $317 = 0, $318 = 0, $319 = 0, $32 = 0, $320 = 0, $321 = 0, $322 = 0, $323 = 0, $324 = 0, $325 = 0, $326 = 0, $327 = 0, $328 = 0, $329 = 0, $33 = 0, $330 = 0, $331 = 0, $332 = 0, $333 = 0, $334 = 0;
 var $335 = 0, $336 = 0, $337 = 0, $338 = 0, $339 = 0, $34 = 0, $340 = 0, $341 = 0, $342 = 0, $343 = 0, $344 = 0, $345 = 0, $346 = 0, $347 = 0, $348 = 0, $349 = 0, $35 = 0, $350 = 0, $351 = 0, $352 = 0;
 var $353 = 0, $354 = 0, $355 = 0, $356 = 0, $357 = 0, $358 = 0, $359 = 0, $36 = 0, $360 = 0, $361 = 0, $362 = 0, $363 = 0, $364 = 0, $365 = 0, $366 = 0, $367 = 0, $368 = 0, $369 = 0, $37 = 0, $370 = 0;
 var $371 = 0, $372 = 0, $373 = 0, $374 = 0, $375 = 0, $376 = 0, $377 = 0, $378 = 0, $379 = 0, $38 = 0, $380 = 0, $381 = 0, $382 = 0, $383 = 0, $384 = 0, $385 = 0, $386 = 0, $387 = 0, $388 = 0, $389 = 0;
 var $39 = 0, $390 = 0, $391 = 0, $392 = 0, $393 = 0, $394 = 0, $395 = 0, $396 = 0, $397 = 0, $398 = 0, $399 = 0, $4 = 0, $40 = 0, $400 = 0, $401 = 0, $402 = 0, $403 = 0, $404 = 0, $405 = 0, $406 = 0;
 var $407 = 0, $408 = 0, $409 = 0, $41 = 0, $410 = 0, $411 = 0, $412 = 0, $413 = 0, $414 = 0, $415 = 0, $416 = 0, $417 = 0, $418 = 0, $419 = 0, $42 = 0, $420 = 0, $421 = 0, $422 = 0, $423 = 0, $424 = 0;
 var $425 = 0, $426 = 0, $427 = 0, $428 = 0, $429 = 0, $43 = 0, $430 = 0, $431 = 0, $432 = 0, $433 = 0, $434 = 0, $435 = 0, $436 = 0, $437 = 0, $438 = 0, $439 = 0, $44 = 0, $440 = 0, $441 = 0, $442 = 0;
 var $443 = 0, $444 = 0, $445 = 0, $446 = 0, $447 = 0, $448 = 0, $449 = 0, $45 = 0, $450 = 0, $451 = 0, $452 = 0, $453 = 0, $454 = 0, $455 = 0, $456 = 0, $457 = 0, $458 = 0, $459 = 0, $46 = 0, $460 = 0;
 var $461 = 0, $462 = 0, $463 = 0, $464 = 0, $465 = 0, $466 = 0, $467 = 0, $468 = 0, $469 = 0, $47 = 0, $470 = 0, $471 = 0, $472 = 0, $473 = 0, $474 = 0, $475 = 0, $476 = 0, $477 = 0, $478 = 0, $479 = 0;
 var $48 = 0, $480 = 0, $481 = 0, $482 = 0, $483 = 0, $484 = 0, $485 = 0, $486 = 0, $487 = 0, $488 = 0, $489 = 0, $49 = 0, $490 = 0, $491 = 0, $492 = 0, $493 = 0, $494 = 0, $495 = 0, $496 = 0, $497 = 0;
 var $498 = 0, $499 = 0, $5 = 0, $50 = 0, $500 = 0, $501 = 0, $502 = 0, $503 = 0, $504 = 0, $505 = 0, $506 = 0, $507 = 0, $508 = 0, $509 = 0, $51 = 0, $510 = 0, $511 = 0, $512 = 0, $513 = 0, $514 = 0;
 var $515 = 0, $516 = 0, $517 = 0, $518 = 0, $519 = 0, $52 = 0, $520 = 0, $521 = 0, $522 = 0, $523 = 0, $524 = 0, $525 = 0, $526 = 0, $527 = 0, $528 = 0, $529 = 0, $53 = 0, $530 = 0, $531 = 0, $532 = 0;
 var $533 = 0, $534 = 0, $535 = 0, $536 = 0, $537 = 0, $538 = 0, $539 = 0, $54 = 0, $540 = 0, $541 = 0, $542 = 0, $543 = 0, $544 = 0, $545 = 0, $546 = 0, $547 = 0, $548 = 0, $549 = 0, $55 = 0, $550 = 0;
 var $551 = 0, $552 = 0, $553 = 0, $554 = 0, $555 = 0, $556 = 0, $557 = 0, $558 = 0, $559 = 0, $56 = 0, $560 = 0, $561 = 0, $562 = 0, $563 = 0, $564 = 0, $565 = 0, $566 = 0, $567 = 0, $568 = 0, $569 = 0;
 var $57 = 0, $570 = 0, $571 = 0, $572 = 0, $573 = 0, $574 = 0, $575 = 0, $576 = 0, $577 = 0, $578 = 0, $579 = 0, $58 = 0, $580 = 0, $581 = 0, $582 = 0, $583 = 0, $584 = 0, $585 = 0, $586 = 0, $587 = 0;
 var $588 = 0, $589 = 0, $59 = 0, $590 = 0, $591 = 0, $592 = 0, $593 = 0, $594 = 0, $595 = 0, $596 = 0, $597 = 0, $598 = 0, $599 = 0, $6 = 0, $60 = 0, $600 = 0, $601 = 0, $602 = 0, $603 = 0, $604 = 0;
 var $605 = 0, $606 = 0, $607 = 0, $608 = 0, $609 = 0, $61 = 0, $610 = 0, $611 = 0, $612 = 0, $613 = 0, $614 = 0, $615 = 0, $616 = 0, $617 = 0, $618 = 0, $619 = 0, $62 = 0, $620 = 0, $621 = 0, $622 = 0;
 var $623 = 0, $624 = 0, $625 = 0, $626 = 0, $627 = 0, $628 = 0, $629 = 0, $63 = 0, $630 = 0, $631 = 0, $632 = 0, $633 = 0, $64 = 0, $65 = 0, $66 = 0, $67 = 0, $68 = 0, $69 = 0, $7 = 0, $70 = 0;
 var $71 = 0, $72 = 0, $73 = 0, $74 = 0, $75 = 0, $76 = 0, $77 = 0, $78 = 0, $79 = 0, $8 = 0, $80 = 0, $81 = 0, $82 = 0, $83 = 0, $84 = 0, $85 = 0, $86 = 0, $87 = 0, $88 = 0, $89 = 0;
 var $9 = 0, $90 = 0, $91 = 0, $92 = 0, $93 = 0, $94 = 0, $95 = 0, $96 = 0, $97 = 0, $98 = 0, $99 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $3 = HEAP32[$1>>2]|0;
 $4 = ((($1)) + 4|0);
 $5 = HEAP32[$4>>2]|0;
 $6 = ((($1)) + 8|0);
 $7 = HEAP32[$6>>2]|0;
 $8 = ((($1)) + 12|0);
 $9 = HEAP32[$8>>2]|0;
 $10 = ((($1)) + 16|0);
 $11 = HEAP32[$10>>2]|0;
 $12 = ((($1)) + 20|0);
 $13 = HEAP32[$12>>2]|0;
 $14 = ((($1)) + 24|0);
 $15 = HEAP32[$14>>2]|0;
 $16 = ((($1)) + 28|0);
 $17 = HEAP32[$16>>2]|0;
 $18 = ((($1)) + 32|0);
 $19 = HEAP32[$18>>2]|0;
 $20 = ((($1)) + 36|0);
 $21 = HEAP32[$20>>2]|0;
 $22 = HEAP32[$2>>2]|0;
 $23 = ((($2)) + 4|0);
 $24 = HEAP32[$23>>2]|0;
 $25 = ((($2)) + 8|0);
 $26 = HEAP32[$25>>2]|0;
 $27 = ((($2)) + 12|0);
 $28 = HEAP32[$27>>2]|0;
 $29 = ((($2)) + 16|0);
 $30 = HEAP32[$29>>2]|0;
 $31 = ((($2)) + 20|0);
 $32 = HEAP32[$31>>2]|0;
 $33 = ((($2)) + 24|0);
 $34 = HEAP32[$33>>2]|0;
 $35 = ((($2)) + 28|0);
 $36 = HEAP32[$35>>2]|0;
 $37 = ((($2)) + 32|0);
 $38 = HEAP32[$37>>2]|0;
 $39 = ((($2)) + 36|0);
 $40 = HEAP32[$39>>2]|0;
 $41 = ($24*19)|0;
 $42 = ($26*19)|0;
 $43 = ($28*19)|0;
 $44 = ($30*19)|0;
 $45 = ($32*19)|0;
 $46 = ($34*19)|0;
 $47 = ($36*19)|0;
 $48 = ($38*19)|0;
 $49 = ($40*19)|0;
 $50 = $5 << 1;
 $51 = $9 << 1;
 $52 = $13 << 1;
 $53 = $17 << 1;
 $54 = $21 << 1;
 $55 = ($3|0)<(0);
 $56 = $55 << 31 >> 31;
 $57 = ($22|0)<(0);
 $58 = $57 << 31 >> 31;
 $59 = (___muldi3(($22|0),($58|0),($3|0),($56|0))|0);
 $60 = tempRet0;
 $61 = ($24|0)<(0);
 $62 = $61 << 31 >> 31;
 $63 = (___muldi3(($24|0),($62|0),($3|0),($56|0))|0);
 $64 = tempRet0;
 $65 = ($26|0)<(0);
 $66 = $65 << 31 >> 31;
 $67 = (___muldi3(($26|0),($66|0),($3|0),($56|0))|0);
 $68 = tempRet0;
 $69 = ($28|0)<(0);
 $70 = $69 << 31 >> 31;
 $71 = (___muldi3(($28|0),($70|0),($3|0),($56|0))|0);
 $72 = tempRet0;
 $73 = ($30|0)<(0);
 $74 = $73 << 31 >> 31;
 $75 = (___muldi3(($30|0),($74|0),($3|0),($56|0))|0);
 $76 = tempRet0;
 $77 = ($32|0)<(0);
 $78 = $77 << 31 >> 31;
 $79 = (___muldi3(($32|0),($78|0),($3|0),($56|0))|0);
 $80 = tempRet0;
 $81 = ($34|0)<(0);
 $82 = $81 << 31 >> 31;
 $83 = (___muldi3(($34|0),($82|0),($3|0),($56|0))|0);
 $84 = tempRet0;
 $85 = ($36|0)<(0);
 $86 = $85 << 31 >> 31;
 $87 = (___muldi3(($36|0),($86|0),($3|0),($56|0))|0);
 $88 = tempRet0;
 $89 = ($38|0)<(0);
 $90 = $89 << 31 >> 31;
 $91 = (___muldi3(($38|0),($90|0),($3|0),($56|0))|0);
 $92 = tempRet0;
 $93 = ($40|0)<(0);
 $94 = $93 << 31 >> 31;
 $95 = (___muldi3(($40|0),($94|0),($3|0),($56|0))|0);
 $96 = tempRet0;
 $97 = ($5|0)<(0);
 $98 = $97 << 31 >> 31;
 $99 = (___muldi3(($22|0),($58|0),($5|0),($98|0))|0);
 $100 = tempRet0;
 $101 = ($50|0)<(0);
 $102 = $101 << 31 >> 31;
 $103 = (___muldi3(($24|0),($62|0),($50|0),($102|0))|0);
 $104 = tempRet0;
 $105 = (___muldi3(($26|0),($66|0),($5|0),($98|0))|0);
 $106 = tempRet0;
 $107 = (___muldi3(($28|0),($70|0),($50|0),($102|0))|0);
 $108 = tempRet0;
 $109 = (___muldi3(($30|0),($74|0),($5|0),($98|0))|0);
 $110 = tempRet0;
 $111 = (___muldi3(($32|0),($78|0),($50|0),($102|0))|0);
 $112 = tempRet0;
 $113 = (___muldi3(($34|0),($82|0),($5|0),($98|0))|0);
 $114 = tempRet0;
 $115 = (___muldi3(($36|0),($86|0),($50|0),($102|0))|0);
 $116 = tempRet0;
 $117 = (___muldi3(($38|0),($90|0),($5|0),($98|0))|0);
 $118 = tempRet0;
 $119 = ($49|0)<(0);
 $120 = $119 << 31 >> 31;
 $121 = (___muldi3(($49|0),($120|0),($50|0),($102|0))|0);
 $122 = tempRet0;
 $123 = ($7|0)<(0);
 $124 = $123 << 31 >> 31;
 $125 = (___muldi3(($22|0),($58|0),($7|0),($124|0))|0);
 $126 = tempRet0;
 $127 = (___muldi3(($24|0),($62|0),($7|0),($124|0))|0);
 $128 = tempRet0;
 $129 = (___muldi3(($26|0),($66|0),($7|0),($124|0))|0);
 $130 = tempRet0;
 $131 = (___muldi3(($28|0),($70|0),($7|0),($124|0))|0);
 $132 = tempRet0;
 $133 = (___muldi3(($30|0),($74|0),($7|0),($124|0))|0);
 $134 = tempRet0;
 $135 = (___muldi3(($32|0),($78|0),($7|0),($124|0))|0);
 $136 = tempRet0;
 $137 = (___muldi3(($34|0),($82|0),($7|0),($124|0))|0);
 $138 = tempRet0;
 $139 = (___muldi3(($36|0),($86|0),($7|0),($124|0))|0);
 $140 = tempRet0;
 $141 = ($48|0)<(0);
 $142 = $141 << 31 >> 31;
 $143 = (___muldi3(($48|0),($142|0),($7|0),($124|0))|0);
 $144 = tempRet0;
 $145 = (___muldi3(($49|0),($120|0),($7|0),($124|0))|0);
 $146 = tempRet0;
 $147 = ($9|0)<(0);
 $148 = $147 << 31 >> 31;
 $149 = (___muldi3(($22|0),($58|0),($9|0),($148|0))|0);
 $150 = tempRet0;
 $151 = ($51|0)<(0);
 $152 = $151 << 31 >> 31;
 $153 = (___muldi3(($24|0),($62|0),($51|0),($152|0))|0);
 $154 = tempRet0;
 $155 = (___muldi3(($26|0),($66|0),($9|0),($148|0))|0);
 $156 = tempRet0;
 $157 = (___muldi3(($28|0),($70|0),($51|0),($152|0))|0);
 $158 = tempRet0;
 $159 = (___muldi3(($30|0),($74|0),($9|0),($148|0))|0);
 $160 = tempRet0;
 $161 = (___muldi3(($32|0),($78|0),($51|0),($152|0))|0);
 $162 = tempRet0;
 $163 = (___muldi3(($34|0),($82|0),($9|0),($148|0))|0);
 $164 = tempRet0;
 $165 = ($47|0)<(0);
 $166 = $165 << 31 >> 31;
 $167 = (___muldi3(($47|0),($166|0),($51|0),($152|0))|0);
 $168 = tempRet0;
 $169 = (___muldi3(($48|0),($142|0),($9|0),($148|0))|0);
 $170 = tempRet0;
 $171 = (___muldi3(($49|0),($120|0),($51|0),($152|0))|0);
 $172 = tempRet0;
 $173 = ($11|0)<(0);
 $174 = $173 << 31 >> 31;
 $175 = (___muldi3(($22|0),($58|0),($11|0),($174|0))|0);
 $176 = tempRet0;
 $177 = (___muldi3(($24|0),($62|0),($11|0),($174|0))|0);
 $178 = tempRet0;
 $179 = (___muldi3(($26|0),($66|0),($11|0),($174|0))|0);
 $180 = tempRet0;
 $181 = (___muldi3(($28|0),($70|0),($11|0),($174|0))|0);
 $182 = tempRet0;
 $183 = (___muldi3(($30|0),($74|0),($11|0),($174|0))|0);
 $184 = tempRet0;
 $185 = (___muldi3(($32|0),($78|0),($11|0),($174|0))|0);
 $186 = tempRet0;
 $187 = ($46|0)<(0);
 $188 = $187 << 31 >> 31;
 $189 = (___muldi3(($46|0),($188|0),($11|0),($174|0))|0);
 $190 = tempRet0;
 $191 = (___muldi3(($47|0),($166|0),($11|0),($174|0))|0);
 $192 = tempRet0;
 $193 = (___muldi3(($48|0),($142|0),($11|0),($174|0))|0);
 $194 = tempRet0;
 $195 = (___muldi3(($49|0),($120|0),($11|0),($174|0))|0);
 $196 = tempRet0;
 $197 = ($13|0)<(0);
 $198 = $197 << 31 >> 31;
 $199 = (___muldi3(($22|0),($58|0),($13|0),($198|0))|0);
 $200 = tempRet0;
 $201 = ($52|0)<(0);
 $202 = $201 << 31 >> 31;
 $203 = (___muldi3(($24|0),($62|0),($52|0),($202|0))|0);
 $204 = tempRet0;
 $205 = (___muldi3(($26|0),($66|0),($13|0),($198|0))|0);
 $206 = tempRet0;
 $207 = (___muldi3(($28|0),($70|0),($52|0),($202|0))|0);
 $208 = tempRet0;
 $209 = (___muldi3(($30|0),($74|0),($13|0),($198|0))|0);
 $210 = tempRet0;
 $211 = ($45|0)<(0);
 $212 = $211 << 31 >> 31;
 $213 = (___muldi3(($45|0),($212|0),($52|0),($202|0))|0);
 $214 = tempRet0;
 $215 = (___muldi3(($46|0),($188|0),($13|0),($198|0))|0);
 $216 = tempRet0;
 $217 = (___muldi3(($47|0),($166|0),($52|0),($202|0))|0);
 $218 = tempRet0;
 $219 = (___muldi3(($48|0),($142|0),($13|0),($198|0))|0);
 $220 = tempRet0;
 $221 = (___muldi3(($49|0),($120|0),($52|0),($202|0))|0);
 $222 = tempRet0;
 $223 = ($15|0)<(0);
 $224 = $223 << 31 >> 31;
 $225 = (___muldi3(($22|0),($58|0),($15|0),($224|0))|0);
 $226 = tempRet0;
 $227 = (___muldi3(($24|0),($62|0),($15|0),($224|0))|0);
 $228 = tempRet0;
 $229 = (___muldi3(($26|0),($66|0),($15|0),($224|0))|0);
 $230 = tempRet0;
 $231 = (___muldi3(($28|0),($70|0),($15|0),($224|0))|0);
 $232 = tempRet0;
 $233 = ($44|0)<(0);
 $234 = $233 << 31 >> 31;
 $235 = (___muldi3(($44|0),($234|0),($15|0),($224|0))|0);
 $236 = tempRet0;
 $237 = (___muldi3(($45|0),($212|0),($15|0),($224|0))|0);
 $238 = tempRet0;
 $239 = (___muldi3(($46|0),($188|0),($15|0),($224|0))|0);
 $240 = tempRet0;
 $241 = (___muldi3(($47|0),($166|0),($15|0),($224|0))|0);
 $242 = tempRet0;
 $243 = (___muldi3(($48|0),($142|0),($15|0),($224|0))|0);
 $244 = tempRet0;
 $245 = (___muldi3(($49|0),($120|0),($15|0),($224|0))|0);
 $246 = tempRet0;
 $247 = ($17|0)<(0);
 $248 = $247 << 31 >> 31;
 $249 = (___muldi3(($22|0),($58|0),($17|0),($248|0))|0);
 $250 = tempRet0;
 $251 = ($53|0)<(0);
 $252 = $251 << 31 >> 31;
 $253 = (___muldi3(($24|0),($62|0),($53|0),($252|0))|0);
 $254 = tempRet0;
 $255 = (___muldi3(($26|0),($66|0),($17|0),($248|0))|0);
 $256 = tempRet0;
 $257 = ($43|0)<(0);
 $258 = $257 << 31 >> 31;
 $259 = (___muldi3(($43|0),($258|0),($53|0),($252|0))|0);
 $260 = tempRet0;
 $261 = (___muldi3(($44|0),($234|0),($17|0),($248|0))|0);
 $262 = tempRet0;
 $263 = (___muldi3(($45|0),($212|0),($53|0),($252|0))|0);
 $264 = tempRet0;
 $265 = (___muldi3(($46|0),($188|0),($17|0),($248|0))|0);
 $266 = tempRet0;
 $267 = (___muldi3(($47|0),($166|0),($53|0),($252|0))|0);
 $268 = tempRet0;
 $269 = (___muldi3(($48|0),($142|0),($17|0),($248|0))|0);
 $270 = tempRet0;
 $271 = (___muldi3(($49|0),($120|0),($53|0),($252|0))|0);
 $272 = tempRet0;
 $273 = ($19|0)<(0);
 $274 = $273 << 31 >> 31;
 $275 = (___muldi3(($22|0),($58|0),($19|0),($274|0))|0);
 $276 = tempRet0;
 $277 = (___muldi3(($24|0),($62|0),($19|0),($274|0))|0);
 $278 = tempRet0;
 $279 = ($42|0)<(0);
 $280 = $279 << 31 >> 31;
 $281 = (___muldi3(($42|0),($280|0),($19|0),($274|0))|0);
 $282 = tempRet0;
 $283 = (___muldi3(($43|0),($258|0),($19|0),($274|0))|0);
 $284 = tempRet0;
 $285 = (___muldi3(($44|0),($234|0),($19|0),($274|0))|0);
 $286 = tempRet0;
 $287 = (___muldi3(($45|0),($212|0),($19|0),($274|0))|0);
 $288 = tempRet0;
 $289 = (___muldi3(($46|0),($188|0),($19|0),($274|0))|0);
 $290 = tempRet0;
 $291 = (___muldi3(($47|0),($166|0),($19|0),($274|0))|0);
 $292 = tempRet0;
 $293 = (___muldi3(($48|0),($142|0),($19|0),($274|0))|0);
 $294 = tempRet0;
 $295 = (___muldi3(($49|0),($120|0),($19|0),($274|0))|0);
 $296 = tempRet0;
 $297 = ($21|0)<(0);
 $298 = $297 << 31 >> 31;
 $299 = (___muldi3(($22|0),($58|0),($21|0),($298|0))|0);
 $300 = tempRet0;
 $301 = ($54|0)<(0);
 $302 = $301 << 31 >> 31;
 $303 = ($41|0)<(0);
 $304 = $303 << 31 >> 31;
 $305 = (___muldi3(($41|0),($304|0),($54|0),($302|0))|0);
 $306 = tempRet0;
 $307 = (___muldi3(($42|0),($280|0),($21|0),($298|0))|0);
 $308 = tempRet0;
 $309 = (___muldi3(($43|0),($258|0),($54|0),($302|0))|0);
 $310 = tempRet0;
 $311 = (___muldi3(($44|0),($234|0),($21|0),($298|0))|0);
 $312 = tempRet0;
 $313 = (___muldi3(($45|0),($212|0),($54|0),($302|0))|0);
 $314 = tempRet0;
 $315 = (___muldi3(($46|0),($188|0),($21|0),($298|0))|0);
 $316 = tempRet0;
 $317 = (___muldi3(($47|0),($166|0),($54|0),($302|0))|0);
 $318 = tempRet0;
 $319 = (___muldi3(($48|0),($142|0),($21|0),($298|0))|0);
 $320 = tempRet0;
 $321 = (___muldi3(($49|0),($120|0),($54|0),($302|0))|0);
 $322 = tempRet0;
 $323 = (_i64Add(($305|0),($306|0),($59|0),($60|0))|0);
 $324 = tempRet0;
 $325 = (_i64Add(($323|0),($324|0),($281|0),($282|0))|0);
 $326 = tempRet0;
 $327 = (_i64Add(($325|0),($326|0),($259|0),($260|0))|0);
 $328 = tempRet0;
 $329 = (_i64Add(($327|0),($328|0),($235|0),($236|0))|0);
 $330 = tempRet0;
 $331 = (_i64Add(($329|0),($330|0),($213|0),($214|0))|0);
 $332 = tempRet0;
 $333 = (_i64Add(($331|0),($332|0),($189|0),($190|0))|0);
 $334 = tempRet0;
 $335 = (_i64Add(($333|0),($334|0),($167|0),($168|0))|0);
 $336 = tempRet0;
 $337 = (_i64Add(($335|0),($336|0),($143|0),($144|0))|0);
 $338 = tempRet0;
 $339 = (_i64Add(($337|0),($338|0),($121|0),($122|0))|0);
 $340 = tempRet0;
 $341 = (_i64Add(($63|0),($64|0),($99|0),($100|0))|0);
 $342 = tempRet0;
 $343 = (_i64Add(($153|0),($154|0),($175|0),($176|0))|0);
 $344 = tempRet0;
 $345 = (_i64Add(($343|0),($344|0),($129|0),($130|0))|0);
 $346 = tempRet0;
 $347 = (_i64Add(($345|0),($346|0),($107|0),($108|0))|0);
 $348 = tempRet0;
 $349 = (_i64Add(($347|0),($348|0),($75|0),($76|0))|0);
 $350 = tempRet0;
 $351 = (_i64Add(($349|0),($350|0),($313|0),($314|0))|0);
 $352 = tempRet0;
 $353 = (_i64Add(($351|0),($352|0),($289|0),($290|0))|0);
 $354 = tempRet0;
 $355 = (_i64Add(($353|0),($354|0),($267|0),($268|0))|0);
 $356 = tempRet0;
 $357 = (_i64Add(($355|0),($356|0),($243|0),($244|0))|0);
 $358 = tempRet0;
 $359 = (_i64Add(($357|0),($358|0),($221|0),($222|0))|0);
 $360 = tempRet0;
 $361 = (_i64Add(($339|0),($340|0),33554432,0)|0);
 $362 = tempRet0;
 $363 = (_bitshift64Ashr(($361|0),($362|0),26)|0);
 $364 = tempRet0;
 $365 = (_i64Add(($341|0),($342|0),($307|0),($308|0))|0);
 $366 = tempRet0;
 $367 = (_i64Add(($365|0),($366|0),($283|0),($284|0))|0);
 $368 = tempRet0;
 $369 = (_i64Add(($367|0),($368|0),($261|0),($262|0))|0);
 $370 = tempRet0;
 $371 = (_i64Add(($369|0),($370|0),($237|0),($238|0))|0);
 $372 = tempRet0;
 $373 = (_i64Add(($371|0),($372|0),($215|0),($216|0))|0);
 $374 = tempRet0;
 $375 = (_i64Add(($373|0),($374|0),($191|0),($192|0))|0);
 $376 = tempRet0;
 $377 = (_i64Add(($375|0),($376|0),($169|0),($170|0))|0);
 $378 = tempRet0;
 $379 = (_i64Add(($377|0),($378|0),($145|0),($146|0))|0);
 $380 = tempRet0;
 $381 = (_i64Add(($379|0),($380|0),($363|0),($364|0))|0);
 $382 = tempRet0;
 $383 = (_bitshift64Shl(($363|0),($364|0),26)|0);
 $384 = tempRet0;
 $385 = (_i64Subtract(($339|0),($340|0),($383|0),($384|0))|0);
 $386 = tempRet0;
 $387 = (_i64Add(($359|0),($360|0),33554432,0)|0);
 $388 = tempRet0;
 $389 = (_bitshift64Ashr(($387|0),($388|0),26)|0);
 $390 = tempRet0;
 $391 = (_i64Add(($177|0),($178|0),($199|0),($200|0))|0);
 $392 = tempRet0;
 $393 = (_i64Add(($391|0),($392|0),($155|0),($156|0))|0);
 $394 = tempRet0;
 $395 = (_i64Add(($393|0),($394|0),($131|0),($132|0))|0);
 $396 = tempRet0;
 $397 = (_i64Add(($395|0),($396|0),($109|0),($110|0))|0);
 $398 = tempRet0;
 $399 = (_i64Add(($397|0),($398|0),($79|0),($80|0))|0);
 $400 = tempRet0;
 $401 = (_i64Add(($399|0),($400|0),($315|0),($316|0))|0);
 $402 = tempRet0;
 $403 = (_i64Add(($401|0),($402|0),($291|0),($292|0))|0);
 $404 = tempRet0;
 $405 = (_i64Add(($403|0),($404|0),($269|0),($270|0))|0);
 $406 = tempRet0;
 $407 = (_i64Add(($405|0),($406|0),($245|0),($246|0))|0);
 $408 = tempRet0;
 $409 = (_i64Add(($407|0),($408|0),($389|0),($390|0))|0);
 $410 = tempRet0;
 $411 = (_bitshift64Shl(($389|0),($390|0),26)|0);
 $412 = tempRet0;
 $413 = (_i64Subtract(($359|0),($360|0),($411|0),($412|0))|0);
 $414 = tempRet0;
 $415 = (_i64Add(($381|0),($382|0),16777216,0)|0);
 $416 = tempRet0;
 $417 = (_bitshift64Ashr(($415|0),($416|0),25)|0);
 $418 = tempRet0;
 $419 = (_i64Add(($103|0),($104|0),($125|0),($126|0))|0);
 $420 = tempRet0;
 $421 = (_i64Add(($419|0),($420|0),($67|0),($68|0))|0);
 $422 = tempRet0;
 $423 = (_i64Add(($421|0),($422|0),($309|0),($310|0))|0);
 $424 = tempRet0;
 $425 = (_i64Add(($423|0),($424|0),($285|0),($286|0))|0);
 $426 = tempRet0;
 $427 = (_i64Add(($425|0),($426|0),($263|0),($264|0))|0);
 $428 = tempRet0;
 $429 = (_i64Add(($427|0),($428|0),($239|0),($240|0))|0);
 $430 = tempRet0;
 $431 = (_i64Add(($429|0),($430|0),($217|0),($218|0))|0);
 $432 = tempRet0;
 $433 = (_i64Add(($431|0),($432|0),($193|0),($194|0))|0);
 $434 = tempRet0;
 $435 = (_i64Add(($433|0),($434|0),($171|0),($172|0))|0);
 $436 = tempRet0;
 $437 = (_i64Add(($435|0),($436|0),($417|0),($418|0))|0);
 $438 = tempRet0;
 $439 = (_bitshift64Shl(($417|0),($418|0),25)|0);
 $440 = tempRet0;
 $441 = (_i64Subtract(($381|0),($382|0),($439|0),($440|0))|0);
 $442 = tempRet0;
 $443 = (_i64Add(($409|0),($410|0),16777216,0)|0);
 $444 = tempRet0;
 $445 = (_bitshift64Ashr(($443|0),($444|0),25)|0);
 $446 = tempRet0;
 $447 = (_i64Add(($203|0),($204|0),($225|0),($226|0))|0);
 $448 = tempRet0;
 $449 = (_i64Add(($447|0),($448|0),($179|0),($180|0))|0);
 $450 = tempRet0;
 $451 = (_i64Add(($449|0),($450|0),($157|0),($158|0))|0);
 $452 = tempRet0;
 $453 = (_i64Add(($451|0),($452|0),($133|0),($134|0))|0);
 $454 = tempRet0;
 $455 = (_i64Add(($453|0),($454|0),($111|0),($112|0))|0);
 $456 = tempRet0;
 $457 = (_i64Add(($455|0),($456|0),($83|0),($84|0))|0);
 $458 = tempRet0;
 $459 = (_i64Add(($457|0),($458|0),($317|0),($318|0))|0);
 $460 = tempRet0;
 $461 = (_i64Add(($459|0),($460|0),($293|0),($294|0))|0);
 $462 = tempRet0;
 $463 = (_i64Add(($461|0),($462|0),($271|0),($272|0))|0);
 $464 = tempRet0;
 $465 = (_i64Add(($463|0),($464|0),($445|0),($446|0))|0);
 $466 = tempRet0;
 $467 = (_bitshift64Shl(($445|0),($446|0),25)|0);
 $468 = tempRet0;
 $469 = (_i64Subtract(($409|0),($410|0),($467|0),($468|0))|0);
 $470 = tempRet0;
 $471 = (_i64Add(($437|0),($438|0),33554432,0)|0);
 $472 = tempRet0;
 $473 = (_bitshift64Ashr(($471|0),($472|0),26)|0);
 $474 = tempRet0;
 $475 = (_i64Add(($127|0),($128|0),($149|0),($150|0))|0);
 $476 = tempRet0;
 $477 = (_i64Add(($475|0),($476|0),($105|0),($106|0))|0);
 $478 = tempRet0;
 $479 = (_i64Add(($477|0),($478|0),($71|0),($72|0))|0);
 $480 = tempRet0;
 $481 = (_i64Add(($479|0),($480|0),($311|0),($312|0))|0);
 $482 = tempRet0;
 $483 = (_i64Add(($481|0),($482|0),($287|0),($288|0))|0);
 $484 = tempRet0;
 $485 = (_i64Add(($483|0),($484|0),($265|0),($266|0))|0);
 $486 = tempRet0;
 $487 = (_i64Add(($485|0),($486|0),($241|0),($242|0))|0);
 $488 = tempRet0;
 $489 = (_i64Add(($487|0),($488|0),($219|0),($220|0))|0);
 $490 = tempRet0;
 $491 = (_i64Add(($489|0),($490|0),($195|0),($196|0))|0);
 $492 = tempRet0;
 $493 = (_i64Add(($491|0),($492|0),($473|0),($474|0))|0);
 $494 = tempRet0;
 $495 = (_bitshift64Shl(($473|0),($474|0),26)|0);
 $496 = tempRet0;
 $497 = (_i64Subtract(($437|0),($438|0),($495|0),($496|0))|0);
 $498 = tempRet0;
 $499 = (_i64Add(($465|0),($466|0),33554432,0)|0);
 $500 = tempRet0;
 $501 = (_bitshift64Ashr(($499|0),($500|0),26)|0);
 $502 = tempRet0;
 $503 = (_i64Add(($227|0),($228|0),($249|0),($250|0))|0);
 $504 = tempRet0;
 $505 = (_i64Add(($503|0),($504|0),($205|0),($206|0))|0);
 $506 = tempRet0;
 $507 = (_i64Add(($505|0),($506|0),($181|0),($182|0))|0);
 $508 = tempRet0;
 $509 = (_i64Add(($507|0),($508|0),($159|0),($160|0))|0);
 $510 = tempRet0;
 $511 = (_i64Add(($509|0),($510|0),($135|0),($136|0))|0);
 $512 = tempRet0;
 $513 = (_i64Add(($511|0),($512|0),($113|0),($114|0))|0);
 $514 = tempRet0;
 $515 = (_i64Add(($513|0),($514|0),($87|0),($88|0))|0);
 $516 = tempRet0;
 $517 = (_i64Add(($515|0),($516|0),($319|0),($320|0))|0);
 $518 = tempRet0;
 $519 = (_i64Add(($517|0),($518|0),($295|0),($296|0))|0);
 $520 = tempRet0;
 $521 = (_i64Add(($519|0),($520|0),($501|0),($502|0))|0);
 $522 = tempRet0;
 $523 = (_bitshift64Shl(($501|0),($502|0),26)|0);
 $524 = tempRet0;
 $525 = (_i64Subtract(($465|0),($466|0),($523|0),($524|0))|0);
 $526 = tempRet0;
 $527 = (_i64Add(($493|0),($494|0),16777216,0)|0);
 $528 = tempRet0;
 $529 = (_bitshift64Ashr(($527|0),($528|0),25)|0);
 $530 = tempRet0;
 $531 = (_i64Add(($529|0),($530|0),($413|0),($414|0))|0);
 $532 = tempRet0;
 $533 = (_bitshift64Shl(($529|0),($530|0),25)|0);
 $534 = tempRet0;
 $535 = (_i64Subtract(($493|0),($494|0),($533|0),($534|0))|0);
 $536 = tempRet0;
 $537 = (_i64Add(($521|0),($522|0),16777216,0)|0);
 $538 = tempRet0;
 $539 = (_bitshift64Ashr(($537|0),($538|0),25)|0);
 $540 = tempRet0;
 $541 = (_i64Add(($253|0),($254|0),($275|0),($276|0))|0);
 $542 = tempRet0;
 $543 = (_i64Add(($541|0),($542|0),($229|0),($230|0))|0);
 $544 = tempRet0;
 $545 = (_i64Add(($543|0),($544|0),($207|0),($208|0))|0);
 $546 = tempRet0;
 $547 = (_i64Add(($545|0),($546|0),($183|0),($184|0))|0);
 $548 = tempRet0;
 $549 = (_i64Add(($547|0),($548|0),($161|0),($162|0))|0);
 $550 = tempRet0;
 $551 = (_i64Add(($549|0),($550|0),($137|0),($138|0))|0);
 $552 = tempRet0;
 $553 = (_i64Add(($551|0),($552|0),($115|0),($116|0))|0);
 $554 = tempRet0;
 $555 = (_i64Add(($553|0),($554|0),($91|0),($92|0))|0);
 $556 = tempRet0;
 $557 = (_i64Add(($555|0),($556|0),($321|0),($322|0))|0);
 $558 = tempRet0;
 $559 = (_i64Add(($557|0),($558|0),($539|0),($540|0))|0);
 $560 = tempRet0;
 $561 = (_bitshift64Shl(($539|0),($540|0),25)|0);
 $562 = tempRet0;
 $563 = (_i64Subtract(($521|0),($522|0),($561|0),($562|0))|0);
 $564 = tempRet0;
 $565 = (_i64Add(($531|0),($532|0),33554432,0)|0);
 $566 = tempRet0;
 $567 = (_bitshift64Ashr(($565|0),($566|0),26)|0);
 $568 = tempRet0;
 $569 = (_i64Add(($469|0),($470|0),($567|0),($568|0))|0);
 $570 = tempRet0;
 $571 = (_bitshift64Shl(($567|0),($568|0),26)|0);
 $572 = tempRet0;
 $573 = (_i64Subtract(($531|0),($532|0),($571|0),($572|0))|0);
 $574 = tempRet0;
 $575 = (_i64Add(($559|0),($560|0),33554432,0)|0);
 $576 = tempRet0;
 $577 = (_bitshift64Ashr(($575|0),($576|0),26)|0);
 $578 = tempRet0;
 $579 = (_i64Add(($277|0),($278|0),($299|0),($300|0))|0);
 $580 = tempRet0;
 $581 = (_i64Add(($579|0),($580|0),($255|0),($256|0))|0);
 $582 = tempRet0;
 $583 = (_i64Add(($581|0),($582|0),($231|0),($232|0))|0);
 $584 = tempRet0;
 $585 = (_i64Add(($583|0),($584|0),($209|0),($210|0))|0);
 $586 = tempRet0;
 $587 = (_i64Add(($585|0),($586|0),($185|0),($186|0))|0);
 $588 = tempRet0;
 $589 = (_i64Add(($587|0),($588|0),($163|0),($164|0))|0);
 $590 = tempRet0;
 $591 = (_i64Add(($589|0),($590|0),($139|0),($140|0))|0);
 $592 = tempRet0;
 $593 = (_i64Add(($591|0),($592|0),($117|0),($118|0))|0);
 $594 = tempRet0;
 $595 = (_i64Add(($593|0),($594|0),($95|0),($96|0))|0);
 $596 = tempRet0;
 $597 = (_i64Add(($595|0),($596|0),($577|0),($578|0))|0);
 $598 = tempRet0;
 $599 = (_bitshift64Shl(($577|0),($578|0),26)|0);
 $600 = tempRet0;
 $601 = (_i64Subtract(($559|0),($560|0),($599|0),($600|0))|0);
 $602 = tempRet0;
 $603 = (_i64Add(($597|0),($598|0),16777216,0)|0);
 $604 = tempRet0;
 $605 = (_bitshift64Ashr(($603|0),($604|0),25)|0);
 $606 = tempRet0;
 $607 = (___muldi3(($605|0),($606|0),19,0)|0);
 $608 = tempRet0;
 $609 = (_i64Add(($607|0),($608|0),($385|0),($386|0))|0);
 $610 = tempRet0;
 $611 = (_bitshift64Shl(($605|0),($606|0),25)|0);
 $612 = tempRet0;
 $613 = (_i64Subtract(($597|0),($598|0),($611|0),($612|0))|0);
 $614 = tempRet0;
 $615 = (_i64Add(($609|0),($610|0),33554432,0)|0);
 $616 = tempRet0;
 $617 = (_bitshift64Ashr(($615|0),($616|0),26)|0);
 $618 = tempRet0;
 $619 = (_i64Add(($441|0),($442|0),($617|0),($618|0))|0);
 $620 = tempRet0;
 $621 = (_bitshift64Shl(($617|0),($618|0),26)|0);
 $622 = tempRet0;
 $623 = (_i64Subtract(($609|0),($610|0),($621|0),($622|0))|0);
 $624 = tempRet0;
 HEAP32[$0>>2] = $623;
 $625 = ((($0)) + 4|0);
 HEAP32[$625>>2] = $619;
 $626 = ((($0)) + 8|0);
 HEAP32[$626>>2] = $497;
 $627 = ((($0)) + 12|0);
 HEAP32[$627>>2] = $535;
 $628 = ((($0)) + 16|0);
 HEAP32[$628>>2] = $573;
 $629 = ((($0)) + 20|0);
 HEAP32[$629>>2] = $569;
 $630 = ((($0)) + 24|0);
 HEAP32[$630>>2] = $525;
 $631 = ((($0)) + 28|0);
 HEAP32[$631>>2] = $563;
 $632 = ((($0)) + 32|0);
 HEAP32[$632>>2] = $601;
 $633 = ((($0)) + 36|0);
 HEAP32[$633>>2] = $613;
 return;
}
function _crypto_sign_ed25519_ref10_fe_neg($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $2 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0;
 var $29 = 0, $3 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = HEAP32[$1>>2]|0;
 $3 = ((($1)) + 4|0);
 $4 = HEAP32[$3>>2]|0;
 $5 = ((($1)) + 8|0);
 $6 = HEAP32[$5>>2]|0;
 $7 = ((($1)) + 12|0);
 $8 = HEAP32[$7>>2]|0;
 $9 = ((($1)) + 16|0);
 $10 = HEAP32[$9>>2]|0;
 $11 = ((($1)) + 20|0);
 $12 = HEAP32[$11>>2]|0;
 $13 = ((($1)) + 24|0);
 $14 = HEAP32[$13>>2]|0;
 $15 = ((($1)) + 28|0);
 $16 = HEAP32[$15>>2]|0;
 $17 = ((($1)) + 32|0);
 $18 = HEAP32[$17>>2]|0;
 $19 = ((($1)) + 36|0);
 $20 = HEAP32[$19>>2]|0;
 $21 = (0 - ($2))|0;
 $22 = (0 - ($4))|0;
 $23 = (0 - ($6))|0;
 $24 = (0 - ($8))|0;
 $25 = (0 - ($10))|0;
 $26 = (0 - ($12))|0;
 $27 = (0 - ($14))|0;
 $28 = (0 - ($16))|0;
 $29 = (0 - ($18))|0;
 $30 = (0 - ($20))|0;
 HEAP32[$0>>2] = $21;
 $31 = ((($0)) + 4|0);
 HEAP32[$31>>2] = $22;
 $32 = ((($0)) + 8|0);
 HEAP32[$32>>2] = $23;
 $33 = ((($0)) + 12|0);
 HEAP32[$33>>2] = $24;
 $34 = ((($0)) + 16|0);
 HEAP32[$34>>2] = $25;
 $35 = ((($0)) + 20|0);
 HEAP32[$35>>2] = $26;
 $36 = ((($0)) + 24|0);
 HEAP32[$36>>2] = $27;
 $37 = ((($0)) + 28|0);
 HEAP32[$37>>2] = $28;
 $38 = ((($0)) + 32|0);
 HEAP32[$38>>2] = $29;
 $39 = ((($0)) + 36|0);
 HEAP32[$39>>2] = $30;
 return;
}
function _crypto_sign_ed25519_ref10_fe_pow22523($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $$729 = 0, $$828 = 0, $$927 = 0, $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $exitcond = 0, $exitcond35 = 0, $exitcond36 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 128|0;
 $2 = sp + 80|0;
 $3 = sp + 40|0;
 $4 = sp;
 _crypto_sign_ed25519_ref10_fe_sq($2,$1);
 _crypto_sign_ed25519_ref10_fe_sq($3,$2);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_mul($3,$1,$3);
 _crypto_sign_ed25519_ref10_fe_mul($2,$2,$3);
 _crypto_sign_ed25519_ref10_fe_sq($2,$2);
 _crypto_sign_ed25519_ref10_fe_mul($2,$3,$2);
 _crypto_sign_ed25519_ref10_fe_sq($3,$2);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_mul($2,$3,$2);
 _crypto_sign_ed25519_ref10_fe_sq($3,$2);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_mul($3,$3,$2);
 _crypto_sign_ed25519_ref10_fe_sq($4,$3);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_sq($4,$4);
 _crypto_sign_ed25519_ref10_fe_mul($3,$4,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 _crypto_sign_ed25519_ref10_fe_mul($2,$3,$2);
 _crypto_sign_ed25519_ref10_fe_sq($3,$2);
 $$729 = 1;
 while(1) {
  _crypto_sign_ed25519_ref10_fe_sq($3,$3);
  $5 = (($$729) + 1)|0;
  $exitcond36 = ($5|0)==(50);
  if ($exitcond36) {
   break;
  } else {
   $$729 = $5;
  }
 }
 _crypto_sign_ed25519_ref10_fe_mul($3,$3,$2);
 _crypto_sign_ed25519_ref10_fe_sq($4,$3);
 $$828 = 1;
 while(1) {
  _crypto_sign_ed25519_ref10_fe_sq($4,$4);
  $6 = (($$828) + 1)|0;
  $exitcond35 = ($6|0)==(100);
  if ($exitcond35) {
   break;
  } else {
   $$828 = $6;
  }
 }
 _crypto_sign_ed25519_ref10_fe_mul($3,$4,$3);
 _crypto_sign_ed25519_ref10_fe_sq($3,$3);
 $$927 = 1;
 while(1) {
  _crypto_sign_ed25519_ref10_fe_sq($3,$3);
  $7 = (($$927) + 1)|0;
  $exitcond = ($7|0)==(50);
  if ($exitcond) {
   break;
  } else {
   $$927 = $7;
  }
 }
 _crypto_sign_ed25519_ref10_fe_mul($2,$3,$2);
 _crypto_sign_ed25519_ref10_fe_sq($2,$2);
 _crypto_sign_ed25519_ref10_fe_sq($2,$2);
 _crypto_sign_ed25519_ref10_fe_mul($0,$2,$1);
 STACKTOP = sp;return;
}
function _crypto_sign_ed25519_ref10_fe_sq($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0, $113 = 0, $114 = 0, $115 = 0, $116 = 0, $117 = 0;
 var $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0, $133 = 0, $134 = 0, $135 = 0;
 var $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0, $15 = 0, $150 = 0, $151 = 0, $152 = 0, $153 = 0;
 var $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $159 = 0, $16 = 0, $160 = 0, $161 = 0, $162 = 0, $163 = 0, $164 = 0, $165 = 0, $166 = 0, $167 = 0, $168 = 0, $169 = 0, $17 = 0, $170 = 0, $171 = 0;
 var $172 = 0, $173 = 0, $174 = 0, $175 = 0, $176 = 0, $177 = 0, $178 = 0, $179 = 0, $18 = 0, $180 = 0, $181 = 0, $182 = 0, $183 = 0, $184 = 0, $185 = 0, $186 = 0, $187 = 0, $188 = 0, $189 = 0, $19 = 0;
 var $190 = 0, $191 = 0, $192 = 0, $193 = 0, $194 = 0, $195 = 0, $196 = 0, $197 = 0, $198 = 0, $199 = 0, $2 = 0, $20 = 0, $200 = 0, $201 = 0, $202 = 0, $203 = 0, $204 = 0, $205 = 0, $206 = 0, $207 = 0;
 var $208 = 0, $209 = 0, $21 = 0, $210 = 0, $211 = 0, $212 = 0, $213 = 0, $214 = 0, $215 = 0, $216 = 0, $217 = 0, $218 = 0, $219 = 0, $22 = 0, $220 = 0, $221 = 0, $222 = 0, $223 = 0, $224 = 0, $225 = 0;
 var $226 = 0, $227 = 0, $228 = 0, $229 = 0, $23 = 0, $230 = 0, $231 = 0, $232 = 0, $233 = 0, $234 = 0, $235 = 0, $236 = 0, $237 = 0, $238 = 0, $239 = 0, $24 = 0, $240 = 0, $241 = 0, $242 = 0, $243 = 0;
 var $244 = 0, $245 = 0, $246 = 0, $247 = 0, $248 = 0, $249 = 0, $25 = 0, $250 = 0, $251 = 0, $252 = 0, $253 = 0, $254 = 0, $255 = 0, $256 = 0, $257 = 0, $258 = 0, $259 = 0, $26 = 0, $260 = 0, $261 = 0;
 var $262 = 0, $263 = 0, $264 = 0, $265 = 0, $266 = 0, $267 = 0, $268 = 0, $269 = 0, $27 = 0, $270 = 0, $271 = 0, $272 = 0, $273 = 0, $274 = 0, $275 = 0, $276 = 0, $277 = 0, $278 = 0, $279 = 0, $28 = 0;
 var $280 = 0, $281 = 0, $282 = 0, $283 = 0, $284 = 0, $285 = 0, $286 = 0, $287 = 0, $288 = 0, $289 = 0, $29 = 0, $290 = 0, $291 = 0, $292 = 0, $293 = 0, $294 = 0, $295 = 0, $296 = 0, $297 = 0, $298 = 0;
 var $299 = 0, $3 = 0, $30 = 0, $300 = 0, $301 = 0, $302 = 0, $303 = 0, $304 = 0, $305 = 0, $306 = 0, $307 = 0, $308 = 0, $309 = 0, $31 = 0, $310 = 0, $311 = 0, $312 = 0, $313 = 0, $314 = 0, $315 = 0;
 var $316 = 0, $317 = 0, $318 = 0, $319 = 0, $32 = 0, $320 = 0, $321 = 0, $322 = 0, $323 = 0, $324 = 0, $325 = 0, $326 = 0, $327 = 0, $328 = 0, $329 = 0, $33 = 0, $330 = 0, $331 = 0, $332 = 0, $333 = 0;
 var $334 = 0, $335 = 0, $336 = 0, $337 = 0, $338 = 0, $339 = 0, $34 = 0, $340 = 0, $341 = 0, $342 = 0, $343 = 0, $344 = 0, $345 = 0, $346 = 0, $347 = 0, $348 = 0, $349 = 0, $35 = 0, $350 = 0, $351 = 0;
 var $352 = 0, $353 = 0, $354 = 0, $355 = 0, $356 = 0, $357 = 0, $358 = 0, $359 = 0, $36 = 0, $360 = 0, $361 = 0, $362 = 0, $363 = 0, $364 = 0, $365 = 0, $366 = 0, $367 = 0, $368 = 0, $369 = 0, $37 = 0;
 var $370 = 0, $371 = 0, $372 = 0, $373 = 0, $374 = 0, $375 = 0, $376 = 0, $377 = 0, $378 = 0, $379 = 0, $38 = 0, $380 = 0, $381 = 0, $382 = 0, $383 = 0, $384 = 0, $385 = 0, $386 = 0, $387 = 0, $388 = 0;
 var $389 = 0, $39 = 0, $390 = 0, $391 = 0, $392 = 0, $393 = 0, $394 = 0, $395 = 0, $396 = 0, $397 = 0, $398 = 0, $399 = 0, $4 = 0, $40 = 0, $400 = 0, $401 = 0, $402 = 0, $403 = 0, $404 = 0, $405 = 0;
 var $406 = 0, $407 = 0, $408 = 0, $409 = 0, $41 = 0, $410 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0, $46 = 0, $47 = 0, $48 = 0, $49 = 0, $5 = 0, $50 = 0, $51 = 0, $52 = 0, $53 = 0, $54 = 0;
 var $55 = 0, $56 = 0, $57 = 0, $58 = 0, $59 = 0, $6 = 0, $60 = 0, $61 = 0, $62 = 0, $63 = 0, $64 = 0, $65 = 0, $66 = 0, $67 = 0, $68 = 0, $69 = 0, $7 = 0, $70 = 0, $71 = 0, $72 = 0;
 var $73 = 0, $74 = 0, $75 = 0, $76 = 0, $77 = 0, $78 = 0, $79 = 0, $8 = 0, $80 = 0, $81 = 0, $82 = 0, $83 = 0, $84 = 0, $85 = 0, $86 = 0, $87 = 0, $88 = 0, $89 = 0, $9 = 0, $90 = 0;
 var $91 = 0, $92 = 0, $93 = 0, $94 = 0, $95 = 0, $96 = 0, $97 = 0, $98 = 0, $99 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = HEAP32[$1>>2]|0;
 $3 = ((($1)) + 4|0);
 $4 = HEAP32[$3>>2]|0;
 $5 = ((($1)) + 8|0);
 $6 = HEAP32[$5>>2]|0;
 $7 = ((($1)) + 12|0);
 $8 = HEAP32[$7>>2]|0;
 $9 = ((($1)) + 16|0);
 $10 = HEAP32[$9>>2]|0;
 $11 = ((($1)) + 20|0);
 $12 = HEAP32[$11>>2]|0;
 $13 = ((($1)) + 24|0);
 $14 = HEAP32[$13>>2]|0;
 $15 = ((($1)) + 28|0);
 $16 = HEAP32[$15>>2]|0;
 $17 = ((($1)) + 32|0);
 $18 = HEAP32[$17>>2]|0;
 $19 = ((($1)) + 36|0);
 $20 = HEAP32[$19>>2]|0;
 $21 = $2 << 1;
 $22 = $4 << 1;
 $23 = $6 << 1;
 $24 = $8 << 1;
 $25 = $10 << 1;
 $26 = $12 << 1;
 $27 = $14 << 1;
 $28 = $16 << 1;
 $29 = ($12*38)|0;
 $30 = ($14*19)|0;
 $31 = ($16*38)|0;
 $32 = ($18*19)|0;
 $33 = ($20*38)|0;
 $34 = ($2|0)<(0);
 $35 = $34 << 31 >> 31;
 $36 = (___muldi3(($2|0),($35|0),($2|0),($35|0))|0);
 $37 = tempRet0;
 $38 = ($21|0)<(0);
 $39 = $38 << 31 >> 31;
 $40 = ($4|0)<(0);
 $41 = $40 << 31 >> 31;
 $42 = (___muldi3(($21|0),($39|0),($4|0),($41|0))|0);
 $43 = tempRet0;
 $44 = ($6|0)<(0);
 $45 = $44 << 31 >> 31;
 $46 = (___muldi3(($6|0),($45|0),($21|0),($39|0))|0);
 $47 = tempRet0;
 $48 = ($8|0)<(0);
 $49 = $48 << 31 >> 31;
 $50 = (___muldi3(($8|0),($49|0),($21|0),($39|0))|0);
 $51 = tempRet0;
 $52 = ($10|0)<(0);
 $53 = $52 << 31 >> 31;
 $54 = (___muldi3(($10|0),($53|0),($21|0),($39|0))|0);
 $55 = tempRet0;
 $56 = ($12|0)<(0);
 $57 = $56 << 31 >> 31;
 $58 = (___muldi3(($12|0),($57|0),($21|0),($39|0))|0);
 $59 = tempRet0;
 $60 = ($14|0)<(0);
 $61 = $60 << 31 >> 31;
 $62 = (___muldi3(($14|0),($61|0),($21|0),($39|0))|0);
 $63 = tempRet0;
 $64 = ($16|0)<(0);
 $65 = $64 << 31 >> 31;
 $66 = (___muldi3(($16|0),($65|0),($21|0),($39|0))|0);
 $67 = tempRet0;
 $68 = ($18|0)<(0);
 $69 = $68 << 31 >> 31;
 $70 = (___muldi3(($18|0),($69|0),($21|0),($39|0))|0);
 $71 = tempRet0;
 $72 = ($20|0)<(0);
 $73 = $72 << 31 >> 31;
 $74 = (___muldi3(($20|0),($73|0),($21|0),($39|0))|0);
 $75 = tempRet0;
 $76 = ($22|0)<(0);
 $77 = $76 << 31 >> 31;
 $78 = (___muldi3(($22|0),($77|0),($4|0),($41|0))|0);
 $79 = tempRet0;
 $80 = (___muldi3(($22|0),($77|0),($6|0),($45|0))|0);
 $81 = tempRet0;
 $82 = ($24|0)<(0);
 $83 = $82 << 31 >> 31;
 $84 = (___muldi3(($24|0),($83|0),($22|0),($77|0))|0);
 $85 = tempRet0;
 $86 = (___muldi3(($10|0),($53|0),($22|0),($77|0))|0);
 $87 = tempRet0;
 $88 = ($26|0)<(0);
 $89 = $88 << 31 >> 31;
 $90 = (___muldi3(($26|0),($89|0),($22|0),($77|0))|0);
 $91 = tempRet0;
 $92 = (___muldi3(($14|0),($61|0),($22|0),($77|0))|0);
 $93 = tempRet0;
 $94 = ($28|0)<(0);
 $95 = $94 << 31 >> 31;
 $96 = (___muldi3(($28|0),($95|0),($22|0),($77|0))|0);
 $97 = tempRet0;
 $98 = (___muldi3(($18|0),($69|0),($22|0),($77|0))|0);
 $99 = tempRet0;
 $100 = ($33|0)<(0);
 $101 = $100 << 31 >> 31;
 $102 = (___muldi3(($33|0),($101|0),($22|0),($77|0))|0);
 $103 = tempRet0;
 $104 = (___muldi3(($6|0),($45|0),($6|0),($45|0))|0);
 $105 = tempRet0;
 $106 = ($23|0)<(0);
 $107 = $106 << 31 >> 31;
 $108 = (___muldi3(($23|0),($107|0),($8|0),($49|0))|0);
 $109 = tempRet0;
 $110 = (___muldi3(($10|0),($53|0),($23|0),($107|0))|0);
 $111 = tempRet0;
 $112 = (___muldi3(($12|0),($57|0),($23|0),($107|0))|0);
 $113 = tempRet0;
 $114 = (___muldi3(($14|0),($61|0),($23|0),($107|0))|0);
 $115 = tempRet0;
 $116 = (___muldi3(($16|0),($65|0),($23|0),($107|0))|0);
 $117 = tempRet0;
 $118 = ($32|0)<(0);
 $119 = $118 << 31 >> 31;
 $120 = (___muldi3(($32|0),($119|0),($23|0),($107|0))|0);
 $121 = tempRet0;
 $122 = (___muldi3(($33|0),($101|0),($6|0),($45|0))|0);
 $123 = tempRet0;
 $124 = (___muldi3(($24|0),($83|0),($8|0),($49|0))|0);
 $125 = tempRet0;
 $126 = (___muldi3(($24|0),($83|0),($10|0),($53|0))|0);
 $127 = tempRet0;
 $128 = (___muldi3(($26|0),($89|0),($24|0),($83|0))|0);
 $129 = tempRet0;
 $130 = (___muldi3(($14|0),($61|0),($24|0),($83|0))|0);
 $131 = tempRet0;
 $132 = ($31|0)<(0);
 $133 = $132 << 31 >> 31;
 $134 = (___muldi3(($31|0),($133|0),($24|0),($83|0))|0);
 $135 = tempRet0;
 $136 = (___muldi3(($32|0),($119|0),($24|0),($83|0))|0);
 $137 = tempRet0;
 $138 = (___muldi3(($33|0),($101|0),($24|0),($83|0))|0);
 $139 = tempRet0;
 $140 = (___muldi3(($10|0),($53|0),($10|0),($53|0))|0);
 $141 = tempRet0;
 $142 = ($25|0)<(0);
 $143 = $142 << 31 >> 31;
 $144 = (___muldi3(($25|0),($143|0),($12|0),($57|0))|0);
 $145 = tempRet0;
 $146 = ($30|0)<(0);
 $147 = $146 << 31 >> 31;
 $148 = (___muldi3(($30|0),($147|0),($25|0),($143|0))|0);
 $149 = tempRet0;
 $150 = (___muldi3(($31|0),($133|0),($10|0),($53|0))|0);
 $151 = tempRet0;
 $152 = (___muldi3(($32|0),($119|0),($25|0),($143|0))|0);
 $153 = tempRet0;
 $154 = (___muldi3(($33|0),($101|0),($10|0),($53|0))|0);
 $155 = tempRet0;
 $156 = ($29|0)<(0);
 $157 = $156 << 31 >> 31;
 $158 = (___muldi3(($29|0),($157|0),($12|0),($57|0))|0);
 $159 = tempRet0;
 $160 = (___muldi3(($30|0),($147|0),($26|0),($89|0))|0);
 $161 = tempRet0;
 $162 = (___muldi3(($31|0),($133|0),($26|0),($89|0))|0);
 $163 = tempRet0;
 $164 = (___muldi3(($32|0),($119|0),($26|0),($89|0))|0);
 $165 = tempRet0;
 $166 = (___muldi3(($33|0),($101|0),($26|0),($89|0))|0);
 $167 = tempRet0;
 $168 = (___muldi3(($30|0),($147|0),($14|0),($61|0))|0);
 $169 = tempRet0;
 $170 = (___muldi3(($31|0),($133|0),($14|0),($61|0))|0);
 $171 = tempRet0;
 $172 = ($27|0)<(0);
 $173 = $172 << 31 >> 31;
 $174 = (___muldi3(($32|0),($119|0),($27|0),($173|0))|0);
 $175 = tempRet0;
 $176 = (___muldi3(($33|0),($101|0),($14|0),($61|0))|0);
 $177 = tempRet0;
 $178 = (___muldi3(($31|0),($133|0),($16|0),($65|0))|0);
 $179 = tempRet0;
 $180 = (___muldi3(($32|0),($119|0),($28|0),($95|0))|0);
 $181 = tempRet0;
 $182 = (___muldi3(($33|0),($101|0),($28|0),($95|0))|0);
 $183 = tempRet0;
 $184 = (___muldi3(($32|0),($119|0),($18|0),($69|0))|0);
 $185 = tempRet0;
 $186 = (___muldi3(($33|0),($101|0),($18|0),($69|0))|0);
 $187 = tempRet0;
 $188 = (___muldi3(($33|0),($101|0),($20|0),($73|0))|0);
 $189 = tempRet0;
 $190 = (_i64Add(($158|0),($159|0),($36|0),($37|0))|0);
 $191 = tempRet0;
 $192 = (_i64Add(($190|0),($191|0),($148|0),($149|0))|0);
 $193 = tempRet0;
 $194 = (_i64Add(($192|0),($193|0),($134|0),($135|0))|0);
 $195 = tempRet0;
 $196 = (_i64Add(($194|0),($195|0),($120|0),($121|0))|0);
 $197 = tempRet0;
 $198 = (_i64Add(($196|0),($197|0),($102|0),($103|0))|0);
 $199 = tempRet0;
 $200 = (_i64Add(($46|0),($47|0),($78|0),($79|0))|0);
 $201 = tempRet0;
 $202 = (_i64Add(($50|0),($51|0),($80|0),($81|0))|0);
 $203 = tempRet0;
 $204 = (_i64Add(($84|0),($85|0),($104|0),($105|0))|0);
 $205 = tempRet0;
 $206 = (_i64Add(($204|0),($205|0),($54|0),($55|0))|0);
 $207 = tempRet0;
 $208 = (_i64Add(($206|0),($207|0),($178|0),($179|0))|0);
 $209 = tempRet0;
 $210 = (_i64Add(($208|0),($209|0),($174|0),($175|0))|0);
 $211 = tempRet0;
 $212 = (_i64Add(($210|0),($211|0),($166|0),($167|0))|0);
 $213 = tempRet0;
 $214 = (_i64Add(($198|0),($199|0),33554432,0)|0);
 $215 = tempRet0;
 $216 = (_bitshift64Ashr(($214|0),($215|0),26)|0);
 $217 = tempRet0;
 $218 = (_i64Add(($160|0),($161|0),($42|0),($43|0))|0);
 $219 = tempRet0;
 $220 = (_i64Add(($218|0),($219|0),($150|0),($151|0))|0);
 $221 = tempRet0;
 $222 = (_i64Add(($220|0),($221|0),($136|0),($137|0))|0);
 $223 = tempRet0;
 $224 = (_i64Add(($222|0),($223|0),($122|0),($123|0))|0);
 $225 = tempRet0;
 $226 = (_i64Add(($224|0),($225|0),($216|0),($217|0))|0);
 $227 = tempRet0;
 $228 = (_bitshift64Shl(($216|0),($217|0),26)|0);
 $229 = tempRet0;
 $230 = (_i64Subtract(($198|0),($199|0),($228|0),($229|0))|0);
 $231 = tempRet0;
 $232 = (_i64Add(($212|0),($213|0),33554432,0)|0);
 $233 = tempRet0;
 $234 = (_bitshift64Ashr(($232|0),($233|0),26)|0);
 $235 = tempRet0;
 $236 = (_i64Add(($86|0),($87|0),($108|0),($109|0))|0);
 $237 = tempRet0;
 $238 = (_i64Add(($236|0),($237|0),($58|0),($59|0))|0);
 $239 = tempRet0;
 $240 = (_i64Add(($238|0),($239|0),($180|0),($181|0))|0);
 $241 = tempRet0;
 $242 = (_i64Add(($240|0),($241|0),($176|0),($177|0))|0);
 $243 = tempRet0;
 $244 = (_i64Add(($242|0),($243|0),($234|0),($235|0))|0);
 $245 = tempRet0;
 $246 = (_bitshift64Shl(($234|0),($235|0),26)|0);
 $247 = tempRet0;
 $248 = (_i64Subtract(($212|0),($213|0),($246|0),($247|0))|0);
 $249 = tempRet0;
 $250 = (_i64Add(($226|0),($227|0),16777216,0)|0);
 $251 = tempRet0;
 $252 = (_bitshift64Ashr(($250|0),($251|0),25)|0);
 $253 = tempRet0;
 $254 = (_i64Add(($200|0),($201|0),($168|0),($169|0))|0);
 $255 = tempRet0;
 $256 = (_i64Add(($254|0),($255|0),($162|0),($163|0))|0);
 $257 = tempRet0;
 $258 = (_i64Add(($256|0),($257|0),($152|0),($153|0))|0);
 $259 = tempRet0;
 $260 = (_i64Add(($258|0),($259|0),($138|0),($139|0))|0);
 $261 = tempRet0;
 $262 = (_i64Add(($260|0),($261|0),($252|0),($253|0))|0);
 $263 = tempRet0;
 $264 = (_bitshift64Shl(($252|0),($253|0),25)|0);
 $265 = tempRet0;
 $266 = (_i64Subtract(($226|0),($227|0),($264|0),($265|0))|0);
 $267 = tempRet0;
 $268 = (_i64Add(($244|0),($245|0),16777216,0)|0);
 $269 = tempRet0;
 $270 = (_bitshift64Ashr(($268|0),($269|0),25)|0);
 $271 = tempRet0;
 $272 = (_i64Add(($124|0),($125|0),($110|0),($111|0))|0);
 $273 = tempRet0;
 $274 = (_i64Add(($272|0),($273|0),($90|0),($91|0))|0);
 $275 = tempRet0;
 $276 = (_i64Add(($274|0),($275|0),($62|0),($63|0))|0);
 $277 = tempRet0;
 $278 = (_i64Add(($276|0),($277|0),($184|0),($185|0))|0);
 $279 = tempRet0;
 $280 = (_i64Add(($278|0),($279|0),($182|0),($183|0))|0);
 $281 = tempRet0;
 $282 = (_i64Add(($280|0),($281|0),($270|0),($271|0))|0);
 $283 = tempRet0;
 $284 = (_bitshift64Shl(($270|0),($271|0),25)|0);
 $285 = tempRet0;
 $286 = (_i64Subtract(($244|0),($245|0),($284|0),($285|0))|0);
 $287 = tempRet0;
 $288 = (_i64Add(($262|0),($263|0),33554432,0)|0);
 $289 = tempRet0;
 $290 = (_bitshift64Ashr(($288|0),($289|0),26)|0);
 $291 = tempRet0;
 $292 = (_i64Add(($202|0),($203|0),($170|0),($171|0))|0);
 $293 = tempRet0;
 $294 = (_i64Add(($292|0),($293|0),($164|0),($165|0))|0);
 $295 = tempRet0;
 $296 = (_i64Add(($294|0),($295|0),($154|0),($155|0))|0);
 $297 = tempRet0;
 $298 = (_i64Add(($296|0),($297|0),($290|0),($291|0))|0);
 $299 = tempRet0;
 $300 = (_bitshift64Shl(($290|0),($291|0),26)|0);
 $301 = tempRet0;
 $302 = (_i64Subtract(($262|0),($263|0),($300|0),($301|0))|0);
 $303 = tempRet0;
 $304 = (_i64Add(($282|0),($283|0),33554432,0)|0);
 $305 = tempRet0;
 $306 = (_bitshift64Ashr(($304|0),($305|0),26)|0);
 $307 = tempRet0;
 $308 = (_i64Add(($112|0),($113|0),($126|0),($127|0))|0);
 $309 = tempRet0;
 $310 = (_i64Add(($308|0),($309|0),($92|0),($93|0))|0);
 $311 = tempRet0;
 $312 = (_i64Add(($310|0),($311|0),($66|0),($67|0))|0);
 $313 = tempRet0;
 $314 = (_i64Add(($312|0),($313|0),($186|0),($187|0))|0);
 $315 = tempRet0;
 $316 = (_i64Add(($314|0),($315|0),($306|0),($307|0))|0);
 $317 = tempRet0;
 $318 = (_bitshift64Shl(($306|0),($307|0),26)|0);
 $319 = tempRet0;
 $320 = (_i64Subtract(($282|0),($283|0),($318|0),($319|0))|0);
 $321 = tempRet0;
 $322 = (_i64Add(($298|0),($299|0),16777216,0)|0);
 $323 = tempRet0;
 $324 = (_bitshift64Ashr(($322|0),($323|0),25)|0);
 $325 = tempRet0;
 $326 = (_i64Add(($324|0),($325|0),($248|0),($249|0))|0);
 $327 = tempRet0;
 $328 = (_bitshift64Shl(($324|0),($325|0),25)|0);
 $329 = tempRet0;
 $330 = (_i64Subtract(($298|0),($299|0),($328|0),($329|0))|0);
 $331 = tempRet0;
 $332 = (_i64Add(($316|0),($317|0),16777216,0)|0);
 $333 = tempRet0;
 $334 = (_bitshift64Ashr(($332|0),($333|0),25)|0);
 $335 = tempRet0;
 $336 = (_i64Add(($114|0),($115|0),($140|0),($141|0))|0);
 $337 = tempRet0;
 $338 = (_i64Add(($336|0),($337|0),($128|0),($129|0))|0);
 $339 = tempRet0;
 $340 = (_i64Add(($338|0),($339|0),($96|0),($97|0))|0);
 $341 = tempRet0;
 $342 = (_i64Add(($340|0),($341|0),($70|0),($71|0))|0);
 $343 = tempRet0;
 $344 = (_i64Add(($342|0),($343|0),($188|0),($189|0))|0);
 $345 = tempRet0;
 $346 = (_i64Add(($344|0),($345|0),($334|0),($335|0))|0);
 $347 = tempRet0;
 $348 = (_bitshift64Shl(($334|0),($335|0),25)|0);
 $349 = tempRet0;
 $350 = (_i64Subtract(($316|0),($317|0),($348|0),($349|0))|0);
 $351 = tempRet0;
 $352 = (_i64Add(($326|0),($327|0),33554432,0)|0);
 $353 = tempRet0;
 $354 = (_bitshift64Ashr(($352|0),($353|0),26)|0);
 $355 = tempRet0;
 $356 = (_i64Add(($286|0),($287|0),($354|0),($355|0))|0);
 $357 = tempRet0;
 $358 = (_bitshift64Shl(($354|0),($355|0),26)|0);
 $359 = tempRet0;
 $360 = (_i64Subtract(($326|0),($327|0),($358|0),($359|0))|0);
 $361 = tempRet0;
 $362 = (_i64Add(($346|0),($347|0),33554432,0)|0);
 $363 = tempRet0;
 $364 = (_bitshift64Ashr(($362|0),($363|0),26)|0);
 $365 = tempRet0;
 $366 = (_i64Add(($130|0),($131|0),($144|0),($145|0))|0);
 $367 = tempRet0;
 $368 = (_i64Add(($366|0),($367|0),($116|0),($117|0))|0);
 $369 = tempRet0;
 $370 = (_i64Add(($368|0),($369|0),($98|0),($99|0))|0);
 $371 = tempRet0;
 $372 = (_i64Add(($370|0),($371|0),($74|0),($75|0))|0);
 $373 = tempRet0;
 $374 = (_i64Add(($372|0),($373|0),($364|0),($365|0))|0);
 $375 = tempRet0;
 $376 = (_bitshift64Shl(($364|0),($365|0),26)|0);
 $377 = tempRet0;
 $378 = (_i64Subtract(($346|0),($347|0),($376|0),($377|0))|0);
 $379 = tempRet0;
 $380 = (_i64Add(($374|0),($375|0),16777216,0)|0);
 $381 = tempRet0;
 $382 = (_bitshift64Ashr(($380|0),($381|0),25)|0);
 $383 = tempRet0;
 $384 = (___muldi3(($382|0),($383|0),19,0)|0);
 $385 = tempRet0;
 $386 = (_i64Add(($384|0),($385|0),($230|0),($231|0))|0);
 $387 = tempRet0;
 $388 = (_bitshift64Shl(($382|0),($383|0),25)|0);
 $389 = tempRet0;
 $390 = (_i64Subtract(($374|0),($375|0),($388|0),($389|0))|0);
 $391 = tempRet0;
 $392 = (_i64Add(($386|0),($387|0),33554432,0)|0);
 $393 = tempRet0;
 $394 = (_bitshift64Ashr(($392|0),($393|0),26)|0);
 $395 = tempRet0;
 $396 = (_i64Add(($266|0),($267|0),($394|0),($395|0))|0);
 $397 = tempRet0;
 $398 = (_bitshift64Shl(($394|0),($395|0),26)|0);
 $399 = tempRet0;
 $400 = (_i64Subtract(($386|0),($387|0),($398|0),($399|0))|0);
 $401 = tempRet0;
 HEAP32[$0>>2] = $400;
 $402 = ((($0)) + 4|0);
 HEAP32[$402>>2] = $396;
 $403 = ((($0)) + 8|0);
 HEAP32[$403>>2] = $302;
 $404 = ((($0)) + 12|0);
 HEAP32[$404>>2] = $330;
 $405 = ((($0)) + 16|0);
 HEAP32[$405>>2] = $360;
 $406 = ((($0)) + 20|0);
 HEAP32[$406>>2] = $356;
 $407 = ((($0)) + 24|0);
 HEAP32[$407>>2] = $320;
 $408 = ((($0)) + 28|0);
 HEAP32[$408>>2] = $350;
 $409 = ((($0)) + 32|0);
 HEAP32[$409>>2] = $378;
 $410 = ((($0)) + 36|0);
 HEAP32[$410>>2] = $390;
 return;
}
function _crypto_sign_ed25519_ref10_fe_sq2($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0, $113 = 0, $114 = 0, $115 = 0, $116 = 0, $117 = 0;
 var $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0, $133 = 0, $134 = 0, $135 = 0;
 var $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0, $15 = 0, $150 = 0, $151 = 0, $152 = 0, $153 = 0;
 var $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $159 = 0, $16 = 0, $160 = 0, $161 = 0, $162 = 0, $163 = 0, $164 = 0, $165 = 0, $166 = 0, $167 = 0, $168 = 0, $169 = 0, $17 = 0, $170 = 0, $171 = 0;
 var $172 = 0, $173 = 0, $174 = 0, $175 = 0, $176 = 0, $177 = 0, $178 = 0, $179 = 0, $18 = 0, $180 = 0, $181 = 0, $182 = 0, $183 = 0, $184 = 0, $185 = 0, $186 = 0, $187 = 0, $188 = 0, $189 = 0, $19 = 0;
 var $190 = 0, $191 = 0, $192 = 0, $193 = 0, $194 = 0, $195 = 0, $196 = 0, $197 = 0, $198 = 0, $199 = 0, $2 = 0, $20 = 0, $200 = 0, $201 = 0, $202 = 0, $203 = 0, $204 = 0, $205 = 0, $206 = 0, $207 = 0;
 var $208 = 0, $209 = 0, $21 = 0, $210 = 0, $211 = 0, $212 = 0, $213 = 0, $214 = 0, $215 = 0, $216 = 0, $217 = 0, $218 = 0, $219 = 0, $22 = 0, $220 = 0, $221 = 0, $222 = 0, $223 = 0, $224 = 0, $225 = 0;
 var $226 = 0, $227 = 0, $228 = 0, $229 = 0, $23 = 0, $230 = 0, $231 = 0, $232 = 0, $233 = 0, $234 = 0, $235 = 0, $236 = 0, $237 = 0, $238 = 0, $239 = 0, $24 = 0, $240 = 0, $241 = 0, $242 = 0, $243 = 0;
 var $244 = 0, $245 = 0, $246 = 0, $247 = 0, $248 = 0, $249 = 0, $25 = 0, $250 = 0, $251 = 0, $252 = 0, $253 = 0, $254 = 0, $255 = 0, $256 = 0, $257 = 0, $258 = 0, $259 = 0, $26 = 0, $260 = 0, $261 = 0;
 var $262 = 0, $263 = 0, $264 = 0, $265 = 0, $266 = 0, $267 = 0, $268 = 0, $269 = 0, $27 = 0, $270 = 0, $271 = 0, $272 = 0, $273 = 0, $274 = 0, $275 = 0, $276 = 0, $277 = 0, $278 = 0, $279 = 0, $28 = 0;
 var $280 = 0, $281 = 0, $282 = 0, $283 = 0, $284 = 0, $285 = 0, $286 = 0, $287 = 0, $288 = 0, $289 = 0, $29 = 0, $290 = 0, $291 = 0, $292 = 0, $293 = 0, $294 = 0, $295 = 0, $296 = 0, $297 = 0, $298 = 0;
 var $299 = 0, $3 = 0, $30 = 0, $300 = 0, $301 = 0, $302 = 0, $303 = 0, $304 = 0, $305 = 0, $306 = 0, $307 = 0, $308 = 0, $309 = 0, $31 = 0, $310 = 0, $311 = 0, $312 = 0, $313 = 0, $314 = 0, $315 = 0;
 var $316 = 0, $317 = 0, $318 = 0, $319 = 0, $32 = 0, $320 = 0, $321 = 0, $322 = 0, $323 = 0, $324 = 0, $325 = 0, $326 = 0, $327 = 0, $328 = 0, $329 = 0, $33 = 0, $330 = 0, $331 = 0, $332 = 0, $333 = 0;
 var $334 = 0, $335 = 0, $336 = 0, $337 = 0, $338 = 0, $339 = 0, $34 = 0, $340 = 0, $341 = 0, $342 = 0, $343 = 0, $344 = 0, $345 = 0, $346 = 0, $347 = 0, $348 = 0, $349 = 0, $35 = 0, $350 = 0, $351 = 0;
 var $352 = 0, $353 = 0, $354 = 0, $355 = 0, $356 = 0, $357 = 0, $358 = 0, $359 = 0, $36 = 0, $360 = 0, $361 = 0, $362 = 0, $363 = 0, $364 = 0, $365 = 0, $366 = 0, $367 = 0, $368 = 0, $369 = 0, $37 = 0;
 var $370 = 0, $371 = 0, $372 = 0, $373 = 0, $374 = 0, $375 = 0, $376 = 0, $377 = 0, $378 = 0, $379 = 0, $38 = 0, $380 = 0, $381 = 0, $382 = 0, $383 = 0, $384 = 0, $385 = 0, $386 = 0, $387 = 0, $388 = 0;
 var $389 = 0, $39 = 0, $390 = 0, $391 = 0, $392 = 0, $393 = 0, $394 = 0, $395 = 0, $396 = 0, $397 = 0, $398 = 0, $399 = 0, $4 = 0, $40 = 0, $400 = 0, $401 = 0, $402 = 0, $403 = 0, $404 = 0, $405 = 0;
 var $406 = 0, $407 = 0, $408 = 0, $409 = 0, $41 = 0, $410 = 0, $411 = 0, $412 = 0, $413 = 0, $414 = 0, $415 = 0, $416 = 0, $417 = 0, $418 = 0, $419 = 0, $42 = 0, $420 = 0, $421 = 0, $422 = 0, $423 = 0;
 var $424 = 0, $425 = 0, $426 = 0, $427 = 0, $428 = 0, $429 = 0, $43 = 0, $430 = 0, $44 = 0, $45 = 0, $46 = 0, $47 = 0, $48 = 0, $49 = 0, $5 = 0, $50 = 0, $51 = 0, $52 = 0, $53 = 0, $54 = 0;
 var $55 = 0, $56 = 0, $57 = 0, $58 = 0, $59 = 0, $6 = 0, $60 = 0, $61 = 0, $62 = 0, $63 = 0, $64 = 0, $65 = 0, $66 = 0, $67 = 0, $68 = 0, $69 = 0, $7 = 0, $70 = 0, $71 = 0, $72 = 0;
 var $73 = 0, $74 = 0, $75 = 0, $76 = 0, $77 = 0, $78 = 0, $79 = 0, $8 = 0, $80 = 0, $81 = 0, $82 = 0, $83 = 0, $84 = 0, $85 = 0, $86 = 0, $87 = 0, $88 = 0, $89 = 0, $9 = 0, $90 = 0;
 var $91 = 0, $92 = 0, $93 = 0, $94 = 0, $95 = 0, $96 = 0, $97 = 0, $98 = 0, $99 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = HEAP32[$1>>2]|0;
 $3 = ((($1)) + 4|0);
 $4 = HEAP32[$3>>2]|0;
 $5 = ((($1)) + 8|0);
 $6 = HEAP32[$5>>2]|0;
 $7 = ((($1)) + 12|0);
 $8 = HEAP32[$7>>2]|0;
 $9 = ((($1)) + 16|0);
 $10 = HEAP32[$9>>2]|0;
 $11 = ((($1)) + 20|0);
 $12 = HEAP32[$11>>2]|0;
 $13 = ((($1)) + 24|0);
 $14 = HEAP32[$13>>2]|0;
 $15 = ((($1)) + 28|0);
 $16 = HEAP32[$15>>2]|0;
 $17 = ((($1)) + 32|0);
 $18 = HEAP32[$17>>2]|0;
 $19 = ((($1)) + 36|0);
 $20 = HEAP32[$19>>2]|0;
 $21 = $2 << 1;
 $22 = $4 << 1;
 $23 = $6 << 1;
 $24 = $8 << 1;
 $25 = $10 << 1;
 $26 = $12 << 1;
 $27 = $14 << 1;
 $28 = $16 << 1;
 $29 = ($12*38)|0;
 $30 = ($14*19)|0;
 $31 = ($16*38)|0;
 $32 = ($18*19)|0;
 $33 = ($20*38)|0;
 $34 = ($2|0)<(0);
 $35 = $34 << 31 >> 31;
 $36 = (___muldi3(($2|0),($35|0),($2|0),($35|0))|0);
 $37 = tempRet0;
 $38 = ($21|0)<(0);
 $39 = $38 << 31 >> 31;
 $40 = ($4|0)<(0);
 $41 = $40 << 31 >> 31;
 $42 = (___muldi3(($21|0),($39|0),($4|0),($41|0))|0);
 $43 = tempRet0;
 $44 = ($6|0)<(0);
 $45 = $44 << 31 >> 31;
 $46 = (___muldi3(($6|0),($45|0),($21|0),($39|0))|0);
 $47 = tempRet0;
 $48 = ($8|0)<(0);
 $49 = $48 << 31 >> 31;
 $50 = (___muldi3(($8|0),($49|0),($21|0),($39|0))|0);
 $51 = tempRet0;
 $52 = ($10|0)<(0);
 $53 = $52 << 31 >> 31;
 $54 = (___muldi3(($10|0),($53|0),($21|0),($39|0))|0);
 $55 = tempRet0;
 $56 = ($12|0)<(0);
 $57 = $56 << 31 >> 31;
 $58 = (___muldi3(($12|0),($57|0),($21|0),($39|0))|0);
 $59 = tempRet0;
 $60 = ($14|0)<(0);
 $61 = $60 << 31 >> 31;
 $62 = (___muldi3(($14|0),($61|0),($21|0),($39|0))|0);
 $63 = tempRet0;
 $64 = ($16|0)<(0);
 $65 = $64 << 31 >> 31;
 $66 = (___muldi3(($16|0),($65|0),($21|0),($39|0))|0);
 $67 = tempRet0;
 $68 = ($18|0)<(0);
 $69 = $68 << 31 >> 31;
 $70 = (___muldi3(($18|0),($69|0),($21|0),($39|0))|0);
 $71 = tempRet0;
 $72 = ($20|0)<(0);
 $73 = $72 << 31 >> 31;
 $74 = (___muldi3(($20|0),($73|0),($21|0),($39|0))|0);
 $75 = tempRet0;
 $76 = ($22|0)<(0);
 $77 = $76 << 31 >> 31;
 $78 = (___muldi3(($22|0),($77|0),($4|0),($41|0))|0);
 $79 = tempRet0;
 $80 = (___muldi3(($22|0),($77|0),($6|0),($45|0))|0);
 $81 = tempRet0;
 $82 = ($24|0)<(0);
 $83 = $82 << 31 >> 31;
 $84 = (___muldi3(($24|0),($83|0),($22|0),($77|0))|0);
 $85 = tempRet0;
 $86 = (___muldi3(($10|0),($53|0),($22|0),($77|0))|0);
 $87 = tempRet0;
 $88 = ($26|0)<(0);
 $89 = $88 << 31 >> 31;
 $90 = (___muldi3(($26|0),($89|0),($22|0),($77|0))|0);
 $91 = tempRet0;
 $92 = (___muldi3(($14|0),($61|0),($22|0),($77|0))|0);
 $93 = tempRet0;
 $94 = ($28|0)<(0);
 $95 = $94 << 31 >> 31;
 $96 = (___muldi3(($28|0),($95|0),($22|0),($77|0))|0);
 $97 = tempRet0;
 $98 = (___muldi3(($18|0),($69|0),($22|0),($77|0))|0);
 $99 = tempRet0;
 $100 = ($33|0)<(0);
 $101 = $100 << 31 >> 31;
 $102 = (___muldi3(($33|0),($101|0),($22|0),($77|0))|0);
 $103 = tempRet0;
 $104 = (___muldi3(($6|0),($45|0),($6|0),($45|0))|0);
 $105 = tempRet0;
 $106 = ($23|0)<(0);
 $107 = $106 << 31 >> 31;
 $108 = (___muldi3(($23|0),($107|0),($8|0),($49|0))|0);
 $109 = tempRet0;
 $110 = (___muldi3(($10|0),($53|0),($23|0),($107|0))|0);
 $111 = tempRet0;
 $112 = (___muldi3(($12|0),($57|0),($23|0),($107|0))|0);
 $113 = tempRet0;
 $114 = (___muldi3(($14|0),($61|0),($23|0),($107|0))|0);
 $115 = tempRet0;
 $116 = (___muldi3(($16|0),($65|0),($23|0),($107|0))|0);
 $117 = tempRet0;
 $118 = ($32|0)<(0);
 $119 = $118 << 31 >> 31;
 $120 = (___muldi3(($32|0),($119|0),($23|0),($107|0))|0);
 $121 = tempRet0;
 $122 = (___muldi3(($33|0),($101|0),($6|0),($45|0))|0);
 $123 = tempRet0;
 $124 = (___muldi3(($24|0),($83|0),($8|0),($49|0))|0);
 $125 = tempRet0;
 $126 = (___muldi3(($24|0),($83|0),($10|0),($53|0))|0);
 $127 = tempRet0;
 $128 = (___muldi3(($26|0),($89|0),($24|0),($83|0))|0);
 $129 = tempRet0;
 $130 = (___muldi3(($14|0),($61|0),($24|0),($83|0))|0);
 $131 = tempRet0;
 $132 = ($31|0)<(0);
 $133 = $132 << 31 >> 31;
 $134 = (___muldi3(($31|0),($133|0),($24|0),($83|0))|0);
 $135 = tempRet0;
 $136 = (___muldi3(($32|0),($119|0),($24|0),($83|0))|0);
 $137 = tempRet0;
 $138 = (___muldi3(($33|0),($101|0),($24|0),($83|0))|0);
 $139 = tempRet0;
 $140 = (___muldi3(($10|0),($53|0),($10|0),($53|0))|0);
 $141 = tempRet0;
 $142 = ($25|0)<(0);
 $143 = $142 << 31 >> 31;
 $144 = (___muldi3(($25|0),($143|0),($12|0),($57|0))|0);
 $145 = tempRet0;
 $146 = ($30|0)<(0);
 $147 = $146 << 31 >> 31;
 $148 = (___muldi3(($30|0),($147|0),($25|0),($143|0))|0);
 $149 = tempRet0;
 $150 = (___muldi3(($31|0),($133|0),($10|0),($53|0))|0);
 $151 = tempRet0;
 $152 = (___muldi3(($32|0),($119|0),($25|0),($143|0))|0);
 $153 = tempRet0;
 $154 = (___muldi3(($33|0),($101|0),($10|0),($53|0))|0);
 $155 = tempRet0;
 $156 = ($29|0)<(0);
 $157 = $156 << 31 >> 31;
 $158 = (___muldi3(($29|0),($157|0),($12|0),($57|0))|0);
 $159 = tempRet0;
 $160 = (___muldi3(($30|0),($147|0),($26|0),($89|0))|0);
 $161 = tempRet0;
 $162 = (___muldi3(($31|0),($133|0),($26|0),($89|0))|0);
 $163 = tempRet0;
 $164 = (___muldi3(($32|0),($119|0),($26|0),($89|0))|0);
 $165 = tempRet0;
 $166 = (___muldi3(($33|0),($101|0),($26|0),($89|0))|0);
 $167 = tempRet0;
 $168 = (___muldi3(($30|0),($147|0),($14|0),($61|0))|0);
 $169 = tempRet0;
 $170 = (___muldi3(($31|0),($133|0),($14|0),($61|0))|0);
 $171 = tempRet0;
 $172 = ($27|0)<(0);
 $173 = $172 << 31 >> 31;
 $174 = (___muldi3(($32|0),($119|0),($27|0),($173|0))|0);
 $175 = tempRet0;
 $176 = (___muldi3(($33|0),($101|0),($14|0),($61|0))|0);
 $177 = tempRet0;
 $178 = (___muldi3(($31|0),($133|0),($16|0),($65|0))|0);
 $179 = tempRet0;
 $180 = (___muldi3(($32|0),($119|0),($28|0),($95|0))|0);
 $181 = tempRet0;
 $182 = (___muldi3(($33|0),($101|0),($28|0),($95|0))|0);
 $183 = tempRet0;
 $184 = (___muldi3(($32|0),($119|0),($18|0),($69|0))|0);
 $185 = tempRet0;
 $186 = (___muldi3(($33|0),($101|0),($18|0),($69|0))|0);
 $187 = tempRet0;
 $188 = (___muldi3(($33|0),($101|0),($20|0),($73|0))|0);
 $189 = tempRet0;
 $190 = (_i64Add(($158|0),($159|0),($36|0),($37|0))|0);
 $191 = tempRet0;
 $192 = (_i64Add(($190|0),($191|0),($148|0),($149|0))|0);
 $193 = tempRet0;
 $194 = (_i64Add(($192|0),($193|0),($134|0),($135|0))|0);
 $195 = tempRet0;
 $196 = (_i64Add(($194|0),($195|0),($120|0),($121|0))|0);
 $197 = tempRet0;
 $198 = (_i64Add(($196|0),($197|0),($102|0),($103|0))|0);
 $199 = tempRet0;
 $200 = (_i64Add(($160|0),($161|0),($42|0),($43|0))|0);
 $201 = tempRet0;
 $202 = (_i64Add(($200|0),($201|0),($150|0),($151|0))|0);
 $203 = tempRet0;
 $204 = (_i64Add(($202|0),($203|0),($136|0),($137|0))|0);
 $205 = tempRet0;
 $206 = (_i64Add(($204|0),($205|0),($122|0),($123|0))|0);
 $207 = tempRet0;
 $208 = (_i64Add(($46|0),($47|0),($78|0),($79|0))|0);
 $209 = tempRet0;
 $210 = (_i64Add(($208|0),($209|0),($168|0),($169|0))|0);
 $211 = tempRet0;
 $212 = (_i64Add(($210|0),($211|0),($162|0),($163|0))|0);
 $213 = tempRet0;
 $214 = (_i64Add(($212|0),($213|0),($152|0),($153|0))|0);
 $215 = tempRet0;
 $216 = (_i64Add(($214|0),($215|0),($138|0),($139|0))|0);
 $217 = tempRet0;
 $218 = (_i64Add(($50|0),($51|0),($80|0),($81|0))|0);
 $219 = tempRet0;
 $220 = (_i64Add(($218|0),($219|0),($170|0),($171|0))|0);
 $221 = tempRet0;
 $222 = (_i64Add(($220|0),($221|0),($164|0),($165|0))|0);
 $223 = tempRet0;
 $224 = (_i64Add(($222|0),($223|0),($154|0),($155|0))|0);
 $225 = tempRet0;
 $226 = (_i64Add(($84|0),($85|0),($104|0),($105|0))|0);
 $227 = tempRet0;
 $228 = (_i64Add(($226|0),($227|0),($54|0),($55|0))|0);
 $229 = tempRet0;
 $230 = (_i64Add(($228|0),($229|0),($178|0),($179|0))|0);
 $231 = tempRet0;
 $232 = (_i64Add(($230|0),($231|0),($174|0),($175|0))|0);
 $233 = tempRet0;
 $234 = (_i64Add(($232|0),($233|0),($166|0),($167|0))|0);
 $235 = tempRet0;
 $236 = (_i64Add(($86|0),($87|0),($108|0),($109|0))|0);
 $237 = tempRet0;
 $238 = (_i64Add(($236|0),($237|0),($58|0),($59|0))|0);
 $239 = tempRet0;
 $240 = (_i64Add(($238|0),($239|0),($180|0),($181|0))|0);
 $241 = tempRet0;
 $242 = (_i64Add(($240|0),($241|0),($176|0),($177|0))|0);
 $243 = tempRet0;
 $244 = (_i64Add(($124|0),($125|0),($110|0),($111|0))|0);
 $245 = tempRet0;
 $246 = (_i64Add(($244|0),($245|0),($90|0),($91|0))|0);
 $247 = tempRet0;
 $248 = (_i64Add(($246|0),($247|0),($62|0),($63|0))|0);
 $249 = tempRet0;
 $250 = (_i64Add(($248|0),($249|0),($184|0),($185|0))|0);
 $251 = tempRet0;
 $252 = (_i64Add(($250|0),($251|0),($182|0),($183|0))|0);
 $253 = tempRet0;
 $254 = (_i64Add(($112|0),($113|0),($126|0),($127|0))|0);
 $255 = tempRet0;
 $256 = (_i64Add(($254|0),($255|0),($92|0),($93|0))|0);
 $257 = tempRet0;
 $258 = (_i64Add(($256|0),($257|0),($66|0),($67|0))|0);
 $259 = tempRet0;
 $260 = (_i64Add(($258|0),($259|0),($186|0),($187|0))|0);
 $261 = tempRet0;
 $262 = (_i64Add(($114|0),($115|0),($140|0),($141|0))|0);
 $263 = tempRet0;
 $264 = (_i64Add(($262|0),($263|0),($128|0),($129|0))|0);
 $265 = tempRet0;
 $266 = (_i64Add(($264|0),($265|0),($96|0),($97|0))|0);
 $267 = tempRet0;
 $268 = (_i64Add(($266|0),($267|0),($70|0),($71|0))|0);
 $269 = tempRet0;
 $270 = (_i64Add(($268|0),($269|0),($188|0),($189|0))|0);
 $271 = tempRet0;
 $272 = (_i64Add(($130|0),($131|0),($144|0),($145|0))|0);
 $273 = tempRet0;
 $274 = (_i64Add(($272|0),($273|0),($116|0),($117|0))|0);
 $275 = tempRet0;
 $276 = (_i64Add(($274|0),($275|0),($98|0),($99|0))|0);
 $277 = tempRet0;
 $278 = (_i64Add(($276|0),($277|0),($74|0),($75|0))|0);
 $279 = tempRet0;
 $280 = (_bitshift64Shl(($198|0),($199|0),1)|0);
 $281 = tempRet0;
 $282 = (_bitshift64Shl(($206|0),($207|0),1)|0);
 $283 = tempRet0;
 $284 = (_bitshift64Shl(($216|0),($217|0),1)|0);
 $285 = tempRet0;
 $286 = (_bitshift64Shl(($224|0),($225|0),1)|0);
 $287 = tempRet0;
 $288 = (_bitshift64Shl(($234|0),($235|0),1)|0);
 $289 = tempRet0;
 $290 = (_bitshift64Shl(($242|0),($243|0),1)|0);
 $291 = tempRet0;
 $292 = (_bitshift64Shl(($252|0),($253|0),1)|0);
 $293 = tempRet0;
 $294 = (_bitshift64Shl(($260|0),($261|0),1)|0);
 $295 = tempRet0;
 $296 = (_bitshift64Shl(($270|0),($271|0),1)|0);
 $297 = tempRet0;
 $298 = (_bitshift64Shl(($278|0),($279|0),1)|0);
 $299 = tempRet0;
 $300 = (_i64Add(($280|0),($281|0),33554432,0)|0);
 $301 = tempRet0;
 $302 = (_bitshift64Ashr(($300|0),($301|0),26)|0);
 $303 = tempRet0;
 $304 = (_i64Add(($302|0),($303|0),($282|0),($283|0))|0);
 $305 = tempRet0;
 $306 = (_bitshift64Shl(($302|0),($303|0),26)|0);
 $307 = tempRet0;
 $308 = (_i64Subtract(($280|0),($281|0),($306|0),($307|0))|0);
 $309 = tempRet0;
 $310 = (_i64Add(($288|0),($289|0),33554432,0)|0);
 $311 = tempRet0;
 $312 = (_bitshift64Ashr(($310|0),($311|0),26)|0);
 $313 = tempRet0;
 $314 = (_i64Add(($312|0),($313|0),($290|0),($291|0))|0);
 $315 = tempRet0;
 $316 = (_bitshift64Shl(($312|0),($313|0),26)|0);
 $317 = tempRet0;
 $318 = (_i64Subtract(($288|0),($289|0),($316|0),($317|0))|0);
 $319 = tempRet0;
 $320 = (_i64Add(($304|0),($305|0),16777216,0)|0);
 $321 = tempRet0;
 $322 = (_bitshift64Ashr(($320|0),($321|0),25)|0);
 $323 = tempRet0;
 $324 = (_i64Add(($322|0),($323|0),($284|0),($285|0))|0);
 $325 = tempRet0;
 $326 = (_bitshift64Shl(($322|0),($323|0),25)|0);
 $327 = tempRet0;
 $328 = (_i64Subtract(($304|0),($305|0),($326|0),($327|0))|0);
 $329 = tempRet0;
 $330 = (_i64Add(($314|0),($315|0),16777216,0)|0);
 $331 = tempRet0;
 $332 = (_bitshift64Ashr(($330|0),($331|0),25)|0);
 $333 = tempRet0;
 $334 = (_i64Add(($332|0),($333|0),($292|0),($293|0))|0);
 $335 = tempRet0;
 $336 = (_bitshift64Shl(($332|0),($333|0),25)|0);
 $337 = tempRet0;
 $338 = (_i64Subtract(($314|0),($315|0),($336|0),($337|0))|0);
 $339 = tempRet0;
 $340 = (_i64Add(($324|0),($325|0),33554432,0)|0);
 $341 = tempRet0;
 $342 = (_bitshift64Ashr(($340|0),($341|0),26)|0);
 $343 = tempRet0;
 $344 = (_i64Add(($342|0),($343|0),($286|0),($287|0))|0);
 $345 = tempRet0;
 $346 = (_bitshift64Shl(($342|0),($343|0),26)|0);
 $347 = tempRet0;
 $348 = (_i64Subtract(($324|0),($325|0),($346|0),($347|0))|0);
 $349 = tempRet0;
 $350 = (_i64Add(($334|0),($335|0),33554432,0)|0);
 $351 = tempRet0;
 $352 = (_bitshift64Ashr(($350|0),($351|0),26)|0);
 $353 = tempRet0;
 $354 = (_i64Add(($352|0),($353|0),($294|0),($295|0))|0);
 $355 = tempRet0;
 $356 = (_bitshift64Shl(($352|0),($353|0),26)|0);
 $357 = tempRet0;
 $358 = (_i64Subtract(($334|0),($335|0),($356|0),($357|0))|0);
 $359 = tempRet0;
 $360 = (_i64Add(($344|0),($345|0),16777216,0)|0);
 $361 = tempRet0;
 $362 = (_bitshift64Ashr(($360|0),($361|0),25)|0);
 $363 = tempRet0;
 $364 = (_i64Add(($362|0),($363|0),($318|0),($319|0))|0);
 $365 = tempRet0;
 $366 = (_bitshift64Shl(($362|0),($363|0),25)|0);
 $367 = tempRet0;
 $368 = (_i64Subtract(($344|0),($345|0),($366|0),($367|0))|0);
 $369 = tempRet0;
 $370 = (_i64Add(($354|0),($355|0),16777216,0)|0);
 $371 = tempRet0;
 $372 = (_bitshift64Ashr(($370|0),($371|0),25)|0);
 $373 = tempRet0;
 $374 = (_i64Add(($372|0),($373|0),($296|0),($297|0))|0);
 $375 = tempRet0;
 $376 = (_bitshift64Shl(($372|0),($373|0),25)|0);
 $377 = tempRet0;
 $378 = (_i64Subtract(($354|0),($355|0),($376|0),($377|0))|0);
 $379 = tempRet0;
 $380 = (_i64Add(($364|0),($365|0),33554432,0)|0);
 $381 = tempRet0;
 $382 = (_bitshift64Ashr(($380|0),($381|0),26)|0);
 $383 = tempRet0;
 $384 = (_i64Add(($338|0),($339|0),($382|0),($383|0))|0);
 $385 = tempRet0;
 $386 = (_bitshift64Shl(($382|0),($383|0),26)|0);
 $387 = tempRet0;
 $388 = (_i64Subtract(($364|0),($365|0),($386|0),($387|0))|0);
 $389 = tempRet0;
 $390 = (_i64Add(($374|0),($375|0),33554432,0)|0);
 $391 = tempRet0;
 $392 = (_bitshift64Ashr(($390|0),($391|0),26)|0);
 $393 = tempRet0;
 $394 = (_i64Add(($392|0),($393|0),($298|0),($299|0))|0);
 $395 = tempRet0;
 $396 = (_bitshift64Shl(($392|0),($393|0),26)|0);
 $397 = tempRet0;
 $398 = (_i64Subtract(($374|0),($375|0),($396|0),($397|0))|0);
 $399 = tempRet0;
 $400 = (_i64Add(($394|0),($395|0),16777216,0)|0);
 $401 = tempRet0;
 $402 = (_bitshift64Ashr(($400|0),($401|0),25)|0);
 $403 = tempRet0;
 $404 = (___muldi3(($402|0),($403|0),19,0)|0);
 $405 = tempRet0;
 $406 = (_i64Add(($404|0),($405|0),($308|0),($309|0))|0);
 $407 = tempRet0;
 $408 = (_bitshift64Shl(($402|0),($403|0),25)|0);
 $409 = tempRet0;
 $410 = (_i64Subtract(($394|0),($395|0),($408|0),($409|0))|0);
 $411 = tempRet0;
 $412 = (_i64Add(($406|0),($407|0),33554432,0)|0);
 $413 = tempRet0;
 $414 = (_bitshift64Ashr(($412|0),($413|0),26)|0);
 $415 = tempRet0;
 $416 = (_i64Add(($328|0),($329|0),($414|0),($415|0))|0);
 $417 = tempRet0;
 $418 = (_bitshift64Shl(($414|0),($415|0),26)|0);
 $419 = tempRet0;
 $420 = (_i64Subtract(($406|0),($407|0),($418|0),($419|0))|0);
 $421 = tempRet0;
 HEAP32[$0>>2] = $420;
 $422 = ((($0)) + 4|0);
 HEAP32[$422>>2] = $416;
 $423 = ((($0)) + 8|0);
 HEAP32[$423>>2] = $348;
 $424 = ((($0)) + 12|0);
 HEAP32[$424>>2] = $368;
 $425 = ((($0)) + 16|0);
 HEAP32[$425>>2] = $388;
 $426 = ((($0)) + 20|0);
 HEAP32[$426>>2] = $384;
 $427 = ((($0)) + 24|0);
 HEAP32[$427>>2] = $358;
 $428 = ((($0)) + 28|0);
 HEAP32[$428>>2] = $378;
 $429 = ((($0)) + 32|0);
 HEAP32[$429>>2] = $398;
 $430 = ((($0)) + 36|0);
 HEAP32[$430>>2] = $410;
 return;
}
function _crypto_sign_ed25519_ref10_fe_sub($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0, $29 = 0;
 var $3 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $4 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0, $46 = 0, $47 = 0;
 var $48 = 0, $49 = 0, $5 = 0, $50 = 0, $51 = 0, $52 = 0, $53 = 0, $54 = 0, $55 = 0, $56 = 0, $57 = 0, $58 = 0, $59 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $3 = HEAP32[$1>>2]|0;
 $4 = ((($1)) + 4|0);
 $5 = HEAP32[$4>>2]|0;
 $6 = ((($1)) + 8|0);
 $7 = HEAP32[$6>>2]|0;
 $8 = ((($1)) + 12|0);
 $9 = HEAP32[$8>>2]|0;
 $10 = ((($1)) + 16|0);
 $11 = HEAP32[$10>>2]|0;
 $12 = ((($1)) + 20|0);
 $13 = HEAP32[$12>>2]|0;
 $14 = ((($1)) + 24|0);
 $15 = HEAP32[$14>>2]|0;
 $16 = ((($1)) + 28|0);
 $17 = HEAP32[$16>>2]|0;
 $18 = ((($1)) + 32|0);
 $19 = HEAP32[$18>>2]|0;
 $20 = ((($1)) + 36|0);
 $21 = HEAP32[$20>>2]|0;
 $22 = HEAP32[$2>>2]|0;
 $23 = ((($2)) + 4|0);
 $24 = HEAP32[$23>>2]|0;
 $25 = ((($2)) + 8|0);
 $26 = HEAP32[$25>>2]|0;
 $27 = ((($2)) + 12|0);
 $28 = HEAP32[$27>>2]|0;
 $29 = ((($2)) + 16|0);
 $30 = HEAP32[$29>>2]|0;
 $31 = ((($2)) + 20|0);
 $32 = HEAP32[$31>>2]|0;
 $33 = ((($2)) + 24|0);
 $34 = HEAP32[$33>>2]|0;
 $35 = ((($2)) + 28|0);
 $36 = HEAP32[$35>>2]|0;
 $37 = ((($2)) + 32|0);
 $38 = HEAP32[$37>>2]|0;
 $39 = ((($2)) + 36|0);
 $40 = HEAP32[$39>>2]|0;
 $41 = (($3) - ($22))|0;
 $42 = (($5) - ($24))|0;
 $43 = (($7) - ($26))|0;
 $44 = (($9) - ($28))|0;
 $45 = (($11) - ($30))|0;
 $46 = (($13) - ($32))|0;
 $47 = (($15) - ($34))|0;
 $48 = (($17) - ($36))|0;
 $49 = (($19) - ($38))|0;
 $50 = (($21) - ($40))|0;
 HEAP32[$0>>2] = $41;
 $51 = ((($0)) + 4|0);
 HEAP32[$51>>2] = $42;
 $52 = ((($0)) + 8|0);
 HEAP32[$52>>2] = $43;
 $53 = ((($0)) + 12|0);
 HEAP32[$53>>2] = $44;
 $54 = ((($0)) + 16|0);
 HEAP32[$54>>2] = $45;
 $55 = ((($0)) + 20|0);
 HEAP32[$55>>2] = $46;
 $56 = ((($0)) + 24|0);
 HEAP32[$56>>2] = $47;
 $57 = ((($0)) + 28|0);
 HEAP32[$57>>2] = $48;
 $58 = ((($0)) + 32|0);
 HEAP32[$58>>2] = $49;
 $59 = ((($0)) + 36|0);
 HEAP32[$59>>2] = $50;
 return;
}
function _crypto_sign_ed25519_ref10_fe_tobytes($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0, $113 = 0, $114 = 0, $115 = 0, $116 = 0, $117 = 0;
 var $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0, $133 = 0, $134 = 0, $135 = 0;
 var $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0, $15 = 0, $150 = 0, $151 = 0, $152 = 0, $153 = 0;
 var $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $159 = 0, $16 = 0, $160 = 0, $161 = 0, $162 = 0, $163 = 0, $164 = 0, $165 = 0, $166 = 0, $167 = 0, $168 = 0, $169 = 0, $17 = 0, $170 = 0, $171 = 0;
 var $172 = 0, $173 = 0, $174 = 0, $175 = 0, $176 = 0, $177 = 0, $178 = 0, $179 = 0, $18 = 0, $180 = 0, $181 = 0, $182 = 0, $183 = 0, $184 = 0, $185 = 0, $186 = 0, $187 = 0, $188 = 0, $189 = 0, $19 = 0;
 var $190 = 0, $191 = 0, $2 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0, $29 = 0, $3 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0;
 var $36 = 0, $37 = 0, $38 = 0, $39 = 0, $4 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0, $46 = 0, $47 = 0, $48 = 0, $49 = 0, $5 = 0, $50 = 0, $51 = 0, $52 = 0, $53 = 0;
 var $54 = 0, $55 = 0, $56 = 0, $57 = 0, $58 = 0, $59 = 0, $6 = 0, $60 = 0, $61 = 0, $62 = 0, $63 = 0, $64 = 0, $65 = 0, $66 = 0, $67 = 0, $68 = 0, $69 = 0, $7 = 0, $70 = 0, $71 = 0;
 var $72 = 0, $73 = 0, $74 = 0, $75 = 0, $76 = 0, $77 = 0, $78 = 0, $79 = 0, $8 = 0, $80 = 0, $81 = 0, $82 = 0, $83 = 0, $84 = 0, $85 = 0, $86 = 0, $87 = 0, $88 = 0, $89 = 0, $9 = 0;
 var $90 = 0, $91 = 0, $92 = 0, $93 = 0, $94 = 0, $95 = 0, $96 = 0, $97 = 0, $98 = 0, $99 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = HEAP32[$1>>2]|0;
 $3 = ((($1)) + 4|0);
 $4 = HEAP32[$3>>2]|0;
 $5 = ((($1)) + 8|0);
 $6 = HEAP32[$5>>2]|0;
 $7 = ((($1)) + 12|0);
 $8 = HEAP32[$7>>2]|0;
 $9 = ((($1)) + 16|0);
 $10 = HEAP32[$9>>2]|0;
 $11 = ((($1)) + 20|0);
 $12 = HEAP32[$11>>2]|0;
 $13 = ((($1)) + 24|0);
 $14 = HEAP32[$13>>2]|0;
 $15 = ((($1)) + 28|0);
 $16 = HEAP32[$15>>2]|0;
 $17 = ((($1)) + 32|0);
 $18 = HEAP32[$17>>2]|0;
 $19 = ((($1)) + 36|0);
 $20 = HEAP32[$19>>2]|0;
 $21 = ($20*19)|0;
 $22 = (($21) + 16777216)|0;
 $23 = $22 >> 25;
 $24 = (($23) + ($2))|0;
 $25 = $24 >> 26;
 $26 = (($25) + ($4))|0;
 $27 = $26 >> 25;
 $28 = (($27) + ($6))|0;
 $29 = $28 >> 26;
 $30 = (($29) + ($8))|0;
 $31 = $30 >> 25;
 $32 = (($31) + ($10))|0;
 $33 = $32 >> 26;
 $34 = (($33) + ($12))|0;
 $35 = $34 >> 25;
 $36 = (($35) + ($14))|0;
 $37 = $36 >> 26;
 $38 = (($37) + ($16))|0;
 $39 = $38 >> 25;
 $40 = (($39) + ($18))|0;
 $41 = $40 >> 26;
 $42 = (($41) + ($20))|0;
 $43 = $42 >> 25;
 $44 = ($43*19)|0;
 $45 = (($44) + ($2))|0;
 $46 = $45 >> 26;
 $47 = (($46) + ($4))|0;
 $48 = $46 << 26;
 $49 = (($45) - ($48))|0;
 $50 = $47 >> 25;
 $51 = (($50) + ($6))|0;
 $52 = $50 << 25;
 $53 = (($47) - ($52))|0;
 $54 = $51 >> 26;
 $55 = (($54) + ($8))|0;
 $56 = $54 << 26;
 $57 = (($51) - ($56))|0;
 $58 = $55 >> 25;
 $59 = (($58) + ($10))|0;
 $60 = $58 << 25;
 $61 = (($55) - ($60))|0;
 $62 = $59 >> 26;
 $63 = (($62) + ($12))|0;
 $64 = $62 << 26;
 $65 = (($59) - ($64))|0;
 $66 = $63 >> 25;
 $67 = (($66) + ($14))|0;
 $68 = $66 << 25;
 $69 = (($63) - ($68))|0;
 $70 = $67 >> 26;
 $71 = (($70) + ($16))|0;
 $72 = $70 << 26;
 $73 = (($67) - ($72))|0;
 $74 = $71 >> 25;
 $75 = (($74) + ($18))|0;
 $76 = $74 << 25;
 $77 = (($71) - ($76))|0;
 $78 = $75 >> 26;
 $79 = (($78) + ($20))|0;
 $80 = $78 << 26;
 $81 = (($75) - ($80))|0;
 $82 = $79 & 33554431;
 $83 = $49&255;
 HEAP8[$0>>0] = $83;
 $84 = $49 >>> 8;
 $85 = $84&255;
 $86 = ((($0)) + 1|0);
 HEAP8[$86>>0] = $85;
 $87 = $49 >>> 16;
 $88 = $87&255;
 $89 = ((($0)) + 2|0);
 HEAP8[$89>>0] = $88;
 $90 = $49 >>> 24;
 $91 = $53 << 2;
 $92 = $91 | $90;
 $93 = $92&255;
 $94 = ((($0)) + 3|0);
 HEAP8[$94>>0] = $93;
 $95 = $53 >>> 6;
 $96 = $95&255;
 $97 = ((($0)) + 4|0);
 HEAP8[$97>>0] = $96;
 $98 = $53 >>> 14;
 $99 = $98&255;
 $100 = ((($0)) + 5|0);
 HEAP8[$100>>0] = $99;
 $101 = $53 >>> 22;
 $102 = $57 << 3;
 $103 = $102 | $101;
 $104 = $103&255;
 $105 = ((($0)) + 6|0);
 HEAP8[$105>>0] = $104;
 $106 = $57 >>> 5;
 $107 = $106&255;
 $108 = ((($0)) + 7|0);
 HEAP8[$108>>0] = $107;
 $109 = $57 >>> 13;
 $110 = $109&255;
 $111 = ((($0)) + 8|0);
 HEAP8[$111>>0] = $110;
 $112 = $57 >>> 21;
 $113 = $61 << 5;
 $114 = $113 | $112;
 $115 = $114&255;
 $116 = ((($0)) + 9|0);
 HEAP8[$116>>0] = $115;
 $117 = $61 >>> 3;
 $118 = $117&255;
 $119 = ((($0)) + 10|0);
 HEAP8[$119>>0] = $118;
 $120 = $61 >>> 11;
 $121 = $120&255;
 $122 = ((($0)) + 11|0);
 HEAP8[$122>>0] = $121;
 $123 = $61 >>> 19;
 $124 = $65 << 6;
 $125 = $124 | $123;
 $126 = $125&255;
 $127 = ((($0)) + 12|0);
 HEAP8[$127>>0] = $126;
 $128 = $65 >>> 2;
 $129 = $128&255;
 $130 = ((($0)) + 13|0);
 HEAP8[$130>>0] = $129;
 $131 = $65 >>> 10;
 $132 = $131&255;
 $133 = ((($0)) + 14|0);
 HEAP8[$133>>0] = $132;
 $134 = $65 >>> 18;
 $135 = $134&255;
 $136 = ((($0)) + 15|0);
 HEAP8[$136>>0] = $135;
 $137 = $69&255;
 $138 = ((($0)) + 16|0);
 HEAP8[$138>>0] = $137;
 $139 = $69 >>> 8;
 $140 = $139&255;
 $141 = ((($0)) + 17|0);
 HEAP8[$141>>0] = $140;
 $142 = $69 >>> 16;
 $143 = $142&255;
 $144 = ((($0)) + 18|0);
 HEAP8[$144>>0] = $143;
 $145 = $69 >>> 24;
 $146 = $73 << 1;
 $147 = $146 | $145;
 $148 = $147&255;
 $149 = ((($0)) + 19|0);
 HEAP8[$149>>0] = $148;
 $150 = $73 >>> 7;
 $151 = $150&255;
 $152 = ((($0)) + 20|0);
 HEAP8[$152>>0] = $151;
 $153 = $73 >>> 15;
 $154 = $153&255;
 $155 = ((($0)) + 21|0);
 HEAP8[$155>>0] = $154;
 $156 = $73 >>> 23;
 $157 = $77 << 3;
 $158 = $157 | $156;
 $159 = $158&255;
 $160 = ((($0)) + 22|0);
 HEAP8[$160>>0] = $159;
 $161 = $77 >>> 5;
 $162 = $161&255;
 $163 = ((($0)) + 23|0);
 HEAP8[$163>>0] = $162;
 $164 = $77 >>> 13;
 $165 = $164&255;
 $166 = ((($0)) + 24|0);
 HEAP8[$166>>0] = $165;
 $167 = $77 >>> 21;
 $168 = $81 << 4;
 $169 = $168 | $167;
 $170 = $169&255;
 $171 = ((($0)) + 25|0);
 HEAP8[$171>>0] = $170;
 $172 = $81 >>> 4;
 $173 = $172&255;
 $174 = ((($0)) + 26|0);
 HEAP8[$174>>0] = $173;
 $175 = $81 >>> 12;
 $176 = $175&255;
 $177 = ((($0)) + 27|0);
 HEAP8[$177>>0] = $176;
 $178 = $81 >>> 20;
 $179 = $82 << 6;
 $180 = $178 | $179;
 $181 = $180&255;
 $182 = ((($0)) + 28|0);
 HEAP8[$182>>0] = $181;
 $183 = $79 >>> 2;
 $184 = $183&255;
 $185 = ((($0)) + 29|0);
 HEAP8[$185>>0] = $184;
 $186 = $79 >>> 10;
 $187 = $186&255;
 $188 = ((($0)) + 30|0);
 HEAP8[$188>>0] = $187;
 $189 = $82 >>> 18;
 $190 = $189&255;
 $191 = ((($0)) + 31|0);
 HEAP8[$191>>0] = $190;
 return;
}
function _crypto_sign_ed25519_ref10_ge_add($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var $10 = 0, $11 = 0, $12 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 48|0;
 $3 = sp;
 $4 = ((($1)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_add($0,$4,$1);
 $5 = ((($0)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_sub($5,$4,$1);
 $6 = ((($0)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_mul($6,$0,$2);
 $7 = ((($2)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_mul($5,$5,$7);
 $8 = ((($0)) + 120|0);
 $9 = ((($2)) + 120|0);
 $10 = ((($1)) + 120|0);
 _crypto_sign_ed25519_ref10_fe_mul($8,$9,$10);
 $11 = ((($1)) + 80|0);
 $12 = ((($2)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_mul($0,$11,$12);
 _crypto_sign_ed25519_ref10_fe_add($3,$0,$0);
 _crypto_sign_ed25519_ref10_fe_sub($0,$6,$5);
 _crypto_sign_ed25519_ref10_fe_add($5,$6,$5);
 _crypto_sign_ed25519_ref10_fe_add($6,$3,$8);
 _crypto_sign_ed25519_ref10_fe_sub($8,$3,$8);
 STACKTOP = sp;return;
}
function _crypto_sign_ed25519_ref10_ge_double_scalarmult_vartime($0,$1,$2,$3) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 $3 = $3|0;
 var $$0$lcssa = 0, $$022 = 0, $$121 = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0;
 var $27 = 0, $28 = 0, $29 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $4 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0;
 var $46 = 0, $47 = 0, $48 = 0, $49 = 0, $5 = 0, $50 = 0, $51 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 2272|0;
 $4 = sp + 2016|0;
 $5 = sp + 1760|0;
 $6 = sp + 480|0;
 $7 = sp + 320|0;
 $8 = sp + 160|0;
 $9 = sp;
 _slide($4,$1);
 _slide($5,$3);
 _crypto_sign_ed25519_ref10_ge_p3_to_cached($6,$2);
 _crypto_sign_ed25519_ref10_ge_p3_dbl($7,$2);
 _crypto_sign_ed25519_ref10_ge_p1p1_to_p3($9,$7);
 _crypto_sign_ed25519_ref10_ge_add($7,$9,$6);
 _crypto_sign_ed25519_ref10_ge_p1p1_to_p3($8,$7);
 $10 = ((($6)) + 160|0);
 _crypto_sign_ed25519_ref10_ge_p3_to_cached($10,$8);
 _crypto_sign_ed25519_ref10_ge_add($7,$9,$10);
 _crypto_sign_ed25519_ref10_ge_p1p1_to_p3($8,$7);
 $11 = ((($6)) + 320|0);
 _crypto_sign_ed25519_ref10_ge_p3_to_cached($11,$8);
 _crypto_sign_ed25519_ref10_ge_add($7,$9,$11);
 _crypto_sign_ed25519_ref10_ge_p1p1_to_p3($8,$7);
 $12 = ((($6)) + 480|0);
 _crypto_sign_ed25519_ref10_ge_p3_to_cached($12,$8);
 _crypto_sign_ed25519_ref10_ge_add($7,$9,$12);
 _crypto_sign_ed25519_ref10_ge_p1p1_to_p3($8,$7);
 $13 = ((($6)) + 640|0);
 _crypto_sign_ed25519_ref10_ge_p3_to_cached($13,$8);
 _crypto_sign_ed25519_ref10_ge_add($7,$9,$13);
 _crypto_sign_ed25519_ref10_ge_p1p1_to_p3($8,$7);
 $14 = ((($6)) + 800|0);
 _crypto_sign_ed25519_ref10_ge_p3_to_cached($14,$8);
 _crypto_sign_ed25519_ref10_ge_add($7,$9,$14);
 _crypto_sign_ed25519_ref10_ge_p1p1_to_p3($8,$7);
 $15 = ((($6)) + 960|0);
 _crypto_sign_ed25519_ref10_ge_p3_to_cached($15,$8);
 _crypto_sign_ed25519_ref10_ge_add($7,$9,$15);
 _crypto_sign_ed25519_ref10_ge_p1p1_to_p3($8,$7);
 $16 = ((($6)) + 1120|0);
 _crypto_sign_ed25519_ref10_ge_p3_to_cached($16,$8);
 _crypto_sign_ed25519_ref10_ge_p2_0($0);
 $$022 = 255;
 while(1) {
  $17 = (($4) + ($$022)|0);
  $18 = HEAP8[$17>>0]|0;
  $19 = ($18<<24>>24)==(0);
  if (!($19)) {
   $$0$lcssa = $$022;
   break;
  }
  $20 = (($5) + ($$022)|0);
  $21 = HEAP8[$20>>0]|0;
  $22 = ($21<<24>>24)==(0);
  if (!($22)) {
   $$0$lcssa = $$022;
   break;
  }
  $24 = (($$022) + -1)|0;
  $25 = ($$022|0)>(0);
  if ($25) {
   $$022 = $24;
  } else {
   $$0$lcssa = $24;
   break;
  }
 }
 $23 = ($$0$lcssa|0)>(-1);
 if ($23) {
  $$121 = $$0$lcssa;
 } else {
  STACKTOP = sp;return;
 }
 while(1) {
  _crypto_sign_ed25519_ref10_ge_p2_dbl($7,$0);
  $26 = (($4) + ($$121)|0);
  $27 = HEAP8[$26>>0]|0;
  $28 = ($27<<24>>24)>(0);
  if ($28) {
   _crypto_sign_ed25519_ref10_ge_p1p1_to_p3($8,$7);
   $29 = HEAP8[$26>>0]|0;
   $30 = (($29<<24>>24) / 2)&-1;
   $31 = $30 << 24 >> 24;
   $32 = (($6) + (($31*160)|0)|0);
   _crypto_sign_ed25519_ref10_ge_add($7,$8,$32);
  } else {
   $33 = ($27<<24>>24)<(0);
   if ($33) {
    _crypto_sign_ed25519_ref10_ge_p1p1_to_p3($8,$7);
    $34 = HEAP8[$26>>0]|0;
    $35 = (($34<<24>>24) / -2)&-1;
    $36 = $35 << 24 >> 24;
    $37 = (($6) + (($36*160)|0)|0);
    _crypto_sign_ed25519_ref10_ge_sub($7,$8,$37);
   }
  }
  $38 = (($5) + ($$121)|0);
  $39 = HEAP8[$38>>0]|0;
  $40 = ($39<<24>>24)>(0);
  if ($40) {
   _crypto_sign_ed25519_ref10_ge_p1p1_to_p3($8,$7);
   $41 = HEAP8[$38>>0]|0;
   $42 = (($41<<24>>24) / 2)&-1;
   $43 = $42 << 24 >> 24;
   $44 = (712 + (($43*120)|0)|0);
   _crypto_sign_ed25519_ref10_ge_madd($7,$8,$44);
  } else {
   $45 = ($39<<24>>24)<(0);
   if ($45) {
    _crypto_sign_ed25519_ref10_ge_p1p1_to_p3($8,$7);
    $46 = HEAP8[$38>>0]|0;
    $47 = (($46<<24>>24) / -2)&-1;
    $48 = $47 << 24 >> 24;
    $49 = (712 + (($48*120)|0)|0);
    _crypto_sign_ed25519_ref10_ge_msub($7,$8,$49);
   }
  }
  _crypto_sign_ed25519_ref10_ge_p1p1_to_p2($0,$7);
  $50 = (($$121) + -1)|0;
  $51 = ($$121|0)>(0);
  if ($51) {
   $$121 = $50;
  } else {
   break;
  }
 }
 STACKTOP = sp;return;
}
function _slide($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $$05559 = 0, $$05663 = 0, $$058 = 0, $$160 = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $2 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0;
 var $25 = 0, $26 = 0, $27 = 0, $28 = 0, $29 = 0, $3 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0;
 var $exitcond = 0, $exitcond65 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $$05663 = 0;
 while(1) {
  $2 = $$05663 >> 3;
  $3 = (($1) + ($2)|0);
  $4 = HEAP8[$3>>0]|0;
  $5 = $4&255;
  $6 = $$05663 & 7;
  $7 = $5 >>> $6;
  $8 = $7 & 1;
  $9 = $8&255;
  $10 = (($0) + ($$05663)|0);
  HEAP8[$10>>0] = $9;
  $11 = (($$05663) + 1)|0;
  $exitcond65 = ($11|0)==(256);
  if ($exitcond65) {
   $$160 = 0;
   break;
  } else {
   $$05663 = $11;
  }
 }
 while(1) {
  $12 = (($0) + ($$160)|0);
  $13 = HEAP8[$12>>0]|0;
  $14 = ($13<<24>>24)==(0);
  L5: do {
   if (!($14)) {
    $$05559 = 1;
    while(1) {
     $15 = (($$05559) + ($$160))|0;
     $16 = ($15|0)<(256);
     if (!($16)) {
      break L5;
     }
     $17 = (($0) + ($15)|0);
     $18 = HEAP8[$17>>0]|0;
     $19 = ($18<<24>>24)==(0);
     L9: do {
      if (!($19)) {
       $20 = HEAP8[$12>>0]|0;
       $21 = $20 << 24 >> 24;
       $22 = $18 << 24 >> 24;
       $23 = $22 << $$05559;
       $24 = (($23) + ($21))|0;
       $25 = ($24|0)<(16);
       if ($25) {
        $26 = $24&255;
        HEAP8[$12>>0] = $26;
        HEAP8[$17>>0] = 0;
        break;
       }
       $27 = (($21) - ($23))|0;
       $28 = ($27|0)>(-16);
       if (!($28)) {
        break L5;
       }
       $29 = $27&255;
       HEAP8[$12>>0] = $29;
       $$058 = $15;
       while(1) {
        $30 = (($0) + ($$058)|0);
        $31 = HEAP8[$30>>0]|0;
        $32 = ($31<<24>>24)==(0);
        if ($32) {
         break;
        }
        HEAP8[$30>>0] = 0;
        $33 = (($$058) + 1)|0;
        $34 = ($$058|0)<(255);
        if ($34) {
         $$058 = $33;
        } else {
         break L9;
        }
       }
       HEAP8[$30>>0] = 1;
      }
     } while(0);
     $35 = (($$05559) + 1)|0;
     $36 = ($$05559|0)<(6);
     if ($36) {
      $$05559 = $35;
     } else {
      break;
     }
    }
   }
  } while(0);
  $37 = (($$160) + 1)|0;
  $exitcond = ($37|0)==(256);
  if ($exitcond) {
   break;
  } else {
   $$160 = $37;
  }
 }
 return;
}
function _crypto_sign_ed25519_ref10_ge_frombytes_negate_vartime($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $$0 = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0;
 var sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 208|0;
 $2 = sp + 160|0;
 $3 = sp + 120|0;
 $4 = sp + 80|0;
 $5 = sp + 40|0;
 $6 = sp;
 $7 = ((($0)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_frombytes($7,$1);
 $8 = ((($0)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_1($8);
 _crypto_sign_ed25519_ref10_fe_sq($2,$7);
 _crypto_sign_ed25519_ref10_fe_mul($3,$2,1672);
 _crypto_sign_ed25519_ref10_fe_sub($2,$2,$8);
 _crypto_sign_ed25519_ref10_fe_add($3,$3,$8);
 _crypto_sign_ed25519_ref10_fe_sq($4,$3);
 _crypto_sign_ed25519_ref10_fe_mul($4,$4,$3);
 _crypto_sign_ed25519_ref10_fe_sq($0,$4);
 _crypto_sign_ed25519_ref10_fe_mul($0,$0,$3);
 _crypto_sign_ed25519_ref10_fe_mul($0,$0,$2);
 _crypto_sign_ed25519_ref10_fe_pow22523($0,$0);
 _crypto_sign_ed25519_ref10_fe_mul($0,$0,$4);
 _crypto_sign_ed25519_ref10_fe_mul($0,$0,$2);
 _crypto_sign_ed25519_ref10_fe_sq($5,$0);
 _crypto_sign_ed25519_ref10_fe_mul($5,$5,$3);
 _crypto_sign_ed25519_ref10_fe_sub($6,$5,$2);
 $9 = (_crypto_sign_ed25519_ref10_fe_isnonzero($6)|0);
 $10 = ($9|0)==(0);
 do {
  if (!($10)) {
   _crypto_sign_ed25519_ref10_fe_add($6,$5,$2);
   $11 = (_crypto_sign_ed25519_ref10_fe_isnonzero($6)|0);
   $12 = ($11|0)==(0);
   if ($12) {
    _crypto_sign_ed25519_ref10_fe_mul($0,$0,1712);
    break;
   } else {
    $$0 = -1;
    STACKTOP = sp;return ($$0|0);
   }
  }
 } while(0);
 $13 = (_crypto_sign_ed25519_ref10_fe_isnegative($0)|0);
 $14 = ((($1)) + 31|0);
 $15 = HEAP8[$14>>0]|0;
 $16 = $15&255;
 $17 = $16 >>> 7;
 $18 = ($13|0)==($17|0);
 if ($18) {
  _crypto_sign_ed25519_ref10_fe_neg($0,$0);
 }
 $19 = ((($0)) + 120|0);
 _crypto_sign_ed25519_ref10_fe_mul($19,$0,$7);
 $$0 = 0;
 STACKTOP = sp;return ($$0|0);
}
function _crypto_sign_ed25519_ref10_ge_madd($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var $10 = 0, $11 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 48|0;
 $3 = sp;
 $4 = ((($1)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_add($0,$4,$1);
 $5 = ((($0)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_sub($5,$4,$1);
 $6 = ((($0)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_mul($6,$0,$2);
 $7 = ((($2)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_mul($5,$5,$7);
 $8 = ((($0)) + 120|0);
 $9 = ((($2)) + 80|0);
 $10 = ((($1)) + 120|0);
 _crypto_sign_ed25519_ref10_fe_mul($8,$9,$10);
 $11 = ((($1)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_add($3,$11,$11);
 _crypto_sign_ed25519_ref10_fe_sub($0,$6,$5);
 _crypto_sign_ed25519_ref10_fe_add($5,$6,$5);
 _crypto_sign_ed25519_ref10_fe_add($6,$3,$8);
 _crypto_sign_ed25519_ref10_fe_sub($8,$3,$8);
 STACKTOP = sp;return;
}
function _crypto_sign_ed25519_ref10_ge_msub($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var $10 = 0, $11 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 48|0;
 $3 = sp;
 $4 = ((($1)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_add($0,$4,$1);
 $5 = ((($0)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_sub($5,$4,$1);
 $6 = ((($0)) + 80|0);
 $7 = ((($2)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_mul($6,$0,$7);
 _crypto_sign_ed25519_ref10_fe_mul($5,$5,$2);
 $8 = ((($0)) + 120|0);
 $9 = ((($2)) + 80|0);
 $10 = ((($1)) + 120|0);
 _crypto_sign_ed25519_ref10_fe_mul($8,$9,$10);
 $11 = ((($1)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_add($3,$11,$11);
 _crypto_sign_ed25519_ref10_fe_sub($0,$6,$5);
 _crypto_sign_ed25519_ref10_fe_add($5,$6,$5);
 _crypto_sign_ed25519_ref10_fe_sub($6,$3,$8);
 _crypto_sign_ed25519_ref10_fe_add($8,$3,$8);
 STACKTOP = sp;return;
}
function _crypto_sign_ed25519_ref10_ge_p1p1_to_p2($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = ((($1)) + 120|0);
 _crypto_sign_ed25519_ref10_fe_mul($0,$1,$2);
 $3 = ((($0)) + 40|0);
 $4 = ((($1)) + 40|0);
 $5 = ((($1)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_mul($3,$4,$5);
 $6 = ((($0)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_mul($6,$5,$2);
 return;
}
function _crypto_sign_ed25519_ref10_ge_p1p1_to_p3($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = ((($1)) + 120|0);
 _crypto_sign_ed25519_ref10_fe_mul($0,$1,$2);
 $3 = ((($0)) + 40|0);
 $4 = ((($1)) + 40|0);
 $5 = ((($1)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_mul($3,$4,$5);
 $6 = ((($0)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_mul($6,$5,$2);
 $7 = ((($0)) + 120|0);
 _crypto_sign_ed25519_ref10_fe_mul($7,$1,$4);
 return;
}
function _crypto_sign_ed25519_ref10_ge_p2_0($0) {
 $0 = $0|0;
 var $1 = 0, $2 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 _crypto_sign_ed25519_ref10_fe_0($0);
 $1 = ((($0)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_1($1);
 $2 = ((($0)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_1($2);
 return;
}
function _crypto_sign_ed25519_ref10_ge_p2_dbl($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 48|0;
 $2 = sp;
 _crypto_sign_ed25519_ref10_fe_sq($0,$1);
 $3 = ((($0)) + 80|0);
 $4 = ((($1)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_sq($3,$4);
 $5 = ((($0)) + 120|0);
 $6 = ((($1)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_sq2($5,$6);
 $7 = ((($0)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_add($7,$1,$4);
 _crypto_sign_ed25519_ref10_fe_sq($2,$7);
 _crypto_sign_ed25519_ref10_fe_add($7,$3,$0);
 _crypto_sign_ed25519_ref10_fe_sub($3,$3,$0);
 _crypto_sign_ed25519_ref10_fe_sub($0,$2,$7);
 _crypto_sign_ed25519_ref10_fe_sub($5,$5,$3);
 STACKTOP = sp;return;
}
function _crypto_sign_ed25519_ref10_ge_p3_0($0) {
 $0 = $0|0;
 var $1 = 0, $2 = 0, $3 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 _crypto_sign_ed25519_ref10_fe_0($0);
 $1 = ((($0)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_1($1);
 $2 = ((($0)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_1($2);
 $3 = ((($0)) + 120|0);
 _crypto_sign_ed25519_ref10_fe_0($3);
 return;
}
function _crypto_sign_ed25519_ref10_ge_p3_dbl($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $2 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 128|0;
 $2 = sp;
 _crypto_sign_ed25519_ref10_ge_p3_to_p2($2,$1);
 _crypto_sign_ed25519_ref10_ge_p2_dbl($0,$2);
 STACKTOP = sp;return;
}
function _crypto_sign_ed25519_ref10_ge_p3_to_cached($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = ((($1)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_add($0,$2,$1);
 $3 = ((($0)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_sub($3,$2,$1);
 $4 = ((($0)) + 80|0);
 $5 = ((($1)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_copy($4,$5);
 $6 = ((($0)) + 120|0);
 $7 = ((($1)) + 120|0);
 _crypto_sign_ed25519_ref10_fe_mul($6,$7,1752);
 return;
}
function _crypto_sign_ed25519_ref10_ge_p3_to_p2($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $2 = 0, $3 = 0, $4 = 0, $5 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 _crypto_sign_ed25519_ref10_fe_copy($0,$1);
 $2 = ((($0)) + 40|0);
 $3 = ((($1)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_copy($2,$3);
 $4 = ((($0)) + 80|0);
 $5 = ((($1)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_copy($4,$5);
 return;
}
function _crypto_sign_ed25519_ref10_ge_p3_tobytes($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $10 = 0, $11 = 0, $12 = 0, $13 = 0, $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 128|0;
 $2 = sp + 80|0;
 $3 = sp + 40|0;
 $4 = sp;
 $5 = ((($1)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_invert($2,$5);
 _crypto_sign_ed25519_ref10_fe_mul($3,$1,$2);
 $6 = ((($1)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_mul($4,$6,$2);
 _crypto_sign_ed25519_ref10_fe_tobytes($0,$4);
 $7 = (_crypto_sign_ed25519_ref10_fe_isnegative($3)|0);
 $8 = $7 << 7;
 $9 = ((($0)) + 31|0);
 $10 = HEAP8[$9>>0]|0;
 $11 = $10&255;
 $12 = $8 ^ $11;
 $13 = $12&255;
 HEAP8[$9>>0] = $13;
 STACKTOP = sp;return;
}
function _crypto_sign_ed25519_ref10_ge_precomp_0($0) {
 $0 = $0|0;
 var $1 = 0, $2 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 _crypto_sign_ed25519_ref10_fe_1($0);
 $1 = ((($0)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_1($1);
 $2 = ((($0)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_0($2);
 return;
}
function _crypto_sign_ed25519_ref10_ge_scalarmult_base($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $$03135 = 0, $$037 = 0, $$136 = 0, $$234 = 0, $$333 = 0, $$udiv = 0, $$udiv38 = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $2 = 0, $20 = 0, $21 = 0;
 var $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0, $29 = 0, $3 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0;
 var $8 = 0, $9 = 0, $exitcond = 0, $exitcond39 = 0, $sext = 0, $sext32 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 464|0;
 $2 = sp + 400|0;
 $3 = sp + 240|0;
 $4 = sp + 120|0;
 $5 = sp;
 $$037 = 0;
 while(1) {
  $6 = (($1) + ($$037)|0);
  $7 = HEAP8[$6>>0]|0;
  $8 = $7 & 15;
  $9 = $$037 << 1;
  $10 = (($2) + ($9)|0);
  HEAP8[$10>>0] = $8;
  $11 = ($7&255) >>> 4;
  $12 = $9 | 1;
  $13 = (($2) + ($12)|0);
  HEAP8[$13>>0] = $11;
  $14 = (($$037) + 1)|0;
  $exitcond39 = ($14|0)==(32);
  if ($exitcond39) {
   $$03135 = 0;$$136 = 0;
   break;
  } else {
   $$037 = $14;
  }
 }
 while(1) {
  $15 = (($2) + ($$136)|0);
  $16 = HEAP8[$15>>0]|0;
  $17 = $16&255;
  $18 = (($$03135) + ($17))|0;
  $sext = $18 << 24;
  $sext32 = (($sext) + 134217728)|0;
  $19 = $sext32 >> 28;
  $20 = $19 << 4;
  $21 = (($18) - ($20))|0;
  $22 = $21&255;
  HEAP8[$15>>0] = $22;
  $23 = (($$136) + 1)|0;
  $exitcond = ($23|0)==(63);
  if ($exitcond) {
   break;
  } else {
   $$03135 = $19;$$136 = $23;
  }
 }
 $24 = ((($2)) + 63|0);
 $25 = HEAP8[$24>>0]|0;
 $26 = $25&255;
 $27 = (($19) + ($26))|0;
 $28 = $27&255;
 HEAP8[$24>>0] = $28;
 _crypto_sign_ed25519_ref10_ge_p3_0($0);
 $$234 = 1;
 while(1) {
  $$udiv38 = $$234 >>> 1;
  $29 = (($2) + ($$234)|0);
  $30 = HEAP8[$29>>0]|0;
  _select_69($5,$$udiv38,$30);
  _crypto_sign_ed25519_ref10_ge_madd($3,$0,$5);
  _crypto_sign_ed25519_ref10_ge_p1p1_to_p3($0,$3);
  $31 = (($$234) + 2)|0;
  $32 = ($$234|0)<(62);
  if ($32) {
   $$234 = $31;
  } else {
   break;
  }
 }
 _crypto_sign_ed25519_ref10_ge_p3_dbl($3,$0);
 _crypto_sign_ed25519_ref10_ge_p1p1_to_p2($4,$3);
 _crypto_sign_ed25519_ref10_ge_p2_dbl($3,$4);
 _crypto_sign_ed25519_ref10_ge_p1p1_to_p2($4,$3);
 _crypto_sign_ed25519_ref10_ge_p2_dbl($3,$4);
 _crypto_sign_ed25519_ref10_ge_p1p1_to_p2($4,$3);
 _crypto_sign_ed25519_ref10_ge_p2_dbl($3,$4);
 _crypto_sign_ed25519_ref10_ge_p1p1_to_p3($0,$3);
 $$333 = 0;
 while(1) {
  $$udiv = $$333 >>> 1;
  $33 = (($2) + ($$333)|0);
  $34 = HEAP8[$33>>0]|0;
  _select_69($5,$$udiv,$34);
  _crypto_sign_ed25519_ref10_ge_madd($3,$0,$5);
  _crypto_sign_ed25519_ref10_ge_p1p1_to_p3($0,$3);
  $35 = (($$333) + 2)|0;
  $36 = ($$333|0)<(62);
  if ($36) {
   $$333 = $35;
  } else {
   break;
  }
 }
 STACKTOP = sp;return;
}
function _select_69($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0, $29 = 0;
 var $3 = 0, $30 = 0, $31 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 128|0;
 $3 = sp;
 $4 = (_negative($2)|0);
 $5 = $2 << 24 >> 24;
 $6 = $4&255;
 $7 = (0 - ($6))|0;
 $8 = $7 & $5;
 $9 = $8 << 1;
 $10 = (($5) - ($9))|0;
 $11 = $10&255;
 _crypto_sign_ed25519_ref10_ge_precomp_0($0);
 $12 = (1792 + (($1*960)|0)|0);
 $13 = (_equal($11,1)|0);
 _cmov($0,$12,$13);
 $14 = (((1792 + (($1*960)|0)|0)) + 120|0);
 $15 = (_equal($11,2)|0);
 _cmov($0,$14,$15);
 $16 = (((1792 + (($1*960)|0)|0)) + 240|0);
 $17 = (_equal($11,3)|0);
 _cmov($0,$16,$17);
 $18 = (((1792 + (($1*960)|0)|0)) + 360|0);
 $19 = (_equal($11,4)|0);
 _cmov($0,$18,$19);
 $20 = (((1792 + (($1*960)|0)|0)) + 480|0);
 $21 = (_equal($11,5)|0);
 _cmov($0,$20,$21);
 $22 = (((1792 + (($1*960)|0)|0)) + 600|0);
 $23 = (_equal($11,6)|0);
 _cmov($0,$22,$23);
 $24 = (((1792 + (($1*960)|0)|0)) + 720|0);
 $25 = (_equal($11,7)|0);
 _cmov($0,$24,$25);
 $26 = (((1792 + (($1*960)|0)|0)) + 840|0);
 $27 = (_equal($11,8)|0);
 _cmov($0,$26,$27);
 $28 = ((($0)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_copy($3,$28);
 $29 = ((($3)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_copy($29,$0);
 $30 = ((($3)) + 80|0);
 $31 = ((($0)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_neg($30,$31);
 _cmov($0,$3,$4);
 STACKTOP = sp;return;
}
function _negative($0) {
 $0 = $0|0;
 var $1 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $1 = ($0&255) >>> 7;
 return ($1|0);
}
function _equal($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $2 = $1 ^ $0;
 $3 = $2&255;
 $4 = (($3) + -1)|0;
 $5 = $4 >>> 31;
 $6 = $5&255;
 return ($6|0);
}
function _cmov($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $3 = $2&255;
 _crypto_sign_ed25519_ref10_fe_cmov($0,$1,$3);
 $4 = ((($0)) + 40|0);
 $5 = ((($1)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_cmov($4,$5,$3);
 $6 = ((($0)) + 80|0);
 $7 = ((($1)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_cmov($6,$7,$3);
 return;
}
function _crypto_sign_ed25519_ref10_ge_sub($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var $10 = 0, $11 = 0, $12 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 48|0;
 $3 = sp;
 $4 = ((($1)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_add($0,$4,$1);
 $5 = ((($0)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_sub($5,$4,$1);
 $6 = ((($0)) + 80|0);
 $7 = ((($2)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_mul($6,$0,$7);
 _crypto_sign_ed25519_ref10_fe_mul($5,$5,$2);
 $8 = ((($0)) + 120|0);
 $9 = ((($2)) + 120|0);
 $10 = ((($1)) + 120|0);
 _crypto_sign_ed25519_ref10_fe_mul($8,$9,$10);
 $11 = ((($1)) + 80|0);
 $12 = ((($2)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_mul($0,$11,$12);
 _crypto_sign_ed25519_ref10_fe_add($3,$0,$0);
 _crypto_sign_ed25519_ref10_fe_sub($0,$6,$5);
 _crypto_sign_ed25519_ref10_fe_add($5,$6,$5);
 _crypto_sign_ed25519_ref10_fe_sub($6,$3,$8);
 _crypto_sign_ed25519_ref10_fe_add($8,$3,$8);
 STACKTOP = sp;return;
}
function _crypto_sign_ed25519_ref10_ge_tobytes($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $10 = 0, $11 = 0, $12 = 0, $13 = 0, $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 128|0;
 $2 = sp + 80|0;
 $3 = sp + 40|0;
 $4 = sp;
 $5 = ((($1)) + 80|0);
 _crypto_sign_ed25519_ref10_fe_invert($2,$5);
 _crypto_sign_ed25519_ref10_fe_mul($3,$1,$2);
 $6 = ((($1)) + 40|0);
 _crypto_sign_ed25519_ref10_fe_mul($4,$6,$2);
 _crypto_sign_ed25519_ref10_fe_tobytes($0,$4);
 $7 = (_crypto_sign_ed25519_ref10_fe_isnegative($3)|0);
 $8 = $7 << 7;
 $9 = ((($0)) + 31|0);
 $10 = HEAP8[$9>>0]|0;
 $11 = $10&255;
 $12 = $8 ^ $11;
 $13 = $12&255;
 HEAP8[$9>>0] = $13;
 STACKTOP = sp;return;
}
function _crypto_sign_edwards25519sha512batch_ref10_open($0,$1,$2,$3,$4,$5) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 $3 = $3|0;
 $4 = $4|0;
 $5 = $5|0;
 var $$0 = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0;
 var $29 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, dest = 0, label = 0, sp = 0, src = 0, stop = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 480|0;
 $6 = sp + 440|0;
 $7 = sp + 408|0;
 $8 = sp + 376|0;
 $9 = sp + 312|0;
 $10 = sp + 280|0;
 $11 = sp + 120|0;
 $12 = sp;
 $13 = ($4>>>0)<(0);
 $14 = ($3>>>0)<(64);
 $15 = ($4|0)==(0);
 $16 = $15 & $14;
 $17 = $13 | $16;
 if (!($17)) {
  $18 = ((($2)) + 63|0);
  $19 = HEAP8[$18>>0]|0;
  $20 = ($19&255)>(31);
  if (!($20)) {
   $21 = (_crypto_sign_ed25519_ref10_ge_frombytes_negate_vartime($11,$5)|0);
   $22 = ($21|0)==(0);
   if ($22) {
    dest=$6; src=$5; stop=dest+32|0; do { HEAP8[dest>>0]=HEAP8[src>>0]|0; dest=dest+1|0; src=src+1|0; } while ((dest|0) < (stop|0));
    dest=$7; src=$2; stop=dest+32|0; do { HEAP8[dest>>0]=HEAP8[src>>0]|0; dest=dest+1|0; src=src+1|0; } while ((dest|0) < (stop|0));
    $23 = ((($2)) + 32|0);
    dest=$8; src=$23; stop=dest+32|0; do { HEAP8[dest>>0]=HEAP8[src>>0]|0; dest=dest+1|0; src=src+1|0; } while ((dest|0) < (stop|0));
    _memmove(($0|0),($2|0),($3|0))|0;
    $24 = ((($0)) + 32|0);
    dest=$24; src=$6; stop=dest+32|0; do { HEAP8[dest>>0]=HEAP8[src>>0]|0; dest=dest+1|0; src=src+1|0; } while ((dest|0) < (stop|0));
    (_crypto_hash_sha512_ref($9,$0,$3,$4)|0);
    _crypto_sign_ed25519_ref10_sc_reduce($9);
    _crypto_sign_ed25519_ref10_ge_double_scalarmult_vartime($12,$9,$11,$8);
    _crypto_sign_ed25519_ref10_ge_tobytes($10,$12);
    $25 = (_crypto_verify_32_ref($10,$7)|0);
    $26 = ($25|0)==(0);
    if ($26) {
     $27 = ((($0)) + 64|0);
     $28 = (_i64Add(($3|0),($4|0),-64,-1)|0);
     $29 = tempRet0;
     _memmove(($0|0),($27|0),($28|0))|0;
     $30 = (($0) + ($3)|0);
     $31 = ((($30)) + -64|0);
     dest=$31; stop=dest+64|0; do { HEAP8[dest>>0]=0|0; dest=dest+1|0; } while ((dest|0) < (stop|0));
     $32 = $1;
     $33 = $32;
     HEAP32[$33>>2] = $28;
     $34 = (($32) + 4)|0;
     $35 = $34;
     HEAP32[$35>>2] = $29;
     $$0 = 0;
     STACKTOP = sp;return ($$0|0);
    }
   }
  }
 }
 $36 = $1;
 $37 = $36;
 HEAP32[$37>>2] = -1;
 $38 = (($36) + 4)|0;
 $39 = $38;
 HEAP32[$39>>2] = -1;
 _memset(($0|0),0,($3|0))|0;
 $$0 = -1;
 STACKTOP = sp;return ($$0|0);
}
function _crypto_sign_ed25519_ref10_sc_muladd($0,$1,$2,$3) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 $3 = $3|0;
 var $10 = 0, $100 = 0, $1000 = 0, $1001 = 0, $1002 = 0, $1003 = 0, $1004 = 0, $1005 = 0, $1006 = 0, $1007 = 0, $1008 = 0, $1009 = 0, $101 = 0, $1010 = 0, $1011 = 0, $1012 = 0, $1013 = 0, $1014 = 0, $1015 = 0, $1016 = 0;
 var $1017 = 0, $1018 = 0, $1019 = 0, $102 = 0, $1020 = 0, $1021 = 0, $1022 = 0, $1023 = 0, $1024 = 0, $1025 = 0, $1026 = 0, $1027 = 0, $1028 = 0, $1029 = 0, $103 = 0, $1030 = 0, $1031 = 0, $1032 = 0, $1033 = 0, $1034 = 0;
 var $1035 = 0, $1036 = 0, $1037 = 0, $1038 = 0, $1039 = 0, $104 = 0, $1040 = 0, $1041 = 0, $1042 = 0, $1043 = 0, $1044 = 0, $1045 = 0, $1046 = 0, $1047 = 0, $1048 = 0, $1049 = 0, $105 = 0, $1050 = 0, $1051 = 0, $1052 = 0;
 var $1053 = 0, $1054 = 0, $1055 = 0, $1056 = 0, $1057 = 0, $1058 = 0, $1059 = 0, $106 = 0, $1060 = 0, $1061 = 0, $1062 = 0, $1063 = 0, $1064 = 0, $1065 = 0, $1066 = 0, $1067 = 0, $1068 = 0, $1069 = 0, $107 = 0, $1070 = 0;
 var $1071 = 0, $1072 = 0, $1073 = 0, $1074 = 0, $1075 = 0, $1076 = 0, $1077 = 0, $1078 = 0, $1079 = 0, $108 = 0, $1080 = 0, $1081 = 0, $1082 = 0, $1083 = 0, $1084 = 0, $1085 = 0, $1086 = 0, $1087 = 0, $1088 = 0, $1089 = 0;
 var $109 = 0, $1090 = 0, $1091 = 0, $1092 = 0, $1093 = 0, $1094 = 0, $1095 = 0, $1096 = 0, $1097 = 0, $1098 = 0, $1099 = 0, $11 = 0, $110 = 0, $1100 = 0, $1101 = 0, $1102 = 0, $1103 = 0, $1104 = 0, $1105 = 0, $1106 = 0;
 var $1107 = 0, $1108 = 0, $1109 = 0, $111 = 0, $1110 = 0, $1111 = 0, $1112 = 0, $1113 = 0, $1114 = 0, $1115 = 0, $1116 = 0, $1117 = 0, $1118 = 0, $1119 = 0, $112 = 0, $1120 = 0, $1121 = 0, $1122 = 0, $1123 = 0, $1124 = 0;
 var $1125 = 0, $1126 = 0, $1127 = 0, $1128 = 0, $1129 = 0, $113 = 0, $1130 = 0, $1131 = 0, $1132 = 0, $1133 = 0, $1134 = 0, $1135 = 0, $1136 = 0, $1137 = 0, $1138 = 0, $1139 = 0, $114 = 0, $1140 = 0, $1141 = 0, $1142 = 0;
 var $1143 = 0, $1144 = 0, $1145 = 0, $1146 = 0, $1147 = 0, $1148 = 0, $1149 = 0, $115 = 0, $1150 = 0, $1151 = 0, $1152 = 0, $1153 = 0, $1154 = 0, $1155 = 0, $1156 = 0, $1157 = 0, $1158 = 0, $1159 = 0, $116 = 0, $1160 = 0;
 var $1161 = 0, $1162 = 0, $1163 = 0, $1164 = 0, $1165 = 0, $1166 = 0, $1167 = 0, $1168 = 0, $1169 = 0, $117 = 0, $1170 = 0, $1171 = 0, $1172 = 0, $1173 = 0, $1174 = 0, $1175 = 0, $1176 = 0, $1177 = 0, $1178 = 0, $1179 = 0;
 var $118 = 0, $1180 = 0, $1181 = 0, $1182 = 0, $1183 = 0, $1184 = 0, $1185 = 0, $1186 = 0, $1187 = 0, $1188 = 0, $1189 = 0, $119 = 0, $1190 = 0, $1191 = 0, $1192 = 0, $1193 = 0, $1194 = 0, $1195 = 0, $1196 = 0, $1197 = 0;
 var $1198 = 0, $1199 = 0, $12 = 0, $120 = 0, $1200 = 0, $1201 = 0, $1202 = 0, $1203 = 0, $1204 = 0, $1205 = 0, $1206 = 0, $1207 = 0, $1208 = 0, $1209 = 0, $121 = 0, $1210 = 0, $1211 = 0, $1212 = 0, $1213 = 0, $1214 = 0;
 var $1215 = 0, $1216 = 0, $1217 = 0, $1218 = 0, $1219 = 0, $122 = 0, $1220 = 0, $1221 = 0, $1222 = 0, $1223 = 0, $1224 = 0, $1225 = 0, $1226 = 0, $1227 = 0, $1228 = 0, $1229 = 0, $123 = 0, $1230 = 0, $1231 = 0, $1232 = 0;
 var $1233 = 0, $1234 = 0, $1235 = 0, $1236 = 0, $1237 = 0, $1238 = 0, $1239 = 0, $124 = 0, $1240 = 0, $1241 = 0, $1242 = 0, $1243 = 0, $1244 = 0, $1245 = 0, $1246 = 0, $1247 = 0, $1248 = 0, $1249 = 0, $125 = 0, $1250 = 0;
 var $1251 = 0, $1252 = 0, $1253 = 0, $1254 = 0, $1255 = 0, $1256 = 0, $1257 = 0, $1258 = 0, $1259 = 0, $126 = 0, $1260 = 0, $1261 = 0, $1262 = 0, $1263 = 0, $1264 = 0, $1265 = 0, $1266 = 0, $1267 = 0, $1268 = 0, $1269 = 0;
 var $127 = 0, $1270 = 0, $1271 = 0, $1272 = 0, $1273 = 0, $1274 = 0, $1275 = 0, $1276 = 0, $1277 = 0, $1278 = 0, $1279 = 0, $128 = 0, $1280 = 0, $1281 = 0, $1282 = 0, $1283 = 0, $1284 = 0, $1285 = 0, $1286 = 0, $1287 = 0;
 var $1288 = 0, $1289 = 0, $129 = 0, $1290 = 0, $1291 = 0, $1292 = 0, $1293 = 0, $1294 = 0, $1295 = 0, $1296 = 0, $1297 = 0, $1298 = 0, $1299 = 0, $13 = 0, $130 = 0, $1300 = 0, $1301 = 0, $1302 = 0, $1303 = 0, $1304 = 0;
 var $1305 = 0, $1306 = 0, $1307 = 0, $1308 = 0, $1309 = 0, $131 = 0, $1310 = 0, $1311 = 0, $1312 = 0, $1313 = 0, $1314 = 0, $1315 = 0, $1316 = 0, $1317 = 0, $1318 = 0, $1319 = 0, $132 = 0, $1320 = 0, $1321 = 0, $1322 = 0;
 var $1323 = 0, $1324 = 0, $1325 = 0, $1326 = 0, $1327 = 0, $1328 = 0, $1329 = 0, $133 = 0, $1330 = 0, $1331 = 0, $1332 = 0, $1333 = 0, $1334 = 0, $1335 = 0, $1336 = 0, $1337 = 0, $1338 = 0, $1339 = 0, $134 = 0, $1340 = 0;
 var $1341 = 0, $1342 = 0, $1343 = 0, $1344 = 0, $1345 = 0, $1346 = 0, $1347 = 0, $1348 = 0, $1349 = 0, $135 = 0, $1350 = 0, $1351 = 0, $1352 = 0, $1353 = 0, $1354 = 0, $1355 = 0, $1356 = 0, $1357 = 0, $1358 = 0, $1359 = 0;
 var $136 = 0, $1360 = 0, $1361 = 0, $1362 = 0, $1363 = 0, $1364 = 0, $1365 = 0, $1366 = 0, $1367 = 0, $1368 = 0, $1369 = 0, $137 = 0, $1370 = 0, $1371 = 0, $1372 = 0, $1373 = 0, $1374 = 0, $1375 = 0, $1376 = 0, $1377 = 0;
 var $1378 = 0, $1379 = 0, $138 = 0, $1380 = 0, $1381 = 0, $1382 = 0, $1383 = 0, $1384 = 0, $1385 = 0, $1386 = 0, $1387 = 0, $1388 = 0, $1389 = 0, $139 = 0, $1390 = 0, $1391 = 0, $1392 = 0, $1393 = 0, $1394 = 0, $1395 = 0;
 var $1396 = 0, $1397 = 0, $1398 = 0, $1399 = 0, $14 = 0, $140 = 0, $1400 = 0, $1401 = 0, $1402 = 0, $1403 = 0, $1404 = 0, $1405 = 0, $1406 = 0, $1407 = 0, $1408 = 0, $1409 = 0, $141 = 0, $1410 = 0, $1411 = 0, $1412 = 0;
 var $1413 = 0, $1414 = 0, $1415 = 0, $1416 = 0, $1417 = 0, $1418 = 0, $1419 = 0, $142 = 0, $1420 = 0, $1421 = 0, $1422 = 0, $1423 = 0, $1424 = 0, $1425 = 0, $1426 = 0, $1427 = 0, $1428 = 0, $1429 = 0, $143 = 0, $1430 = 0;
 var $1431 = 0, $1432 = 0, $1433 = 0, $1434 = 0, $1435 = 0, $1436 = 0, $1437 = 0, $1438 = 0, $1439 = 0, $144 = 0, $1440 = 0, $1441 = 0, $1442 = 0, $1443 = 0, $1444 = 0, $1445 = 0, $1446 = 0, $1447 = 0, $1448 = 0, $1449 = 0;
 var $145 = 0, $1450 = 0, $1451 = 0, $1452 = 0, $1453 = 0, $1454 = 0, $1455 = 0, $1456 = 0, $1457 = 0, $1458 = 0, $1459 = 0, $146 = 0, $1460 = 0, $1461 = 0, $1462 = 0, $1463 = 0, $1464 = 0, $1465 = 0, $1466 = 0, $1467 = 0;
 var $1468 = 0, $1469 = 0, $147 = 0, $1470 = 0, $1471 = 0, $1472 = 0, $1473 = 0, $1474 = 0, $1475 = 0, $1476 = 0, $1477 = 0, $1478 = 0, $1479 = 0, $148 = 0, $1480 = 0, $1481 = 0, $1482 = 0, $1483 = 0, $1484 = 0, $1485 = 0;
 var $1486 = 0, $1487 = 0, $1488 = 0, $1489 = 0, $149 = 0, $1490 = 0, $1491 = 0, $1492 = 0, $1493 = 0, $1494 = 0, $1495 = 0, $1496 = 0, $1497 = 0, $1498 = 0, $1499 = 0, $15 = 0, $150 = 0, $1500 = 0, $1501 = 0, $1502 = 0;
 var $1503 = 0, $1504 = 0, $1505 = 0, $1506 = 0, $1507 = 0, $1508 = 0, $1509 = 0, $151 = 0, $1510 = 0, $1511 = 0, $1512 = 0, $1513 = 0, $1514 = 0, $1515 = 0, $1516 = 0, $1517 = 0, $1518 = 0, $1519 = 0, $152 = 0, $1520 = 0;
 var $1521 = 0, $1522 = 0, $1523 = 0, $1524 = 0, $1525 = 0, $1526 = 0, $1527 = 0, $1528 = 0, $1529 = 0, $153 = 0, $1530 = 0, $1531 = 0, $1532 = 0, $1533 = 0, $1534 = 0, $1535 = 0, $1536 = 0, $1537 = 0, $1538 = 0, $1539 = 0;
 var $154 = 0, $1540 = 0, $1541 = 0, $1542 = 0, $1543 = 0, $1544 = 0, $1545 = 0, $1546 = 0, $1547 = 0, $1548 = 0, $1549 = 0, $155 = 0, $1550 = 0, $1551 = 0, $1552 = 0, $1553 = 0, $1554 = 0, $1555 = 0, $1556 = 0, $1557 = 0;
 var $1558 = 0, $1559 = 0, $156 = 0, $1560 = 0, $1561 = 0, $1562 = 0, $1563 = 0, $1564 = 0, $1565 = 0, $1566 = 0, $1567 = 0, $1568 = 0, $1569 = 0, $157 = 0, $1570 = 0, $1571 = 0, $1572 = 0, $1573 = 0, $1574 = 0, $1575 = 0;
 var $1576 = 0, $1577 = 0, $1578 = 0, $1579 = 0, $158 = 0, $1580 = 0, $1581 = 0, $1582 = 0, $1583 = 0, $1584 = 0, $1585 = 0, $1586 = 0, $1587 = 0, $1588 = 0, $1589 = 0, $159 = 0, $1590 = 0, $1591 = 0, $1592 = 0, $1593 = 0;
 var $1594 = 0, $1595 = 0, $1596 = 0, $1597 = 0, $1598 = 0, $1599 = 0, $16 = 0, $160 = 0, $1600 = 0, $1601 = 0, $1602 = 0, $1603 = 0, $1604 = 0, $1605 = 0, $1606 = 0, $1607 = 0, $1608 = 0, $1609 = 0, $161 = 0, $1610 = 0;
 var $1611 = 0, $1612 = 0, $1613 = 0, $1614 = 0, $1615 = 0, $1616 = 0, $1617 = 0, $1618 = 0, $1619 = 0, $162 = 0, $1620 = 0, $1621 = 0, $1622 = 0, $1623 = 0, $1624 = 0, $1625 = 0, $1626 = 0, $1627 = 0, $1628 = 0, $1629 = 0;
 var $163 = 0, $1630 = 0, $1631 = 0, $1632 = 0, $1633 = 0, $1634 = 0, $1635 = 0, $1636 = 0, $1637 = 0, $1638 = 0, $1639 = 0, $164 = 0, $1640 = 0, $1641 = 0, $1642 = 0, $1643 = 0, $1644 = 0, $1645 = 0, $1646 = 0, $1647 = 0;
 var $1648 = 0, $1649 = 0, $165 = 0, $1650 = 0, $1651 = 0, $1652 = 0, $1653 = 0, $1654 = 0, $1655 = 0, $1656 = 0, $1657 = 0, $1658 = 0, $1659 = 0, $166 = 0, $1660 = 0, $1661 = 0, $1662 = 0, $1663 = 0, $1664 = 0, $1665 = 0;
 var $1666 = 0, $1667 = 0, $1668 = 0, $1669 = 0, $167 = 0, $1670 = 0, $1671 = 0, $1672 = 0, $1673 = 0, $1674 = 0, $1675 = 0, $1676 = 0, $1677 = 0, $1678 = 0, $1679 = 0, $168 = 0, $1680 = 0, $1681 = 0, $1682 = 0, $1683 = 0;
 var $1684 = 0, $1685 = 0, $1686 = 0, $1687 = 0, $1688 = 0, $1689 = 0, $169 = 0, $1690 = 0, $1691 = 0, $1692 = 0, $1693 = 0, $1694 = 0, $1695 = 0, $1696 = 0, $1697 = 0, $1698 = 0, $1699 = 0, $17 = 0, $170 = 0, $1700 = 0;
 var $1701 = 0, $1702 = 0, $1703 = 0, $1704 = 0, $1705 = 0, $1706 = 0, $1707 = 0, $1708 = 0, $1709 = 0, $171 = 0, $1710 = 0, $1711 = 0, $1712 = 0, $1713 = 0, $1714 = 0, $1715 = 0, $1716 = 0, $1717 = 0, $1718 = 0, $1719 = 0;
 var $172 = 0, $1720 = 0, $1721 = 0, $1722 = 0, $1723 = 0, $1724 = 0, $1725 = 0, $1726 = 0, $1727 = 0, $1728 = 0, $1729 = 0, $173 = 0, $1730 = 0, $1731 = 0, $1732 = 0, $1733 = 0, $1734 = 0, $1735 = 0, $1736 = 0, $1737 = 0;
 var $1738 = 0, $1739 = 0, $174 = 0, $1740 = 0, $1741 = 0, $1742 = 0, $1743 = 0, $1744 = 0, $1745 = 0, $1746 = 0, $1747 = 0, $1748 = 0, $1749 = 0, $175 = 0, $1750 = 0, $1751 = 0, $1752 = 0, $1753 = 0, $1754 = 0, $1755 = 0;
 var $1756 = 0, $1757 = 0, $1758 = 0, $1759 = 0, $176 = 0, $1760 = 0, $1761 = 0, $1762 = 0, $1763 = 0, $1764 = 0, $1765 = 0, $1766 = 0, $1767 = 0, $1768 = 0, $1769 = 0, $177 = 0, $1770 = 0, $1771 = 0, $1772 = 0, $1773 = 0;
 var $1774 = 0, $1775 = 0, $1776 = 0, $1777 = 0, $1778 = 0, $1779 = 0, $178 = 0, $1780 = 0, $1781 = 0, $1782 = 0, $1783 = 0, $1784 = 0, $1785 = 0, $1786 = 0, $1787 = 0, $1788 = 0, $1789 = 0, $179 = 0, $1790 = 0, $1791 = 0;
 var $1792 = 0, $1793 = 0, $1794 = 0, $1795 = 0, $1796 = 0, $1797 = 0, $1798 = 0, $1799 = 0, $18 = 0, $180 = 0, $1800 = 0, $1801 = 0, $1802 = 0, $1803 = 0, $1804 = 0, $1805 = 0, $1806 = 0, $1807 = 0, $1808 = 0, $1809 = 0;
 var $181 = 0, $1810 = 0, $1811 = 0, $1812 = 0, $1813 = 0, $1814 = 0, $1815 = 0, $1816 = 0, $1817 = 0, $1818 = 0, $1819 = 0, $182 = 0, $1820 = 0, $1821 = 0, $1822 = 0, $1823 = 0, $1824 = 0, $1825 = 0, $1826 = 0, $1827 = 0;
 var $1828 = 0, $1829 = 0, $183 = 0, $1830 = 0, $1831 = 0, $1832 = 0, $1833 = 0, $1834 = 0, $1835 = 0, $1836 = 0, $1837 = 0, $1838 = 0, $1839 = 0, $184 = 0, $1840 = 0, $1841 = 0, $1842 = 0, $1843 = 0, $1844 = 0, $1845 = 0;
 var $1846 = 0, $1847 = 0, $1848 = 0, $1849 = 0, $185 = 0, $1850 = 0, $1851 = 0, $1852 = 0, $1853 = 0, $1854 = 0, $1855 = 0, $1856 = 0, $1857 = 0, $1858 = 0, $1859 = 0, $186 = 0, $1860 = 0, $1861 = 0, $1862 = 0, $1863 = 0;
 var $1864 = 0, $1865 = 0, $1866 = 0, $1867 = 0, $1868 = 0, $1869 = 0, $187 = 0, $1870 = 0, $1871 = 0, $1872 = 0, $1873 = 0, $1874 = 0, $1875 = 0, $1876 = 0, $1877 = 0, $1878 = 0, $1879 = 0, $188 = 0, $1880 = 0, $189 = 0;
 var $19 = 0, $190 = 0, $191 = 0, $192 = 0, $193 = 0, $194 = 0, $195 = 0, $196 = 0, $197 = 0, $198 = 0, $199 = 0, $20 = 0, $200 = 0, $201 = 0, $202 = 0, $203 = 0, $204 = 0, $205 = 0, $206 = 0, $207 = 0;
 var $208 = 0, $209 = 0, $21 = 0, $210 = 0, $211 = 0, $212 = 0, $213 = 0, $214 = 0, $215 = 0, $216 = 0, $217 = 0, $218 = 0, $219 = 0, $22 = 0, $220 = 0, $221 = 0, $222 = 0, $223 = 0, $224 = 0, $225 = 0;
 var $226 = 0, $227 = 0, $228 = 0, $229 = 0, $23 = 0, $230 = 0, $231 = 0, $232 = 0, $233 = 0, $234 = 0, $235 = 0, $236 = 0, $237 = 0, $238 = 0, $239 = 0, $24 = 0, $240 = 0, $241 = 0, $242 = 0, $243 = 0;
 var $244 = 0, $245 = 0, $246 = 0, $247 = 0, $248 = 0, $249 = 0, $25 = 0, $250 = 0, $251 = 0, $252 = 0, $253 = 0, $254 = 0, $255 = 0, $256 = 0, $257 = 0, $258 = 0, $259 = 0, $26 = 0, $260 = 0, $261 = 0;
 var $262 = 0, $263 = 0, $264 = 0, $265 = 0, $266 = 0, $267 = 0, $268 = 0, $269 = 0, $27 = 0, $270 = 0, $271 = 0, $272 = 0, $273 = 0, $274 = 0, $275 = 0, $276 = 0, $277 = 0, $278 = 0, $279 = 0, $28 = 0;
 var $280 = 0, $281 = 0, $282 = 0, $283 = 0, $284 = 0, $285 = 0, $286 = 0, $287 = 0, $288 = 0, $289 = 0, $29 = 0, $290 = 0, $291 = 0, $292 = 0, $293 = 0, $294 = 0, $295 = 0, $296 = 0, $297 = 0, $298 = 0;
 var $299 = 0, $30 = 0, $300 = 0, $301 = 0, $302 = 0, $303 = 0, $304 = 0, $305 = 0, $306 = 0, $307 = 0, $308 = 0, $309 = 0, $31 = 0, $310 = 0, $311 = 0, $312 = 0, $313 = 0, $314 = 0, $315 = 0, $316 = 0;
 var $317 = 0, $318 = 0, $319 = 0, $32 = 0, $320 = 0, $321 = 0, $322 = 0, $323 = 0, $324 = 0, $325 = 0, $326 = 0, $327 = 0, $328 = 0, $329 = 0, $33 = 0, $330 = 0, $331 = 0, $332 = 0, $333 = 0, $334 = 0;
 var $335 = 0, $336 = 0, $337 = 0, $338 = 0, $339 = 0, $34 = 0, $340 = 0, $341 = 0, $342 = 0, $343 = 0, $344 = 0, $345 = 0, $346 = 0, $347 = 0, $348 = 0, $349 = 0, $35 = 0, $350 = 0, $351 = 0, $352 = 0;
 var $353 = 0, $354 = 0, $355 = 0, $356 = 0, $357 = 0, $358 = 0, $359 = 0, $36 = 0, $360 = 0, $361 = 0, $362 = 0, $363 = 0, $364 = 0, $365 = 0, $366 = 0, $367 = 0, $368 = 0, $369 = 0, $37 = 0, $370 = 0;
 var $371 = 0, $372 = 0, $373 = 0, $374 = 0, $375 = 0, $376 = 0, $377 = 0, $378 = 0, $379 = 0, $38 = 0, $380 = 0, $381 = 0, $382 = 0, $383 = 0, $384 = 0, $385 = 0, $386 = 0, $387 = 0, $388 = 0, $389 = 0;
 var $39 = 0, $390 = 0, $391 = 0, $392 = 0, $393 = 0, $394 = 0, $395 = 0, $396 = 0, $397 = 0, $398 = 0, $399 = 0, $4 = 0, $40 = 0, $400 = 0, $401 = 0, $402 = 0, $403 = 0, $404 = 0, $405 = 0, $406 = 0;
 var $407 = 0, $408 = 0, $409 = 0, $41 = 0, $410 = 0, $411 = 0, $412 = 0, $413 = 0, $414 = 0, $415 = 0, $416 = 0, $417 = 0, $418 = 0, $419 = 0, $42 = 0, $420 = 0, $421 = 0, $422 = 0, $423 = 0, $424 = 0;
 var $425 = 0, $426 = 0, $427 = 0, $428 = 0, $429 = 0, $43 = 0, $430 = 0, $431 = 0, $432 = 0, $433 = 0, $434 = 0, $435 = 0, $436 = 0, $437 = 0, $438 = 0, $439 = 0, $44 = 0, $440 = 0, $441 = 0, $442 = 0;
 var $443 = 0, $444 = 0, $445 = 0, $446 = 0, $447 = 0, $448 = 0, $449 = 0, $45 = 0, $450 = 0, $451 = 0, $452 = 0, $453 = 0, $454 = 0, $455 = 0, $456 = 0, $457 = 0, $458 = 0, $459 = 0, $46 = 0, $460 = 0;
 var $461 = 0, $462 = 0, $463 = 0, $464 = 0, $465 = 0, $466 = 0, $467 = 0, $468 = 0, $469 = 0, $47 = 0, $470 = 0, $471 = 0, $472 = 0, $473 = 0, $474 = 0, $475 = 0, $476 = 0, $477 = 0, $478 = 0, $479 = 0;
 var $48 = 0, $480 = 0, $481 = 0, $482 = 0, $483 = 0, $484 = 0, $485 = 0, $486 = 0, $487 = 0, $488 = 0, $489 = 0, $49 = 0, $490 = 0, $491 = 0, $492 = 0, $493 = 0, $494 = 0, $495 = 0, $496 = 0, $497 = 0;
 var $498 = 0, $499 = 0, $5 = 0, $50 = 0, $500 = 0, $501 = 0, $502 = 0, $503 = 0, $504 = 0, $505 = 0, $506 = 0, $507 = 0, $508 = 0, $509 = 0, $51 = 0, $510 = 0, $511 = 0, $512 = 0, $513 = 0, $514 = 0;
 var $515 = 0, $516 = 0, $517 = 0, $518 = 0, $519 = 0, $52 = 0, $520 = 0, $521 = 0, $522 = 0, $523 = 0, $524 = 0, $525 = 0, $526 = 0, $527 = 0, $528 = 0, $529 = 0, $53 = 0, $530 = 0, $531 = 0, $532 = 0;
 var $533 = 0, $534 = 0, $535 = 0, $536 = 0, $537 = 0, $538 = 0, $539 = 0, $54 = 0, $540 = 0, $541 = 0, $542 = 0, $543 = 0, $544 = 0, $545 = 0, $546 = 0, $547 = 0, $548 = 0, $549 = 0, $55 = 0, $550 = 0;
 var $551 = 0, $552 = 0, $553 = 0, $554 = 0, $555 = 0, $556 = 0, $557 = 0, $558 = 0, $559 = 0, $56 = 0, $560 = 0, $561 = 0, $562 = 0, $563 = 0, $564 = 0, $565 = 0, $566 = 0, $567 = 0, $568 = 0, $569 = 0;
 var $57 = 0, $570 = 0, $571 = 0, $572 = 0, $573 = 0, $574 = 0, $575 = 0, $576 = 0, $577 = 0, $578 = 0, $579 = 0, $58 = 0, $580 = 0, $581 = 0, $582 = 0, $583 = 0, $584 = 0, $585 = 0, $586 = 0, $587 = 0;
 var $588 = 0, $589 = 0, $59 = 0, $590 = 0, $591 = 0, $592 = 0, $593 = 0, $594 = 0, $595 = 0, $596 = 0, $597 = 0, $598 = 0, $599 = 0, $6 = 0, $60 = 0, $600 = 0, $601 = 0, $602 = 0, $603 = 0, $604 = 0;
 var $605 = 0, $606 = 0, $607 = 0, $608 = 0, $609 = 0, $61 = 0, $610 = 0, $611 = 0, $612 = 0, $613 = 0, $614 = 0, $615 = 0, $616 = 0, $617 = 0, $618 = 0, $619 = 0, $62 = 0, $620 = 0, $621 = 0, $622 = 0;
 var $623 = 0, $624 = 0, $625 = 0, $626 = 0, $627 = 0, $628 = 0, $629 = 0, $63 = 0, $630 = 0, $631 = 0, $632 = 0, $633 = 0, $634 = 0, $635 = 0, $636 = 0, $637 = 0, $638 = 0, $639 = 0, $64 = 0, $640 = 0;
 var $641 = 0, $642 = 0, $643 = 0, $644 = 0, $645 = 0, $646 = 0, $647 = 0, $648 = 0, $649 = 0, $65 = 0, $650 = 0, $651 = 0, $652 = 0, $653 = 0, $654 = 0, $655 = 0, $656 = 0, $657 = 0, $658 = 0, $659 = 0;
 var $66 = 0, $660 = 0, $661 = 0, $662 = 0, $663 = 0, $664 = 0, $665 = 0, $666 = 0, $667 = 0, $668 = 0, $669 = 0, $67 = 0, $670 = 0, $671 = 0, $672 = 0, $673 = 0, $674 = 0, $675 = 0, $676 = 0, $677 = 0;
 var $678 = 0, $679 = 0, $68 = 0, $680 = 0, $681 = 0, $682 = 0, $683 = 0, $684 = 0, $685 = 0, $686 = 0, $687 = 0, $688 = 0, $689 = 0, $69 = 0, $690 = 0, $691 = 0, $692 = 0, $693 = 0, $694 = 0, $695 = 0;
 var $696 = 0, $697 = 0, $698 = 0, $699 = 0, $7 = 0, $70 = 0, $700 = 0, $701 = 0, $702 = 0, $703 = 0, $704 = 0, $705 = 0, $706 = 0, $707 = 0, $708 = 0, $709 = 0, $71 = 0, $710 = 0, $711 = 0, $712 = 0;
 var $713 = 0, $714 = 0, $715 = 0, $716 = 0, $717 = 0, $718 = 0, $719 = 0, $72 = 0, $720 = 0, $721 = 0, $722 = 0, $723 = 0, $724 = 0, $725 = 0, $726 = 0, $727 = 0, $728 = 0, $729 = 0, $73 = 0, $730 = 0;
 var $731 = 0, $732 = 0, $733 = 0, $734 = 0, $735 = 0, $736 = 0, $737 = 0, $738 = 0, $739 = 0, $74 = 0, $740 = 0, $741 = 0, $742 = 0, $743 = 0, $744 = 0, $745 = 0, $746 = 0, $747 = 0, $748 = 0, $749 = 0;
 var $75 = 0, $750 = 0, $751 = 0, $752 = 0, $753 = 0, $754 = 0, $755 = 0, $756 = 0, $757 = 0, $758 = 0, $759 = 0, $76 = 0, $760 = 0, $761 = 0, $762 = 0, $763 = 0, $764 = 0, $765 = 0, $766 = 0, $767 = 0;
 var $768 = 0, $769 = 0, $77 = 0, $770 = 0, $771 = 0, $772 = 0, $773 = 0, $774 = 0, $775 = 0, $776 = 0, $777 = 0, $778 = 0, $779 = 0, $78 = 0, $780 = 0, $781 = 0, $782 = 0, $783 = 0, $784 = 0, $785 = 0;
 var $786 = 0, $787 = 0, $788 = 0, $789 = 0, $79 = 0, $790 = 0, $791 = 0, $792 = 0, $793 = 0, $794 = 0, $795 = 0, $796 = 0, $797 = 0, $798 = 0, $799 = 0, $8 = 0, $80 = 0, $800 = 0, $801 = 0, $802 = 0;
 var $803 = 0, $804 = 0, $805 = 0, $806 = 0, $807 = 0, $808 = 0, $809 = 0, $81 = 0, $810 = 0, $811 = 0, $812 = 0, $813 = 0, $814 = 0, $815 = 0, $816 = 0, $817 = 0, $818 = 0, $819 = 0, $82 = 0, $820 = 0;
 var $821 = 0, $822 = 0, $823 = 0, $824 = 0, $825 = 0, $826 = 0, $827 = 0, $828 = 0, $829 = 0, $83 = 0, $830 = 0, $831 = 0, $832 = 0, $833 = 0, $834 = 0, $835 = 0, $836 = 0, $837 = 0, $838 = 0, $839 = 0;
 var $84 = 0, $840 = 0, $841 = 0, $842 = 0, $843 = 0, $844 = 0, $845 = 0, $846 = 0, $847 = 0, $848 = 0, $849 = 0, $85 = 0, $850 = 0, $851 = 0, $852 = 0, $853 = 0, $854 = 0, $855 = 0, $856 = 0, $857 = 0;
 var $858 = 0, $859 = 0, $86 = 0, $860 = 0, $861 = 0, $862 = 0, $863 = 0, $864 = 0, $865 = 0, $866 = 0, $867 = 0, $868 = 0, $869 = 0, $87 = 0, $870 = 0, $871 = 0, $872 = 0, $873 = 0, $874 = 0, $875 = 0;
 var $876 = 0, $877 = 0, $878 = 0, $879 = 0, $88 = 0, $880 = 0, $881 = 0, $882 = 0, $883 = 0, $884 = 0, $885 = 0, $886 = 0, $887 = 0, $888 = 0, $889 = 0, $89 = 0, $890 = 0, $891 = 0, $892 = 0, $893 = 0;
 var $894 = 0, $895 = 0, $896 = 0, $897 = 0, $898 = 0, $899 = 0, $9 = 0, $90 = 0, $900 = 0, $901 = 0, $902 = 0, $903 = 0, $904 = 0, $905 = 0, $906 = 0, $907 = 0, $908 = 0, $909 = 0, $91 = 0, $910 = 0;
 var $911 = 0, $912 = 0, $913 = 0, $914 = 0, $915 = 0, $916 = 0, $917 = 0, $918 = 0, $919 = 0, $92 = 0, $920 = 0, $921 = 0, $922 = 0, $923 = 0, $924 = 0, $925 = 0, $926 = 0, $927 = 0, $928 = 0, $929 = 0;
 var $93 = 0, $930 = 0, $931 = 0, $932 = 0, $933 = 0, $934 = 0, $935 = 0, $936 = 0, $937 = 0, $938 = 0, $939 = 0, $94 = 0, $940 = 0, $941 = 0, $942 = 0, $943 = 0, $944 = 0, $945 = 0, $946 = 0, $947 = 0;
 var $948 = 0, $949 = 0, $95 = 0, $950 = 0, $951 = 0, $952 = 0, $953 = 0, $954 = 0, $955 = 0, $956 = 0, $957 = 0, $958 = 0, $959 = 0, $96 = 0, $960 = 0, $961 = 0, $962 = 0, $963 = 0, $964 = 0, $965 = 0;
 var $966 = 0, $967 = 0, $968 = 0, $969 = 0, $97 = 0, $970 = 0, $971 = 0, $972 = 0, $973 = 0, $974 = 0, $975 = 0, $976 = 0, $977 = 0, $978 = 0, $979 = 0, $98 = 0, $980 = 0, $981 = 0, $982 = 0, $983 = 0;
 var $984 = 0, $985 = 0, $986 = 0, $987 = 0, $988 = 0, $989 = 0, $99 = 0, $990 = 0, $991 = 0, $992 = 0, $993 = 0, $994 = 0, $995 = 0, $996 = 0, $997 = 0, $998 = 0, $999 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $4 = (_load_3_47($1)|0);
 $5 = tempRet0;
 $6 = $4 & 2097151;
 $7 = ((($1)) + 2|0);
 $8 = (_load_4_48($7)|0);
 $9 = tempRet0;
 $10 = (_bitshift64Lshr(($8|0),($9|0),5)|0);
 $11 = tempRet0;
 $12 = $10 & 2097151;
 $13 = ((($1)) + 5|0);
 $14 = (_load_3_47($13)|0);
 $15 = tempRet0;
 $16 = (_bitshift64Lshr(($14|0),($15|0),2)|0);
 $17 = tempRet0;
 $18 = $16 & 2097151;
 $19 = ((($1)) + 7|0);
 $20 = (_load_4_48($19)|0);
 $21 = tempRet0;
 $22 = (_bitshift64Lshr(($20|0),($21|0),7)|0);
 $23 = tempRet0;
 $24 = $22 & 2097151;
 $25 = ((($1)) + 10|0);
 $26 = (_load_4_48($25)|0);
 $27 = tempRet0;
 $28 = (_bitshift64Lshr(($26|0),($27|0),4)|0);
 $29 = tempRet0;
 $30 = $28 & 2097151;
 $31 = ((($1)) + 13|0);
 $32 = (_load_3_47($31)|0);
 $33 = tempRet0;
 $34 = (_bitshift64Lshr(($32|0),($33|0),1)|0);
 $35 = tempRet0;
 $36 = $34 & 2097151;
 $37 = ((($1)) + 15|0);
 $38 = (_load_4_48($37)|0);
 $39 = tempRet0;
 $40 = (_bitshift64Lshr(($38|0),($39|0),6)|0);
 $41 = tempRet0;
 $42 = $40 & 2097151;
 $43 = ((($1)) + 18|0);
 $44 = (_load_3_47($43)|0);
 $45 = tempRet0;
 $46 = (_bitshift64Lshr(($44|0),($45|0),3)|0);
 $47 = tempRet0;
 $48 = $46 & 2097151;
 $49 = ((($1)) + 21|0);
 $50 = (_load_3_47($49)|0);
 $51 = tempRet0;
 $52 = $50 & 2097151;
 $53 = ((($1)) + 23|0);
 $54 = (_load_4_48($53)|0);
 $55 = tempRet0;
 $56 = (_bitshift64Lshr(($54|0),($55|0),5)|0);
 $57 = tempRet0;
 $58 = $56 & 2097151;
 $59 = ((($1)) + 26|0);
 $60 = (_load_3_47($59)|0);
 $61 = tempRet0;
 $62 = (_bitshift64Lshr(($60|0),($61|0),2)|0);
 $63 = tempRet0;
 $64 = $62 & 2097151;
 $65 = ((($1)) + 28|0);
 $66 = (_load_4_48($65)|0);
 $67 = tempRet0;
 $68 = (_bitshift64Lshr(($66|0),($67|0),7)|0);
 $69 = tempRet0;
 $70 = (_load_3_47($2)|0);
 $71 = tempRet0;
 $72 = $70 & 2097151;
 $73 = ((($2)) + 2|0);
 $74 = (_load_4_48($73)|0);
 $75 = tempRet0;
 $76 = (_bitshift64Lshr(($74|0),($75|0),5)|0);
 $77 = tempRet0;
 $78 = $76 & 2097151;
 $79 = ((($2)) + 5|0);
 $80 = (_load_3_47($79)|0);
 $81 = tempRet0;
 $82 = (_bitshift64Lshr(($80|0),($81|0),2)|0);
 $83 = tempRet0;
 $84 = $82 & 2097151;
 $85 = ((($2)) + 7|0);
 $86 = (_load_4_48($85)|0);
 $87 = tempRet0;
 $88 = (_bitshift64Lshr(($86|0),($87|0),7)|0);
 $89 = tempRet0;
 $90 = $88 & 2097151;
 $91 = ((($2)) + 10|0);
 $92 = (_load_4_48($91)|0);
 $93 = tempRet0;
 $94 = (_bitshift64Lshr(($92|0),($93|0),4)|0);
 $95 = tempRet0;
 $96 = $94 & 2097151;
 $97 = ((($2)) + 13|0);
 $98 = (_load_3_47($97)|0);
 $99 = tempRet0;
 $100 = (_bitshift64Lshr(($98|0),($99|0),1)|0);
 $101 = tempRet0;
 $102 = $100 & 2097151;
 $103 = ((($2)) + 15|0);
 $104 = (_load_4_48($103)|0);
 $105 = tempRet0;
 $106 = (_bitshift64Lshr(($104|0),($105|0),6)|0);
 $107 = tempRet0;
 $108 = $106 & 2097151;
 $109 = ((($2)) + 18|0);
 $110 = (_load_3_47($109)|0);
 $111 = tempRet0;
 $112 = (_bitshift64Lshr(($110|0),($111|0),3)|0);
 $113 = tempRet0;
 $114 = $112 & 2097151;
 $115 = ((($2)) + 21|0);
 $116 = (_load_3_47($115)|0);
 $117 = tempRet0;
 $118 = $116 & 2097151;
 $119 = ((($2)) + 23|0);
 $120 = (_load_4_48($119)|0);
 $121 = tempRet0;
 $122 = (_bitshift64Lshr(($120|0),($121|0),5)|0);
 $123 = tempRet0;
 $124 = $122 & 2097151;
 $125 = ((($2)) + 26|0);
 $126 = (_load_3_47($125)|0);
 $127 = tempRet0;
 $128 = (_bitshift64Lshr(($126|0),($127|0),2)|0);
 $129 = tempRet0;
 $130 = $128 & 2097151;
 $131 = ((($2)) + 28|0);
 $132 = (_load_4_48($131)|0);
 $133 = tempRet0;
 $134 = (_bitshift64Lshr(($132|0),($133|0),7)|0);
 $135 = tempRet0;
 $136 = (_load_3_47($3)|0);
 $137 = tempRet0;
 $138 = $136 & 2097151;
 $139 = ((($3)) + 2|0);
 $140 = (_load_4_48($139)|0);
 $141 = tempRet0;
 $142 = (_bitshift64Lshr(($140|0),($141|0),5)|0);
 $143 = tempRet0;
 $144 = $142 & 2097151;
 $145 = ((($3)) + 5|0);
 $146 = (_load_3_47($145)|0);
 $147 = tempRet0;
 $148 = (_bitshift64Lshr(($146|0),($147|0),2)|0);
 $149 = tempRet0;
 $150 = $148 & 2097151;
 $151 = ((($3)) + 7|0);
 $152 = (_load_4_48($151)|0);
 $153 = tempRet0;
 $154 = (_bitshift64Lshr(($152|0),($153|0),7)|0);
 $155 = tempRet0;
 $156 = $154 & 2097151;
 $157 = ((($3)) + 10|0);
 $158 = (_load_4_48($157)|0);
 $159 = tempRet0;
 $160 = (_bitshift64Lshr(($158|0),($159|0),4)|0);
 $161 = tempRet0;
 $162 = $160 & 2097151;
 $163 = ((($3)) + 13|0);
 $164 = (_load_3_47($163)|0);
 $165 = tempRet0;
 $166 = (_bitshift64Lshr(($164|0),($165|0),1)|0);
 $167 = tempRet0;
 $168 = $166 & 2097151;
 $169 = ((($3)) + 15|0);
 $170 = (_load_4_48($169)|0);
 $171 = tempRet0;
 $172 = (_bitshift64Lshr(($170|0),($171|0),6)|0);
 $173 = tempRet0;
 $174 = $172 & 2097151;
 $175 = ((($3)) + 18|0);
 $176 = (_load_3_47($175)|0);
 $177 = tempRet0;
 $178 = (_bitshift64Lshr(($176|0),($177|0),3)|0);
 $179 = tempRet0;
 $180 = $178 & 2097151;
 $181 = ((($3)) + 21|0);
 $182 = (_load_3_47($181)|0);
 $183 = tempRet0;
 $184 = $182 & 2097151;
 $185 = ((($3)) + 23|0);
 $186 = (_load_4_48($185)|0);
 $187 = tempRet0;
 $188 = (_bitshift64Lshr(($186|0),($187|0),5)|0);
 $189 = tempRet0;
 $190 = $188 & 2097151;
 $191 = ((($3)) + 26|0);
 $192 = (_load_3_47($191)|0);
 $193 = tempRet0;
 $194 = (_bitshift64Lshr(($192|0),($193|0),2)|0);
 $195 = tempRet0;
 $196 = $194 & 2097151;
 $197 = ((($3)) + 28|0);
 $198 = (_load_4_48($197)|0);
 $199 = tempRet0;
 $200 = (_bitshift64Lshr(($198|0),($199|0),7)|0);
 $201 = tempRet0;
 $202 = (___muldi3(($72|0),0,($6|0),0)|0);
 $203 = tempRet0;
 $204 = (_i64Add(($138|0),0,($202|0),($203|0))|0);
 $205 = tempRet0;
 $206 = (___muldi3(($78|0),0,($6|0),0)|0);
 $207 = tempRet0;
 $208 = (___muldi3(($72|0),0,($12|0),0)|0);
 $209 = tempRet0;
 $210 = (___muldi3(($84|0),0,($6|0),0)|0);
 $211 = tempRet0;
 $212 = (___muldi3(($78|0),0,($12|0),0)|0);
 $213 = tempRet0;
 $214 = (___muldi3(($72|0),0,($18|0),0)|0);
 $215 = tempRet0;
 $216 = (_i64Add(($212|0),($213|0),($214|0),($215|0))|0);
 $217 = tempRet0;
 $218 = (_i64Add(($216|0),($217|0),($210|0),($211|0))|0);
 $219 = tempRet0;
 $220 = (_i64Add(($218|0),($219|0),($150|0),0)|0);
 $221 = tempRet0;
 $222 = (___muldi3(($90|0),0,($6|0),0)|0);
 $223 = tempRet0;
 $224 = (___muldi3(($84|0),0,($12|0),0)|0);
 $225 = tempRet0;
 $226 = (___muldi3(($78|0),0,($18|0),0)|0);
 $227 = tempRet0;
 $228 = (___muldi3(($72|0),0,($24|0),0)|0);
 $229 = tempRet0;
 $230 = (___muldi3(($96|0),0,($6|0),0)|0);
 $231 = tempRet0;
 $232 = (___muldi3(($90|0),0,($12|0),0)|0);
 $233 = tempRet0;
 $234 = (___muldi3(($84|0),0,($18|0),0)|0);
 $235 = tempRet0;
 $236 = (___muldi3(($78|0),0,($24|0),0)|0);
 $237 = tempRet0;
 $238 = (___muldi3(($72|0),0,($30|0),0)|0);
 $239 = tempRet0;
 $240 = (_i64Add(($236|0),($237|0),($238|0),($239|0))|0);
 $241 = tempRet0;
 $242 = (_i64Add(($240|0),($241|0),($234|0),($235|0))|0);
 $243 = tempRet0;
 $244 = (_i64Add(($242|0),($243|0),($232|0),($233|0))|0);
 $245 = tempRet0;
 $246 = (_i64Add(($244|0),($245|0),($230|0),($231|0))|0);
 $247 = tempRet0;
 $248 = (_i64Add(($246|0),($247|0),($162|0),0)|0);
 $249 = tempRet0;
 $250 = (___muldi3(($102|0),0,($6|0),0)|0);
 $251 = tempRet0;
 $252 = (___muldi3(($96|0),0,($12|0),0)|0);
 $253 = tempRet0;
 $254 = (___muldi3(($90|0),0,($18|0),0)|0);
 $255 = tempRet0;
 $256 = (___muldi3(($84|0),0,($24|0),0)|0);
 $257 = tempRet0;
 $258 = (___muldi3(($78|0),0,($30|0),0)|0);
 $259 = tempRet0;
 $260 = (___muldi3(($72|0),0,($36|0),0)|0);
 $261 = tempRet0;
 $262 = (___muldi3(($108|0),0,($6|0),0)|0);
 $263 = tempRet0;
 $264 = (___muldi3(($102|0),0,($12|0),0)|0);
 $265 = tempRet0;
 $266 = (___muldi3(($96|0),0,($18|0),0)|0);
 $267 = tempRet0;
 $268 = (___muldi3(($90|0),0,($24|0),0)|0);
 $269 = tempRet0;
 $270 = (___muldi3(($84|0),0,($30|0),0)|0);
 $271 = tempRet0;
 $272 = (___muldi3(($78|0),0,($36|0),0)|0);
 $273 = tempRet0;
 $274 = (___muldi3(($72|0),0,($42|0),0)|0);
 $275 = tempRet0;
 $276 = (_i64Add(($272|0),($273|0),($274|0),($275|0))|0);
 $277 = tempRet0;
 $278 = (_i64Add(($276|0),($277|0),($270|0),($271|0))|0);
 $279 = tempRet0;
 $280 = (_i64Add(($278|0),($279|0),($268|0),($269|0))|0);
 $281 = tempRet0;
 $282 = (_i64Add(($280|0),($281|0),($266|0),($267|0))|0);
 $283 = tempRet0;
 $284 = (_i64Add(($282|0),($283|0),($264|0),($265|0))|0);
 $285 = tempRet0;
 $286 = (_i64Add(($284|0),($285|0),($262|0),($263|0))|0);
 $287 = tempRet0;
 $288 = (_i64Add(($286|0),($287|0),($174|0),0)|0);
 $289 = tempRet0;
 $290 = (___muldi3(($114|0),0,($6|0),0)|0);
 $291 = tempRet0;
 $292 = (___muldi3(($108|0),0,($12|0),0)|0);
 $293 = tempRet0;
 $294 = (___muldi3(($102|0),0,($18|0),0)|0);
 $295 = tempRet0;
 $296 = (___muldi3(($96|0),0,($24|0),0)|0);
 $297 = tempRet0;
 $298 = (___muldi3(($90|0),0,($30|0),0)|0);
 $299 = tempRet0;
 $300 = (___muldi3(($84|0),0,($36|0),0)|0);
 $301 = tempRet0;
 $302 = (___muldi3(($78|0),0,($42|0),0)|0);
 $303 = tempRet0;
 $304 = (___muldi3(($72|0),0,($48|0),0)|0);
 $305 = tempRet0;
 $306 = (___muldi3(($118|0),0,($6|0),0)|0);
 $307 = tempRet0;
 $308 = (___muldi3(($114|0),0,($12|0),0)|0);
 $309 = tempRet0;
 $310 = (___muldi3(($108|0),0,($18|0),0)|0);
 $311 = tempRet0;
 $312 = (___muldi3(($102|0),0,($24|0),0)|0);
 $313 = tempRet0;
 $314 = (___muldi3(($96|0),0,($30|0),0)|0);
 $315 = tempRet0;
 $316 = (___muldi3(($90|0),0,($36|0),0)|0);
 $317 = tempRet0;
 $318 = (___muldi3(($84|0),0,($42|0),0)|0);
 $319 = tempRet0;
 $320 = (___muldi3(($78|0),0,($48|0),0)|0);
 $321 = tempRet0;
 $322 = (___muldi3(($72|0),0,($52|0),0)|0);
 $323 = tempRet0;
 $324 = (_i64Add(($320|0),($321|0),($322|0),($323|0))|0);
 $325 = tempRet0;
 $326 = (_i64Add(($324|0),($325|0),($318|0),($319|0))|0);
 $327 = tempRet0;
 $328 = (_i64Add(($326|0),($327|0),($316|0),($317|0))|0);
 $329 = tempRet0;
 $330 = (_i64Add(($328|0),($329|0),($314|0),($315|0))|0);
 $331 = tempRet0;
 $332 = (_i64Add(($330|0),($331|0),($312|0),($313|0))|0);
 $333 = tempRet0;
 $334 = (_i64Add(($332|0),($333|0),($310|0),($311|0))|0);
 $335 = tempRet0;
 $336 = (_i64Add(($334|0),($335|0),($306|0),($307|0))|0);
 $337 = tempRet0;
 $338 = (_i64Add(($336|0),($337|0),($308|0),($309|0))|0);
 $339 = tempRet0;
 $340 = (_i64Add(($338|0),($339|0),($184|0),0)|0);
 $341 = tempRet0;
 $342 = (___muldi3(($124|0),0,($6|0),0)|0);
 $343 = tempRet0;
 $344 = (___muldi3(($118|0),0,($12|0),0)|0);
 $345 = tempRet0;
 $346 = (___muldi3(($114|0),0,($18|0),0)|0);
 $347 = tempRet0;
 $348 = (___muldi3(($108|0),0,($24|0),0)|0);
 $349 = tempRet0;
 $350 = (___muldi3(($102|0),0,($30|0),0)|0);
 $351 = tempRet0;
 $352 = (___muldi3(($96|0),0,($36|0),0)|0);
 $353 = tempRet0;
 $354 = (___muldi3(($90|0),0,($42|0),0)|0);
 $355 = tempRet0;
 $356 = (___muldi3(($84|0),0,($48|0),0)|0);
 $357 = tempRet0;
 $358 = (___muldi3(($78|0),0,($52|0),0)|0);
 $359 = tempRet0;
 $360 = (___muldi3(($72|0),0,($58|0),0)|0);
 $361 = tempRet0;
 $362 = (___muldi3(($130|0),0,($6|0),0)|0);
 $363 = tempRet0;
 $364 = (___muldi3(($124|0),0,($12|0),0)|0);
 $365 = tempRet0;
 $366 = (___muldi3(($118|0),0,($18|0),0)|0);
 $367 = tempRet0;
 $368 = (___muldi3(($114|0),0,($24|0),0)|0);
 $369 = tempRet0;
 $370 = (___muldi3(($108|0),0,($30|0),0)|0);
 $371 = tempRet0;
 $372 = (___muldi3(($102|0),0,($36|0),0)|0);
 $373 = tempRet0;
 $374 = (___muldi3(($96|0),0,($42|0),0)|0);
 $375 = tempRet0;
 $376 = (___muldi3(($90|0),0,($48|0),0)|0);
 $377 = tempRet0;
 $378 = (___muldi3(($84|0),0,($52|0),0)|0);
 $379 = tempRet0;
 $380 = (___muldi3(($78|0),0,($58|0),0)|0);
 $381 = tempRet0;
 $382 = (___muldi3(($72|0),0,($64|0),0)|0);
 $383 = tempRet0;
 $384 = (_i64Add(($380|0),($381|0),($382|0),($383|0))|0);
 $385 = tempRet0;
 $386 = (_i64Add(($384|0),($385|0),($378|0),($379|0))|0);
 $387 = tempRet0;
 $388 = (_i64Add(($386|0),($387|0),($376|0),($377|0))|0);
 $389 = tempRet0;
 $390 = (_i64Add(($388|0),($389|0),($374|0),($375|0))|0);
 $391 = tempRet0;
 $392 = (_i64Add(($390|0),($391|0),($372|0),($373|0))|0);
 $393 = tempRet0;
 $394 = (_i64Add(($392|0),($393|0),($370|0),($371|0))|0);
 $395 = tempRet0;
 $396 = (_i64Add(($394|0),($395|0),($366|0),($367|0))|0);
 $397 = tempRet0;
 $398 = (_i64Add(($396|0),($397|0),($368|0),($369|0))|0);
 $399 = tempRet0;
 $400 = (_i64Add(($398|0),($399|0),($364|0),($365|0))|0);
 $401 = tempRet0;
 $402 = (_i64Add(($400|0),($401|0),($362|0),($363|0))|0);
 $403 = tempRet0;
 $404 = (_i64Add(($402|0),($403|0),($196|0),0)|0);
 $405 = tempRet0;
 $406 = (___muldi3(($134|0),($135|0),($6|0),0)|0);
 $407 = tempRet0;
 $408 = (___muldi3(($130|0),0,($12|0),0)|0);
 $409 = tempRet0;
 $410 = (___muldi3(($124|0),0,($18|0),0)|0);
 $411 = tempRet0;
 $412 = (___muldi3(($118|0),0,($24|0),0)|0);
 $413 = tempRet0;
 $414 = (___muldi3(($114|0),0,($30|0),0)|0);
 $415 = tempRet0;
 $416 = (___muldi3(($108|0),0,($36|0),0)|0);
 $417 = tempRet0;
 $418 = (___muldi3(($102|0),0,($42|0),0)|0);
 $419 = tempRet0;
 $420 = (___muldi3(($96|0),0,($48|0),0)|0);
 $421 = tempRet0;
 $422 = (___muldi3(($90|0),0,($52|0),0)|0);
 $423 = tempRet0;
 $424 = (___muldi3(($84|0),0,($58|0),0)|0);
 $425 = tempRet0;
 $426 = (___muldi3(($78|0),0,($64|0),0)|0);
 $427 = tempRet0;
 $428 = (___muldi3(($72|0),0,($68|0),($69|0))|0);
 $429 = tempRet0;
 $430 = (___muldi3(($134|0),($135|0),($12|0),0)|0);
 $431 = tempRet0;
 $432 = (___muldi3(($130|0),0,($18|0),0)|0);
 $433 = tempRet0;
 $434 = (___muldi3(($124|0),0,($24|0),0)|0);
 $435 = tempRet0;
 $436 = (___muldi3(($118|0),0,($30|0),0)|0);
 $437 = tempRet0;
 $438 = (___muldi3(($114|0),0,($36|0),0)|0);
 $439 = tempRet0;
 $440 = (___muldi3(($108|0),0,($42|0),0)|0);
 $441 = tempRet0;
 $442 = (___muldi3(($102|0),0,($48|0),0)|0);
 $443 = tempRet0;
 $444 = (___muldi3(($96|0),0,($52|0),0)|0);
 $445 = tempRet0;
 $446 = (___muldi3(($90|0),0,($58|0),0)|0);
 $447 = tempRet0;
 $448 = (___muldi3(($84|0),0,($64|0),0)|0);
 $449 = tempRet0;
 $450 = (___muldi3(($78|0),0,($68|0),($69|0))|0);
 $451 = tempRet0;
 $452 = (_i64Add(($448|0),($449|0),($450|0),($451|0))|0);
 $453 = tempRet0;
 $454 = (_i64Add(($452|0),($453|0),($446|0),($447|0))|0);
 $455 = tempRet0;
 $456 = (_i64Add(($454|0),($455|0),($444|0),($445|0))|0);
 $457 = tempRet0;
 $458 = (_i64Add(($456|0),($457|0),($442|0),($443|0))|0);
 $459 = tempRet0;
 $460 = (_i64Add(($458|0),($459|0),($440|0),($441|0))|0);
 $461 = tempRet0;
 $462 = (_i64Add(($460|0),($461|0),($436|0),($437|0))|0);
 $463 = tempRet0;
 $464 = (_i64Add(($462|0),($463|0),($438|0),($439|0))|0);
 $465 = tempRet0;
 $466 = (_i64Add(($464|0),($465|0),($434|0),($435|0))|0);
 $467 = tempRet0;
 $468 = (_i64Add(($466|0),($467|0),($432|0),($433|0))|0);
 $469 = tempRet0;
 $470 = (_i64Add(($468|0),($469|0),($430|0),($431|0))|0);
 $471 = tempRet0;
 $472 = (___muldi3(($134|0),($135|0),($18|0),0)|0);
 $473 = tempRet0;
 $474 = (___muldi3(($130|0),0,($24|0),0)|0);
 $475 = tempRet0;
 $476 = (___muldi3(($124|0),0,($30|0),0)|0);
 $477 = tempRet0;
 $478 = (___muldi3(($118|0),0,($36|0),0)|0);
 $479 = tempRet0;
 $480 = (___muldi3(($114|0),0,($42|0),0)|0);
 $481 = tempRet0;
 $482 = (___muldi3(($108|0),0,($48|0),0)|0);
 $483 = tempRet0;
 $484 = (___muldi3(($102|0),0,($52|0),0)|0);
 $485 = tempRet0;
 $486 = (___muldi3(($96|0),0,($58|0),0)|0);
 $487 = tempRet0;
 $488 = (___muldi3(($90|0),0,($64|0),0)|0);
 $489 = tempRet0;
 $490 = (___muldi3(($84|0),0,($68|0),($69|0))|0);
 $491 = tempRet0;
 $492 = (___muldi3(($134|0),($135|0),($24|0),0)|0);
 $493 = tempRet0;
 $494 = (___muldi3(($130|0),0,($30|0),0)|0);
 $495 = tempRet0;
 $496 = (___muldi3(($124|0),0,($36|0),0)|0);
 $497 = tempRet0;
 $498 = (___muldi3(($118|0),0,($42|0),0)|0);
 $499 = tempRet0;
 $500 = (___muldi3(($114|0),0,($48|0),0)|0);
 $501 = tempRet0;
 $502 = (___muldi3(($108|0),0,($52|0),0)|0);
 $503 = tempRet0;
 $504 = (___muldi3(($102|0),0,($58|0),0)|0);
 $505 = tempRet0;
 $506 = (___muldi3(($96|0),0,($64|0),0)|0);
 $507 = tempRet0;
 $508 = (___muldi3(($90|0),0,($68|0),($69|0))|0);
 $509 = tempRet0;
 $510 = (_i64Add(($506|0),($507|0),($508|0),($509|0))|0);
 $511 = tempRet0;
 $512 = (_i64Add(($510|0),($511|0),($504|0),($505|0))|0);
 $513 = tempRet0;
 $514 = (_i64Add(($512|0),($513|0),($502|0),($503|0))|0);
 $515 = tempRet0;
 $516 = (_i64Add(($514|0),($515|0),($498|0),($499|0))|0);
 $517 = tempRet0;
 $518 = (_i64Add(($516|0),($517|0),($500|0),($501|0))|0);
 $519 = tempRet0;
 $520 = (_i64Add(($518|0),($519|0),($496|0),($497|0))|0);
 $521 = tempRet0;
 $522 = (_i64Add(($520|0),($521|0),($494|0),($495|0))|0);
 $523 = tempRet0;
 $524 = (_i64Add(($522|0),($523|0),($492|0),($493|0))|0);
 $525 = tempRet0;
 $526 = (___muldi3(($134|0),($135|0),($30|0),0)|0);
 $527 = tempRet0;
 $528 = (___muldi3(($130|0),0,($36|0),0)|0);
 $529 = tempRet0;
 $530 = (___muldi3(($124|0),0,($42|0),0)|0);
 $531 = tempRet0;
 $532 = (___muldi3(($118|0),0,($48|0),0)|0);
 $533 = tempRet0;
 $534 = (___muldi3(($114|0),0,($52|0),0)|0);
 $535 = tempRet0;
 $536 = (___muldi3(($108|0),0,($58|0),0)|0);
 $537 = tempRet0;
 $538 = (___muldi3(($102|0),0,($64|0),0)|0);
 $539 = tempRet0;
 $540 = (___muldi3(($96|0),0,($68|0),($69|0))|0);
 $541 = tempRet0;
 $542 = (___muldi3(($134|0),($135|0),($36|0),0)|0);
 $543 = tempRet0;
 $544 = (___muldi3(($130|0),0,($42|0),0)|0);
 $545 = tempRet0;
 $546 = (___muldi3(($124|0),0,($48|0),0)|0);
 $547 = tempRet0;
 $548 = (___muldi3(($118|0),0,($52|0),0)|0);
 $549 = tempRet0;
 $550 = (___muldi3(($114|0),0,($58|0),0)|0);
 $551 = tempRet0;
 $552 = (___muldi3(($108|0),0,($64|0),0)|0);
 $553 = tempRet0;
 $554 = (___muldi3(($102|0),0,($68|0),($69|0))|0);
 $555 = tempRet0;
 $556 = (_i64Add(($552|0),($553|0),($554|0),($555|0))|0);
 $557 = tempRet0;
 $558 = (_i64Add(($556|0),($557|0),($548|0),($549|0))|0);
 $559 = tempRet0;
 $560 = (_i64Add(($558|0),($559|0),($550|0),($551|0))|0);
 $561 = tempRet0;
 $562 = (_i64Add(($560|0),($561|0),($546|0),($547|0))|0);
 $563 = tempRet0;
 $564 = (_i64Add(($562|0),($563|0),($544|0),($545|0))|0);
 $565 = tempRet0;
 $566 = (_i64Add(($564|0),($565|0),($542|0),($543|0))|0);
 $567 = tempRet0;
 $568 = (___muldi3(($134|0),($135|0),($42|0),0)|0);
 $569 = tempRet0;
 $570 = (___muldi3(($130|0),0,($48|0),0)|0);
 $571 = tempRet0;
 $572 = (___muldi3(($124|0),0,($52|0),0)|0);
 $573 = tempRet0;
 $574 = (___muldi3(($118|0),0,($58|0),0)|0);
 $575 = tempRet0;
 $576 = (___muldi3(($114|0),0,($64|0),0)|0);
 $577 = tempRet0;
 $578 = (___muldi3(($108|0),0,($68|0),($69|0))|0);
 $579 = tempRet0;
 $580 = (___muldi3(($134|0),($135|0),($48|0),0)|0);
 $581 = tempRet0;
 $582 = (___muldi3(($130|0),0,($52|0),0)|0);
 $583 = tempRet0;
 $584 = (___muldi3(($124|0),0,($58|0),0)|0);
 $585 = tempRet0;
 $586 = (___muldi3(($118|0),0,($64|0),0)|0);
 $587 = tempRet0;
 $588 = (___muldi3(($114|0),0,($68|0),($69|0))|0);
 $589 = tempRet0;
 $590 = (_i64Add(($588|0),($589|0),($586|0),($587|0))|0);
 $591 = tempRet0;
 $592 = (_i64Add(($590|0),($591|0),($584|0),($585|0))|0);
 $593 = tempRet0;
 $594 = (_i64Add(($592|0),($593|0),($582|0),($583|0))|0);
 $595 = tempRet0;
 $596 = (_i64Add(($594|0),($595|0),($580|0),($581|0))|0);
 $597 = tempRet0;
 $598 = (___muldi3(($134|0),($135|0),($52|0),0)|0);
 $599 = tempRet0;
 $600 = (___muldi3(($130|0),0,($58|0),0)|0);
 $601 = tempRet0;
 $602 = (___muldi3(($124|0),0,($64|0),0)|0);
 $603 = tempRet0;
 $604 = (___muldi3(($118|0),0,($68|0),($69|0))|0);
 $605 = tempRet0;
 $606 = (___muldi3(($134|0),($135|0),($58|0),0)|0);
 $607 = tempRet0;
 $608 = (___muldi3(($130|0),0,($64|0),0)|0);
 $609 = tempRet0;
 $610 = (___muldi3(($124|0),0,($68|0),($69|0))|0);
 $611 = tempRet0;
 $612 = (_i64Add(($608|0),($609|0),($610|0),($611|0))|0);
 $613 = tempRet0;
 $614 = (_i64Add(($612|0),($613|0),($606|0),($607|0))|0);
 $615 = tempRet0;
 $616 = (___muldi3(($134|0),($135|0),($64|0),0)|0);
 $617 = tempRet0;
 $618 = (___muldi3(($130|0),0,($68|0),($69|0))|0);
 $619 = tempRet0;
 $620 = (_i64Add(($616|0),($617|0),($618|0),($619|0))|0);
 $621 = tempRet0;
 $622 = (___muldi3(($134|0),($135|0),($68|0),($69|0))|0);
 $623 = tempRet0;
 $624 = (_i64Add(($204|0),($205|0),1048576,0)|0);
 $625 = tempRet0;
 $626 = (_bitshift64Lshr(($624|0),($625|0),21)|0);
 $627 = tempRet0;
 $628 = (_i64Add(($206|0),($207|0),($208|0),($209|0))|0);
 $629 = tempRet0;
 $630 = (_i64Add(($628|0),($629|0),($144|0),0)|0);
 $631 = tempRet0;
 $632 = (_i64Add(($630|0),($631|0),($626|0),($627|0))|0);
 $633 = tempRet0;
 $634 = $624 & -2097152;
 $635 = $625 & 4095;
 $636 = (_i64Subtract(($204|0),($205|0),($634|0),($635|0))|0);
 $637 = tempRet0;
 $638 = (_i64Add(($220|0),($221|0),1048576,0)|0);
 $639 = tempRet0;
 $640 = (_bitshift64Lshr(($638|0),($639|0),21)|0);
 $641 = tempRet0;
 $642 = (_i64Add(($226|0),($227|0),($228|0),($229|0))|0);
 $643 = tempRet0;
 $644 = (_i64Add(($642|0),($643|0),($224|0),($225|0))|0);
 $645 = tempRet0;
 $646 = (_i64Add(($644|0),($645|0),($222|0),($223|0))|0);
 $647 = tempRet0;
 $648 = (_i64Add(($646|0),($647|0),($156|0),0)|0);
 $649 = tempRet0;
 $650 = (_i64Add(($648|0),($649|0),($640|0),($641|0))|0);
 $651 = tempRet0;
 $652 = $638 & -2097152;
 $653 = (_i64Add(($248|0),($249|0),1048576,0)|0);
 $654 = tempRet0;
 $655 = (_bitshift64Ashr(($653|0),($654|0),21)|0);
 $656 = tempRet0;
 $657 = (_i64Add(($258|0),($259|0),($260|0),($261|0))|0);
 $658 = tempRet0;
 $659 = (_i64Add(($657|0),($658|0),($256|0),($257|0))|0);
 $660 = tempRet0;
 $661 = (_i64Add(($659|0),($660|0),($254|0),($255|0))|0);
 $662 = tempRet0;
 $663 = (_i64Add(($661|0),($662|0),($252|0),($253|0))|0);
 $664 = tempRet0;
 $665 = (_i64Add(($663|0),($664|0),($250|0),($251|0))|0);
 $666 = tempRet0;
 $667 = (_i64Add(($665|0),($666|0),($168|0),0)|0);
 $668 = tempRet0;
 $669 = (_i64Add(($667|0),($668|0),($655|0),($656|0))|0);
 $670 = tempRet0;
 $671 = (_bitshift64Shl(($655|0),($656|0),21)|0);
 $672 = tempRet0;
 $673 = (_i64Add(($288|0),($289|0),1048576,0)|0);
 $674 = tempRet0;
 $675 = (_bitshift64Ashr(($673|0),($674|0),21)|0);
 $676 = tempRet0;
 $677 = (_i64Add(($302|0),($303|0),($304|0),($305|0))|0);
 $678 = tempRet0;
 $679 = (_i64Add(($677|0),($678|0),($300|0),($301|0))|0);
 $680 = tempRet0;
 $681 = (_i64Add(($679|0),($680|0),($298|0),($299|0))|0);
 $682 = tempRet0;
 $683 = (_i64Add(($681|0),($682|0),($296|0),($297|0))|0);
 $684 = tempRet0;
 $685 = (_i64Add(($683|0),($684|0),($294|0),($295|0))|0);
 $686 = tempRet0;
 $687 = (_i64Add(($685|0),($686|0),($292|0),($293|0))|0);
 $688 = tempRet0;
 $689 = (_i64Add(($687|0),($688|0),($290|0),($291|0))|0);
 $690 = tempRet0;
 $691 = (_i64Add(($689|0),($690|0),($180|0),0)|0);
 $692 = tempRet0;
 $693 = (_i64Add(($691|0),($692|0),($675|0),($676|0))|0);
 $694 = tempRet0;
 $695 = (_bitshift64Shl(($675|0),($676|0),21)|0);
 $696 = tempRet0;
 $697 = (_i64Add(($340|0),($341|0),1048576,0)|0);
 $698 = tempRet0;
 $699 = (_bitshift64Ashr(($697|0),($698|0),21)|0);
 $700 = tempRet0;
 $701 = (_i64Add(($358|0),($359|0),($360|0),($361|0))|0);
 $702 = tempRet0;
 $703 = (_i64Add(($701|0),($702|0),($356|0),($357|0))|0);
 $704 = tempRet0;
 $705 = (_i64Add(($703|0),($704|0),($354|0),($355|0))|0);
 $706 = tempRet0;
 $707 = (_i64Add(($705|0),($706|0),($352|0),($353|0))|0);
 $708 = tempRet0;
 $709 = (_i64Add(($707|0),($708|0),($350|0),($351|0))|0);
 $710 = tempRet0;
 $711 = (_i64Add(($709|0),($710|0),($348|0),($349|0))|0);
 $712 = tempRet0;
 $713 = (_i64Add(($711|0),($712|0),($344|0),($345|0))|0);
 $714 = tempRet0;
 $715 = (_i64Add(($713|0),($714|0),($346|0),($347|0))|0);
 $716 = tempRet0;
 $717 = (_i64Add(($715|0),($716|0),($342|0),($343|0))|0);
 $718 = tempRet0;
 $719 = (_i64Add(($717|0),($718|0),($190|0),0)|0);
 $720 = tempRet0;
 $721 = (_i64Add(($719|0),($720|0),($699|0),($700|0))|0);
 $722 = tempRet0;
 $723 = (_bitshift64Shl(($699|0),($700|0),21)|0);
 $724 = tempRet0;
 $725 = (_i64Add(($404|0),($405|0),1048576,0)|0);
 $726 = tempRet0;
 $727 = (_bitshift64Ashr(($725|0),($726|0),21)|0);
 $728 = tempRet0;
 $729 = (_i64Add(($426|0),($427|0),($428|0),($429|0))|0);
 $730 = tempRet0;
 $731 = (_i64Add(($729|0),($730|0),($424|0),($425|0))|0);
 $732 = tempRet0;
 $733 = (_i64Add(($731|0),($732|0),($422|0),($423|0))|0);
 $734 = tempRet0;
 $735 = (_i64Add(($733|0),($734|0),($420|0),($421|0))|0);
 $736 = tempRet0;
 $737 = (_i64Add(($735|0),($736|0),($418|0),($419|0))|0);
 $738 = tempRet0;
 $739 = (_i64Add(($737|0),($738|0),($416|0),($417|0))|0);
 $740 = tempRet0;
 $741 = (_i64Add(($739|0),($740|0),($412|0),($413|0))|0);
 $742 = tempRet0;
 $743 = (_i64Add(($741|0),($742|0),($414|0),($415|0))|0);
 $744 = tempRet0;
 $745 = (_i64Add(($743|0),($744|0),($410|0),($411|0))|0);
 $746 = tempRet0;
 $747 = (_i64Add(($745|0),($746|0),($406|0),($407|0))|0);
 $748 = tempRet0;
 $749 = (_i64Add(($747|0),($748|0),($408|0),($409|0))|0);
 $750 = tempRet0;
 $751 = (_i64Add(($749|0),($750|0),($200|0),($201|0))|0);
 $752 = tempRet0;
 $753 = (_i64Add(($751|0),($752|0),($727|0),($728|0))|0);
 $754 = tempRet0;
 $755 = (_bitshift64Shl(($727|0),($728|0),21)|0);
 $756 = tempRet0;
 $757 = (_i64Add(($470|0),($471|0),1048576,0)|0);
 $758 = tempRet0;
 $759 = (_bitshift64Ashr(($757|0),($758|0),21)|0);
 $760 = tempRet0;
 $761 = (_i64Add(($488|0),($489|0),($490|0),($491|0))|0);
 $762 = tempRet0;
 $763 = (_i64Add(($761|0),($762|0),($486|0),($487|0))|0);
 $764 = tempRet0;
 $765 = (_i64Add(($763|0),($764|0),($484|0),($485|0))|0);
 $766 = tempRet0;
 $767 = (_i64Add(($765|0),($766|0),($482|0),($483|0))|0);
 $768 = tempRet0;
 $769 = (_i64Add(($767|0),($768|0),($478|0),($479|0))|0);
 $770 = tempRet0;
 $771 = (_i64Add(($769|0),($770|0),($480|0),($481|0))|0);
 $772 = tempRet0;
 $773 = (_i64Add(($771|0),($772|0),($476|0),($477|0))|0);
 $774 = tempRet0;
 $775 = (_i64Add(($773|0),($774|0),($474|0),($475|0))|0);
 $776 = tempRet0;
 $777 = (_i64Add(($775|0),($776|0),($472|0),($473|0))|0);
 $778 = tempRet0;
 $779 = (_i64Add(($777|0),($778|0),($759|0),($760|0))|0);
 $780 = tempRet0;
 $781 = (_bitshift64Shl(($759|0),($760|0),21)|0);
 $782 = tempRet0;
 $783 = (_i64Add(($524|0),($525|0),1048576,0)|0);
 $784 = tempRet0;
 $785 = (_bitshift64Ashr(($783|0),($784|0),21)|0);
 $786 = tempRet0;
 $787 = (_i64Add(($538|0),($539|0),($540|0),($541|0))|0);
 $788 = tempRet0;
 $789 = (_i64Add(($787|0),($788|0),($536|0),($537|0))|0);
 $790 = tempRet0;
 $791 = (_i64Add(($789|0),($790|0),($532|0),($533|0))|0);
 $792 = tempRet0;
 $793 = (_i64Add(($791|0),($792|0),($534|0),($535|0))|0);
 $794 = tempRet0;
 $795 = (_i64Add(($793|0),($794|0),($530|0),($531|0))|0);
 $796 = tempRet0;
 $797 = (_i64Add(($795|0),($796|0),($528|0),($529|0))|0);
 $798 = tempRet0;
 $799 = (_i64Add(($797|0),($798|0),($526|0),($527|0))|0);
 $800 = tempRet0;
 $801 = (_i64Add(($799|0),($800|0),($785|0),($786|0))|0);
 $802 = tempRet0;
 $803 = (_bitshift64Shl(($785|0),($786|0),21)|0);
 $804 = tempRet0;
 $805 = (_i64Add(($566|0),($567|0),1048576,0)|0);
 $806 = tempRet0;
 $807 = (_bitshift64Ashr(($805|0),($806|0),21)|0);
 $808 = tempRet0;
 $809 = (_i64Add(($574|0),($575|0),($578|0),($579|0))|0);
 $810 = tempRet0;
 $811 = (_i64Add(($809|0),($810|0),($576|0),($577|0))|0);
 $812 = tempRet0;
 $813 = (_i64Add(($811|0),($812|0),($572|0),($573|0))|0);
 $814 = tempRet0;
 $815 = (_i64Add(($813|0),($814|0),($570|0),($571|0))|0);
 $816 = tempRet0;
 $817 = (_i64Add(($815|0),($816|0),($568|0),($569|0))|0);
 $818 = tempRet0;
 $819 = (_i64Add(($817|0),($818|0),($807|0),($808|0))|0);
 $820 = tempRet0;
 $821 = (_bitshift64Shl(($807|0),($808|0),21)|0);
 $822 = tempRet0;
 $823 = (_i64Add(($596|0),($597|0),1048576,0)|0);
 $824 = tempRet0;
 $825 = (_bitshift64Ashr(($823|0),($824|0),21)|0);
 $826 = tempRet0;
 $827 = (_i64Add(($602|0),($603|0),($604|0),($605|0))|0);
 $828 = tempRet0;
 $829 = (_i64Add(($827|0),($828|0),($600|0),($601|0))|0);
 $830 = tempRet0;
 $831 = (_i64Add(($829|0),($830|0),($598|0),($599|0))|0);
 $832 = tempRet0;
 $833 = (_i64Add(($831|0),($832|0),($825|0),($826|0))|0);
 $834 = tempRet0;
 $835 = (_bitshift64Shl(($825|0),($826|0),21)|0);
 $836 = tempRet0;
 $837 = (_i64Subtract(($596|0),($597|0),($835|0),($836|0))|0);
 $838 = tempRet0;
 $839 = (_i64Add(($614|0),($615|0),1048576,0)|0);
 $840 = tempRet0;
 $841 = (_bitshift64Lshr(($839|0),($840|0),21)|0);
 $842 = tempRet0;
 $843 = (_i64Add(($620|0),($621|0),($841|0),($842|0))|0);
 $844 = tempRet0;
 $845 = $839 & -2097152;
 $846 = $840 & 2147483647;
 $847 = (_i64Subtract(($614|0),($615|0),($845|0),($846|0))|0);
 $848 = tempRet0;
 $849 = (_i64Add(($622|0),($623|0),1048576,0)|0);
 $850 = tempRet0;
 $851 = (_bitshift64Lshr(($849|0),($850|0),21)|0);
 $852 = tempRet0;
 $853 = $849 & -2097152;
 $854 = $850 & 2147483647;
 $855 = (_i64Subtract(($622|0),($623|0),($853|0),($854|0))|0);
 $856 = tempRet0;
 $857 = (_i64Add(($632|0),($633|0),1048576,0)|0);
 $858 = tempRet0;
 $859 = (_bitshift64Lshr(($857|0),($858|0),21)|0);
 $860 = tempRet0;
 $861 = $857 & -2097152;
 $862 = (_i64Subtract(($632|0),($633|0),($861|0),($858|0))|0);
 $863 = tempRet0;
 $864 = (_i64Add(($650|0),($651|0),1048576,0)|0);
 $865 = tempRet0;
 $866 = (_bitshift64Ashr(($864|0),($865|0),21)|0);
 $867 = tempRet0;
 $868 = (_bitshift64Shl(($866|0),($867|0),21)|0);
 $869 = tempRet0;
 $870 = (_i64Subtract(($650|0),($651|0),($868|0),($869|0))|0);
 $871 = tempRet0;
 $872 = (_i64Add(($669|0),($670|0),1048576,0)|0);
 $873 = tempRet0;
 $874 = (_bitshift64Ashr(($872|0),($873|0),21)|0);
 $875 = tempRet0;
 $876 = (_bitshift64Shl(($874|0),($875|0),21)|0);
 $877 = tempRet0;
 $878 = (_i64Subtract(($669|0),($670|0),($876|0),($877|0))|0);
 $879 = tempRet0;
 $880 = (_i64Add(($693|0),($694|0),1048576,0)|0);
 $881 = tempRet0;
 $882 = (_bitshift64Ashr(($880|0),($881|0),21)|0);
 $883 = tempRet0;
 $884 = (_bitshift64Shl(($882|0),($883|0),21)|0);
 $885 = tempRet0;
 $886 = (_i64Add(($721|0),($722|0),1048576,0)|0);
 $887 = tempRet0;
 $888 = (_bitshift64Ashr(($886|0),($887|0),21)|0);
 $889 = tempRet0;
 $890 = (_bitshift64Shl(($888|0),($889|0),21)|0);
 $891 = tempRet0;
 $892 = (_i64Add(($753|0),($754|0),1048576,0)|0);
 $893 = tempRet0;
 $894 = (_bitshift64Ashr(($892|0),($893|0),21)|0);
 $895 = tempRet0;
 $896 = (_bitshift64Shl(($894|0),($895|0),21)|0);
 $897 = tempRet0;
 $898 = (_i64Add(($779|0),($780|0),1048576,0)|0);
 $899 = tempRet0;
 $900 = (_bitshift64Ashr(($898|0),($899|0),21)|0);
 $901 = tempRet0;
 $902 = (_bitshift64Shl(($900|0),($901|0),21)|0);
 $903 = tempRet0;
 $904 = (_i64Add(($801|0),($802|0),1048576,0)|0);
 $905 = tempRet0;
 $906 = (_bitshift64Ashr(($904|0),($905|0),21)|0);
 $907 = tempRet0;
 $908 = (_bitshift64Shl(($906|0),($907|0),21)|0);
 $909 = tempRet0;
 $910 = (_i64Add(($819|0),($820|0),1048576,0)|0);
 $911 = tempRet0;
 $912 = (_bitshift64Ashr(($910|0),($911|0),21)|0);
 $913 = tempRet0;
 $914 = (_i64Add(($912|0),($913|0),($837|0),($838|0))|0);
 $915 = tempRet0;
 $916 = (_bitshift64Shl(($912|0),($913|0),21)|0);
 $917 = tempRet0;
 $918 = (_i64Subtract(($819|0),($820|0),($916|0),($917|0))|0);
 $919 = tempRet0;
 $920 = (_i64Add(($833|0),($834|0),1048576,0)|0);
 $921 = tempRet0;
 $922 = (_bitshift64Ashr(($920|0),($921|0),21)|0);
 $923 = tempRet0;
 $924 = (_i64Add(($922|0),($923|0),($847|0),($848|0))|0);
 $925 = tempRet0;
 $926 = (_bitshift64Shl(($922|0),($923|0),21)|0);
 $927 = tempRet0;
 $928 = (_i64Subtract(($833|0),($834|0),($926|0),($927|0))|0);
 $929 = tempRet0;
 $930 = (_i64Add(($843|0),($844|0),1048576,0)|0);
 $931 = tempRet0;
 $932 = (_bitshift64Lshr(($930|0),($931|0),21)|0);
 $933 = tempRet0;
 $934 = (_i64Add(($932|0),($933|0),($855|0),($856|0))|0);
 $935 = tempRet0;
 $936 = $930 & -2097152;
 $937 = $931 & 2147483647;
 $938 = (_i64Subtract(($843|0),($844|0),($936|0),($937|0))|0);
 $939 = tempRet0;
 $940 = (___muldi3(($851|0),($852|0),666643,0)|0);
 $941 = tempRet0;
 $942 = (___muldi3(($851|0),($852|0),470296,0)|0);
 $943 = tempRet0;
 $944 = (___muldi3(($851|0),($852|0),654183,0)|0);
 $945 = tempRet0;
 $946 = (___muldi3(($851|0),($852|0),-997805,-1)|0);
 $947 = tempRet0;
 $948 = (___muldi3(($851|0),($852|0),136657,0)|0);
 $949 = tempRet0;
 $950 = (___muldi3(($851|0),($852|0),-683901,-1)|0);
 $951 = tempRet0;
 $952 = (_i64Add(($566|0),($567|0),($950|0),($951|0))|0);
 $953 = tempRet0;
 $954 = (_i64Subtract(($952|0),($953|0),($821|0),($822|0))|0);
 $955 = tempRet0;
 $956 = (_i64Add(($954|0),($955|0),($906|0),($907|0))|0);
 $957 = tempRet0;
 $958 = (___muldi3(($934|0),($935|0),666643,0)|0);
 $959 = tempRet0;
 $960 = (___muldi3(($934|0),($935|0),470296,0)|0);
 $961 = tempRet0;
 $962 = (___muldi3(($934|0),($935|0),654183,0)|0);
 $963 = tempRet0;
 $964 = (___muldi3(($934|0),($935|0),-997805,-1)|0);
 $965 = tempRet0;
 $966 = (___muldi3(($934|0),($935|0),136657,0)|0);
 $967 = tempRet0;
 $968 = (___muldi3(($934|0),($935|0),-683901,-1)|0);
 $969 = tempRet0;
 $970 = (___muldi3(($938|0),($939|0),666643,0)|0);
 $971 = tempRet0;
 $972 = (___muldi3(($938|0),($939|0),470296,0)|0);
 $973 = tempRet0;
 $974 = (___muldi3(($938|0),($939|0),654183,0)|0);
 $975 = tempRet0;
 $976 = (___muldi3(($938|0),($939|0),-997805,-1)|0);
 $977 = tempRet0;
 $978 = (___muldi3(($938|0),($939|0),136657,0)|0);
 $979 = tempRet0;
 $980 = (___muldi3(($938|0),($939|0),-683901,-1)|0);
 $981 = tempRet0;
 $982 = (_i64Add(($524|0),($525|0),($946|0),($947|0))|0);
 $983 = tempRet0;
 $984 = (_i64Add(($982|0),($983|0),($966|0),($967|0))|0);
 $985 = tempRet0;
 $986 = (_i64Add(($984|0),($985|0),($980|0),($981|0))|0);
 $987 = tempRet0;
 $988 = (_i64Subtract(($986|0),($987|0),($803|0),($804|0))|0);
 $989 = tempRet0;
 $990 = (_i64Add(($988|0),($989|0),($900|0),($901|0))|0);
 $991 = tempRet0;
 $992 = (___muldi3(($924|0),($925|0),666643,0)|0);
 $993 = tempRet0;
 $994 = (___muldi3(($924|0),($925|0),470296,0)|0);
 $995 = tempRet0;
 $996 = (___muldi3(($924|0),($925|0),654183,0)|0);
 $997 = tempRet0;
 $998 = (___muldi3(($924|0),($925|0),-997805,-1)|0);
 $999 = tempRet0;
 $1000 = (___muldi3(($924|0),($925|0),136657,0)|0);
 $1001 = tempRet0;
 $1002 = (___muldi3(($924|0),($925|0),-683901,-1)|0);
 $1003 = tempRet0;
 $1004 = (___muldi3(($928|0),($929|0),666643,0)|0);
 $1005 = tempRet0;
 $1006 = (___muldi3(($928|0),($929|0),470296,0)|0);
 $1007 = tempRet0;
 $1008 = (___muldi3(($928|0),($929|0),654183,0)|0);
 $1009 = tempRet0;
 $1010 = (___muldi3(($928|0),($929|0),-997805,-1)|0);
 $1011 = tempRet0;
 $1012 = (___muldi3(($928|0),($929|0),136657,0)|0);
 $1013 = tempRet0;
 $1014 = (___muldi3(($928|0),($929|0),-683901,-1)|0);
 $1015 = tempRet0;
 $1016 = (_i64Add(($962|0),($963|0),($942|0),($943|0))|0);
 $1017 = tempRet0;
 $1018 = (_i64Add(($1016|0),($1017|0),($976|0),($977|0))|0);
 $1019 = tempRet0;
 $1020 = (_i64Add(($1018|0),($1019|0),($470|0),($471|0))|0);
 $1021 = tempRet0;
 $1022 = (_i64Add(($1020|0),($1021|0),($1000|0),($1001|0))|0);
 $1023 = tempRet0;
 $1024 = (_i64Add(($1022|0),($1023|0),($1014|0),($1015|0))|0);
 $1025 = tempRet0;
 $1026 = (_i64Subtract(($1024|0),($1025|0),($781|0),($782|0))|0);
 $1027 = tempRet0;
 $1028 = (_i64Add(($1026|0),($1027|0),($894|0),($895|0))|0);
 $1029 = tempRet0;
 $1030 = (___muldi3(($914|0),($915|0),666643,0)|0);
 $1031 = tempRet0;
 $1032 = (_i64Add(($288|0),($289|0),($1030|0),($1031|0))|0);
 $1033 = tempRet0;
 $1034 = (_i64Add(($1032|0),($1033|0),($874|0),($875|0))|0);
 $1035 = tempRet0;
 $1036 = (_i64Subtract(($1034|0),($1035|0),($695|0),($696|0))|0);
 $1037 = tempRet0;
 $1038 = (___muldi3(($914|0),($915|0),470296,0)|0);
 $1039 = tempRet0;
 $1040 = (___muldi3(($914|0),($915|0),654183,0)|0);
 $1041 = tempRet0;
 $1042 = (_i64Add(($1006|0),($1007|0),($992|0),($993|0))|0);
 $1043 = tempRet0;
 $1044 = (_i64Add(($1042|0),($1043|0),($1040|0),($1041|0))|0);
 $1045 = tempRet0;
 $1046 = (_i64Add(($1044|0),($1045|0),($340|0),($341|0))|0);
 $1047 = tempRet0;
 $1048 = (_i64Add(($1046|0),($1047|0),($882|0),($883|0))|0);
 $1049 = tempRet0;
 $1050 = (_i64Subtract(($1048|0),($1049|0),($723|0),($724|0))|0);
 $1051 = tempRet0;
 $1052 = (___muldi3(($914|0),($915|0),-997805,-1)|0);
 $1053 = tempRet0;
 $1054 = (___muldi3(($914|0),($915|0),136657,0)|0);
 $1055 = tempRet0;
 $1056 = (_i64Add(($972|0),($973|0),($958|0),($959|0))|0);
 $1057 = tempRet0;
 $1058 = (_i64Add(($1056|0),($1057|0),($996|0),($997|0))|0);
 $1059 = tempRet0;
 $1060 = (_i64Add(($1058|0),($1059|0),($1010|0),($1011|0))|0);
 $1061 = tempRet0;
 $1062 = (_i64Add(($1060|0),($1061|0),($1054|0),($1055|0))|0);
 $1063 = tempRet0;
 $1064 = (_i64Add(($1062|0),($1063|0),($404|0),($405|0))|0);
 $1065 = tempRet0;
 $1066 = (_i64Add(($1064|0),($1065|0),($888|0),($889|0))|0);
 $1067 = tempRet0;
 $1068 = (_i64Subtract(($1066|0),($1067|0),($755|0),($756|0))|0);
 $1069 = tempRet0;
 $1070 = (___muldi3(($914|0),($915|0),-683901,-1)|0);
 $1071 = tempRet0;
 $1072 = (_i64Add(($1036|0),($1037|0),1048576,0)|0);
 $1073 = tempRet0;
 $1074 = (_bitshift64Ashr(($1072|0),($1073|0),21)|0);
 $1075 = tempRet0;
 $1076 = (_i64Add(($1038|0),($1039|0),($1004|0),($1005|0))|0);
 $1077 = tempRet0;
 $1078 = (_i64Add(($1076|0),($1077|0),($693|0),($694|0))|0);
 $1079 = tempRet0;
 $1080 = (_i64Subtract(($1078|0),($1079|0),($884|0),($885|0))|0);
 $1081 = tempRet0;
 $1082 = (_i64Add(($1080|0),($1081|0),($1074|0),($1075|0))|0);
 $1083 = tempRet0;
 $1084 = (_bitshift64Shl(($1074|0),($1075|0),21)|0);
 $1085 = tempRet0;
 $1086 = (_i64Add(($1050|0),($1051|0),1048576,0)|0);
 $1087 = tempRet0;
 $1088 = (_bitshift64Ashr(($1086|0),($1087|0),21)|0);
 $1089 = tempRet0;
 $1090 = (_i64Add(($994|0),($995|0),($970|0),($971|0))|0);
 $1091 = tempRet0;
 $1092 = (_i64Add(($1090|0),($1091|0),($1008|0),($1009|0))|0);
 $1093 = tempRet0;
 $1094 = (_i64Add(($1092|0),($1093|0),($1052|0),($1053|0))|0);
 $1095 = tempRet0;
 $1096 = (_i64Add(($1094|0),($1095|0),($721|0),($722|0))|0);
 $1097 = tempRet0;
 $1098 = (_i64Subtract(($1096|0),($1097|0),($890|0),($891|0))|0);
 $1099 = tempRet0;
 $1100 = (_i64Add(($1098|0),($1099|0),($1088|0),($1089|0))|0);
 $1101 = tempRet0;
 $1102 = (_bitshift64Shl(($1088|0),($1089|0),21)|0);
 $1103 = tempRet0;
 $1104 = (_i64Add(($1068|0),($1069|0),1048576,0)|0);
 $1105 = tempRet0;
 $1106 = (_bitshift64Ashr(($1104|0),($1105|0),21)|0);
 $1107 = tempRet0;
 $1108 = (_i64Add(($960|0),($961|0),($940|0),($941|0))|0);
 $1109 = tempRet0;
 $1110 = (_i64Add(($1108|0),($1109|0),($974|0),($975|0))|0);
 $1111 = tempRet0;
 $1112 = (_i64Add(($1110|0),($1111|0),($998|0),($999|0))|0);
 $1113 = tempRet0;
 $1114 = (_i64Add(($1112|0),($1113|0),($1012|0),($1013|0))|0);
 $1115 = tempRet0;
 $1116 = (_i64Add(($1114|0),($1115|0),($1070|0),($1071|0))|0);
 $1117 = tempRet0;
 $1118 = (_i64Add(($1116|0),($1117|0),($753|0),($754|0))|0);
 $1119 = tempRet0;
 $1120 = (_i64Subtract(($1118|0),($1119|0),($896|0),($897|0))|0);
 $1121 = tempRet0;
 $1122 = (_i64Add(($1120|0),($1121|0),($1106|0),($1107|0))|0);
 $1123 = tempRet0;
 $1124 = (_bitshift64Shl(($1106|0),($1107|0),21)|0);
 $1125 = tempRet0;
 $1126 = (_i64Add(($1028|0),($1029|0),1048576,0)|0);
 $1127 = tempRet0;
 $1128 = (_bitshift64Ashr(($1126|0),($1127|0),21)|0);
 $1129 = tempRet0;
 $1130 = (_i64Add(($964|0),($965|0),($944|0),($945|0))|0);
 $1131 = tempRet0;
 $1132 = (_i64Add(($1130|0),($1131|0),($978|0),($979|0))|0);
 $1133 = tempRet0;
 $1134 = (_i64Add(($1132|0),($1133|0),($1002|0),($1003|0))|0);
 $1135 = tempRet0;
 $1136 = (_i64Add(($1134|0),($1135|0),($779|0),($780|0))|0);
 $1137 = tempRet0;
 $1138 = (_i64Subtract(($1136|0),($1137|0),($902|0),($903|0))|0);
 $1139 = tempRet0;
 $1140 = (_i64Add(($1138|0),($1139|0),($1128|0),($1129|0))|0);
 $1141 = tempRet0;
 $1142 = (_bitshift64Shl(($1128|0),($1129|0),21)|0);
 $1143 = tempRet0;
 $1144 = (_i64Subtract(($1028|0),($1029|0),($1142|0),($1143|0))|0);
 $1145 = tempRet0;
 $1146 = (_i64Add(($990|0),($991|0),1048576,0)|0);
 $1147 = tempRet0;
 $1148 = (_bitshift64Ashr(($1146|0),($1147|0),21)|0);
 $1149 = tempRet0;
 $1150 = (_i64Add(($968|0),($969|0),($948|0),($949|0))|0);
 $1151 = tempRet0;
 $1152 = (_i64Add(($1150|0),($1151|0),($801|0),($802|0))|0);
 $1153 = tempRet0;
 $1154 = (_i64Subtract(($1152|0),($1153|0),($908|0),($909|0))|0);
 $1155 = tempRet0;
 $1156 = (_i64Add(($1154|0),($1155|0),($1148|0),($1149|0))|0);
 $1157 = tempRet0;
 $1158 = (_bitshift64Shl(($1148|0),($1149|0),21)|0);
 $1159 = tempRet0;
 $1160 = (_i64Subtract(($990|0),($991|0),($1158|0),($1159|0))|0);
 $1161 = tempRet0;
 $1162 = (_i64Add(($956|0),($957|0),1048576,0)|0);
 $1163 = tempRet0;
 $1164 = (_bitshift64Ashr(($1162|0),($1163|0),21)|0);
 $1165 = tempRet0;
 $1166 = (_i64Add(($1164|0),($1165|0),($918|0),($919|0))|0);
 $1167 = tempRet0;
 $1168 = (_bitshift64Shl(($1164|0),($1165|0),21)|0);
 $1169 = tempRet0;
 $1170 = (_i64Subtract(($956|0),($957|0),($1168|0),($1169|0))|0);
 $1171 = tempRet0;
 $1172 = (_i64Add(($1082|0),($1083|0),1048576,0)|0);
 $1173 = tempRet0;
 $1174 = (_bitshift64Ashr(($1172|0),($1173|0),21)|0);
 $1175 = tempRet0;
 $1176 = (_bitshift64Shl(($1174|0),($1175|0),21)|0);
 $1177 = tempRet0;
 $1178 = (_i64Add(($1100|0),($1101|0),1048576,0)|0);
 $1179 = tempRet0;
 $1180 = (_bitshift64Ashr(($1178|0),($1179|0),21)|0);
 $1181 = tempRet0;
 $1182 = (_bitshift64Shl(($1180|0),($1181|0),21)|0);
 $1183 = tempRet0;
 $1184 = (_i64Add(($1122|0),($1123|0),1048576,0)|0);
 $1185 = tempRet0;
 $1186 = (_bitshift64Ashr(($1184|0),($1185|0),21)|0);
 $1187 = tempRet0;
 $1188 = (_i64Add(($1186|0),($1187|0),($1144|0),($1145|0))|0);
 $1189 = tempRet0;
 $1190 = (_bitshift64Shl(($1186|0),($1187|0),21)|0);
 $1191 = tempRet0;
 $1192 = (_i64Subtract(($1122|0),($1123|0),($1190|0),($1191|0))|0);
 $1193 = tempRet0;
 $1194 = (_i64Add(($1140|0),($1141|0),1048576,0)|0);
 $1195 = tempRet0;
 $1196 = (_bitshift64Ashr(($1194|0),($1195|0),21)|0);
 $1197 = tempRet0;
 $1198 = (_i64Add(($1196|0),($1197|0),($1160|0),($1161|0))|0);
 $1199 = tempRet0;
 $1200 = (_bitshift64Shl(($1196|0),($1197|0),21)|0);
 $1201 = tempRet0;
 $1202 = (_i64Subtract(($1140|0),($1141|0),($1200|0),($1201|0))|0);
 $1203 = tempRet0;
 $1204 = (_i64Add(($1156|0),($1157|0),1048576,0)|0);
 $1205 = tempRet0;
 $1206 = (_bitshift64Ashr(($1204|0),($1205|0),21)|0);
 $1207 = tempRet0;
 $1208 = (_i64Add(($1206|0),($1207|0),($1170|0),($1171|0))|0);
 $1209 = tempRet0;
 $1210 = (_bitshift64Shl(($1206|0),($1207|0),21)|0);
 $1211 = tempRet0;
 $1212 = (_i64Subtract(($1156|0),($1157|0),($1210|0),($1211|0))|0);
 $1213 = tempRet0;
 $1214 = (___muldi3(($1166|0),($1167|0),666643,0)|0);
 $1215 = tempRet0;
 $1216 = (_i64Add(($878|0),($879|0),($1214|0),($1215|0))|0);
 $1217 = tempRet0;
 $1218 = (___muldi3(($1166|0),($1167|0),470296,0)|0);
 $1219 = tempRet0;
 $1220 = (___muldi3(($1166|0),($1167|0),654183,0)|0);
 $1221 = tempRet0;
 $1222 = (___muldi3(($1166|0),($1167|0),-997805,-1)|0);
 $1223 = tempRet0;
 $1224 = (___muldi3(($1166|0),($1167|0),136657,0)|0);
 $1225 = tempRet0;
 $1226 = (___muldi3(($1166|0),($1167|0),-683901,-1)|0);
 $1227 = tempRet0;
 $1228 = (_i64Add(($1068|0),($1069|0),($1226|0),($1227|0))|0);
 $1229 = tempRet0;
 $1230 = (_i64Add(($1228|0),($1229|0),($1180|0),($1181|0))|0);
 $1231 = tempRet0;
 $1232 = (_i64Subtract(($1230|0),($1231|0),($1124|0),($1125|0))|0);
 $1233 = tempRet0;
 $1234 = (___muldi3(($1208|0),($1209|0),666643,0)|0);
 $1235 = tempRet0;
 $1236 = (___muldi3(($1208|0),($1209|0),470296,0)|0);
 $1237 = tempRet0;
 $1238 = (_i64Add(($1216|0),($1217|0),($1236|0),($1237|0))|0);
 $1239 = tempRet0;
 $1240 = (___muldi3(($1208|0),($1209|0),654183,0)|0);
 $1241 = tempRet0;
 $1242 = (___muldi3(($1208|0),($1209|0),-997805,-1)|0);
 $1243 = tempRet0;
 $1244 = (___muldi3(($1208|0),($1209|0),136657,0)|0);
 $1245 = tempRet0;
 $1246 = (___muldi3(($1208|0),($1209|0),-683901,-1)|0);
 $1247 = tempRet0;
 $1248 = (___muldi3(($1212|0),($1213|0),666643,0)|0);
 $1249 = tempRet0;
 $1250 = (_i64Add(($870|0),($871|0),($1248|0),($1249|0))|0);
 $1251 = tempRet0;
 $1252 = (___muldi3(($1212|0),($1213|0),470296,0)|0);
 $1253 = tempRet0;
 $1254 = (___muldi3(($1212|0),($1213|0),654183,0)|0);
 $1255 = tempRet0;
 $1256 = (_i64Add(($1238|0),($1239|0),($1254|0),($1255|0))|0);
 $1257 = tempRet0;
 $1258 = (___muldi3(($1212|0),($1213|0),-997805,-1)|0);
 $1259 = tempRet0;
 $1260 = (___muldi3(($1212|0),($1213|0),136657,0)|0);
 $1261 = tempRet0;
 $1262 = (___muldi3(($1212|0),($1213|0),-683901,-1)|0);
 $1263 = tempRet0;
 $1264 = (_i64Add(($1050|0),($1051|0),($1222|0),($1223|0))|0);
 $1265 = tempRet0;
 $1266 = (_i64Add(($1264|0),($1265|0),($1174|0),($1175|0))|0);
 $1267 = tempRet0;
 $1268 = (_i64Add(($1266|0),($1267|0),($1244|0),($1245|0))|0);
 $1269 = tempRet0;
 $1270 = (_i64Add(($1268|0),($1269|0),($1262|0),($1263|0))|0);
 $1271 = tempRet0;
 $1272 = (_i64Subtract(($1270|0),($1271|0),($1102|0),($1103|0))|0);
 $1273 = tempRet0;
 $1274 = (___muldi3(($1198|0),($1199|0),666643,0)|0);
 $1275 = tempRet0;
 $1276 = (___muldi3(($1198|0),($1199|0),470296,0)|0);
 $1277 = tempRet0;
 $1278 = (_i64Add(($1250|0),($1251|0),($1276|0),($1277|0))|0);
 $1279 = tempRet0;
 $1280 = (___muldi3(($1198|0),($1199|0),654183,0)|0);
 $1281 = tempRet0;
 $1282 = (___muldi3(($1198|0),($1199|0),-997805,-1)|0);
 $1283 = tempRet0;
 $1284 = (_i64Add(($1256|0),($1257|0),($1282|0),($1283|0))|0);
 $1285 = tempRet0;
 $1286 = (___muldi3(($1198|0),($1199|0),136657,0)|0);
 $1287 = tempRet0;
 $1288 = (___muldi3(($1198|0),($1199|0),-683901,-1)|0);
 $1289 = tempRet0;
 $1290 = (___muldi3(($1202|0),($1203|0),666643,0)|0);
 $1291 = tempRet0;
 $1292 = (___muldi3(($1202|0),($1203|0),470296,0)|0);
 $1293 = tempRet0;
 $1294 = (___muldi3(($1202|0),($1203|0),654183,0)|0);
 $1295 = tempRet0;
 $1296 = (___muldi3(($1202|0),($1203|0),-997805,-1)|0);
 $1297 = tempRet0;
 $1298 = (___muldi3(($1202|0),($1203|0),136657,0)|0);
 $1299 = tempRet0;
 $1300 = (___muldi3(($1202|0),($1203|0),-683901,-1)|0);
 $1301 = tempRet0;
 $1302 = (_i64Add(($1036|0),($1037|0),($1218|0),($1219|0))|0);
 $1303 = tempRet0;
 $1304 = (_i64Subtract(($1302|0),($1303|0),($1084|0),($1085|0))|0);
 $1305 = tempRet0;
 $1306 = (_i64Add(($1304|0),($1305|0),($1240|0),($1241|0))|0);
 $1307 = tempRet0;
 $1308 = (_i64Add(($1306|0),($1307|0),($1258|0),($1259|0))|0);
 $1309 = tempRet0;
 $1310 = (_i64Add(($1308|0),($1309|0),($1286|0),($1287|0))|0);
 $1311 = tempRet0;
 $1312 = (_i64Add(($1310|0),($1311|0),($1300|0),($1301|0))|0);
 $1313 = tempRet0;
 $1314 = (___muldi3(($1188|0),($1189|0),666643,0)|0);
 $1315 = tempRet0;
 $1316 = (_i64Add(($1314|0),($1315|0),($636|0),($637|0))|0);
 $1317 = tempRet0;
 $1318 = (___muldi3(($1188|0),($1189|0),470296,0)|0);
 $1319 = tempRet0;
 $1320 = (___muldi3(($1188|0),($1189|0),654183,0)|0);
 $1321 = tempRet0;
 $1322 = (_i64Add(($859|0),($860|0),($220|0),($221|0))|0);
 $1323 = tempRet0;
 $1324 = (_i64Subtract(($1322|0),($1323|0),($652|0),($639|0))|0);
 $1325 = tempRet0;
 $1326 = (_i64Add(($1324|0),($1325|0),($1274|0),($1275|0))|0);
 $1327 = tempRet0;
 $1328 = (_i64Add(($1326|0),($1327|0),($1320|0),($1321|0))|0);
 $1329 = tempRet0;
 $1330 = (_i64Add(($1328|0),($1329|0),($1292|0),($1293|0))|0);
 $1331 = tempRet0;
 $1332 = (___muldi3(($1188|0),($1189|0),-997805,-1)|0);
 $1333 = tempRet0;
 $1334 = (___muldi3(($1188|0),($1189|0),136657,0)|0);
 $1335 = tempRet0;
 $1336 = (_i64Add(($866|0),($867|0),($248|0),($249|0))|0);
 $1337 = tempRet0;
 $1338 = (_i64Subtract(($1336|0),($1337|0),($671|0),($672|0))|0);
 $1339 = tempRet0;
 $1340 = (_i64Add(($1338|0),($1339|0),($1234|0),($1235|0))|0);
 $1341 = tempRet0;
 $1342 = (_i64Add(($1340|0),($1341|0),($1252|0),($1253|0))|0);
 $1343 = tempRet0;
 $1344 = (_i64Add(($1342|0),($1343|0),($1280|0),($1281|0))|0);
 $1345 = tempRet0;
 $1346 = (_i64Add(($1344|0),($1345|0),($1334|0),($1335|0))|0);
 $1347 = tempRet0;
 $1348 = (_i64Add(($1346|0),($1347|0),($1296|0),($1297|0))|0);
 $1349 = tempRet0;
 $1350 = (___muldi3(($1188|0),($1189|0),-683901,-1)|0);
 $1351 = tempRet0;
 $1352 = (_i64Add(($1316|0),($1317|0),1048576,0)|0);
 $1353 = tempRet0;
 $1354 = (_bitshift64Ashr(($1352|0),($1353|0),21)|0);
 $1355 = tempRet0;
 $1356 = (_i64Add(($862|0),($863|0),($1318|0),($1319|0))|0);
 $1357 = tempRet0;
 $1358 = (_i64Add(($1356|0),($1357|0),($1290|0),($1291|0))|0);
 $1359 = tempRet0;
 $1360 = (_i64Add(($1358|0),($1359|0),($1354|0),($1355|0))|0);
 $1361 = tempRet0;
 $1362 = (_bitshift64Shl(($1354|0),($1355|0),21)|0);
 $1363 = tempRet0;
 $1364 = (_i64Subtract(($1316|0),($1317|0),($1362|0),($1363|0))|0);
 $1365 = tempRet0;
 $1366 = (_i64Add(($1330|0),($1331|0),1048576,0)|0);
 $1367 = tempRet0;
 $1368 = (_bitshift64Ashr(($1366|0),($1367|0),21)|0);
 $1369 = tempRet0;
 $1370 = (_i64Add(($1278|0),($1279|0),($1332|0),($1333|0))|0);
 $1371 = tempRet0;
 $1372 = (_i64Add(($1370|0),($1371|0),($1294|0),($1295|0))|0);
 $1373 = tempRet0;
 $1374 = (_i64Add(($1372|0),($1373|0),($1368|0),($1369|0))|0);
 $1375 = tempRet0;
 $1376 = (_bitshift64Shl(($1368|0),($1369|0),21)|0);
 $1377 = tempRet0;
 $1378 = (_i64Add(($1348|0),($1349|0),1048576,0)|0);
 $1379 = tempRet0;
 $1380 = (_bitshift64Ashr(($1378|0),($1379|0),21)|0);
 $1381 = tempRet0;
 $1382 = (_i64Add(($1284|0),($1285|0),($1350|0),($1351|0))|0);
 $1383 = tempRet0;
 $1384 = (_i64Add(($1382|0),($1383|0),($1298|0),($1299|0))|0);
 $1385 = tempRet0;
 $1386 = (_i64Add(($1384|0),($1385|0),($1380|0),($1381|0))|0);
 $1387 = tempRet0;
 $1388 = (_bitshift64Shl(($1380|0),($1381|0),21)|0);
 $1389 = tempRet0;
 $1390 = (_i64Add(($1312|0),($1313|0),1048576,0)|0);
 $1391 = tempRet0;
 $1392 = (_bitshift64Ashr(($1390|0),($1391|0),21)|0);
 $1393 = tempRet0;
 $1394 = (_i64Add(($1082|0),($1083|0),($1220|0),($1221|0))|0);
 $1395 = tempRet0;
 $1396 = (_i64Add(($1394|0),($1395|0),($1242|0),($1243|0))|0);
 $1397 = tempRet0;
 $1398 = (_i64Subtract(($1396|0),($1397|0),($1176|0),($1177|0))|0);
 $1399 = tempRet0;
 $1400 = (_i64Add(($1398|0),($1399|0),($1260|0),($1261|0))|0);
 $1401 = tempRet0;
 $1402 = (_i64Add(($1400|0),($1401|0),($1288|0),($1289|0))|0);
 $1403 = tempRet0;
 $1404 = (_i64Add(($1402|0),($1403|0),($1392|0),($1393|0))|0);
 $1405 = tempRet0;
 $1406 = (_bitshift64Shl(($1392|0),($1393|0),21)|0);
 $1407 = tempRet0;
 $1408 = (_i64Subtract(($1312|0),($1313|0),($1406|0),($1407|0))|0);
 $1409 = tempRet0;
 $1410 = (_i64Add(($1272|0),($1273|0),1048576,0)|0);
 $1411 = tempRet0;
 $1412 = (_bitshift64Ashr(($1410|0),($1411|0),21)|0);
 $1413 = tempRet0;
 $1414 = (_i64Add(($1246|0),($1247|0),($1224|0),($1225|0))|0);
 $1415 = tempRet0;
 $1416 = (_i64Add(($1414|0),($1415|0),($1100|0),($1101|0))|0);
 $1417 = tempRet0;
 $1418 = (_i64Subtract(($1416|0),($1417|0),($1182|0),($1183|0))|0);
 $1419 = tempRet0;
 $1420 = (_i64Add(($1418|0),($1419|0),($1412|0),($1413|0))|0);
 $1421 = tempRet0;
 $1422 = (_bitshift64Shl(($1412|0),($1413|0),21)|0);
 $1423 = tempRet0;
 $1424 = (_i64Subtract(($1272|0),($1273|0),($1422|0),($1423|0))|0);
 $1425 = tempRet0;
 $1426 = (_i64Add(($1232|0),($1233|0),1048576,0)|0);
 $1427 = tempRet0;
 $1428 = (_bitshift64Ashr(($1426|0),($1427|0),21)|0);
 $1429 = tempRet0;
 $1430 = (_i64Add(($1192|0),($1193|0),($1428|0),($1429|0))|0);
 $1431 = tempRet0;
 $1432 = (_bitshift64Shl(($1428|0),($1429|0),21)|0);
 $1433 = tempRet0;
 $1434 = (_i64Add(($1360|0),($1361|0),1048576,0)|0);
 $1435 = tempRet0;
 $1436 = (_bitshift64Ashr(($1434|0),($1435|0),21)|0);
 $1437 = tempRet0;
 $1438 = (_bitshift64Shl(($1436|0),($1437|0),21)|0);
 $1439 = tempRet0;
 $1440 = (_i64Add(($1374|0),($1375|0),1048576,0)|0);
 $1441 = tempRet0;
 $1442 = (_bitshift64Ashr(($1440|0),($1441|0),21)|0);
 $1443 = tempRet0;
 $1444 = (_bitshift64Shl(($1442|0),($1443|0),21)|0);
 $1445 = tempRet0;
 $1446 = (_i64Add(($1386|0),($1387|0),1048576,0)|0);
 $1447 = tempRet0;
 $1448 = (_bitshift64Ashr(($1446|0),($1447|0),21)|0);
 $1449 = tempRet0;
 $1450 = (_i64Add(($1408|0),($1409|0),($1448|0),($1449|0))|0);
 $1451 = tempRet0;
 $1452 = (_bitshift64Shl(($1448|0),($1449|0),21)|0);
 $1453 = tempRet0;
 $1454 = (_i64Add(($1404|0),($1405|0),1048576,0)|0);
 $1455 = tempRet0;
 $1456 = (_bitshift64Ashr(($1454|0),($1455|0),21)|0);
 $1457 = tempRet0;
 $1458 = (_i64Add(($1424|0),($1425|0),($1456|0),($1457|0))|0);
 $1459 = tempRet0;
 $1460 = (_bitshift64Shl(($1456|0),($1457|0),21)|0);
 $1461 = tempRet0;
 $1462 = (_i64Subtract(($1404|0),($1405|0),($1460|0),($1461|0))|0);
 $1463 = tempRet0;
 $1464 = (_i64Add(($1420|0),($1421|0),1048576,0)|0);
 $1465 = tempRet0;
 $1466 = (_bitshift64Ashr(($1464|0),($1465|0),21)|0);
 $1467 = tempRet0;
 $1468 = (_bitshift64Shl(($1466|0),($1467|0),21)|0);
 $1469 = tempRet0;
 $1470 = (_i64Subtract(($1420|0),($1421|0),($1468|0),($1469|0))|0);
 $1471 = tempRet0;
 $1472 = (_i64Add(($1430|0),($1431|0),1048576,0)|0);
 $1473 = tempRet0;
 $1474 = (_bitshift64Ashr(($1472|0),($1473|0),21)|0);
 $1475 = tempRet0;
 $1476 = (_bitshift64Shl(($1474|0),($1475|0),21)|0);
 $1477 = tempRet0;
 $1478 = (_i64Subtract(($1430|0),($1431|0),($1476|0),($1477|0))|0);
 $1479 = tempRet0;
 $1480 = (___muldi3(($1474|0),($1475|0),666643,0)|0);
 $1481 = tempRet0;
 $1482 = (_i64Add(($1364|0),($1365|0),($1480|0),($1481|0))|0);
 $1483 = tempRet0;
 $1484 = (___muldi3(($1474|0),($1475|0),470296,0)|0);
 $1485 = tempRet0;
 $1486 = (___muldi3(($1474|0),($1475|0),654183,0)|0);
 $1487 = tempRet0;
 $1488 = (___muldi3(($1474|0),($1475|0),-997805,-1)|0);
 $1489 = tempRet0;
 $1490 = (___muldi3(($1474|0),($1475|0),136657,0)|0);
 $1491 = tempRet0;
 $1492 = (___muldi3(($1474|0),($1475|0),-683901,-1)|0);
 $1493 = tempRet0;
 $1494 = (_bitshift64Ashr(($1482|0),($1483|0),21)|0);
 $1495 = tempRet0;
 $1496 = (_i64Add(($1484|0),($1485|0),($1360|0),($1361|0))|0);
 $1497 = tempRet0;
 $1498 = (_i64Subtract(($1496|0),($1497|0),($1438|0),($1439|0))|0);
 $1499 = tempRet0;
 $1500 = (_i64Add(($1498|0),($1499|0),($1494|0),($1495|0))|0);
 $1501 = tempRet0;
 $1502 = (_bitshift64Shl(($1494|0),($1495|0),21)|0);
 $1503 = tempRet0;
 $1504 = (_i64Subtract(($1482|0),($1483|0),($1502|0),($1503|0))|0);
 $1505 = tempRet0;
 $1506 = (_bitshift64Ashr(($1500|0),($1501|0),21)|0);
 $1507 = tempRet0;
 $1508 = (_i64Add(($1486|0),($1487|0),($1330|0),($1331|0))|0);
 $1509 = tempRet0;
 $1510 = (_i64Subtract(($1508|0),($1509|0),($1376|0),($1377|0))|0);
 $1511 = tempRet0;
 $1512 = (_i64Add(($1510|0),($1511|0),($1436|0),($1437|0))|0);
 $1513 = tempRet0;
 $1514 = (_i64Add(($1512|0),($1513|0),($1506|0),($1507|0))|0);
 $1515 = tempRet0;
 $1516 = (_bitshift64Shl(($1506|0),($1507|0),21)|0);
 $1517 = tempRet0;
 $1518 = (_i64Subtract(($1500|0),($1501|0),($1516|0),($1517|0))|0);
 $1519 = tempRet0;
 $1520 = (_bitshift64Ashr(($1514|0),($1515|0),21)|0);
 $1521 = tempRet0;
 $1522 = (_i64Add(($1374|0),($1375|0),($1488|0),($1489|0))|0);
 $1523 = tempRet0;
 $1524 = (_i64Subtract(($1522|0),($1523|0),($1444|0),($1445|0))|0);
 $1525 = tempRet0;
 $1526 = (_i64Add(($1524|0),($1525|0),($1520|0),($1521|0))|0);
 $1527 = tempRet0;
 $1528 = (_bitshift64Shl(($1520|0),($1521|0),21)|0);
 $1529 = tempRet0;
 $1530 = (_i64Subtract(($1514|0),($1515|0),($1528|0),($1529|0))|0);
 $1531 = tempRet0;
 $1532 = (_bitshift64Ashr(($1526|0),($1527|0),21)|0);
 $1533 = tempRet0;
 $1534 = (_i64Add(($1490|0),($1491|0),($1348|0),($1349|0))|0);
 $1535 = tempRet0;
 $1536 = (_i64Subtract(($1534|0),($1535|0),($1388|0),($1389|0))|0);
 $1537 = tempRet0;
 $1538 = (_i64Add(($1536|0),($1537|0),($1442|0),($1443|0))|0);
 $1539 = tempRet0;
 $1540 = (_i64Add(($1538|0),($1539|0),($1532|0),($1533|0))|0);
 $1541 = tempRet0;
 $1542 = (_bitshift64Shl(($1532|0),($1533|0),21)|0);
 $1543 = tempRet0;
 $1544 = (_i64Subtract(($1526|0),($1527|0),($1542|0),($1543|0))|0);
 $1545 = tempRet0;
 $1546 = (_bitshift64Ashr(($1540|0),($1541|0),21)|0);
 $1547 = tempRet0;
 $1548 = (_i64Add(($1386|0),($1387|0),($1492|0),($1493|0))|0);
 $1549 = tempRet0;
 $1550 = (_i64Subtract(($1548|0),($1549|0),($1452|0),($1453|0))|0);
 $1551 = tempRet0;
 $1552 = (_i64Add(($1550|0),($1551|0),($1546|0),($1547|0))|0);
 $1553 = tempRet0;
 $1554 = (_bitshift64Shl(($1546|0),($1547|0),21)|0);
 $1555 = tempRet0;
 $1556 = (_i64Subtract(($1540|0),($1541|0),($1554|0),($1555|0))|0);
 $1557 = tempRet0;
 $1558 = (_bitshift64Ashr(($1552|0),($1553|0),21)|0);
 $1559 = tempRet0;
 $1560 = (_i64Add(($1450|0),($1451|0),($1558|0),($1559|0))|0);
 $1561 = tempRet0;
 $1562 = (_bitshift64Shl(($1558|0),($1559|0),21)|0);
 $1563 = tempRet0;
 $1564 = (_i64Subtract(($1552|0),($1553|0),($1562|0),($1563|0))|0);
 $1565 = tempRet0;
 $1566 = (_bitshift64Ashr(($1560|0),($1561|0),21)|0);
 $1567 = tempRet0;
 $1568 = (_i64Add(($1566|0),($1567|0),($1462|0),($1463|0))|0);
 $1569 = tempRet0;
 $1570 = (_bitshift64Shl(($1566|0),($1567|0),21)|0);
 $1571 = tempRet0;
 $1572 = (_i64Subtract(($1560|0),($1561|0),($1570|0),($1571|0))|0);
 $1573 = tempRet0;
 $1574 = (_bitshift64Ashr(($1568|0),($1569|0),21)|0);
 $1575 = tempRet0;
 $1576 = (_i64Add(($1458|0),($1459|0),($1574|0),($1575|0))|0);
 $1577 = tempRet0;
 $1578 = (_bitshift64Shl(($1574|0),($1575|0),21)|0);
 $1579 = tempRet0;
 $1580 = (_i64Subtract(($1568|0),($1569|0),($1578|0),($1579|0))|0);
 $1581 = tempRet0;
 $1582 = (_bitshift64Ashr(($1576|0),($1577|0),21)|0);
 $1583 = tempRet0;
 $1584 = (_i64Add(($1582|0),($1583|0),($1470|0),($1471|0))|0);
 $1585 = tempRet0;
 $1586 = (_bitshift64Shl(($1582|0),($1583|0),21)|0);
 $1587 = tempRet0;
 $1588 = (_i64Subtract(($1576|0),($1577|0),($1586|0),($1587|0))|0);
 $1589 = tempRet0;
 $1590 = (_bitshift64Ashr(($1584|0),($1585|0),21)|0);
 $1591 = tempRet0;
 $1592 = (_i64Add(($1466|0),($1467|0),($1232|0),($1233|0))|0);
 $1593 = tempRet0;
 $1594 = (_i64Subtract(($1592|0),($1593|0),($1432|0),($1433|0))|0);
 $1595 = tempRet0;
 $1596 = (_i64Add(($1594|0),($1595|0),($1590|0),($1591|0))|0);
 $1597 = tempRet0;
 $1598 = (_bitshift64Shl(($1590|0),($1591|0),21)|0);
 $1599 = tempRet0;
 $1600 = (_i64Subtract(($1584|0),($1585|0),($1598|0),($1599|0))|0);
 $1601 = tempRet0;
 $1602 = (_bitshift64Ashr(($1596|0),($1597|0),21)|0);
 $1603 = tempRet0;
 $1604 = (_i64Add(($1602|0),($1603|0),($1478|0),($1479|0))|0);
 $1605 = tempRet0;
 $1606 = (_bitshift64Shl(($1602|0),($1603|0),21)|0);
 $1607 = tempRet0;
 $1608 = (_i64Subtract(($1596|0),($1597|0),($1606|0),($1607|0))|0);
 $1609 = tempRet0;
 $1610 = (_bitshift64Ashr(($1604|0),($1605|0),21)|0);
 $1611 = tempRet0;
 $1612 = (_bitshift64Shl(($1610|0),($1611|0),21)|0);
 $1613 = tempRet0;
 $1614 = (_i64Subtract(($1604|0),($1605|0),($1612|0),($1613|0))|0);
 $1615 = tempRet0;
 $1616 = (___muldi3(($1610|0),($1611|0),666643,0)|0);
 $1617 = tempRet0;
 $1618 = (_i64Add(($1616|0),($1617|0),($1504|0),($1505|0))|0);
 $1619 = tempRet0;
 $1620 = (___muldi3(($1610|0),($1611|0),470296,0)|0);
 $1621 = tempRet0;
 $1622 = (_i64Add(($1518|0),($1519|0),($1620|0),($1621|0))|0);
 $1623 = tempRet0;
 $1624 = (___muldi3(($1610|0),($1611|0),654183,0)|0);
 $1625 = tempRet0;
 $1626 = (_i64Add(($1530|0),($1531|0),($1624|0),($1625|0))|0);
 $1627 = tempRet0;
 $1628 = (___muldi3(($1610|0),($1611|0),-997805,-1)|0);
 $1629 = tempRet0;
 $1630 = (_i64Add(($1544|0),($1545|0),($1628|0),($1629|0))|0);
 $1631 = tempRet0;
 $1632 = (___muldi3(($1610|0),($1611|0),136657,0)|0);
 $1633 = tempRet0;
 $1634 = (_i64Add(($1556|0),($1557|0),($1632|0),($1633|0))|0);
 $1635 = tempRet0;
 $1636 = (___muldi3(($1610|0),($1611|0),-683901,-1)|0);
 $1637 = tempRet0;
 $1638 = (_i64Add(($1564|0),($1565|0),($1636|0),($1637|0))|0);
 $1639 = tempRet0;
 $1640 = (_bitshift64Ashr(($1618|0),($1619|0),21)|0);
 $1641 = tempRet0;
 $1642 = (_i64Add(($1622|0),($1623|0),($1640|0),($1641|0))|0);
 $1643 = tempRet0;
 $1644 = (_bitshift64Shl(($1640|0),($1641|0),21)|0);
 $1645 = tempRet0;
 $1646 = (_i64Subtract(($1618|0),($1619|0),($1644|0),($1645|0))|0);
 $1647 = tempRet0;
 $1648 = (_bitshift64Ashr(($1642|0),($1643|0),21)|0);
 $1649 = tempRet0;
 $1650 = (_i64Add(($1626|0),($1627|0),($1648|0),($1649|0))|0);
 $1651 = tempRet0;
 $1652 = (_bitshift64Shl(($1648|0),($1649|0),21)|0);
 $1653 = tempRet0;
 $1654 = (_i64Subtract(($1642|0),($1643|0),($1652|0),($1653|0))|0);
 $1655 = tempRet0;
 $1656 = (_bitshift64Ashr(($1650|0),($1651|0),21)|0);
 $1657 = tempRet0;
 $1658 = (_i64Add(($1630|0),($1631|0),($1656|0),($1657|0))|0);
 $1659 = tempRet0;
 $1660 = (_bitshift64Shl(($1656|0),($1657|0),21)|0);
 $1661 = tempRet0;
 $1662 = (_i64Subtract(($1650|0),($1651|0),($1660|0),($1661|0))|0);
 $1663 = tempRet0;
 $1664 = (_bitshift64Ashr(($1658|0),($1659|0),21)|0);
 $1665 = tempRet0;
 $1666 = (_i64Add(($1634|0),($1635|0),($1664|0),($1665|0))|0);
 $1667 = tempRet0;
 $1668 = (_bitshift64Shl(($1664|0),($1665|0),21)|0);
 $1669 = tempRet0;
 $1670 = (_i64Subtract(($1658|0),($1659|0),($1668|0),($1669|0))|0);
 $1671 = tempRet0;
 $1672 = (_bitshift64Ashr(($1666|0),($1667|0),21)|0);
 $1673 = tempRet0;
 $1674 = (_i64Add(($1638|0),($1639|0),($1672|0),($1673|0))|0);
 $1675 = tempRet0;
 $1676 = (_bitshift64Shl(($1672|0),($1673|0),21)|0);
 $1677 = tempRet0;
 $1678 = (_i64Subtract(($1666|0),($1667|0),($1676|0),($1677|0))|0);
 $1679 = tempRet0;
 $1680 = (_bitshift64Ashr(($1674|0),($1675|0),21)|0);
 $1681 = tempRet0;
 $1682 = (_i64Add(($1680|0),($1681|0),($1572|0),($1573|0))|0);
 $1683 = tempRet0;
 $1684 = (_bitshift64Shl(($1680|0),($1681|0),21)|0);
 $1685 = tempRet0;
 $1686 = (_i64Subtract(($1674|0),($1675|0),($1684|0),($1685|0))|0);
 $1687 = tempRet0;
 $1688 = (_bitshift64Ashr(($1682|0),($1683|0),21)|0);
 $1689 = tempRet0;
 $1690 = (_i64Add(($1688|0),($1689|0),($1580|0),($1581|0))|0);
 $1691 = tempRet0;
 $1692 = (_bitshift64Shl(($1688|0),($1689|0),21)|0);
 $1693 = tempRet0;
 $1694 = (_i64Subtract(($1682|0),($1683|0),($1692|0),($1693|0))|0);
 $1695 = tempRet0;
 $1696 = (_bitshift64Ashr(($1690|0),($1691|0),21)|0);
 $1697 = tempRet0;
 $1698 = (_i64Add(($1696|0),($1697|0),($1588|0),($1589|0))|0);
 $1699 = tempRet0;
 $1700 = (_bitshift64Shl(($1696|0),($1697|0),21)|0);
 $1701 = tempRet0;
 $1702 = (_i64Subtract(($1690|0),($1691|0),($1700|0),($1701|0))|0);
 $1703 = tempRet0;
 $1704 = (_bitshift64Ashr(($1698|0),($1699|0),21)|0);
 $1705 = tempRet0;
 $1706 = (_i64Add(($1704|0),($1705|0),($1600|0),($1601|0))|0);
 $1707 = tempRet0;
 $1708 = (_bitshift64Shl(($1704|0),($1705|0),21)|0);
 $1709 = tempRet0;
 $1710 = (_i64Subtract(($1698|0),($1699|0),($1708|0),($1709|0))|0);
 $1711 = tempRet0;
 $1712 = (_bitshift64Ashr(($1706|0),($1707|0),21)|0);
 $1713 = tempRet0;
 $1714 = (_i64Add(($1712|0),($1713|0),($1608|0),($1609|0))|0);
 $1715 = tempRet0;
 $1716 = (_bitshift64Shl(($1712|0),($1713|0),21)|0);
 $1717 = tempRet0;
 $1718 = (_i64Subtract(($1706|0),($1707|0),($1716|0),($1717|0))|0);
 $1719 = tempRet0;
 $1720 = (_bitshift64Ashr(($1714|0),($1715|0),21)|0);
 $1721 = tempRet0;
 $1722 = (_i64Add(($1720|0),($1721|0),($1614|0),($1615|0))|0);
 $1723 = tempRet0;
 $1724 = (_bitshift64Shl(($1720|0),($1721|0),21)|0);
 $1725 = tempRet0;
 $1726 = (_i64Subtract(($1714|0),($1715|0),($1724|0),($1725|0))|0);
 $1727 = tempRet0;
 $1728 = $1646&255;
 HEAP8[$0>>0] = $1728;
 $1729 = (_bitshift64Lshr(($1646|0),($1647|0),8)|0);
 $1730 = tempRet0;
 $1731 = $1729&255;
 $1732 = ((($0)) + 1|0);
 HEAP8[$1732>>0] = $1731;
 $1733 = (_bitshift64Lshr(($1646|0),($1647|0),16)|0);
 $1734 = tempRet0;
 $1735 = (_bitshift64Shl(($1654|0),($1655|0),5)|0);
 $1736 = tempRet0;
 $1737 = $1735 | $1733;
 $1736 | $1734;
 $1738 = $1737&255;
 $1739 = ((($0)) + 2|0);
 HEAP8[$1739>>0] = $1738;
 $1740 = (_bitshift64Lshr(($1654|0),($1655|0),3)|0);
 $1741 = tempRet0;
 $1742 = $1740&255;
 $1743 = ((($0)) + 3|0);
 HEAP8[$1743>>0] = $1742;
 $1744 = (_bitshift64Lshr(($1654|0),($1655|0),11)|0);
 $1745 = tempRet0;
 $1746 = $1744&255;
 $1747 = ((($0)) + 4|0);
 HEAP8[$1747>>0] = $1746;
 $1748 = (_bitshift64Lshr(($1654|0),($1655|0),19)|0);
 $1749 = tempRet0;
 $1750 = (_bitshift64Shl(($1662|0),($1663|0),2)|0);
 $1751 = tempRet0;
 $1752 = $1750 | $1748;
 $1751 | $1749;
 $1753 = $1752&255;
 $1754 = ((($0)) + 5|0);
 HEAP8[$1754>>0] = $1753;
 $1755 = (_bitshift64Lshr(($1662|0),($1663|0),6)|0);
 $1756 = tempRet0;
 $1757 = $1755&255;
 $1758 = ((($0)) + 6|0);
 HEAP8[$1758>>0] = $1757;
 $1759 = (_bitshift64Lshr(($1662|0),($1663|0),14)|0);
 $1760 = tempRet0;
 $1761 = (_bitshift64Shl(($1670|0),($1671|0),7)|0);
 $1762 = tempRet0;
 $1763 = $1761 | $1759;
 $1762 | $1760;
 $1764 = $1763&255;
 $1765 = ((($0)) + 7|0);
 HEAP8[$1765>>0] = $1764;
 $1766 = (_bitshift64Lshr(($1670|0),($1671|0),1)|0);
 $1767 = tempRet0;
 $1768 = $1766&255;
 $1769 = ((($0)) + 8|0);
 HEAP8[$1769>>0] = $1768;
 $1770 = (_bitshift64Lshr(($1670|0),($1671|0),9)|0);
 $1771 = tempRet0;
 $1772 = $1770&255;
 $1773 = ((($0)) + 9|0);
 HEAP8[$1773>>0] = $1772;
 $1774 = (_bitshift64Lshr(($1670|0),($1671|0),17)|0);
 $1775 = tempRet0;
 $1776 = (_bitshift64Shl(($1678|0),($1679|0),4)|0);
 $1777 = tempRet0;
 $1778 = $1776 | $1774;
 $1777 | $1775;
 $1779 = $1778&255;
 $1780 = ((($0)) + 10|0);
 HEAP8[$1780>>0] = $1779;
 $1781 = (_bitshift64Lshr(($1678|0),($1679|0),4)|0);
 $1782 = tempRet0;
 $1783 = $1781&255;
 $1784 = ((($0)) + 11|0);
 HEAP8[$1784>>0] = $1783;
 $1785 = (_bitshift64Lshr(($1678|0),($1679|0),12)|0);
 $1786 = tempRet0;
 $1787 = $1785&255;
 $1788 = ((($0)) + 12|0);
 HEAP8[$1788>>0] = $1787;
 $1789 = (_bitshift64Lshr(($1678|0),($1679|0),20)|0);
 $1790 = tempRet0;
 $1791 = (_bitshift64Shl(($1686|0),($1687|0),1)|0);
 $1792 = tempRet0;
 $1793 = $1791 | $1789;
 $1792 | $1790;
 $1794 = $1793&255;
 $1795 = ((($0)) + 13|0);
 HEAP8[$1795>>0] = $1794;
 $1796 = (_bitshift64Lshr(($1686|0),($1687|0),7)|0);
 $1797 = tempRet0;
 $1798 = $1796&255;
 $1799 = ((($0)) + 14|0);
 HEAP8[$1799>>0] = $1798;
 $1800 = (_bitshift64Lshr(($1686|0),($1687|0),15)|0);
 $1801 = tempRet0;
 $1802 = (_bitshift64Shl(($1694|0),($1695|0),6)|0);
 $1803 = tempRet0;
 $1804 = $1802 | $1800;
 $1803 | $1801;
 $1805 = $1804&255;
 $1806 = ((($0)) + 15|0);
 HEAP8[$1806>>0] = $1805;
 $1807 = (_bitshift64Lshr(($1694|0),($1695|0),2)|0);
 $1808 = tempRet0;
 $1809 = $1807&255;
 $1810 = ((($0)) + 16|0);
 HEAP8[$1810>>0] = $1809;
 $1811 = (_bitshift64Lshr(($1694|0),($1695|0),10)|0);
 $1812 = tempRet0;
 $1813 = $1811&255;
 $1814 = ((($0)) + 17|0);
 HEAP8[$1814>>0] = $1813;
 $1815 = (_bitshift64Lshr(($1694|0),($1695|0),18)|0);
 $1816 = tempRet0;
 $1817 = (_bitshift64Shl(($1702|0),($1703|0),3)|0);
 $1818 = tempRet0;
 $1819 = $1817 | $1815;
 $1818 | $1816;
 $1820 = $1819&255;
 $1821 = ((($0)) + 18|0);
 HEAP8[$1821>>0] = $1820;
 $1822 = (_bitshift64Lshr(($1702|0),($1703|0),5)|0);
 $1823 = tempRet0;
 $1824 = $1822&255;
 $1825 = ((($0)) + 19|0);
 HEAP8[$1825>>0] = $1824;
 $1826 = (_bitshift64Lshr(($1702|0),($1703|0),13)|0);
 $1827 = tempRet0;
 $1828 = $1826&255;
 $1829 = ((($0)) + 20|0);
 HEAP8[$1829>>0] = $1828;
 $1830 = $1710&255;
 $1831 = ((($0)) + 21|0);
 HEAP8[$1831>>0] = $1830;
 $1832 = (_bitshift64Lshr(($1710|0),($1711|0),8)|0);
 $1833 = tempRet0;
 $1834 = $1832&255;
 $1835 = ((($0)) + 22|0);
 HEAP8[$1835>>0] = $1834;
 $1836 = (_bitshift64Lshr(($1710|0),($1711|0),16)|0);
 $1837 = tempRet0;
 $1838 = (_bitshift64Shl(($1718|0),($1719|0),5)|0);
 $1839 = tempRet0;
 $1840 = $1838 | $1836;
 $1839 | $1837;
 $1841 = $1840&255;
 $1842 = ((($0)) + 23|0);
 HEAP8[$1842>>0] = $1841;
 $1843 = (_bitshift64Lshr(($1718|0),($1719|0),3)|0);
 $1844 = tempRet0;
 $1845 = $1843&255;
 $1846 = ((($0)) + 24|0);
 HEAP8[$1846>>0] = $1845;
 $1847 = (_bitshift64Lshr(($1718|0),($1719|0),11)|0);
 $1848 = tempRet0;
 $1849 = $1847&255;
 $1850 = ((($0)) + 25|0);
 HEAP8[$1850>>0] = $1849;
 $1851 = (_bitshift64Lshr(($1718|0),($1719|0),19)|0);
 $1852 = tempRet0;
 $1853 = (_bitshift64Shl(($1726|0),($1727|0),2)|0);
 $1854 = tempRet0;
 $1855 = $1853 | $1851;
 $1854 | $1852;
 $1856 = $1855&255;
 $1857 = ((($0)) + 26|0);
 HEAP8[$1857>>0] = $1856;
 $1858 = (_bitshift64Lshr(($1726|0),($1727|0),6)|0);
 $1859 = tempRet0;
 $1860 = $1858&255;
 $1861 = ((($0)) + 27|0);
 HEAP8[$1861>>0] = $1860;
 $1862 = (_bitshift64Lshr(($1726|0),($1727|0),14)|0);
 $1863 = tempRet0;
 $1864 = (_bitshift64Shl(($1722|0),($1723|0),7)|0);
 $1865 = tempRet0;
 $1866 = $1862 | $1864;
 $1863 | $1865;
 $1867 = $1866&255;
 $1868 = ((($0)) + 28|0);
 HEAP8[$1868>>0] = $1867;
 $1869 = (_bitshift64Lshr(($1722|0),($1723|0),1)|0);
 $1870 = tempRet0;
 $1871 = $1869&255;
 $1872 = ((($0)) + 29|0);
 HEAP8[$1872>>0] = $1871;
 $1873 = (_bitshift64Lshr(($1722|0),($1723|0),9)|0);
 $1874 = tempRet0;
 $1875 = $1873&255;
 $1876 = ((($0)) + 30|0);
 HEAP8[$1876>>0] = $1875;
 $1877 = (_bitshift64Lshr(($1722|0),($1723|0),17)|0);
 $1878 = tempRet0;
 $1879 = $1877&255;
 $1880 = ((($0)) + 31|0);
 HEAP8[$1880>>0] = $1879;
 return;
}
function _load_3_47($0) {
 $0 = $0|0;
 var $1 = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $1 = HEAP8[$0>>0]|0;
 $2 = $1&255;
 $3 = ((($0)) + 1|0);
 $4 = HEAP8[$3>>0]|0;
 $5 = $4&255;
 $6 = (_bitshift64Shl(($5|0),0,8)|0);
 $7 = tempRet0;
 $8 = $6 | $2;
 $9 = ((($0)) + 2|0);
 $10 = HEAP8[$9>>0]|0;
 $11 = $10&255;
 $12 = (_bitshift64Shl(($11|0),0,16)|0);
 $13 = tempRet0;
 $14 = $8 | $12;
 $15 = $7 | $13;
 tempRet0 = ($15);
 return ($14|0);
}
function _load_4_48($0) {
 $0 = $0|0;
 var $1 = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $2 = 0, $20 = 0, $21 = 0, $22 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0;
 var $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $1 = HEAP8[$0>>0]|0;
 $2 = $1&255;
 $3 = ((($0)) + 1|0);
 $4 = HEAP8[$3>>0]|0;
 $5 = $4&255;
 $6 = (_bitshift64Shl(($5|0),0,8)|0);
 $7 = tempRet0;
 $8 = $6 | $2;
 $9 = ((($0)) + 2|0);
 $10 = HEAP8[$9>>0]|0;
 $11 = $10&255;
 $12 = (_bitshift64Shl(($11|0),0,16)|0);
 $13 = tempRet0;
 $14 = $8 | $12;
 $15 = $7 | $13;
 $16 = ((($0)) + 3|0);
 $17 = HEAP8[$16>>0]|0;
 $18 = $17&255;
 $19 = (_bitshift64Shl(($18|0),0,24)|0);
 $20 = tempRet0;
 $21 = $14 | $19;
 $22 = $15 | $20;
 tempRet0 = ($22);
 return ($21|0);
}
function _crypto_sign_ed25519_ref10_sc_reduce($0) {
 $0 = $0|0;
 var $1 = 0, $10 = 0, $100 = 0, $1000 = 0, $1001 = 0, $1002 = 0, $1003 = 0, $1004 = 0, $1005 = 0, $1006 = 0, $1007 = 0, $1008 = 0, $1009 = 0, $101 = 0, $1010 = 0, $1011 = 0, $1012 = 0, $1013 = 0, $1014 = 0, $1015 = 0;
 var $1016 = 0, $1017 = 0, $1018 = 0, $1019 = 0, $102 = 0, $1020 = 0, $1021 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0, $113 = 0, $114 = 0;
 var $115 = 0, $116 = 0, $117 = 0, $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0;
 var $133 = 0, $134 = 0, $135 = 0, $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0, $15 = 0, $150 = 0;
 var $151 = 0, $152 = 0, $153 = 0, $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $159 = 0, $16 = 0, $160 = 0, $161 = 0, $162 = 0, $163 = 0, $164 = 0, $165 = 0, $166 = 0, $167 = 0, $168 = 0, $169 = 0;
 var $17 = 0, $170 = 0, $171 = 0, $172 = 0, $173 = 0, $174 = 0, $175 = 0, $176 = 0, $177 = 0, $178 = 0, $179 = 0, $18 = 0, $180 = 0, $181 = 0, $182 = 0, $183 = 0, $184 = 0, $185 = 0, $186 = 0, $187 = 0;
 var $188 = 0, $189 = 0, $19 = 0, $190 = 0, $191 = 0, $192 = 0, $193 = 0, $194 = 0, $195 = 0, $196 = 0, $197 = 0, $198 = 0, $199 = 0, $2 = 0, $20 = 0, $200 = 0, $201 = 0, $202 = 0, $203 = 0, $204 = 0;
 var $205 = 0, $206 = 0, $207 = 0, $208 = 0, $209 = 0, $21 = 0, $210 = 0, $211 = 0, $212 = 0, $213 = 0, $214 = 0, $215 = 0, $216 = 0, $217 = 0, $218 = 0, $219 = 0, $22 = 0, $220 = 0, $221 = 0, $222 = 0;
 var $223 = 0, $224 = 0, $225 = 0, $226 = 0, $227 = 0, $228 = 0, $229 = 0, $23 = 0, $230 = 0, $231 = 0, $232 = 0, $233 = 0, $234 = 0, $235 = 0, $236 = 0, $237 = 0, $238 = 0, $239 = 0, $24 = 0, $240 = 0;
 var $241 = 0, $242 = 0, $243 = 0, $244 = 0, $245 = 0, $246 = 0, $247 = 0, $248 = 0, $249 = 0, $25 = 0, $250 = 0, $251 = 0, $252 = 0, $253 = 0, $254 = 0, $255 = 0, $256 = 0, $257 = 0, $258 = 0, $259 = 0;
 var $26 = 0, $260 = 0, $261 = 0, $262 = 0, $263 = 0, $264 = 0, $265 = 0, $266 = 0, $267 = 0, $268 = 0, $269 = 0, $27 = 0, $270 = 0, $271 = 0, $272 = 0, $273 = 0, $274 = 0, $275 = 0, $276 = 0, $277 = 0;
 var $278 = 0, $279 = 0, $28 = 0, $280 = 0, $281 = 0, $282 = 0, $283 = 0, $284 = 0, $285 = 0, $286 = 0, $287 = 0, $288 = 0, $289 = 0, $29 = 0, $290 = 0, $291 = 0, $292 = 0, $293 = 0, $294 = 0, $295 = 0;
 var $296 = 0, $297 = 0, $298 = 0, $299 = 0, $3 = 0, $30 = 0, $300 = 0, $301 = 0, $302 = 0, $303 = 0, $304 = 0, $305 = 0, $306 = 0, $307 = 0, $308 = 0, $309 = 0, $31 = 0, $310 = 0, $311 = 0, $312 = 0;
 var $313 = 0, $314 = 0, $315 = 0, $316 = 0, $317 = 0, $318 = 0, $319 = 0, $32 = 0, $320 = 0, $321 = 0, $322 = 0, $323 = 0, $324 = 0, $325 = 0, $326 = 0, $327 = 0, $328 = 0, $329 = 0, $33 = 0, $330 = 0;
 var $331 = 0, $332 = 0, $333 = 0, $334 = 0, $335 = 0, $336 = 0, $337 = 0, $338 = 0, $339 = 0, $34 = 0, $340 = 0, $341 = 0, $342 = 0, $343 = 0, $344 = 0, $345 = 0, $346 = 0, $347 = 0, $348 = 0, $349 = 0;
 var $35 = 0, $350 = 0, $351 = 0, $352 = 0, $353 = 0, $354 = 0, $355 = 0, $356 = 0, $357 = 0, $358 = 0, $359 = 0, $36 = 0, $360 = 0, $361 = 0, $362 = 0, $363 = 0, $364 = 0, $365 = 0, $366 = 0, $367 = 0;
 var $368 = 0, $369 = 0, $37 = 0, $370 = 0, $371 = 0, $372 = 0, $373 = 0, $374 = 0, $375 = 0, $376 = 0, $377 = 0, $378 = 0, $379 = 0, $38 = 0, $380 = 0, $381 = 0, $382 = 0, $383 = 0, $384 = 0, $385 = 0;
 var $386 = 0, $387 = 0, $388 = 0, $389 = 0, $39 = 0, $390 = 0, $391 = 0, $392 = 0, $393 = 0, $394 = 0, $395 = 0, $396 = 0, $397 = 0, $398 = 0, $399 = 0, $4 = 0, $40 = 0, $400 = 0, $401 = 0, $402 = 0;
 var $403 = 0, $404 = 0, $405 = 0, $406 = 0, $407 = 0, $408 = 0, $409 = 0, $41 = 0, $410 = 0, $411 = 0, $412 = 0, $413 = 0, $414 = 0, $415 = 0, $416 = 0, $417 = 0, $418 = 0, $419 = 0, $42 = 0, $420 = 0;
 var $421 = 0, $422 = 0, $423 = 0, $424 = 0, $425 = 0, $426 = 0, $427 = 0, $428 = 0, $429 = 0, $43 = 0, $430 = 0, $431 = 0, $432 = 0, $433 = 0, $434 = 0, $435 = 0, $436 = 0, $437 = 0, $438 = 0, $439 = 0;
 var $44 = 0, $440 = 0, $441 = 0, $442 = 0, $443 = 0, $444 = 0, $445 = 0, $446 = 0, $447 = 0, $448 = 0, $449 = 0, $45 = 0, $450 = 0, $451 = 0, $452 = 0, $453 = 0, $454 = 0, $455 = 0, $456 = 0, $457 = 0;
 var $458 = 0, $459 = 0, $46 = 0, $460 = 0, $461 = 0, $462 = 0, $463 = 0, $464 = 0, $465 = 0, $466 = 0, $467 = 0, $468 = 0, $469 = 0, $47 = 0, $470 = 0, $471 = 0, $472 = 0, $473 = 0, $474 = 0, $475 = 0;
 var $476 = 0, $477 = 0, $478 = 0, $479 = 0, $48 = 0, $480 = 0, $481 = 0, $482 = 0, $483 = 0, $484 = 0, $485 = 0, $486 = 0, $487 = 0, $488 = 0, $489 = 0, $49 = 0, $490 = 0, $491 = 0, $492 = 0, $493 = 0;
 var $494 = 0, $495 = 0, $496 = 0, $497 = 0, $498 = 0, $499 = 0, $5 = 0, $50 = 0, $500 = 0, $501 = 0, $502 = 0, $503 = 0, $504 = 0, $505 = 0, $506 = 0, $507 = 0, $508 = 0, $509 = 0, $51 = 0, $510 = 0;
 var $511 = 0, $512 = 0, $513 = 0, $514 = 0, $515 = 0, $516 = 0, $517 = 0, $518 = 0, $519 = 0, $52 = 0, $520 = 0, $521 = 0, $522 = 0, $523 = 0, $524 = 0, $525 = 0, $526 = 0, $527 = 0, $528 = 0, $529 = 0;
 var $53 = 0, $530 = 0, $531 = 0, $532 = 0, $533 = 0, $534 = 0, $535 = 0, $536 = 0, $537 = 0, $538 = 0, $539 = 0, $54 = 0, $540 = 0, $541 = 0, $542 = 0, $543 = 0, $544 = 0, $545 = 0, $546 = 0, $547 = 0;
 var $548 = 0, $549 = 0, $55 = 0, $550 = 0, $551 = 0, $552 = 0, $553 = 0, $554 = 0, $555 = 0, $556 = 0, $557 = 0, $558 = 0, $559 = 0, $56 = 0, $560 = 0, $561 = 0, $562 = 0, $563 = 0, $564 = 0, $565 = 0;
 var $566 = 0, $567 = 0, $568 = 0, $569 = 0, $57 = 0, $570 = 0, $571 = 0, $572 = 0, $573 = 0, $574 = 0, $575 = 0, $576 = 0, $577 = 0, $578 = 0, $579 = 0, $58 = 0, $580 = 0, $581 = 0, $582 = 0, $583 = 0;
 var $584 = 0, $585 = 0, $586 = 0, $587 = 0, $588 = 0, $589 = 0, $59 = 0, $590 = 0, $591 = 0, $592 = 0, $593 = 0, $594 = 0, $595 = 0, $596 = 0, $597 = 0, $598 = 0, $599 = 0, $6 = 0, $60 = 0, $600 = 0;
 var $601 = 0, $602 = 0, $603 = 0, $604 = 0, $605 = 0, $606 = 0, $607 = 0, $608 = 0, $609 = 0, $61 = 0, $610 = 0, $611 = 0, $612 = 0, $613 = 0, $614 = 0, $615 = 0, $616 = 0, $617 = 0, $618 = 0, $619 = 0;
 var $62 = 0, $620 = 0, $621 = 0, $622 = 0, $623 = 0, $624 = 0, $625 = 0, $626 = 0, $627 = 0, $628 = 0, $629 = 0, $63 = 0, $630 = 0, $631 = 0, $632 = 0, $633 = 0, $634 = 0, $635 = 0, $636 = 0, $637 = 0;
 var $638 = 0, $639 = 0, $64 = 0, $640 = 0, $641 = 0, $642 = 0, $643 = 0, $644 = 0, $645 = 0, $646 = 0, $647 = 0, $648 = 0, $649 = 0, $65 = 0, $650 = 0, $651 = 0, $652 = 0, $653 = 0, $654 = 0, $655 = 0;
 var $656 = 0, $657 = 0, $658 = 0, $659 = 0, $66 = 0, $660 = 0, $661 = 0, $662 = 0, $663 = 0, $664 = 0, $665 = 0, $666 = 0, $667 = 0, $668 = 0, $669 = 0, $67 = 0, $670 = 0, $671 = 0, $672 = 0, $673 = 0;
 var $674 = 0, $675 = 0, $676 = 0, $677 = 0, $678 = 0, $679 = 0, $68 = 0, $680 = 0, $681 = 0, $682 = 0, $683 = 0, $684 = 0, $685 = 0, $686 = 0, $687 = 0, $688 = 0, $689 = 0, $69 = 0, $690 = 0, $691 = 0;
 var $692 = 0, $693 = 0, $694 = 0, $695 = 0, $696 = 0, $697 = 0, $698 = 0, $699 = 0, $7 = 0, $70 = 0, $700 = 0, $701 = 0, $702 = 0, $703 = 0, $704 = 0, $705 = 0, $706 = 0, $707 = 0, $708 = 0, $709 = 0;
 var $71 = 0, $710 = 0, $711 = 0, $712 = 0, $713 = 0, $714 = 0, $715 = 0, $716 = 0, $717 = 0, $718 = 0, $719 = 0, $72 = 0, $720 = 0, $721 = 0, $722 = 0, $723 = 0, $724 = 0, $725 = 0, $726 = 0, $727 = 0;
 var $728 = 0, $729 = 0, $73 = 0, $730 = 0, $731 = 0, $732 = 0, $733 = 0, $734 = 0, $735 = 0, $736 = 0, $737 = 0, $738 = 0, $739 = 0, $74 = 0, $740 = 0, $741 = 0, $742 = 0, $743 = 0, $744 = 0, $745 = 0;
 var $746 = 0, $747 = 0, $748 = 0, $749 = 0, $75 = 0, $750 = 0, $751 = 0, $752 = 0, $753 = 0, $754 = 0, $755 = 0, $756 = 0, $757 = 0, $758 = 0, $759 = 0, $76 = 0, $760 = 0, $761 = 0, $762 = 0, $763 = 0;
 var $764 = 0, $765 = 0, $766 = 0, $767 = 0, $768 = 0, $769 = 0, $77 = 0, $770 = 0, $771 = 0, $772 = 0, $773 = 0, $774 = 0, $775 = 0, $776 = 0, $777 = 0, $778 = 0, $779 = 0, $78 = 0, $780 = 0, $781 = 0;
 var $782 = 0, $783 = 0, $784 = 0, $785 = 0, $786 = 0, $787 = 0, $788 = 0, $789 = 0, $79 = 0, $790 = 0, $791 = 0, $792 = 0, $793 = 0, $794 = 0, $795 = 0, $796 = 0, $797 = 0, $798 = 0, $799 = 0, $8 = 0;
 var $80 = 0, $800 = 0, $801 = 0, $802 = 0, $803 = 0, $804 = 0, $805 = 0, $806 = 0, $807 = 0, $808 = 0, $809 = 0, $81 = 0, $810 = 0, $811 = 0, $812 = 0, $813 = 0, $814 = 0, $815 = 0, $816 = 0, $817 = 0;
 var $818 = 0, $819 = 0, $82 = 0, $820 = 0, $821 = 0, $822 = 0, $823 = 0, $824 = 0, $825 = 0, $826 = 0, $827 = 0, $828 = 0, $829 = 0, $83 = 0, $830 = 0, $831 = 0, $832 = 0, $833 = 0, $834 = 0, $835 = 0;
 var $836 = 0, $837 = 0, $838 = 0, $839 = 0, $84 = 0, $840 = 0, $841 = 0, $842 = 0, $843 = 0, $844 = 0, $845 = 0, $846 = 0, $847 = 0, $848 = 0, $849 = 0, $85 = 0, $850 = 0, $851 = 0, $852 = 0, $853 = 0;
 var $854 = 0, $855 = 0, $856 = 0, $857 = 0, $858 = 0, $859 = 0, $86 = 0, $860 = 0, $861 = 0, $862 = 0, $863 = 0, $864 = 0, $865 = 0, $866 = 0, $867 = 0, $868 = 0, $869 = 0, $87 = 0, $870 = 0, $871 = 0;
 var $872 = 0, $873 = 0, $874 = 0, $875 = 0, $876 = 0, $877 = 0, $878 = 0, $879 = 0, $88 = 0, $880 = 0, $881 = 0, $882 = 0, $883 = 0, $884 = 0, $885 = 0, $886 = 0, $887 = 0, $888 = 0, $889 = 0, $89 = 0;
 var $890 = 0, $891 = 0, $892 = 0, $893 = 0, $894 = 0, $895 = 0, $896 = 0, $897 = 0, $898 = 0, $899 = 0, $9 = 0, $90 = 0, $900 = 0, $901 = 0, $902 = 0, $903 = 0, $904 = 0, $905 = 0, $906 = 0, $907 = 0;
 var $908 = 0, $909 = 0, $91 = 0, $910 = 0, $911 = 0, $912 = 0, $913 = 0, $914 = 0, $915 = 0, $916 = 0, $917 = 0, $918 = 0, $919 = 0, $92 = 0, $920 = 0, $921 = 0, $922 = 0, $923 = 0, $924 = 0, $925 = 0;
 var $926 = 0, $927 = 0, $928 = 0, $929 = 0, $93 = 0, $930 = 0, $931 = 0, $932 = 0, $933 = 0, $934 = 0, $935 = 0, $936 = 0, $937 = 0, $938 = 0, $939 = 0, $94 = 0, $940 = 0, $941 = 0, $942 = 0, $943 = 0;
 var $944 = 0, $945 = 0, $946 = 0, $947 = 0, $948 = 0, $949 = 0, $95 = 0, $950 = 0, $951 = 0, $952 = 0, $953 = 0, $954 = 0, $955 = 0, $956 = 0, $957 = 0, $958 = 0, $959 = 0, $96 = 0, $960 = 0, $961 = 0;
 var $962 = 0, $963 = 0, $964 = 0, $965 = 0, $966 = 0, $967 = 0, $968 = 0, $969 = 0, $97 = 0, $970 = 0, $971 = 0, $972 = 0, $973 = 0, $974 = 0, $975 = 0, $976 = 0, $977 = 0, $978 = 0, $979 = 0, $98 = 0;
 var $980 = 0, $981 = 0, $982 = 0, $983 = 0, $984 = 0, $985 = 0, $986 = 0, $987 = 0, $988 = 0, $989 = 0, $99 = 0, $990 = 0, $991 = 0, $992 = 0, $993 = 0, $994 = 0, $995 = 0, $996 = 0, $997 = 0, $998 = 0;
 var $999 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $1 = (_load_3_51($0)|0);
 $2 = tempRet0;
 $3 = $1 & 2097151;
 $4 = ((($0)) + 2|0);
 $5 = (_load_4_52($4)|0);
 $6 = tempRet0;
 $7 = (_bitshift64Lshr(($5|0),($6|0),5)|0);
 $8 = tempRet0;
 $9 = $7 & 2097151;
 $10 = ((($0)) + 5|0);
 $11 = (_load_3_51($10)|0);
 $12 = tempRet0;
 $13 = (_bitshift64Lshr(($11|0),($12|0),2)|0);
 $14 = tempRet0;
 $15 = $13 & 2097151;
 $16 = ((($0)) + 7|0);
 $17 = (_load_4_52($16)|0);
 $18 = tempRet0;
 $19 = (_bitshift64Lshr(($17|0),($18|0),7)|0);
 $20 = tempRet0;
 $21 = $19 & 2097151;
 $22 = ((($0)) + 10|0);
 $23 = (_load_4_52($22)|0);
 $24 = tempRet0;
 $25 = (_bitshift64Lshr(($23|0),($24|0),4)|0);
 $26 = tempRet0;
 $27 = $25 & 2097151;
 $28 = ((($0)) + 13|0);
 $29 = (_load_3_51($28)|0);
 $30 = tempRet0;
 $31 = (_bitshift64Lshr(($29|0),($30|0),1)|0);
 $32 = tempRet0;
 $33 = $31 & 2097151;
 $34 = ((($0)) + 15|0);
 $35 = (_load_4_52($34)|0);
 $36 = tempRet0;
 $37 = (_bitshift64Lshr(($35|0),($36|0),6)|0);
 $38 = tempRet0;
 $39 = $37 & 2097151;
 $40 = ((($0)) + 18|0);
 $41 = (_load_3_51($40)|0);
 $42 = tempRet0;
 $43 = (_bitshift64Lshr(($41|0),($42|0),3)|0);
 $44 = tempRet0;
 $45 = $43 & 2097151;
 $46 = ((($0)) + 21|0);
 $47 = (_load_3_51($46)|0);
 $48 = tempRet0;
 $49 = $47 & 2097151;
 $50 = ((($0)) + 23|0);
 $51 = (_load_4_52($50)|0);
 $52 = tempRet0;
 $53 = (_bitshift64Lshr(($51|0),($52|0),5)|0);
 $54 = tempRet0;
 $55 = $53 & 2097151;
 $56 = ((($0)) + 26|0);
 $57 = (_load_3_51($56)|0);
 $58 = tempRet0;
 $59 = (_bitshift64Lshr(($57|0),($58|0),2)|0);
 $60 = tempRet0;
 $61 = $59 & 2097151;
 $62 = ((($0)) + 28|0);
 $63 = (_load_4_52($62)|0);
 $64 = tempRet0;
 $65 = (_bitshift64Lshr(($63|0),($64|0),7)|0);
 $66 = tempRet0;
 $67 = $65 & 2097151;
 $68 = ((($0)) + 31|0);
 $69 = (_load_4_52($68)|0);
 $70 = tempRet0;
 $71 = (_bitshift64Lshr(($69|0),($70|0),4)|0);
 $72 = tempRet0;
 $73 = $71 & 2097151;
 $74 = ((($0)) + 34|0);
 $75 = (_load_3_51($74)|0);
 $76 = tempRet0;
 $77 = (_bitshift64Lshr(($75|0),($76|0),1)|0);
 $78 = tempRet0;
 $79 = $77 & 2097151;
 $80 = ((($0)) + 36|0);
 $81 = (_load_4_52($80)|0);
 $82 = tempRet0;
 $83 = (_bitshift64Lshr(($81|0),($82|0),6)|0);
 $84 = tempRet0;
 $85 = $83 & 2097151;
 $86 = ((($0)) + 39|0);
 $87 = (_load_3_51($86)|0);
 $88 = tempRet0;
 $89 = (_bitshift64Lshr(($87|0),($88|0),3)|0);
 $90 = tempRet0;
 $91 = $89 & 2097151;
 $92 = ((($0)) + 42|0);
 $93 = (_load_3_51($92)|0);
 $94 = tempRet0;
 $95 = $93 & 2097151;
 $96 = ((($0)) + 44|0);
 $97 = (_load_4_52($96)|0);
 $98 = tempRet0;
 $99 = (_bitshift64Lshr(($97|0),($98|0),5)|0);
 $100 = tempRet0;
 $101 = $99 & 2097151;
 $102 = ((($0)) + 47|0);
 $103 = (_load_3_51($102)|0);
 $104 = tempRet0;
 $105 = (_bitshift64Lshr(($103|0),($104|0),2)|0);
 $106 = tempRet0;
 $107 = $105 & 2097151;
 $108 = ((($0)) + 49|0);
 $109 = (_load_4_52($108)|0);
 $110 = tempRet0;
 $111 = (_bitshift64Lshr(($109|0),($110|0),7)|0);
 $112 = tempRet0;
 $113 = $111 & 2097151;
 $114 = ((($0)) + 52|0);
 $115 = (_load_4_52($114)|0);
 $116 = tempRet0;
 $117 = (_bitshift64Lshr(($115|0),($116|0),4)|0);
 $118 = tempRet0;
 $119 = $117 & 2097151;
 $120 = ((($0)) + 55|0);
 $121 = (_load_3_51($120)|0);
 $122 = tempRet0;
 $123 = (_bitshift64Lshr(($121|0),($122|0),1)|0);
 $124 = tempRet0;
 $125 = $123 & 2097151;
 $126 = ((($0)) + 57|0);
 $127 = (_load_4_52($126)|0);
 $128 = tempRet0;
 $129 = (_bitshift64Lshr(($127|0),($128|0),6)|0);
 $130 = tempRet0;
 $131 = $129 & 2097151;
 $132 = ((($0)) + 60|0);
 $133 = (_load_4_52($132)|0);
 $134 = tempRet0;
 $135 = (_bitshift64Lshr(($133|0),($134|0),3)|0);
 $136 = tempRet0;
 $137 = (___muldi3(($135|0),($136|0),666643,0)|0);
 $138 = tempRet0;
 $139 = (___muldi3(($135|0),($136|0),470296,0)|0);
 $140 = tempRet0;
 $141 = (___muldi3(($135|0),($136|0),654183,0)|0);
 $142 = tempRet0;
 $143 = (___muldi3(($135|0),($136|0),-997805,-1)|0);
 $144 = tempRet0;
 $145 = (___muldi3(($135|0),($136|0),136657,0)|0);
 $146 = tempRet0;
 $147 = (_i64Add(($145|0),($146|0),($91|0),0)|0);
 $148 = tempRet0;
 $149 = (___muldi3(($135|0),($136|0),-683901,-1)|0);
 $150 = tempRet0;
 $151 = (_i64Add(($149|0),($150|0),($95|0),0)|0);
 $152 = tempRet0;
 $153 = (___muldi3(($131|0),0,666643,0)|0);
 $154 = tempRet0;
 $155 = (___muldi3(($131|0),0,470296,0)|0);
 $156 = tempRet0;
 $157 = (___muldi3(($131|0),0,654183,0)|0);
 $158 = tempRet0;
 $159 = (___muldi3(($131|0),0,-997805,-1)|0);
 $160 = tempRet0;
 $161 = (___muldi3(($131|0),0,136657,0)|0);
 $162 = tempRet0;
 $163 = (___muldi3(($131|0),0,-683901,-1)|0);
 $164 = tempRet0;
 $165 = (_i64Add(($147|0),($148|0),($163|0),($164|0))|0);
 $166 = tempRet0;
 $167 = (___muldi3(($125|0),0,666643,0)|0);
 $168 = tempRet0;
 $169 = (___muldi3(($125|0),0,470296,0)|0);
 $170 = tempRet0;
 $171 = (___muldi3(($125|0),0,654183,0)|0);
 $172 = tempRet0;
 $173 = (___muldi3(($125|0),0,-997805,-1)|0);
 $174 = tempRet0;
 $175 = (___muldi3(($125|0),0,136657,0)|0);
 $176 = tempRet0;
 $177 = (___muldi3(($125|0),0,-683901,-1)|0);
 $178 = tempRet0;
 $179 = (_i64Add(($177|0),($178|0),($85|0),0)|0);
 $180 = tempRet0;
 $181 = (_i64Add(($179|0),($180|0),($143|0),($144|0))|0);
 $182 = tempRet0;
 $183 = (_i64Add(($181|0),($182|0),($161|0),($162|0))|0);
 $184 = tempRet0;
 $185 = (___muldi3(($119|0),0,666643,0)|0);
 $186 = tempRet0;
 $187 = (___muldi3(($119|0),0,470296,0)|0);
 $188 = tempRet0;
 $189 = (___muldi3(($119|0),0,654183,0)|0);
 $190 = tempRet0;
 $191 = (___muldi3(($119|0),0,-997805,-1)|0);
 $192 = tempRet0;
 $193 = (___muldi3(($119|0),0,136657,0)|0);
 $194 = tempRet0;
 $195 = (___muldi3(($119|0),0,-683901,-1)|0);
 $196 = tempRet0;
 $197 = (___muldi3(($113|0),0,666643,0)|0);
 $198 = tempRet0;
 $199 = (___muldi3(($113|0),0,470296,0)|0);
 $200 = tempRet0;
 $201 = (___muldi3(($113|0),0,654183,0)|0);
 $202 = tempRet0;
 $203 = (___muldi3(($113|0),0,-997805,-1)|0);
 $204 = tempRet0;
 $205 = (___muldi3(($113|0),0,136657,0)|0);
 $206 = tempRet0;
 $207 = (___muldi3(($113|0),0,-683901,-1)|0);
 $208 = tempRet0;
 $209 = (_i64Add(($207|0),($208|0),($73|0),0)|0);
 $210 = tempRet0;
 $211 = (_i64Add(($209|0),($210|0),($193|0),($194|0))|0);
 $212 = tempRet0;
 $213 = (_i64Add(($211|0),($212|0),($173|0),($174|0))|0);
 $214 = tempRet0;
 $215 = (_i64Add(($213|0),($214|0),($139|0),($140|0))|0);
 $216 = tempRet0;
 $217 = (_i64Add(($215|0),($216|0),($157|0),($158|0))|0);
 $218 = tempRet0;
 $219 = (___muldi3(($107|0),0,666643,0)|0);
 $220 = tempRet0;
 $221 = (_i64Add(($219|0),($220|0),($39|0),0)|0);
 $222 = tempRet0;
 $223 = (___muldi3(($107|0),0,470296,0)|0);
 $224 = tempRet0;
 $225 = (___muldi3(($107|0),0,654183,0)|0);
 $226 = tempRet0;
 $227 = (_i64Add(($225|0),($226|0),($49|0),0)|0);
 $228 = tempRet0;
 $229 = (_i64Add(($227|0),($228|0),($199|0),($200|0))|0);
 $230 = tempRet0;
 $231 = (_i64Add(($229|0),($230|0),($185|0),($186|0))|0);
 $232 = tempRet0;
 $233 = (___muldi3(($107|0),0,-997805,-1)|0);
 $234 = tempRet0;
 $235 = (___muldi3(($107|0),0,136657,0)|0);
 $236 = tempRet0;
 $237 = (_i64Add(($235|0),($236|0),($61|0),0)|0);
 $238 = tempRet0;
 $239 = (_i64Add(($237|0),($238|0),($203|0),($204|0))|0);
 $240 = tempRet0;
 $241 = (_i64Add(($239|0),($240|0),($189|0),($190|0))|0);
 $242 = tempRet0;
 $243 = (_i64Add(($241|0),($242|0),($169|0),($170|0))|0);
 $244 = tempRet0;
 $245 = (_i64Add(($243|0),($244|0),($153|0),($154|0))|0);
 $246 = tempRet0;
 $247 = (___muldi3(($107|0),0,-683901,-1)|0);
 $248 = tempRet0;
 $249 = (_i64Add(($221|0),($222|0),1048576,0)|0);
 $250 = tempRet0;
 $251 = (_bitshift64Lshr(($249|0),($250|0),21)|0);
 $252 = tempRet0;
 $253 = (_i64Add(($223|0),($224|0),($45|0),0)|0);
 $254 = tempRet0;
 $255 = (_i64Add(($253|0),($254|0),($197|0),($198|0))|0);
 $256 = tempRet0;
 $257 = (_i64Add(($255|0),($256|0),($251|0),($252|0))|0);
 $258 = tempRet0;
 $259 = $249 & -2097152;
 $260 = $250 & 2047;
 $261 = (_i64Subtract(($221|0),($222|0),($259|0),($260|0))|0);
 $262 = tempRet0;
 $263 = (_i64Add(($231|0),($232|0),1048576,0)|0);
 $264 = tempRet0;
 $265 = (_bitshift64Lshr(($263|0),($264|0),21)|0);
 $266 = tempRet0;
 $267 = (_i64Add(($233|0),($234|0),($55|0),0)|0);
 $268 = tempRet0;
 $269 = (_i64Add(($267|0),($268|0),($201|0),($202|0))|0);
 $270 = tempRet0;
 $271 = (_i64Add(($269|0),($270|0),($187|0),($188|0))|0);
 $272 = tempRet0;
 $273 = (_i64Add(($271|0),($272|0),($167|0),($168|0))|0);
 $274 = tempRet0;
 $275 = (_i64Add(($273|0),($274|0),($265|0),($266|0))|0);
 $276 = tempRet0;
 $277 = $263 & -2097152;
 $278 = (_i64Add(($245|0),($246|0),1048576,0)|0);
 $279 = tempRet0;
 $280 = (_bitshift64Ashr(($278|0),($279|0),21)|0);
 $281 = tempRet0;
 $282 = (_i64Add(($247|0),($248|0),($67|0),0)|0);
 $283 = tempRet0;
 $284 = (_i64Add(($282|0),($283|0),($205|0),($206|0))|0);
 $285 = tempRet0;
 $286 = (_i64Add(($284|0),($285|0),($191|0),($192|0))|0);
 $287 = tempRet0;
 $288 = (_i64Add(($286|0),($287|0),($171|0),($172|0))|0);
 $289 = tempRet0;
 $290 = (_i64Add(($288|0),($289|0),($137|0),($138|0))|0);
 $291 = tempRet0;
 $292 = (_i64Add(($290|0),($291|0),($155|0),($156|0))|0);
 $293 = tempRet0;
 $294 = (_i64Add(($292|0),($293|0),($280|0),($281|0))|0);
 $295 = tempRet0;
 $296 = (_bitshift64Shl(($280|0),($281|0),21)|0);
 $297 = tempRet0;
 $298 = (_i64Add(($217|0),($218|0),1048576,0)|0);
 $299 = tempRet0;
 $300 = (_bitshift64Ashr(($298|0),($299|0),21)|0);
 $301 = tempRet0;
 $302 = (_i64Add(($195|0),($196|0),($79|0),0)|0);
 $303 = tempRet0;
 $304 = (_i64Add(($302|0),($303|0),($175|0),($176|0))|0);
 $305 = tempRet0;
 $306 = (_i64Add(($304|0),($305|0),($141|0),($142|0))|0);
 $307 = tempRet0;
 $308 = (_i64Add(($306|0),($307|0),($159|0),($160|0))|0);
 $309 = tempRet0;
 $310 = (_i64Add(($308|0),($309|0),($300|0),($301|0))|0);
 $311 = tempRet0;
 $312 = (_bitshift64Shl(($300|0),($301|0),21)|0);
 $313 = tempRet0;
 $314 = (_i64Subtract(($217|0),($218|0),($312|0),($313|0))|0);
 $315 = tempRet0;
 $316 = (_i64Add(($183|0),($184|0),1048576,0)|0);
 $317 = tempRet0;
 $318 = (_bitshift64Ashr(($316|0),($317|0),21)|0);
 $319 = tempRet0;
 $320 = (_i64Add(($165|0),($166|0),($318|0),($319|0))|0);
 $321 = tempRet0;
 $322 = (_bitshift64Shl(($318|0),($319|0),21)|0);
 $323 = tempRet0;
 $324 = (_i64Subtract(($183|0),($184|0),($322|0),($323|0))|0);
 $325 = tempRet0;
 $326 = (_i64Add(($151|0),($152|0),1048576,0)|0);
 $327 = tempRet0;
 $328 = (_bitshift64Ashr(($326|0),($327|0),21)|0);
 $329 = tempRet0;
 $330 = (_i64Add(($328|0),($329|0),($101|0),0)|0);
 $331 = tempRet0;
 $332 = (_bitshift64Shl(($328|0),($329|0),21)|0);
 $333 = tempRet0;
 $334 = (_i64Subtract(($151|0),($152|0),($332|0),($333|0))|0);
 $335 = tempRet0;
 $336 = (_i64Add(($257|0),($258|0),1048576,0)|0);
 $337 = tempRet0;
 $338 = (_bitshift64Lshr(($336|0),($337|0),21)|0);
 $339 = tempRet0;
 $340 = $336 & -2097152;
 $341 = (_i64Subtract(($257|0),($258|0),($340|0),($337|0))|0);
 $342 = tempRet0;
 $343 = (_i64Add(($275|0),($276|0),1048576,0)|0);
 $344 = tempRet0;
 $345 = (_bitshift64Ashr(($343|0),($344|0),21)|0);
 $346 = tempRet0;
 $347 = (_bitshift64Shl(($345|0),($346|0),21)|0);
 $348 = tempRet0;
 $349 = (_i64Add(($294|0),($295|0),1048576,0)|0);
 $350 = tempRet0;
 $351 = (_bitshift64Ashr(($349|0),($350|0),21)|0);
 $352 = tempRet0;
 $353 = (_i64Add(($351|0),($352|0),($314|0),($315|0))|0);
 $354 = tempRet0;
 $355 = (_bitshift64Shl(($351|0),($352|0),21)|0);
 $356 = tempRet0;
 $357 = (_i64Subtract(($294|0),($295|0),($355|0),($356|0))|0);
 $358 = tempRet0;
 $359 = (_i64Add(($310|0),($311|0),1048576,0)|0);
 $360 = tempRet0;
 $361 = (_bitshift64Ashr(($359|0),($360|0),21)|0);
 $362 = tempRet0;
 $363 = (_i64Add(($361|0),($362|0),($324|0),($325|0))|0);
 $364 = tempRet0;
 $365 = (_bitshift64Shl(($361|0),($362|0),21)|0);
 $366 = tempRet0;
 $367 = (_i64Subtract(($310|0),($311|0),($365|0),($366|0))|0);
 $368 = tempRet0;
 $369 = (_i64Add(($320|0),($321|0),1048576,0)|0);
 $370 = tempRet0;
 $371 = (_bitshift64Ashr(($369|0),($370|0),21)|0);
 $372 = tempRet0;
 $373 = (_i64Add(($371|0),($372|0),($334|0),($335|0))|0);
 $374 = tempRet0;
 $375 = (_bitshift64Shl(($371|0),($372|0),21)|0);
 $376 = tempRet0;
 $377 = (_i64Subtract(($320|0),($321|0),($375|0),($376|0))|0);
 $378 = tempRet0;
 $379 = (___muldi3(($330|0),($331|0),666643,0)|0);
 $380 = tempRet0;
 $381 = (_i64Add(($379|0),($380|0),($33|0),0)|0);
 $382 = tempRet0;
 $383 = (___muldi3(($330|0),($331|0),470296,0)|0);
 $384 = tempRet0;
 $385 = (_i64Add(($261|0),($262|0),($383|0),($384|0))|0);
 $386 = tempRet0;
 $387 = (___muldi3(($330|0),($331|0),654183,0)|0);
 $388 = tempRet0;
 $389 = (_i64Add(($341|0),($342|0),($387|0),($388|0))|0);
 $390 = tempRet0;
 $391 = (___muldi3(($330|0),($331|0),-997805,-1)|0);
 $392 = tempRet0;
 $393 = (___muldi3(($330|0),($331|0),136657,0)|0);
 $394 = tempRet0;
 $395 = (___muldi3(($330|0),($331|0),-683901,-1)|0);
 $396 = tempRet0;
 $397 = (_i64Add(($395|0),($396|0),($245|0),($246|0))|0);
 $398 = tempRet0;
 $399 = (_i64Add(($397|0),($398|0),($345|0),($346|0))|0);
 $400 = tempRet0;
 $401 = (_i64Subtract(($399|0),($400|0),($296|0),($297|0))|0);
 $402 = tempRet0;
 $403 = (___muldi3(($373|0),($374|0),666643,0)|0);
 $404 = tempRet0;
 $405 = (_i64Add(($403|0),($404|0),($27|0),0)|0);
 $406 = tempRet0;
 $407 = (___muldi3(($373|0),($374|0),470296,0)|0);
 $408 = tempRet0;
 $409 = (_i64Add(($381|0),($382|0),($407|0),($408|0))|0);
 $410 = tempRet0;
 $411 = (___muldi3(($373|0),($374|0),654183,0)|0);
 $412 = tempRet0;
 $413 = (_i64Add(($385|0),($386|0),($411|0),($412|0))|0);
 $414 = tempRet0;
 $415 = (___muldi3(($373|0),($374|0),-997805,-1)|0);
 $416 = tempRet0;
 $417 = (_i64Add(($389|0),($390|0),($415|0),($416|0))|0);
 $418 = tempRet0;
 $419 = (___muldi3(($373|0),($374|0),136657,0)|0);
 $420 = tempRet0;
 $421 = (___muldi3(($373|0),($374|0),-683901,-1)|0);
 $422 = tempRet0;
 $423 = (___muldi3(($377|0),($378|0),666643,0)|0);
 $424 = tempRet0;
 $425 = (_i64Add(($423|0),($424|0),($21|0),0)|0);
 $426 = tempRet0;
 $427 = (___muldi3(($377|0),($378|0),470296,0)|0);
 $428 = tempRet0;
 $429 = (_i64Add(($405|0),($406|0),($427|0),($428|0))|0);
 $430 = tempRet0;
 $431 = (___muldi3(($377|0),($378|0),654183,0)|0);
 $432 = tempRet0;
 $433 = (_i64Add(($409|0),($410|0),($431|0),($432|0))|0);
 $434 = tempRet0;
 $435 = (___muldi3(($377|0),($378|0),-997805,-1)|0);
 $436 = tempRet0;
 $437 = (_i64Add(($413|0),($414|0),($435|0),($436|0))|0);
 $438 = tempRet0;
 $439 = (___muldi3(($377|0),($378|0),136657,0)|0);
 $440 = tempRet0;
 $441 = (_i64Add(($417|0),($418|0),($439|0),($440|0))|0);
 $442 = tempRet0;
 $443 = (___muldi3(($377|0),($378|0),-683901,-1)|0);
 $444 = tempRet0;
 $445 = (_i64Add(($338|0),($339|0),($231|0),($232|0))|0);
 $446 = tempRet0;
 $447 = (_i64Subtract(($445|0),($446|0),($277|0),($264|0))|0);
 $448 = tempRet0;
 $449 = (_i64Add(($447|0),($448|0),($391|0),($392|0))|0);
 $450 = tempRet0;
 $451 = (_i64Add(($449|0),($450|0),($419|0),($420|0))|0);
 $452 = tempRet0;
 $453 = (_i64Add(($451|0),($452|0),($443|0),($444|0))|0);
 $454 = tempRet0;
 $455 = (___muldi3(($363|0),($364|0),666643,0)|0);
 $456 = tempRet0;
 $457 = (_i64Add(($455|0),($456|0),($15|0),0)|0);
 $458 = tempRet0;
 $459 = (___muldi3(($363|0),($364|0),470296,0)|0);
 $460 = tempRet0;
 $461 = (_i64Add(($425|0),($426|0),($459|0),($460|0))|0);
 $462 = tempRet0;
 $463 = (___muldi3(($363|0),($364|0),654183,0)|0);
 $464 = tempRet0;
 $465 = (_i64Add(($429|0),($430|0),($463|0),($464|0))|0);
 $466 = tempRet0;
 $467 = (___muldi3(($363|0),($364|0),-997805,-1)|0);
 $468 = tempRet0;
 $469 = (_i64Add(($433|0),($434|0),($467|0),($468|0))|0);
 $470 = tempRet0;
 $471 = (___muldi3(($363|0),($364|0),136657,0)|0);
 $472 = tempRet0;
 $473 = (_i64Add(($437|0),($438|0),($471|0),($472|0))|0);
 $474 = tempRet0;
 $475 = (___muldi3(($363|0),($364|0),-683901,-1)|0);
 $476 = tempRet0;
 $477 = (_i64Add(($441|0),($442|0),($475|0),($476|0))|0);
 $478 = tempRet0;
 $479 = (___muldi3(($367|0),($368|0),666643,0)|0);
 $480 = tempRet0;
 $481 = (___muldi3(($367|0),($368|0),470296,0)|0);
 $482 = tempRet0;
 $483 = (___muldi3(($367|0),($368|0),654183,0)|0);
 $484 = tempRet0;
 $485 = (___muldi3(($367|0),($368|0),-997805,-1)|0);
 $486 = tempRet0;
 $487 = (___muldi3(($367|0),($368|0),136657,0)|0);
 $488 = tempRet0;
 $489 = (___muldi3(($367|0),($368|0),-683901,-1)|0);
 $490 = tempRet0;
 $491 = (_i64Add(($473|0),($474|0),($489|0),($490|0))|0);
 $492 = tempRet0;
 $493 = (___muldi3(($353|0),($354|0),666643,0)|0);
 $494 = tempRet0;
 $495 = (_i64Add(($493|0),($494|0),($3|0),0)|0);
 $496 = tempRet0;
 $497 = (___muldi3(($353|0),($354|0),470296,0)|0);
 $498 = tempRet0;
 $499 = (___muldi3(($353|0),($354|0),654183,0)|0);
 $500 = tempRet0;
 $501 = (_i64Add(($457|0),($458|0),($499|0),($500|0))|0);
 $502 = tempRet0;
 $503 = (_i64Add(($501|0),($502|0),($481|0),($482|0))|0);
 $504 = tempRet0;
 $505 = (___muldi3(($353|0),($354|0),-997805,-1)|0);
 $506 = tempRet0;
 $507 = (___muldi3(($353|0),($354|0),136657,0)|0);
 $508 = tempRet0;
 $509 = (_i64Add(($465|0),($466|0),($507|0),($508|0))|0);
 $510 = tempRet0;
 $511 = (_i64Add(($509|0),($510|0),($485|0),($486|0))|0);
 $512 = tempRet0;
 $513 = (___muldi3(($353|0),($354|0),-683901,-1)|0);
 $514 = tempRet0;
 $515 = (_i64Add(($495|0),($496|0),1048576,0)|0);
 $516 = tempRet0;
 $517 = (_bitshift64Ashr(($515|0),($516|0),21)|0);
 $518 = tempRet0;
 $519 = (_i64Add(($497|0),($498|0),($9|0),0)|0);
 $520 = tempRet0;
 $521 = (_i64Add(($519|0),($520|0),($479|0),($480|0))|0);
 $522 = tempRet0;
 $523 = (_i64Add(($521|0),($522|0),($517|0),($518|0))|0);
 $524 = tempRet0;
 $525 = (_bitshift64Shl(($517|0),($518|0),21)|0);
 $526 = tempRet0;
 $527 = (_i64Subtract(($495|0),($496|0),($525|0),($526|0))|0);
 $528 = tempRet0;
 $529 = (_i64Add(($503|0),($504|0),1048576,0)|0);
 $530 = tempRet0;
 $531 = (_bitshift64Ashr(($529|0),($530|0),21)|0);
 $532 = tempRet0;
 $533 = (_i64Add(($461|0),($462|0),($505|0),($506|0))|0);
 $534 = tempRet0;
 $535 = (_i64Add(($533|0),($534|0),($483|0),($484|0))|0);
 $536 = tempRet0;
 $537 = (_i64Add(($535|0),($536|0),($531|0),($532|0))|0);
 $538 = tempRet0;
 $539 = (_bitshift64Shl(($531|0),($532|0),21)|0);
 $540 = tempRet0;
 $541 = (_i64Add(($511|0),($512|0),1048576,0)|0);
 $542 = tempRet0;
 $543 = (_bitshift64Ashr(($541|0),($542|0),21)|0);
 $544 = tempRet0;
 $545 = (_i64Add(($469|0),($470|0),($513|0),($514|0))|0);
 $546 = tempRet0;
 $547 = (_i64Add(($545|0),($546|0),($487|0),($488|0))|0);
 $548 = tempRet0;
 $549 = (_i64Add(($547|0),($548|0),($543|0),($544|0))|0);
 $550 = tempRet0;
 $551 = (_bitshift64Shl(($543|0),($544|0),21)|0);
 $552 = tempRet0;
 $553 = (_i64Add(($491|0),($492|0),1048576,0)|0);
 $554 = tempRet0;
 $555 = (_bitshift64Ashr(($553|0),($554|0),21)|0);
 $556 = tempRet0;
 $557 = (_i64Add(($477|0),($478|0),($555|0),($556|0))|0);
 $558 = tempRet0;
 $559 = (_bitshift64Shl(($555|0),($556|0),21)|0);
 $560 = tempRet0;
 $561 = (_i64Subtract(($491|0),($492|0),($559|0),($560|0))|0);
 $562 = tempRet0;
 $563 = (_i64Add(($453|0),($454|0),1048576,0)|0);
 $564 = tempRet0;
 $565 = (_bitshift64Ashr(($563|0),($564|0),21)|0);
 $566 = tempRet0;
 $567 = (_i64Add(($393|0),($394|0),($275|0),($276|0))|0);
 $568 = tempRet0;
 $569 = (_i64Subtract(($567|0),($568|0),($347|0),($348|0))|0);
 $570 = tempRet0;
 $571 = (_i64Add(($569|0),($570|0),($421|0),($422|0))|0);
 $572 = tempRet0;
 $573 = (_i64Add(($571|0),($572|0),($565|0),($566|0))|0);
 $574 = tempRet0;
 $575 = (_bitshift64Shl(($565|0),($566|0),21)|0);
 $576 = tempRet0;
 $577 = (_i64Subtract(($453|0),($454|0),($575|0),($576|0))|0);
 $578 = tempRet0;
 $579 = (_i64Add(($401|0),($402|0),1048576,0)|0);
 $580 = tempRet0;
 $581 = (_bitshift64Ashr(($579|0),($580|0),21)|0);
 $582 = tempRet0;
 $583 = (_i64Add(($581|0),($582|0),($357|0),($358|0))|0);
 $584 = tempRet0;
 $585 = (_bitshift64Shl(($581|0),($582|0),21)|0);
 $586 = tempRet0;
 $587 = (_i64Subtract(($401|0),($402|0),($585|0),($586|0))|0);
 $588 = tempRet0;
 $589 = (_i64Add(($523|0),($524|0),1048576,0)|0);
 $590 = tempRet0;
 $591 = (_bitshift64Ashr(($589|0),($590|0),21)|0);
 $592 = tempRet0;
 $593 = (_bitshift64Shl(($591|0),($592|0),21)|0);
 $594 = tempRet0;
 $595 = (_i64Add(($537|0),($538|0),1048576,0)|0);
 $596 = tempRet0;
 $597 = (_bitshift64Ashr(($595|0),($596|0),21)|0);
 $598 = tempRet0;
 $599 = (_bitshift64Shl(($597|0),($598|0),21)|0);
 $600 = tempRet0;
 $601 = (_i64Add(($549|0),($550|0),1048576,0)|0);
 $602 = tempRet0;
 $603 = (_bitshift64Ashr(($601|0),($602|0),21)|0);
 $604 = tempRet0;
 $605 = (_i64Add(($561|0),($562|0),($603|0),($604|0))|0);
 $606 = tempRet0;
 $607 = (_bitshift64Shl(($603|0),($604|0),21)|0);
 $608 = tempRet0;
 $609 = (_i64Add(($557|0),($558|0),1048576,0)|0);
 $610 = tempRet0;
 $611 = (_bitshift64Ashr(($609|0),($610|0),21)|0);
 $612 = tempRet0;
 $613 = (_i64Add(($577|0),($578|0),($611|0),($612|0))|0);
 $614 = tempRet0;
 $615 = (_bitshift64Shl(($611|0),($612|0),21)|0);
 $616 = tempRet0;
 $617 = (_i64Subtract(($557|0),($558|0),($615|0),($616|0))|0);
 $618 = tempRet0;
 $619 = (_i64Add(($573|0),($574|0),1048576,0)|0);
 $620 = tempRet0;
 $621 = (_bitshift64Ashr(($619|0),($620|0),21)|0);
 $622 = tempRet0;
 $623 = (_i64Add(($587|0),($588|0),($621|0),($622|0))|0);
 $624 = tempRet0;
 $625 = (_bitshift64Shl(($621|0),($622|0),21)|0);
 $626 = tempRet0;
 $627 = (_i64Subtract(($573|0),($574|0),($625|0),($626|0))|0);
 $628 = tempRet0;
 $629 = (_i64Add(($583|0),($584|0),1048576,0)|0);
 $630 = tempRet0;
 $631 = (_bitshift64Ashr(($629|0),($630|0),21)|0);
 $632 = tempRet0;
 $633 = (_bitshift64Shl(($631|0),($632|0),21)|0);
 $634 = tempRet0;
 $635 = (_i64Subtract(($583|0),($584|0),($633|0),($634|0))|0);
 $636 = tempRet0;
 $637 = (___muldi3(($631|0),($632|0),666643,0)|0);
 $638 = tempRet0;
 $639 = (_i64Add(($527|0),($528|0),($637|0),($638|0))|0);
 $640 = tempRet0;
 $641 = (___muldi3(($631|0),($632|0),470296,0)|0);
 $642 = tempRet0;
 $643 = (___muldi3(($631|0),($632|0),654183,0)|0);
 $644 = tempRet0;
 $645 = (___muldi3(($631|0),($632|0),-997805,-1)|0);
 $646 = tempRet0;
 $647 = (___muldi3(($631|0),($632|0),136657,0)|0);
 $648 = tempRet0;
 $649 = (___muldi3(($631|0),($632|0),-683901,-1)|0);
 $650 = tempRet0;
 $651 = (_bitshift64Ashr(($639|0),($640|0),21)|0);
 $652 = tempRet0;
 $653 = (_i64Add(($641|0),($642|0),($523|0),($524|0))|0);
 $654 = tempRet0;
 $655 = (_i64Subtract(($653|0),($654|0),($593|0),($594|0))|0);
 $656 = tempRet0;
 $657 = (_i64Add(($655|0),($656|0),($651|0),($652|0))|0);
 $658 = tempRet0;
 $659 = (_bitshift64Shl(($651|0),($652|0),21)|0);
 $660 = tempRet0;
 $661 = (_i64Subtract(($639|0),($640|0),($659|0),($660|0))|0);
 $662 = tempRet0;
 $663 = (_bitshift64Ashr(($657|0),($658|0),21)|0);
 $664 = tempRet0;
 $665 = (_i64Add(($643|0),($644|0),($503|0),($504|0))|0);
 $666 = tempRet0;
 $667 = (_i64Subtract(($665|0),($666|0),($539|0),($540|0))|0);
 $668 = tempRet0;
 $669 = (_i64Add(($667|0),($668|0),($591|0),($592|0))|0);
 $670 = tempRet0;
 $671 = (_i64Add(($669|0),($670|0),($663|0),($664|0))|0);
 $672 = tempRet0;
 $673 = (_bitshift64Shl(($663|0),($664|0),21)|0);
 $674 = tempRet0;
 $675 = (_i64Subtract(($657|0),($658|0),($673|0),($674|0))|0);
 $676 = tempRet0;
 $677 = (_bitshift64Ashr(($671|0),($672|0),21)|0);
 $678 = tempRet0;
 $679 = (_i64Add(($537|0),($538|0),($645|0),($646|0))|0);
 $680 = tempRet0;
 $681 = (_i64Subtract(($679|0),($680|0),($599|0),($600|0))|0);
 $682 = tempRet0;
 $683 = (_i64Add(($681|0),($682|0),($677|0),($678|0))|0);
 $684 = tempRet0;
 $685 = (_bitshift64Shl(($677|0),($678|0),21)|0);
 $686 = tempRet0;
 $687 = (_i64Subtract(($671|0),($672|0),($685|0),($686|0))|0);
 $688 = tempRet0;
 $689 = (_bitshift64Ashr(($683|0),($684|0),21)|0);
 $690 = tempRet0;
 $691 = (_i64Add(($647|0),($648|0),($511|0),($512|0))|0);
 $692 = tempRet0;
 $693 = (_i64Subtract(($691|0),($692|0),($551|0),($552|0))|0);
 $694 = tempRet0;
 $695 = (_i64Add(($693|0),($694|0),($597|0),($598|0))|0);
 $696 = tempRet0;
 $697 = (_i64Add(($695|0),($696|0),($689|0),($690|0))|0);
 $698 = tempRet0;
 $699 = (_bitshift64Shl(($689|0),($690|0),21)|0);
 $700 = tempRet0;
 $701 = (_i64Subtract(($683|0),($684|0),($699|0),($700|0))|0);
 $702 = tempRet0;
 $703 = (_bitshift64Ashr(($697|0),($698|0),21)|0);
 $704 = tempRet0;
 $705 = (_i64Add(($549|0),($550|0),($649|0),($650|0))|0);
 $706 = tempRet0;
 $707 = (_i64Subtract(($705|0),($706|0),($607|0),($608|0))|0);
 $708 = tempRet0;
 $709 = (_i64Add(($707|0),($708|0),($703|0),($704|0))|0);
 $710 = tempRet0;
 $711 = (_bitshift64Shl(($703|0),($704|0),21)|0);
 $712 = tempRet0;
 $713 = (_i64Subtract(($697|0),($698|0),($711|0),($712|0))|0);
 $714 = tempRet0;
 $715 = (_bitshift64Ashr(($709|0),($710|0),21)|0);
 $716 = tempRet0;
 $717 = (_i64Add(($605|0),($606|0),($715|0),($716|0))|0);
 $718 = tempRet0;
 $719 = (_bitshift64Shl(($715|0),($716|0),21)|0);
 $720 = tempRet0;
 $721 = (_i64Subtract(($709|0),($710|0),($719|0),($720|0))|0);
 $722 = tempRet0;
 $723 = (_bitshift64Ashr(($717|0),($718|0),21)|0);
 $724 = tempRet0;
 $725 = (_i64Add(($723|0),($724|0),($617|0),($618|0))|0);
 $726 = tempRet0;
 $727 = (_bitshift64Shl(($723|0),($724|0),21)|0);
 $728 = tempRet0;
 $729 = (_i64Subtract(($717|0),($718|0),($727|0),($728|0))|0);
 $730 = tempRet0;
 $731 = (_bitshift64Ashr(($725|0),($726|0),21)|0);
 $732 = tempRet0;
 $733 = (_i64Add(($613|0),($614|0),($731|0),($732|0))|0);
 $734 = tempRet0;
 $735 = (_bitshift64Shl(($731|0),($732|0),21)|0);
 $736 = tempRet0;
 $737 = (_i64Subtract(($725|0),($726|0),($735|0),($736|0))|0);
 $738 = tempRet0;
 $739 = (_bitshift64Ashr(($733|0),($734|0),21)|0);
 $740 = tempRet0;
 $741 = (_i64Add(($739|0),($740|0),($627|0),($628|0))|0);
 $742 = tempRet0;
 $743 = (_bitshift64Shl(($739|0),($740|0),21)|0);
 $744 = tempRet0;
 $745 = (_i64Subtract(($733|0),($734|0),($743|0),($744|0))|0);
 $746 = tempRet0;
 $747 = (_bitshift64Ashr(($741|0),($742|0),21)|0);
 $748 = tempRet0;
 $749 = (_i64Add(($623|0),($624|0),($747|0),($748|0))|0);
 $750 = tempRet0;
 $751 = (_bitshift64Shl(($747|0),($748|0),21)|0);
 $752 = tempRet0;
 $753 = (_i64Subtract(($741|0),($742|0),($751|0),($752|0))|0);
 $754 = tempRet0;
 $755 = (_bitshift64Ashr(($749|0),($750|0),21)|0);
 $756 = tempRet0;
 $757 = (_i64Add(($755|0),($756|0),($635|0),($636|0))|0);
 $758 = tempRet0;
 $759 = (_bitshift64Shl(($755|0),($756|0),21)|0);
 $760 = tempRet0;
 $761 = (_i64Subtract(($749|0),($750|0),($759|0),($760|0))|0);
 $762 = tempRet0;
 $763 = (_bitshift64Ashr(($757|0),($758|0),21)|0);
 $764 = tempRet0;
 $765 = (_bitshift64Shl(($763|0),($764|0),21)|0);
 $766 = tempRet0;
 $767 = (_i64Subtract(($757|0),($758|0),($765|0),($766|0))|0);
 $768 = tempRet0;
 $769 = (___muldi3(($763|0),($764|0),666643,0)|0);
 $770 = tempRet0;
 $771 = (_i64Add(($769|0),($770|0),($661|0),($662|0))|0);
 $772 = tempRet0;
 $773 = (___muldi3(($763|0),($764|0),470296,0)|0);
 $774 = tempRet0;
 $775 = (_i64Add(($675|0),($676|0),($773|0),($774|0))|0);
 $776 = tempRet0;
 $777 = (___muldi3(($763|0),($764|0),654183,0)|0);
 $778 = tempRet0;
 $779 = (_i64Add(($687|0),($688|0),($777|0),($778|0))|0);
 $780 = tempRet0;
 $781 = (___muldi3(($763|0),($764|0),-997805,-1)|0);
 $782 = tempRet0;
 $783 = (_i64Add(($701|0),($702|0),($781|0),($782|0))|0);
 $784 = tempRet0;
 $785 = (___muldi3(($763|0),($764|0),136657,0)|0);
 $786 = tempRet0;
 $787 = (_i64Add(($713|0),($714|0),($785|0),($786|0))|0);
 $788 = tempRet0;
 $789 = (___muldi3(($763|0),($764|0),-683901,-1)|0);
 $790 = tempRet0;
 $791 = (_i64Add(($721|0),($722|0),($789|0),($790|0))|0);
 $792 = tempRet0;
 $793 = (_bitshift64Ashr(($771|0),($772|0),21)|0);
 $794 = tempRet0;
 $795 = (_i64Add(($775|0),($776|0),($793|0),($794|0))|0);
 $796 = tempRet0;
 $797 = (_bitshift64Shl(($793|0),($794|0),21)|0);
 $798 = tempRet0;
 $799 = (_i64Subtract(($771|0),($772|0),($797|0),($798|0))|0);
 $800 = tempRet0;
 $801 = (_bitshift64Ashr(($795|0),($796|0),21)|0);
 $802 = tempRet0;
 $803 = (_i64Add(($779|0),($780|0),($801|0),($802|0))|0);
 $804 = tempRet0;
 $805 = (_bitshift64Shl(($801|0),($802|0),21)|0);
 $806 = tempRet0;
 $807 = (_i64Subtract(($795|0),($796|0),($805|0),($806|0))|0);
 $808 = tempRet0;
 $809 = (_bitshift64Ashr(($803|0),($804|0),21)|0);
 $810 = tempRet0;
 $811 = (_i64Add(($783|0),($784|0),($809|0),($810|0))|0);
 $812 = tempRet0;
 $813 = (_bitshift64Shl(($809|0),($810|0),21)|0);
 $814 = tempRet0;
 $815 = (_i64Subtract(($803|0),($804|0),($813|0),($814|0))|0);
 $816 = tempRet0;
 $817 = (_bitshift64Ashr(($811|0),($812|0),21)|0);
 $818 = tempRet0;
 $819 = (_i64Add(($787|0),($788|0),($817|0),($818|0))|0);
 $820 = tempRet0;
 $821 = (_bitshift64Shl(($817|0),($818|0),21)|0);
 $822 = tempRet0;
 $823 = (_i64Subtract(($811|0),($812|0),($821|0),($822|0))|0);
 $824 = tempRet0;
 $825 = (_bitshift64Ashr(($819|0),($820|0),21)|0);
 $826 = tempRet0;
 $827 = (_i64Add(($791|0),($792|0),($825|0),($826|0))|0);
 $828 = tempRet0;
 $829 = (_bitshift64Shl(($825|0),($826|0),21)|0);
 $830 = tempRet0;
 $831 = (_i64Subtract(($819|0),($820|0),($829|0),($830|0))|0);
 $832 = tempRet0;
 $833 = (_bitshift64Ashr(($827|0),($828|0),21)|0);
 $834 = tempRet0;
 $835 = (_i64Add(($833|0),($834|0),($729|0),($730|0))|0);
 $836 = tempRet0;
 $837 = (_bitshift64Shl(($833|0),($834|0),21)|0);
 $838 = tempRet0;
 $839 = (_i64Subtract(($827|0),($828|0),($837|0),($838|0))|0);
 $840 = tempRet0;
 $841 = (_bitshift64Ashr(($835|0),($836|0),21)|0);
 $842 = tempRet0;
 $843 = (_i64Add(($841|0),($842|0),($737|0),($738|0))|0);
 $844 = tempRet0;
 $845 = (_bitshift64Shl(($841|0),($842|0),21)|0);
 $846 = tempRet0;
 $847 = (_i64Subtract(($835|0),($836|0),($845|0),($846|0))|0);
 $848 = tempRet0;
 $849 = (_bitshift64Ashr(($843|0),($844|0),21)|0);
 $850 = tempRet0;
 $851 = (_i64Add(($849|0),($850|0),($745|0),($746|0))|0);
 $852 = tempRet0;
 $853 = (_bitshift64Shl(($849|0),($850|0),21)|0);
 $854 = tempRet0;
 $855 = (_i64Subtract(($843|0),($844|0),($853|0),($854|0))|0);
 $856 = tempRet0;
 $857 = (_bitshift64Ashr(($851|0),($852|0),21)|0);
 $858 = tempRet0;
 $859 = (_i64Add(($857|0),($858|0),($753|0),($754|0))|0);
 $860 = tempRet0;
 $861 = (_bitshift64Shl(($857|0),($858|0),21)|0);
 $862 = tempRet0;
 $863 = (_i64Subtract(($851|0),($852|0),($861|0),($862|0))|0);
 $864 = tempRet0;
 $865 = (_bitshift64Ashr(($859|0),($860|0),21)|0);
 $866 = tempRet0;
 $867 = (_i64Add(($865|0),($866|0),($761|0),($762|0))|0);
 $868 = tempRet0;
 $869 = (_bitshift64Shl(($865|0),($866|0),21)|0);
 $870 = tempRet0;
 $871 = (_i64Subtract(($859|0),($860|0),($869|0),($870|0))|0);
 $872 = tempRet0;
 $873 = (_bitshift64Ashr(($867|0),($868|0),21)|0);
 $874 = tempRet0;
 $875 = (_i64Add(($873|0),($874|0),($767|0),($768|0))|0);
 $876 = tempRet0;
 $877 = (_bitshift64Shl(($873|0),($874|0),21)|0);
 $878 = tempRet0;
 $879 = (_i64Subtract(($867|0),($868|0),($877|0),($878|0))|0);
 $880 = tempRet0;
 $881 = $799&255;
 HEAP8[$0>>0] = $881;
 $882 = (_bitshift64Lshr(($799|0),($800|0),8)|0);
 $883 = tempRet0;
 $884 = $882&255;
 $885 = ((($0)) + 1|0);
 HEAP8[$885>>0] = $884;
 $886 = (_bitshift64Lshr(($799|0),($800|0),16)|0);
 $887 = tempRet0;
 $888 = (_bitshift64Shl(($807|0),($808|0),5)|0);
 $889 = tempRet0;
 $890 = $888 | $886;
 $889 | $887;
 $891 = $890&255;
 HEAP8[$4>>0] = $891;
 $892 = (_bitshift64Lshr(($807|0),($808|0),3)|0);
 $893 = tempRet0;
 $894 = $892&255;
 $895 = ((($0)) + 3|0);
 HEAP8[$895>>0] = $894;
 $896 = (_bitshift64Lshr(($807|0),($808|0),11)|0);
 $897 = tempRet0;
 $898 = $896&255;
 $899 = ((($0)) + 4|0);
 HEAP8[$899>>0] = $898;
 $900 = (_bitshift64Lshr(($807|0),($808|0),19)|0);
 $901 = tempRet0;
 $902 = (_bitshift64Shl(($815|0),($816|0),2)|0);
 $903 = tempRet0;
 $904 = $902 | $900;
 $903 | $901;
 $905 = $904&255;
 HEAP8[$10>>0] = $905;
 $906 = (_bitshift64Lshr(($815|0),($816|0),6)|0);
 $907 = tempRet0;
 $908 = $906&255;
 $909 = ((($0)) + 6|0);
 HEAP8[$909>>0] = $908;
 $910 = (_bitshift64Lshr(($815|0),($816|0),14)|0);
 $911 = tempRet0;
 $912 = (_bitshift64Shl(($823|0),($824|0),7)|0);
 $913 = tempRet0;
 $914 = $912 | $910;
 $913 | $911;
 $915 = $914&255;
 HEAP8[$16>>0] = $915;
 $916 = (_bitshift64Lshr(($823|0),($824|0),1)|0);
 $917 = tempRet0;
 $918 = $916&255;
 $919 = ((($0)) + 8|0);
 HEAP8[$919>>0] = $918;
 $920 = (_bitshift64Lshr(($823|0),($824|0),9)|0);
 $921 = tempRet0;
 $922 = $920&255;
 $923 = ((($0)) + 9|0);
 HEAP8[$923>>0] = $922;
 $924 = (_bitshift64Lshr(($823|0),($824|0),17)|0);
 $925 = tempRet0;
 $926 = (_bitshift64Shl(($831|0),($832|0),4)|0);
 $927 = tempRet0;
 $928 = $926 | $924;
 $927 | $925;
 $929 = $928&255;
 HEAP8[$22>>0] = $929;
 $930 = (_bitshift64Lshr(($831|0),($832|0),4)|0);
 $931 = tempRet0;
 $932 = $930&255;
 $933 = ((($0)) + 11|0);
 HEAP8[$933>>0] = $932;
 $934 = (_bitshift64Lshr(($831|0),($832|0),12)|0);
 $935 = tempRet0;
 $936 = $934&255;
 $937 = ((($0)) + 12|0);
 HEAP8[$937>>0] = $936;
 $938 = (_bitshift64Lshr(($831|0),($832|0),20)|0);
 $939 = tempRet0;
 $940 = (_bitshift64Shl(($839|0),($840|0),1)|0);
 $941 = tempRet0;
 $942 = $940 | $938;
 $941 | $939;
 $943 = $942&255;
 HEAP8[$28>>0] = $943;
 $944 = (_bitshift64Lshr(($839|0),($840|0),7)|0);
 $945 = tempRet0;
 $946 = $944&255;
 $947 = ((($0)) + 14|0);
 HEAP8[$947>>0] = $946;
 $948 = (_bitshift64Lshr(($839|0),($840|0),15)|0);
 $949 = tempRet0;
 $950 = (_bitshift64Shl(($847|0),($848|0),6)|0);
 $951 = tempRet0;
 $952 = $950 | $948;
 $951 | $949;
 $953 = $952&255;
 HEAP8[$34>>0] = $953;
 $954 = (_bitshift64Lshr(($847|0),($848|0),2)|0);
 $955 = tempRet0;
 $956 = $954&255;
 $957 = ((($0)) + 16|0);
 HEAP8[$957>>0] = $956;
 $958 = (_bitshift64Lshr(($847|0),($848|0),10)|0);
 $959 = tempRet0;
 $960 = $958&255;
 $961 = ((($0)) + 17|0);
 HEAP8[$961>>0] = $960;
 $962 = (_bitshift64Lshr(($847|0),($848|0),18)|0);
 $963 = tempRet0;
 $964 = (_bitshift64Shl(($855|0),($856|0),3)|0);
 $965 = tempRet0;
 $966 = $964 | $962;
 $965 | $963;
 $967 = $966&255;
 HEAP8[$40>>0] = $967;
 $968 = (_bitshift64Lshr(($855|0),($856|0),5)|0);
 $969 = tempRet0;
 $970 = $968&255;
 $971 = ((($0)) + 19|0);
 HEAP8[$971>>0] = $970;
 $972 = (_bitshift64Lshr(($855|0),($856|0),13)|0);
 $973 = tempRet0;
 $974 = $972&255;
 $975 = ((($0)) + 20|0);
 HEAP8[$975>>0] = $974;
 $976 = $863&255;
 HEAP8[$46>>0] = $976;
 $977 = (_bitshift64Lshr(($863|0),($864|0),8)|0);
 $978 = tempRet0;
 $979 = $977&255;
 $980 = ((($0)) + 22|0);
 HEAP8[$980>>0] = $979;
 $981 = (_bitshift64Lshr(($863|0),($864|0),16)|0);
 $982 = tempRet0;
 $983 = (_bitshift64Shl(($871|0),($872|0),5)|0);
 $984 = tempRet0;
 $985 = $983 | $981;
 $984 | $982;
 $986 = $985&255;
 HEAP8[$50>>0] = $986;
 $987 = (_bitshift64Lshr(($871|0),($872|0),3)|0);
 $988 = tempRet0;
 $989 = $987&255;
 $990 = ((($0)) + 24|0);
 HEAP8[$990>>0] = $989;
 $991 = (_bitshift64Lshr(($871|0),($872|0),11)|0);
 $992 = tempRet0;
 $993 = $991&255;
 $994 = ((($0)) + 25|0);
 HEAP8[$994>>0] = $993;
 $995 = (_bitshift64Lshr(($871|0),($872|0),19)|0);
 $996 = tempRet0;
 $997 = (_bitshift64Shl(($879|0),($880|0),2)|0);
 $998 = tempRet0;
 $999 = $997 | $995;
 $998 | $996;
 $1000 = $999&255;
 HEAP8[$56>>0] = $1000;
 $1001 = (_bitshift64Lshr(($879|0),($880|0),6)|0);
 $1002 = tempRet0;
 $1003 = $1001&255;
 $1004 = ((($0)) + 27|0);
 HEAP8[$1004>>0] = $1003;
 $1005 = (_bitshift64Lshr(($879|0),($880|0),14)|0);
 $1006 = tempRet0;
 $1007 = (_bitshift64Shl(($875|0),($876|0),7)|0);
 $1008 = tempRet0;
 $1009 = $1005 | $1007;
 $1006 | $1008;
 $1010 = $1009&255;
 HEAP8[$62>>0] = $1010;
 $1011 = (_bitshift64Lshr(($875|0),($876|0),1)|0);
 $1012 = tempRet0;
 $1013 = $1011&255;
 $1014 = ((($0)) + 29|0);
 HEAP8[$1014>>0] = $1013;
 $1015 = (_bitshift64Lshr(($875|0),($876|0),9)|0);
 $1016 = tempRet0;
 $1017 = $1015&255;
 $1018 = ((($0)) + 30|0);
 HEAP8[$1018>>0] = $1017;
 $1019 = (_bitshift64Lshr(($875|0),($876|0),17)|0);
 $1020 = tempRet0;
 $1021 = $1019&255;
 HEAP8[$68>>0] = $1021;
 return;
}
function _load_3_51($0) {
 $0 = $0|0;
 var $1 = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $1 = HEAP8[$0>>0]|0;
 $2 = $1&255;
 $3 = ((($0)) + 1|0);
 $4 = HEAP8[$3>>0]|0;
 $5 = $4&255;
 $6 = (_bitshift64Shl(($5|0),0,8)|0);
 $7 = tempRet0;
 $8 = $6 | $2;
 $9 = ((($0)) + 2|0);
 $10 = HEAP8[$9>>0]|0;
 $11 = $10&255;
 $12 = (_bitshift64Shl(($11|0),0,16)|0);
 $13 = tempRet0;
 $14 = $8 | $12;
 $15 = $7 | $13;
 tempRet0 = ($15);
 return ($14|0);
}
function _load_4_52($0) {
 $0 = $0|0;
 var $1 = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $2 = 0, $20 = 0, $21 = 0, $22 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0;
 var $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $1 = HEAP8[$0>>0]|0;
 $2 = $1&255;
 $3 = ((($0)) + 1|0);
 $4 = HEAP8[$3>>0]|0;
 $5 = $4&255;
 $6 = (_bitshift64Shl(($5|0),0,8)|0);
 $7 = tempRet0;
 $8 = $6 | $2;
 $9 = ((($0)) + 2|0);
 $10 = HEAP8[$9>>0]|0;
 $11 = $10&255;
 $12 = (_bitshift64Shl(($11|0),0,16)|0);
 $13 = tempRet0;
 $14 = $8 | $12;
 $15 = $7 | $13;
 $16 = ((($0)) + 3|0);
 $17 = HEAP8[$16>>0]|0;
 $18 = $17&255;
 $19 = (_bitshift64Shl(($18|0),0,24)|0);
 $20 = tempRet0;
 $21 = $14 | $19;
 $22 = $15 | $20;
 tempRet0 = ($22);
 return ($21|0);
}
function _sph_sha512_init($0) {
 $0 = $0|0;
 var $1 = 0, $2 = 0, $3 = 0, $4 = 0, $5 = 0, $6 = 0, dest = 0, label = 0, sp = 0, src = 0, stop = 0;
 sp = STACKTOP;
 $1 = ((($0)) + 128|0);
 dest=$1; src=8; stop=dest+64|0; do { HEAP32[dest>>2]=HEAP32[src>>2]|0; dest=dest+4|0; src=src+4|0; } while ((dest|0) < (stop|0));
 $2 = ((($0)) + 192|0);
 $3 = $2;
 $4 = $3;
 HEAP32[$4>>2] = 0;
 $5 = (($3) + 4)|0;
 $6 = $5;
 HEAP32[$6>>2] = 0;
 return;
}
function _sph_sha384($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var $$02631 = 0, $$02730 = 0, $$028$ = 0, $$02829 = 0, $$1 = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0;
 var $25 = 0, $26 = 0, $27 = 0, $28 = 0, $29 = 0, $3 = 0, $30 = 0, $31 = 0, $32 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $3 = ((($0)) + 192|0);
 $4 = ($2|0)==(0);
 if ($4) {
  return;
 }
 $5 = $3;
 $6 = $5;
 $7 = HEAP32[$6>>2]|0;
 $8 = (($5) + 4)|0;
 $9 = $8;
 $10 = HEAP32[$9>>2]|0;
 $11 = $7 & 127;
 $12 = ((($0)) + 128|0);
 $$02631 = $11;$$02730 = $1;$$02829 = $2;
 while(1) {
  $13 = (128 - ($$02631))|0;
  $14 = ($13>>>0)>($$02829>>>0);
  $$028$ = $14 ? $$02829 : $13;
  $15 = (($0) + ($$02631)|0);
  _memcpy(($15|0),($$02730|0),($$028$|0))|0;
  $16 = (($$02730) + ($$028$)|0);
  $17 = (($$028$) + ($$02631))|0;
  $18 = (($$02829) - ($$028$))|0;
  $19 = ($17|0)==(128);
  if ($19) {
   _sha3_round($0,$12);
   $$1 = 0;
  } else {
   $$1 = $17;
  }
  $20 = $3;
  $21 = $20;
  $22 = HEAP32[$21>>2]|0;
  $23 = (($20) + 4)|0;
  $24 = $23;
  $25 = HEAP32[$24>>2]|0;
  $26 = (_i64Add(($22|0),($25|0),($$028$|0),0)|0);
  $27 = tempRet0;
  $28 = $3;
  $29 = $28;
  HEAP32[$29>>2] = $26;
  $30 = (($28) + 4)|0;
  $31 = $30;
  HEAP32[$31>>2] = $27;
  $32 = ($18|0)==(0);
  if ($32) {
   break;
  } else {
   $$02631 = $$1;$$02730 = $16;$$02829 = $18;
  }
 }
 return;
}
function _sha3_round($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var $$0344 = 0, $$1343 = 0, $$2342 = 0, $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0, $113 = 0, $114 = 0;
 var $115 = 0, $116 = 0, $117 = 0, $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0;
 var $133 = 0, $134 = 0, $135 = 0, $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0, $15 = 0, $150 = 0;
 var $151 = 0, $152 = 0, $153 = 0, $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $159 = 0, $16 = 0, $160 = 0, $161 = 0, $162 = 0, $163 = 0, $164 = 0, $165 = 0, $166 = 0, $167 = 0, $168 = 0, $169 = 0;
 var $17 = 0, $170 = 0, $171 = 0, $172 = 0, $173 = 0, $174 = 0, $175 = 0, $176 = 0, $177 = 0, $178 = 0, $179 = 0, $18 = 0, $180 = 0, $181 = 0, $182 = 0, $183 = 0, $184 = 0, $185 = 0, $186 = 0, $187 = 0;
 var $188 = 0, $189 = 0, $19 = 0, $190 = 0, $191 = 0, $192 = 0, $193 = 0, $194 = 0, $195 = 0, $196 = 0, $197 = 0, $198 = 0, $199 = 0, $2 = 0, $20 = 0, $200 = 0, $201 = 0, $202 = 0, $203 = 0, $204 = 0;
 var $205 = 0, $206 = 0, $207 = 0, $208 = 0, $209 = 0, $21 = 0, $210 = 0, $211 = 0, $212 = 0, $213 = 0, $214 = 0, $215 = 0, $216 = 0, $217 = 0, $218 = 0, $219 = 0, $22 = 0, $220 = 0, $221 = 0, $222 = 0;
 var $223 = 0, $224 = 0, $225 = 0, $226 = 0, $227 = 0, $228 = 0, $229 = 0, $23 = 0, $230 = 0, $231 = 0, $232 = 0, $233 = 0, $234 = 0, $235 = 0, $236 = 0, $237 = 0, $238 = 0, $239 = 0, $24 = 0, $240 = 0;
 var $241 = 0, $242 = 0, $243 = 0, $244 = 0, $245 = 0, $246 = 0, $247 = 0, $248 = 0, $249 = 0, $25 = 0, $250 = 0, $251 = 0, $252 = 0, $253 = 0, $254 = 0, $255 = 0, $256 = 0, $257 = 0, $258 = 0, $259 = 0;
 var $26 = 0, $260 = 0, $261 = 0, $262 = 0, $263 = 0, $264 = 0, $265 = 0, $266 = 0, $267 = 0, $268 = 0, $269 = 0, $27 = 0, $270 = 0, $271 = 0, $272 = 0, $273 = 0, $274 = 0, $275 = 0, $276 = 0, $277 = 0;
 var $278 = 0, $279 = 0, $28 = 0, $280 = 0, $281 = 0, $282 = 0, $283 = 0, $284 = 0, $285 = 0, $286 = 0, $287 = 0, $288 = 0, $289 = 0, $29 = 0, $290 = 0, $291 = 0, $292 = 0, $293 = 0, $294 = 0, $295 = 0;
 var $296 = 0, $297 = 0, $298 = 0, $299 = 0, $3 = 0, $30 = 0, $300 = 0, $301 = 0, $302 = 0, $303 = 0, $304 = 0, $305 = 0, $306 = 0, $307 = 0, $308 = 0, $309 = 0, $31 = 0, $310 = 0, $311 = 0, $312 = 0;
 var $313 = 0, $314 = 0, $315 = 0, $316 = 0, $317 = 0, $318 = 0, $319 = 0, $32 = 0, $320 = 0, $321 = 0, $322 = 0, $323 = 0, $324 = 0, $325 = 0, $326 = 0, $327 = 0, $328 = 0, $329 = 0, $33 = 0, $330 = 0;
 var $331 = 0, $332 = 0, $333 = 0, $334 = 0, $335 = 0, $336 = 0, $337 = 0, $338 = 0, $339 = 0, $34 = 0, $340 = 0, $341 = 0, $342 = 0, $343 = 0, $344 = 0, $345 = 0, $346 = 0, $347 = 0, $348 = 0, $349 = 0;
 var $35 = 0, $350 = 0, $351 = 0, $352 = 0, $353 = 0, $354 = 0, $355 = 0, $356 = 0, $357 = 0, $358 = 0, $359 = 0, $36 = 0, $360 = 0, $361 = 0, $362 = 0, $363 = 0, $364 = 0, $365 = 0, $366 = 0, $367 = 0;
 var $368 = 0, $369 = 0, $37 = 0, $370 = 0, $371 = 0, $372 = 0, $373 = 0, $374 = 0, $375 = 0, $376 = 0, $377 = 0, $378 = 0, $379 = 0, $38 = 0, $380 = 0, $381 = 0, $382 = 0, $383 = 0, $384 = 0, $385 = 0;
 var $386 = 0, $387 = 0, $388 = 0, $389 = 0, $39 = 0, $390 = 0, $391 = 0, $392 = 0, $393 = 0, $394 = 0, $395 = 0, $396 = 0, $397 = 0, $398 = 0, $399 = 0, $4 = 0, $40 = 0, $400 = 0, $401 = 0, $402 = 0;
 var $403 = 0, $404 = 0, $405 = 0, $406 = 0, $407 = 0, $408 = 0, $409 = 0, $41 = 0, $410 = 0, $411 = 0, $412 = 0, $413 = 0, $414 = 0, $415 = 0, $416 = 0, $417 = 0, $418 = 0, $419 = 0, $42 = 0, $420 = 0;
 var $421 = 0, $422 = 0, $423 = 0, $424 = 0, $425 = 0, $426 = 0, $427 = 0, $428 = 0, $429 = 0, $43 = 0, $430 = 0, $431 = 0, $432 = 0, $433 = 0, $434 = 0, $435 = 0, $436 = 0, $437 = 0, $438 = 0, $439 = 0;
 var $44 = 0, $440 = 0, $441 = 0, $442 = 0, $443 = 0, $444 = 0, $445 = 0, $446 = 0, $447 = 0, $448 = 0, $449 = 0, $45 = 0, $450 = 0, $451 = 0, $452 = 0, $453 = 0, $454 = 0, $455 = 0, $456 = 0, $457 = 0;
 var $458 = 0, $459 = 0, $46 = 0, $460 = 0, $461 = 0, $462 = 0, $463 = 0, $464 = 0, $465 = 0, $466 = 0, $467 = 0, $468 = 0, $469 = 0, $47 = 0, $470 = 0, $471 = 0, $472 = 0, $473 = 0, $474 = 0, $475 = 0;
 var $476 = 0, $477 = 0, $478 = 0, $479 = 0, $48 = 0, $480 = 0, $481 = 0, $482 = 0, $483 = 0, $484 = 0, $485 = 0, $486 = 0, $487 = 0, $488 = 0, $489 = 0, $49 = 0, $490 = 0, $491 = 0, $492 = 0, $493 = 0;
 var $494 = 0, $495 = 0, $496 = 0, $497 = 0, $498 = 0, $499 = 0, $5 = 0, $50 = 0, $500 = 0, $501 = 0, $502 = 0, $503 = 0, $504 = 0, $505 = 0, $506 = 0, $507 = 0, $508 = 0, $509 = 0, $51 = 0, $510 = 0;
 var $511 = 0, $512 = 0, $513 = 0, $514 = 0, $515 = 0, $516 = 0, $517 = 0, $518 = 0, $519 = 0, $52 = 0, $520 = 0, $521 = 0, $522 = 0, $523 = 0, $524 = 0, $525 = 0, $526 = 0, $527 = 0, $528 = 0, $529 = 0;
 var $53 = 0, $530 = 0, $531 = 0, $532 = 0, $533 = 0, $534 = 0, $535 = 0, $536 = 0, $537 = 0, $538 = 0, $539 = 0, $54 = 0, $540 = 0, $541 = 0, $542 = 0, $543 = 0, $544 = 0, $545 = 0, $546 = 0, $547 = 0;
 var $548 = 0, $549 = 0, $55 = 0, $550 = 0, $551 = 0, $552 = 0, $553 = 0, $554 = 0, $555 = 0, $556 = 0, $557 = 0, $558 = 0, $559 = 0, $56 = 0, $560 = 0, $561 = 0, $562 = 0, $563 = 0, $564 = 0, $565 = 0;
 var $566 = 0, $567 = 0, $568 = 0, $569 = 0, $57 = 0, $570 = 0, $571 = 0, $572 = 0, $573 = 0, $574 = 0, $575 = 0, $576 = 0, $577 = 0, $578 = 0, $579 = 0, $58 = 0, $580 = 0, $581 = 0, $582 = 0, $583 = 0;
 var $584 = 0, $585 = 0, $586 = 0, $587 = 0, $588 = 0, $589 = 0, $59 = 0, $590 = 0, $591 = 0, $592 = 0, $593 = 0, $594 = 0, $595 = 0, $596 = 0, $597 = 0, $598 = 0, $599 = 0, $6 = 0, $60 = 0, $600 = 0;
 var $601 = 0, $602 = 0, $603 = 0, $604 = 0, $605 = 0, $606 = 0, $607 = 0, $608 = 0, $609 = 0, $61 = 0, $610 = 0, $611 = 0, $612 = 0, $613 = 0, $614 = 0, $615 = 0, $616 = 0, $617 = 0, $618 = 0, $619 = 0;
 var $62 = 0, $620 = 0, $621 = 0, $622 = 0, $623 = 0, $624 = 0, $625 = 0, $626 = 0, $627 = 0, $628 = 0, $629 = 0, $63 = 0, $630 = 0, $631 = 0, $632 = 0, $633 = 0, $634 = 0, $635 = 0, $636 = 0, $637 = 0;
 var $638 = 0, $639 = 0, $64 = 0, $640 = 0, $641 = 0, $642 = 0, $643 = 0, $644 = 0, $645 = 0, $646 = 0, $647 = 0, $648 = 0, $649 = 0, $65 = 0, $650 = 0, $651 = 0, $652 = 0, $653 = 0, $654 = 0, $655 = 0;
 var $656 = 0, $657 = 0, $658 = 0, $659 = 0, $66 = 0, $660 = 0, $661 = 0, $662 = 0, $663 = 0, $664 = 0, $665 = 0, $666 = 0, $667 = 0, $668 = 0, $669 = 0, $67 = 0, $670 = 0, $671 = 0, $672 = 0, $673 = 0;
 var $674 = 0, $675 = 0, $676 = 0, $677 = 0, $678 = 0, $679 = 0, $68 = 0, $680 = 0, $681 = 0, $682 = 0, $683 = 0, $684 = 0, $685 = 0, $686 = 0, $687 = 0, $688 = 0, $689 = 0, $69 = 0, $690 = 0, $691 = 0;
 var $692 = 0, $693 = 0, $694 = 0, $695 = 0, $696 = 0, $697 = 0, $698 = 0, $699 = 0, $7 = 0, $70 = 0, $700 = 0, $701 = 0, $702 = 0, $703 = 0, $704 = 0, $705 = 0, $706 = 0, $707 = 0, $708 = 0, $709 = 0;
 var $71 = 0, $710 = 0, $711 = 0, $712 = 0, $713 = 0, $714 = 0, $715 = 0, $716 = 0, $717 = 0, $718 = 0, $719 = 0, $72 = 0, $720 = 0, $721 = 0, $722 = 0, $723 = 0, $724 = 0, $725 = 0, $726 = 0, $727 = 0;
 var $728 = 0, $729 = 0, $73 = 0, $730 = 0, $731 = 0, $732 = 0, $733 = 0, $734 = 0, $735 = 0, $736 = 0, $737 = 0, $738 = 0, $739 = 0, $74 = 0, $740 = 0, $741 = 0, $742 = 0, $743 = 0, $744 = 0, $745 = 0;
 var $746 = 0, $747 = 0, $748 = 0, $749 = 0, $75 = 0, $750 = 0, $751 = 0, $752 = 0, $753 = 0, $754 = 0, $755 = 0, $756 = 0, $757 = 0, $758 = 0, $759 = 0, $76 = 0, $760 = 0, $761 = 0, $762 = 0, $763 = 0;
 var $764 = 0, $765 = 0, $766 = 0, $767 = 0, $768 = 0, $769 = 0, $77 = 0, $770 = 0, $771 = 0, $772 = 0, $773 = 0, $774 = 0, $775 = 0, $776 = 0, $777 = 0, $778 = 0, $779 = 0, $78 = 0, $780 = 0, $781 = 0;
 var $782 = 0, $783 = 0, $784 = 0, $785 = 0, $786 = 0, $787 = 0, $788 = 0, $789 = 0, $79 = 0, $790 = 0, $791 = 0, $792 = 0, $793 = 0, $794 = 0, $795 = 0, $796 = 0, $797 = 0, $798 = 0, $799 = 0, $8 = 0;
 var $80 = 0, $800 = 0, $801 = 0, $802 = 0, $803 = 0, $804 = 0, $805 = 0, $806 = 0, $807 = 0, $808 = 0, $809 = 0, $81 = 0, $810 = 0, $811 = 0, $812 = 0, $813 = 0, $814 = 0, $815 = 0, $816 = 0, $817 = 0;
 var $818 = 0, $819 = 0, $82 = 0, $820 = 0, $821 = 0, $822 = 0, $823 = 0, $824 = 0, $825 = 0, $826 = 0, $827 = 0, $828 = 0, $829 = 0, $83 = 0, $830 = 0, $831 = 0, $832 = 0, $833 = 0, $834 = 0, $835 = 0;
 var $836 = 0, $837 = 0, $838 = 0, $839 = 0, $84 = 0, $840 = 0, $841 = 0, $842 = 0, $843 = 0, $844 = 0, $845 = 0, $846 = 0, $847 = 0, $848 = 0, $849 = 0, $85 = 0, $850 = 0, $851 = 0, $852 = 0, $853 = 0;
 var $854 = 0, $855 = 0, $856 = 0, $857 = 0, $858 = 0, $859 = 0, $86 = 0, $860 = 0, $861 = 0, $862 = 0, $863 = 0, $864 = 0, $865 = 0, $866 = 0, $867 = 0, $868 = 0, $869 = 0, $87 = 0, $870 = 0, $871 = 0;
 var $872 = 0, $873 = 0, $874 = 0, $875 = 0, $876 = 0, $877 = 0, $878 = 0, $879 = 0, $88 = 0, $880 = 0, $881 = 0, $882 = 0, $883 = 0, $884 = 0, $885 = 0, $886 = 0, $887 = 0, $888 = 0, $889 = 0, $89 = 0;
 var $890 = 0, $891 = 0, $892 = 0, $893 = 0, $894 = 0, $895 = 0, $896 = 0, $897 = 0, $898 = 0, $899 = 0, $9 = 0, $90 = 0, $900 = 0, $901 = 0, $902 = 0, $903 = 0, $904 = 0, $905 = 0, $906 = 0, $907 = 0;
 var $908 = 0, $909 = 0, $91 = 0, $910 = 0, $911 = 0, $912 = 0, $913 = 0, $914 = 0, $915 = 0, $916 = 0, $917 = 0, $918 = 0, $919 = 0, $92 = 0, $920 = 0, $921 = 0, $922 = 0, $923 = 0, $924 = 0, $925 = 0;
 var $926 = 0, $927 = 0, $928 = 0, $929 = 0, $93 = 0, $930 = 0, $931 = 0, $932 = 0, $933 = 0, $934 = 0, $935 = 0, $936 = 0, $937 = 0, $938 = 0, $939 = 0, $94 = 0, $940 = 0, $941 = 0, $942 = 0, $943 = 0;
 var $944 = 0, $945 = 0, $946 = 0, $947 = 0, $948 = 0, $949 = 0, $95 = 0, $950 = 0, $951 = 0, $952 = 0, $953 = 0, $954 = 0, $955 = 0, $956 = 0, $96 = 0, $97 = 0, $98 = 0, $99 = 0, $exitcond = 0, $exitcond352 = 0;
 var label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 640|0;
 $2 = sp;
 $$0344 = 0;
 while(1) {
  $3 = $$0344 << 3;
  $4 = (($0) + ($3)|0);
  $5 = (_sph_dec64be_aligned($4)|0);
  $6 = tempRet0;
  $7 = (($2) + ($$0344<<3)|0);
  $8 = $7;
  $9 = $8;
  HEAP32[$9>>2] = $5;
  $10 = (($8) + 4)|0;
  $11 = $10;
  HEAP32[$11>>2] = $6;
  $12 = (($$0344) + 1)|0;
  $exitcond352 = ($12|0)==(16);
  if ($exitcond352) {
   $$1343 = 16;
   break;
  } else {
   $$0344 = $12;
  }
 }
 while(1) {
  $13 = (($$1343) + -2)|0;
  $14 = (($2) + ($13<<3)|0);
  $15 = $14;
  $16 = $15;
  $17 = HEAP32[$16>>2]|0;
  $18 = (($15) + 4)|0;
  $19 = $18;
  $20 = HEAP32[$19>>2]|0;
  $21 = (_bitshift64Shl(($17|0),($20|0),45)|0);
  $22 = tempRet0;
  $23 = (_bitshift64Lshr(($17|0),($20|0),19)|0);
  $24 = tempRet0;
  $25 = $21 | $23;
  $26 = $22 | $24;
  $27 = (_bitshift64Shl(($17|0),($20|0),3)|0);
  $28 = tempRet0;
  $29 = (_bitshift64Lshr(($17|0),($20|0),61)|0);
  $30 = tempRet0;
  $31 = $27 | $29;
  $32 = $28 | $30;
  $33 = (_bitshift64Lshr(($17|0),($20|0),6)|0);
  $34 = tempRet0;
  $35 = $31 ^ $33;
  $36 = $32 ^ $34;
  $37 = $35 ^ $25;
  $38 = $36 ^ $26;
  $39 = (($$1343) + -7)|0;
  $40 = (($2) + ($39<<3)|0);
  $41 = $40;
  $42 = $41;
  $43 = HEAP32[$42>>2]|0;
  $44 = (($41) + 4)|0;
  $45 = $44;
  $46 = HEAP32[$45>>2]|0;
  $47 = (($$1343) + -15)|0;
  $48 = (($2) + ($47<<3)|0);
  $49 = $48;
  $50 = $49;
  $51 = HEAP32[$50>>2]|0;
  $52 = (($49) + 4)|0;
  $53 = $52;
  $54 = HEAP32[$53>>2]|0;
  $55 = (_bitshift64Shl(($51|0),($54|0),63)|0);
  $56 = tempRet0;
  $57 = (_bitshift64Lshr(($51|0),($54|0),1)|0);
  $58 = tempRet0;
  $59 = $55 | $57;
  $60 = $56 | $58;
  $61 = (_bitshift64Shl(($51|0),($54|0),56)|0);
  $62 = tempRet0;
  $63 = (_bitshift64Lshr(($51|0),($54|0),8)|0);
  $64 = tempRet0;
  $65 = $61 | $63;
  $66 = $62 | $64;
  $67 = (_bitshift64Lshr(($51|0),($54|0),7)|0);
  $68 = tempRet0;
  $69 = $65 ^ $67;
  $70 = $66 ^ $68;
  $71 = $69 ^ $59;
  $72 = $70 ^ $60;
  $73 = (($$1343) + -16)|0;
  $74 = (($2) + ($73<<3)|0);
  $75 = $74;
  $76 = $75;
  $77 = HEAP32[$76>>2]|0;
  $78 = (($75) + 4)|0;
  $79 = $78;
  $80 = HEAP32[$79>>2]|0;
  $81 = (_i64Add(($77|0),($80|0),($43|0),($46|0))|0);
  $82 = tempRet0;
  $83 = (_i64Add(($81|0),($82|0),($37|0),($38|0))|0);
  $84 = tempRet0;
  $85 = (_i64Add(($83|0),($84|0),($71|0),($72|0))|0);
  $86 = tempRet0;
  $87 = (($2) + ($$1343<<3)|0);
  $88 = $87;
  $89 = $88;
  HEAP32[$89>>2] = $85;
  $90 = (($88) + 4)|0;
  $91 = $90;
  HEAP32[$91>>2] = $86;
  $92 = (($$1343) + 1)|0;
  $exitcond = ($92|0)==(80);
  if ($exitcond) {
   break;
  } else {
   $$1343 = $92;
  }
 }
 $93 = $1;
 $94 = $93;
 $95 = HEAP32[$94>>2]|0;
 $96 = (($93) + 4)|0;
 $97 = $96;
 $98 = HEAP32[$97>>2]|0;
 $99 = ((($1)) + 8|0);
 $100 = $99;
 $101 = $100;
 $102 = HEAP32[$101>>2]|0;
 $103 = (($100) + 4)|0;
 $104 = $103;
 $105 = HEAP32[$104>>2]|0;
 $106 = ((($1)) + 16|0);
 $107 = $106;
 $108 = $107;
 $109 = HEAP32[$108>>2]|0;
 $110 = (($107) + 4)|0;
 $111 = $110;
 $112 = HEAP32[$111>>2]|0;
 $113 = ((($1)) + 24|0);
 $114 = $113;
 $115 = $114;
 $116 = HEAP32[$115>>2]|0;
 $117 = (($114) + 4)|0;
 $118 = $117;
 $119 = HEAP32[$118>>2]|0;
 $120 = ((($1)) + 32|0);
 $121 = $120;
 $122 = $121;
 $123 = HEAP32[$122>>2]|0;
 $124 = (($121) + 4)|0;
 $125 = $124;
 $126 = HEAP32[$125>>2]|0;
 $127 = ((($1)) + 40|0);
 $128 = $127;
 $129 = $128;
 $130 = HEAP32[$129>>2]|0;
 $131 = (($128) + 4)|0;
 $132 = $131;
 $133 = HEAP32[$132>>2]|0;
 $134 = ((($1)) + 48|0);
 $135 = $134;
 $136 = $135;
 $137 = HEAP32[$136>>2]|0;
 $138 = (($135) + 4)|0;
 $139 = $138;
 $140 = HEAP32[$139>>2]|0;
 $141 = ((($1)) + 56|0);
 $142 = $141;
 $143 = $142;
 $144 = HEAP32[$143>>2]|0;
 $145 = (($142) + 4)|0;
 $146 = $145;
 $147 = HEAP32[$146>>2]|0;
 $$2342 = 0;$148 = $123;$149 = $126;$173 = $137;$174 = $130;$176 = $140;$177 = $133;$196 = $144;$197 = $147;$206 = $95;$207 = $98;$231 = $102;$233 = $105;$237 = $109;$239 = $112;$244 = $116;$245 = $119;
 while(1) {
  $150 = (_bitshift64Shl(($148|0),($149|0),50)|0);
  $151 = tempRet0;
  $152 = (_bitshift64Lshr(($148|0),($149|0),14)|0);
  $153 = tempRet0;
  $154 = $150 | $152;
  $155 = $151 | $153;
  $156 = (_bitshift64Shl(($148|0),($149|0),46)|0);
  $157 = tempRet0;
  $158 = (_bitshift64Lshr(($148|0),($149|0),18)|0);
  $159 = tempRet0;
  $160 = $156 | $158;
  $161 = $157 | $159;
  $162 = $154 ^ $160;
  $163 = $155 ^ $161;
  $164 = (_bitshift64Shl(($148|0),($149|0),23)|0);
  $165 = tempRet0;
  $166 = (_bitshift64Lshr(($148|0),($149|0),41)|0);
  $167 = tempRet0;
  $168 = $164 | $166;
  $169 = $165 | $167;
  $170 = $162 ^ $168;
  $171 = $163 ^ $169;
  $172 = $174 ^ $173;
  $175 = $177 ^ $176;
  $178 = $172 & $148;
  $179 = $175 & $149;
  $180 = $178 ^ $173;
  $181 = $179 ^ $176;
  $182 = (72 + ($$2342<<3)|0);
  $183 = $182;
  $184 = $183;
  $185 = HEAP32[$184>>2]|0;
  $186 = (($183) + 4)|0;
  $187 = $186;
  $188 = HEAP32[$187>>2]|0;
  $189 = (($2) + ($$2342<<3)|0);
  $190 = $189;
  $191 = $190;
  $192 = HEAP32[$191>>2]|0;
  $193 = (($190) + 4)|0;
  $194 = $193;
  $195 = HEAP32[$194>>2]|0;
  $198 = (_i64Add(($180|0),($181|0),($196|0),($197|0))|0);
  $199 = tempRet0;
  $200 = (_i64Add(($198|0),($199|0),($170|0),($171|0))|0);
  $201 = tempRet0;
  $202 = (_i64Add(($200|0),($201|0),($185|0),($188|0))|0);
  $203 = tempRet0;
  $204 = (_i64Add(($202|0),($203|0),($192|0),($195|0))|0);
  $205 = tempRet0;
  $208 = (_bitshift64Shl(($206|0),($207|0),36)|0);
  $209 = tempRet0;
  $210 = (_bitshift64Lshr(($206|0),($207|0),28)|0);
  $211 = tempRet0;
  $212 = $208 | $210;
  $213 = $209 | $211;
  $214 = (_bitshift64Shl(($206|0),($207|0),30)|0);
  $215 = tempRet0;
  $216 = (_bitshift64Lshr(($206|0),($207|0),34)|0);
  $217 = tempRet0;
  $218 = $214 | $216;
  $219 = $215 | $217;
  $220 = $212 ^ $218;
  $221 = $213 ^ $219;
  $222 = (_bitshift64Shl(($206|0),($207|0),25)|0);
  $223 = tempRet0;
  $224 = (_bitshift64Lshr(($206|0),($207|0),39)|0);
  $225 = tempRet0;
  $226 = $222 | $224;
  $227 = $223 | $225;
  $228 = $220 ^ $226;
  $229 = $221 ^ $227;
  $230 = $206 & $231;
  $232 = $207 & $233;
  $234 = $206 | $231;
  $235 = $207 | $233;
  $236 = $234 & $237;
  $238 = $235 & $239;
  $240 = $236 | $230;
  $241 = $238 | $232;
  $242 = (_i64Add(($228|0),($229|0),($240|0),($241|0))|0);
  $243 = tempRet0;
  $246 = (_i64Add(($204|0),($205|0),($244|0),($245|0))|0);
  $247 = tempRet0;
  $248 = (_i64Add(($242|0),($243|0),($204|0),($205|0))|0);
  $249 = tempRet0;
  $250 = (_bitshift64Shl(($246|0),($247|0),50)|0);
  $251 = tempRet0;
  $252 = (_bitshift64Lshr(($246|0),($247|0),14)|0);
  $253 = tempRet0;
  $254 = $250 | $252;
  $255 = $251 | $253;
  $256 = (_bitshift64Shl(($246|0),($247|0),46)|0);
  $257 = tempRet0;
  $258 = (_bitshift64Lshr(($246|0),($247|0),18)|0);
  $259 = tempRet0;
  $260 = $256 | $258;
  $261 = $257 | $259;
  $262 = $254 ^ $260;
  $263 = $255 ^ $261;
  $264 = (_bitshift64Shl(($246|0),($247|0),23)|0);
  $265 = tempRet0;
  $266 = (_bitshift64Lshr(($246|0),($247|0),41)|0);
  $267 = tempRet0;
  $268 = $264 | $266;
  $269 = $265 | $267;
  $270 = $262 ^ $268;
  $271 = $263 ^ $269;
  $272 = $148 ^ $174;
  $273 = $149 ^ $177;
  $274 = $246 & $272;
  $275 = $247 & $273;
  $276 = $274 ^ $174;
  $277 = $275 ^ $177;
  $278 = $$2342 | 1;
  $279 = (72 + ($278<<3)|0);
  $280 = $279;
  $281 = $280;
  $282 = HEAP32[$281>>2]|0;
  $283 = (($280) + 4)|0;
  $284 = $283;
  $285 = HEAP32[$284>>2]|0;
  $286 = (($2) + ($278<<3)|0);
  $287 = $286;
  $288 = $287;
  $289 = HEAP32[$288>>2]|0;
  $290 = (($287) + 4)|0;
  $291 = $290;
  $292 = HEAP32[$291>>2]|0;
  $293 = (_i64Add(($282|0),($285|0),($173|0),($176|0))|0);
  $294 = tempRet0;
  $295 = (_i64Add(($293|0),($294|0),($289|0),($292|0))|0);
  $296 = tempRet0;
  $297 = (_i64Add(($295|0),($296|0),($276|0),($277|0))|0);
  $298 = tempRet0;
  $299 = (_i64Add(($297|0),($298|0),($270|0),($271|0))|0);
  $300 = tempRet0;
  $301 = (_bitshift64Shl(($248|0),($249|0),36)|0);
  $302 = tempRet0;
  $303 = (_bitshift64Lshr(($248|0),($249|0),28)|0);
  $304 = tempRet0;
  $305 = $301 | $303;
  $306 = $302 | $304;
  $307 = (_bitshift64Shl(($248|0),($249|0),30)|0);
  $308 = tempRet0;
  $309 = (_bitshift64Lshr(($248|0),($249|0),34)|0);
  $310 = tempRet0;
  $311 = $307 | $309;
  $312 = $308 | $310;
  $313 = $305 ^ $311;
  $314 = $306 ^ $312;
  $315 = (_bitshift64Shl(($248|0),($249|0),25)|0);
  $316 = tempRet0;
  $317 = (_bitshift64Lshr(($248|0),($249|0),39)|0);
  $318 = tempRet0;
  $319 = $315 | $317;
  $320 = $316 | $318;
  $321 = $313 ^ $319;
  $322 = $314 ^ $320;
  $323 = $248 & $206;
  $324 = $249 & $207;
  $325 = $248 | $206;
  $326 = $249 | $207;
  $327 = $325 & $231;
  $328 = $326 & $233;
  $329 = $327 | $323;
  $330 = $328 | $324;
  $331 = (_i64Add(($321|0),($322|0),($329|0),($330|0))|0);
  $332 = tempRet0;
  $333 = (_i64Add(($299|0),($300|0),($237|0),($239|0))|0);
  $334 = tempRet0;
  $335 = (_i64Add(($331|0),($332|0),($299|0),($300|0))|0);
  $336 = tempRet0;
  $337 = (_bitshift64Shl(($333|0),($334|0),50)|0);
  $338 = tempRet0;
  $339 = (_bitshift64Lshr(($333|0),($334|0),14)|0);
  $340 = tempRet0;
  $341 = $337 | $339;
  $342 = $338 | $340;
  $343 = (_bitshift64Shl(($333|0),($334|0),46)|0);
  $344 = tempRet0;
  $345 = (_bitshift64Lshr(($333|0),($334|0),18)|0);
  $346 = tempRet0;
  $347 = $343 | $345;
  $348 = $344 | $346;
  $349 = $341 ^ $347;
  $350 = $342 ^ $348;
  $351 = (_bitshift64Shl(($333|0),($334|0),23)|0);
  $352 = tempRet0;
  $353 = (_bitshift64Lshr(($333|0),($334|0),41)|0);
  $354 = tempRet0;
  $355 = $351 | $353;
  $356 = $352 | $354;
  $357 = $349 ^ $355;
  $358 = $350 ^ $356;
  $359 = $246 ^ $148;
  $360 = $247 ^ $149;
  $361 = $333 & $359;
  $362 = $334 & $360;
  $363 = $361 ^ $148;
  $364 = $362 ^ $149;
  $365 = $$2342 | 2;
  $366 = (72 + ($365<<3)|0);
  $367 = $366;
  $368 = $367;
  $369 = HEAP32[$368>>2]|0;
  $370 = (($367) + 4)|0;
  $371 = $370;
  $372 = HEAP32[$371>>2]|0;
  $373 = (($2) + ($365<<3)|0);
  $374 = $373;
  $375 = $374;
  $376 = HEAP32[$375>>2]|0;
  $377 = (($374) + 4)|0;
  $378 = $377;
  $379 = HEAP32[$378>>2]|0;
  $380 = (_i64Add(($369|0),($372|0),($174|0),($177|0))|0);
  $381 = tempRet0;
  $382 = (_i64Add(($380|0),($381|0),($376|0),($379|0))|0);
  $383 = tempRet0;
  $384 = (_i64Add(($382|0),($383|0),($363|0),($364|0))|0);
  $385 = tempRet0;
  $386 = (_i64Add(($384|0),($385|0),($357|0),($358|0))|0);
  $387 = tempRet0;
  $388 = (_bitshift64Shl(($335|0),($336|0),36)|0);
  $389 = tempRet0;
  $390 = (_bitshift64Lshr(($335|0),($336|0),28)|0);
  $391 = tempRet0;
  $392 = $388 | $390;
  $393 = $389 | $391;
  $394 = (_bitshift64Shl(($335|0),($336|0),30)|0);
  $395 = tempRet0;
  $396 = (_bitshift64Lshr(($335|0),($336|0),34)|0);
  $397 = tempRet0;
  $398 = $394 | $396;
  $399 = $395 | $397;
  $400 = $392 ^ $398;
  $401 = $393 ^ $399;
  $402 = (_bitshift64Shl(($335|0),($336|0),25)|0);
  $403 = tempRet0;
  $404 = (_bitshift64Lshr(($335|0),($336|0),39)|0);
  $405 = tempRet0;
  $406 = $402 | $404;
  $407 = $403 | $405;
  $408 = $400 ^ $406;
  $409 = $401 ^ $407;
  $410 = $335 & $248;
  $411 = $336 & $249;
  $412 = $335 | $248;
  $413 = $336 | $249;
  $414 = $412 & $206;
  $415 = $413 & $207;
  $416 = $414 | $410;
  $417 = $415 | $411;
  $418 = (_i64Add(($408|0),($409|0),($416|0),($417|0))|0);
  $419 = tempRet0;
  $420 = (_i64Add(($386|0),($387|0),($231|0),($233|0))|0);
  $421 = tempRet0;
  $422 = (_i64Add(($418|0),($419|0),($386|0),($387|0))|0);
  $423 = tempRet0;
  $424 = (_bitshift64Shl(($420|0),($421|0),50)|0);
  $425 = tempRet0;
  $426 = (_bitshift64Lshr(($420|0),($421|0),14)|0);
  $427 = tempRet0;
  $428 = $424 | $426;
  $429 = $425 | $427;
  $430 = (_bitshift64Shl(($420|0),($421|0),46)|0);
  $431 = tempRet0;
  $432 = (_bitshift64Lshr(($420|0),($421|0),18)|0);
  $433 = tempRet0;
  $434 = $430 | $432;
  $435 = $431 | $433;
  $436 = $428 ^ $434;
  $437 = $429 ^ $435;
  $438 = (_bitshift64Shl(($420|0),($421|0),23)|0);
  $439 = tempRet0;
  $440 = (_bitshift64Lshr(($420|0),($421|0),41)|0);
  $441 = tempRet0;
  $442 = $438 | $440;
  $443 = $439 | $441;
  $444 = $436 ^ $442;
  $445 = $437 ^ $443;
  $446 = $333 ^ $246;
  $447 = $334 ^ $247;
  $448 = $420 & $446;
  $449 = $421 & $447;
  $450 = $448 ^ $246;
  $451 = $449 ^ $247;
  $452 = $$2342 | 3;
  $453 = (72 + ($452<<3)|0);
  $454 = $453;
  $455 = $454;
  $456 = HEAP32[$455>>2]|0;
  $457 = (($454) + 4)|0;
  $458 = $457;
  $459 = HEAP32[$458>>2]|0;
  $460 = (($2) + ($452<<3)|0);
  $461 = $460;
  $462 = $461;
  $463 = HEAP32[$462>>2]|0;
  $464 = (($461) + 4)|0;
  $465 = $464;
  $466 = HEAP32[$465>>2]|0;
  $467 = (_i64Add(($456|0),($459|0),($148|0),($149|0))|0);
  $468 = tempRet0;
  $469 = (_i64Add(($467|0),($468|0),($463|0),($466|0))|0);
  $470 = tempRet0;
  $471 = (_i64Add(($469|0),($470|0),($450|0),($451|0))|0);
  $472 = tempRet0;
  $473 = (_i64Add(($471|0),($472|0),($444|0),($445|0))|0);
  $474 = tempRet0;
  $475 = (_bitshift64Shl(($422|0),($423|0),36)|0);
  $476 = tempRet0;
  $477 = (_bitshift64Lshr(($422|0),($423|0),28)|0);
  $478 = tempRet0;
  $479 = $475 | $477;
  $480 = $476 | $478;
  $481 = (_bitshift64Shl(($422|0),($423|0),30)|0);
  $482 = tempRet0;
  $483 = (_bitshift64Lshr(($422|0),($423|0),34)|0);
  $484 = tempRet0;
  $485 = $481 | $483;
  $486 = $482 | $484;
  $487 = $479 ^ $485;
  $488 = $480 ^ $486;
  $489 = (_bitshift64Shl(($422|0),($423|0),25)|0);
  $490 = tempRet0;
  $491 = (_bitshift64Lshr(($422|0),($423|0),39)|0);
  $492 = tempRet0;
  $493 = $489 | $491;
  $494 = $490 | $492;
  $495 = $487 ^ $493;
  $496 = $488 ^ $494;
  $497 = $422 & $335;
  $498 = $423 & $336;
  $499 = $422 | $335;
  $500 = $423 | $336;
  $501 = $499 & $248;
  $502 = $500 & $249;
  $503 = $501 | $497;
  $504 = $502 | $498;
  $505 = (_i64Add(($495|0),($496|0),($503|0),($504|0))|0);
  $506 = tempRet0;
  $507 = (_i64Add(($473|0),($474|0),($206|0),($207|0))|0);
  $508 = tempRet0;
  $509 = (_i64Add(($505|0),($506|0),($473|0),($474|0))|0);
  $510 = tempRet0;
  $511 = (_bitshift64Shl(($507|0),($508|0),50)|0);
  $512 = tempRet0;
  $513 = (_bitshift64Lshr(($507|0),($508|0),14)|0);
  $514 = tempRet0;
  $515 = $511 | $513;
  $516 = $512 | $514;
  $517 = (_bitshift64Shl(($507|0),($508|0),46)|0);
  $518 = tempRet0;
  $519 = (_bitshift64Lshr(($507|0),($508|0),18)|0);
  $520 = tempRet0;
  $521 = $517 | $519;
  $522 = $518 | $520;
  $523 = $515 ^ $521;
  $524 = $516 ^ $522;
  $525 = (_bitshift64Shl(($507|0),($508|0),23)|0);
  $526 = tempRet0;
  $527 = (_bitshift64Lshr(($507|0),($508|0),41)|0);
  $528 = tempRet0;
  $529 = $525 | $527;
  $530 = $526 | $528;
  $531 = $523 ^ $529;
  $532 = $524 ^ $530;
  $533 = $420 ^ $333;
  $534 = $421 ^ $334;
  $535 = $507 & $533;
  $536 = $508 & $534;
  $537 = $535 ^ $333;
  $538 = $536 ^ $334;
  $539 = $$2342 | 4;
  $540 = (72 + ($539<<3)|0);
  $541 = $540;
  $542 = $541;
  $543 = HEAP32[$542>>2]|0;
  $544 = (($541) + 4)|0;
  $545 = $544;
  $546 = HEAP32[$545>>2]|0;
  $547 = (($2) + ($539<<3)|0);
  $548 = $547;
  $549 = $548;
  $550 = HEAP32[$549>>2]|0;
  $551 = (($548) + 4)|0;
  $552 = $551;
  $553 = HEAP32[$552>>2]|0;
  $554 = (_i64Add(($543|0),($546|0),($246|0),($247|0))|0);
  $555 = tempRet0;
  $556 = (_i64Add(($554|0),($555|0),($550|0),($553|0))|0);
  $557 = tempRet0;
  $558 = (_i64Add(($556|0),($557|0),($537|0),($538|0))|0);
  $559 = tempRet0;
  $560 = (_i64Add(($558|0),($559|0),($531|0),($532|0))|0);
  $561 = tempRet0;
  $562 = (_bitshift64Shl(($509|0),($510|0),36)|0);
  $563 = tempRet0;
  $564 = (_bitshift64Lshr(($509|0),($510|0),28)|0);
  $565 = tempRet0;
  $566 = $562 | $564;
  $567 = $563 | $565;
  $568 = (_bitshift64Shl(($509|0),($510|0),30)|0);
  $569 = tempRet0;
  $570 = (_bitshift64Lshr(($509|0),($510|0),34)|0);
  $571 = tempRet0;
  $572 = $568 | $570;
  $573 = $569 | $571;
  $574 = $566 ^ $572;
  $575 = $567 ^ $573;
  $576 = (_bitshift64Shl(($509|0),($510|0),25)|0);
  $577 = tempRet0;
  $578 = (_bitshift64Lshr(($509|0),($510|0),39)|0);
  $579 = tempRet0;
  $580 = $576 | $578;
  $581 = $577 | $579;
  $582 = $574 ^ $580;
  $583 = $575 ^ $581;
  $584 = $509 & $422;
  $585 = $510 & $423;
  $586 = $509 | $422;
  $587 = $510 | $423;
  $588 = $586 & $335;
  $589 = $587 & $336;
  $590 = $588 | $584;
  $591 = $589 | $585;
  $592 = (_i64Add(($582|0),($583|0),($590|0),($591|0))|0);
  $593 = tempRet0;
  $594 = (_i64Add(($560|0),($561|0),($248|0),($249|0))|0);
  $595 = tempRet0;
  $596 = (_i64Add(($592|0),($593|0),($560|0),($561|0))|0);
  $597 = tempRet0;
  $598 = (_bitshift64Shl(($594|0),($595|0),50)|0);
  $599 = tempRet0;
  $600 = (_bitshift64Lshr(($594|0),($595|0),14)|0);
  $601 = tempRet0;
  $602 = $598 | $600;
  $603 = $599 | $601;
  $604 = (_bitshift64Shl(($594|0),($595|0),46)|0);
  $605 = tempRet0;
  $606 = (_bitshift64Lshr(($594|0),($595|0),18)|0);
  $607 = tempRet0;
  $608 = $604 | $606;
  $609 = $605 | $607;
  $610 = $602 ^ $608;
  $611 = $603 ^ $609;
  $612 = (_bitshift64Shl(($594|0),($595|0),23)|0);
  $613 = tempRet0;
  $614 = (_bitshift64Lshr(($594|0),($595|0),41)|0);
  $615 = tempRet0;
  $616 = $612 | $614;
  $617 = $613 | $615;
  $618 = $610 ^ $616;
  $619 = $611 ^ $617;
  $620 = $507 ^ $420;
  $621 = $508 ^ $421;
  $622 = $594 & $620;
  $623 = $595 & $621;
  $624 = $622 ^ $420;
  $625 = $623 ^ $421;
  $626 = $$2342 | 5;
  $627 = (72 + ($626<<3)|0);
  $628 = $627;
  $629 = $628;
  $630 = HEAP32[$629>>2]|0;
  $631 = (($628) + 4)|0;
  $632 = $631;
  $633 = HEAP32[$632>>2]|0;
  $634 = (($2) + ($626<<3)|0);
  $635 = $634;
  $636 = $635;
  $637 = HEAP32[$636>>2]|0;
  $638 = (($635) + 4)|0;
  $639 = $638;
  $640 = HEAP32[$639>>2]|0;
  $641 = (_i64Add(($637|0),($640|0),($630|0),($633|0))|0);
  $642 = tempRet0;
  $643 = (_i64Add(($641|0),($642|0),($333|0),($334|0))|0);
  $644 = tempRet0;
  $645 = (_i64Add(($643|0),($644|0),($624|0),($625|0))|0);
  $646 = tempRet0;
  $647 = (_i64Add(($645|0),($646|0),($618|0),($619|0))|0);
  $648 = tempRet0;
  $649 = (_bitshift64Shl(($596|0),($597|0),36)|0);
  $650 = tempRet0;
  $651 = (_bitshift64Lshr(($596|0),($597|0),28)|0);
  $652 = tempRet0;
  $653 = $649 | $651;
  $654 = $650 | $652;
  $655 = (_bitshift64Shl(($596|0),($597|0),30)|0);
  $656 = tempRet0;
  $657 = (_bitshift64Lshr(($596|0),($597|0),34)|0);
  $658 = tempRet0;
  $659 = $655 | $657;
  $660 = $656 | $658;
  $661 = $653 ^ $659;
  $662 = $654 ^ $660;
  $663 = (_bitshift64Shl(($596|0),($597|0),25)|0);
  $664 = tempRet0;
  $665 = (_bitshift64Lshr(($596|0),($597|0),39)|0);
  $666 = tempRet0;
  $667 = $663 | $665;
  $668 = $664 | $666;
  $669 = $661 ^ $667;
  $670 = $662 ^ $668;
  $671 = $596 & $509;
  $672 = $597 & $510;
  $673 = $596 | $509;
  $674 = $597 | $510;
  $675 = $673 & $422;
  $676 = $674 & $423;
  $677 = $675 | $671;
  $678 = $676 | $672;
  $679 = (_i64Add(($669|0),($670|0),($677|0),($678|0))|0);
  $680 = tempRet0;
  $681 = (_i64Add(($647|0),($648|0),($335|0),($336|0))|0);
  $682 = tempRet0;
  $683 = (_i64Add(($679|0),($680|0),($647|0),($648|0))|0);
  $684 = tempRet0;
  $685 = (_bitshift64Shl(($681|0),($682|0),50)|0);
  $686 = tempRet0;
  $687 = (_bitshift64Lshr(($681|0),($682|0),14)|0);
  $688 = tempRet0;
  $689 = $685 | $687;
  $690 = $686 | $688;
  $691 = (_bitshift64Shl(($681|0),($682|0),46)|0);
  $692 = tempRet0;
  $693 = (_bitshift64Lshr(($681|0),($682|0),18)|0);
  $694 = tempRet0;
  $695 = $691 | $693;
  $696 = $692 | $694;
  $697 = $689 ^ $695;
  $698 = $690 ^ $696;
  $699 = (_bitshift64Shl(($681|0),($682|0),23)|0);
  $700 = tempRet0;
  $701 = (_bitshift64Lshr(($681|0),($682|0),41)|0);
  $702 = tempRet0;
  $703 = $699 | $701;
  $704 = $700 | $702;
  $705 = $697 ^ $703;
  $706 = $698 ^ $704;
  $707 = $594 ^ $507;
  $708 = $595 ^ $508;
  $709 = $681 & $707;
  $710 = $682 & $708;
  $711 = $709 ^ $507;
  $712 = $710 ^ $508;
  $713 = $$2342 | 6;
  $714 = (72 + ($713<<3)|0);
  $715 = $714;
  $716 = $715;
  $717 = HEAP32[$716>>2]|0;
  $718 = (($715) + 4)|0;
  $719 = $718;
  $720 = HEAP32[$719>>2]|0;
  $721 = (($2) + ($713<<3)|0);
  $722 = $721;
  $723 = $722;
  $724 = HEAP32[$723>>2]|0;
  $725 = (($722) + 4)|0;
  $726 = $725;
  $727 = HEAP32[$726>>2]|0;
  $728 = (_i64Add(($724|0),($727|0),($717|0),($720|0))|0);
  $729 = tempRet0;
  $730 = (_i64Add(($728|0),($729|0),($420|0),($421|0))|0);
  $731 = tempRet0;
  $732 = (_i64Add(($730|0),($731|0),($711|0),($712|0))|0);
  $733 = tempRet0;
  $734 = (_i64Add(($732|0),($733|0),($705|0),($706|0))|0);
  $735 = tempRet0;
  $736 = (_bitshift64Shl(($683|0),($684|0),36)|0);
  $737 = tempRet0;
  $738 = (_bitshift64Lshr(($683|0),($684|0),28)|0);
  $739 = tempRet0;
  $740 = $736 | $738;
  $741 = $737 | $739;
  $742 = (_bitshift64Shl(($683|0),($684|0),30)|0);
  $743 = tempRet0;
  $744 = (_bitshift64Lshr(($683|0),($684|0),34)|0);
  $745 = tempRet0;
  $746 = $742 | $744;
  $747 = $743 | $745;
  $748 = $740 ^ $746;
  $749 = $741 ^ $747;
  $750 = (_bitshift64Shl(($683|0),($684|0),25)|0);
  $751 = tempRet0;
  $752 = (_bitshift64Lshr(($683|0),($684|0),39)|0);
  $753 = tempRet0;
  $754 = $750 | $752;
  $755 = $751 | $753;
  $756 = $748 ^ $754;
  $757 = $749 ^ $755;
  $758 = $683 & $596;
  $759 = $684 & $597;
  $760 = $683 | $596;
  $761 = $684 | $597;
  $762 = $760 & $509;
  $763 = $761 & $510;
  $764 = $762 | $758;
  $765 = $763 | $759;
  $766 = (_i64Add(($756|0),($757|0),($764|0),($765|0))|0);
  $767 = tempRet0;
  $768 = (_i64Add(($734|0),($735|0),($422|0),($423|0))|0);
  $769 = tempRet0;
  $770 = (_i64Add(($766|0),($767|0),($734|0),($735|0))|0);
  $771 = tempRet0;
  $772 = (_bitshift64Shl(($768|0),($769|0),50)|0);
  $773 = tempRet0;
  $774 = (_bitshift64Lshr(($768|0),($769|0),14)|0);
  $775 = tempRet0;
  $776 = $772 | $774;
  $777 = $773 | $775;
  $778 = (_bitshift64Shl(($768|0),($769|0),46)|0);
  $779 = tempRet0;
  $780 = (_bitshift64Lshr(($768|0),($769|0),18)|0);
  $781 = tempRet0;
  $782 = $778 | $780;
  $783 = $779 | $781;
  $784 = $776 ^ $782;
  $785 = $777 ^ $783;
  $786 = (_bitshift64Shl(($768|0),($769|0),23)|0);
  $787 = tempRet0;
  $788 = (_bitshift64Lshr(($768|0),($769|0),41)|0);
  $789 = tempRet0;
  $790 = $786 | $788;
  $791 = $787 | $789;
  $792 = $784 ^ $790;
  $793 = $785 ^ $791;
  $794 = $681 ^ $594;
  $795 = $682 ^ $595;
  $796 = $768 & $794;
  $797 = $769 & $795;
  $798 = $796 ^ $594;
  $799 = $797 ^ $595;
  $800 = $$2342 | 7;
  $801 = (72 + ($800<<3)|0);
  $802 = $801;
  $803 = $802;
  $804 = HEAP32[$803>>2]|0;
  $805 = (($802) + 4)|0;
  $806 = $805;
  $807 = HEAP32[$806>>2]|0;
  $808 = (($2) + ($800<<3)|0);
  $809 = $808;
  $810 = $809;
  $811 = HEAP32[$810>>2]|0;
  $812 = (($809) + 4)|0;
  $813 = $812;
  $814 = HEAP32[$813>>2]|0;
  $815 = (_i64Add(($811|0),($814|0),($804|0),($807|0))|0);
  $816 = tempRet0;
  $817 = (_i64Add(($815|0),($816|0),($507|0),($508|0))|0);
  $818 = tempRet0;
  $819 = (_i64Add(($817|0),($818|0),($798|0),($799|0))|0);
  $820 = tempRet0;
  $821 = (_i64Add(($819|0),($820|0),($792|0),($793|0))|0);
  $822 = tempRet0;
  $823 = (_bitshift64Shl(($770|0),($771|0),36)|0);
  $824 = tempRet0;
  $825 = (_bitshift64Lshr(($770|0),($771|0),28)|0);
  $826 = tempRet0;
  $827 = $823 | $825;
  $828 = $824 | $826;
  $829 = (_bitshift64Shl(($770|0),($771|0),30)|0);
  $830 = tempRet0;
  $831 = (_bitshift64Lshr(($770|0),($771|0),34)|0);
  $832 = tempRet0;
  $833 = $829 | $831;
  $834 = $830 | $832;
  $835 = $827 ^ $833;
  $836 = $828 ^ $834;
  $837 = (_bitshift64Shl(($770|0),($771|0),25)|0);
  $838 = tempRet0;
  $839 = (_bitshift64Lshr(($770|0),($771|0),39)|0);
  $840 = tempRet0;
  $841 = $837 | $839;
  $842 = $838 | $840;
  $843 = $835 ^ $841;
  $844 = $836 ^ $842;
  $845 = $770 & $683;
  $846 = $771 & $684;
  $847 = $770 | $683;
  $848 = $771 | $684;
  $849 = $847 & $596;
  $850 = $848 & $597;
  $851 = $849 | $845;
  $852 = $850 | $846;
  $853 = (_i64Add(($843|0),($844|0),($851|0),($852|0))|0);
  $854 = tempRet0;
  $855 = (_i64Add(($821|0),($822|0),($509|0),($510|0))|0);
  $856 = tempRet0;
  $857 = (_i64Add(($853|0),($854|0),($821|0),($822|0))|0);
  $858 = tempRet0;
  $859 = (($$2342) + 8)|0;
  $860 = ($$2342|0)<(72);
  if ($860) {
   $$2342 = $859;$148 = $855;$149 = $856;$173 = $681;$174 = $768;$176 = $682;$177 = $769;$196 = $594;$197 = $595;$206 = $857;$207 = $858;$231 = $770;$233 = $771;$237 = $683;$239 = $684;$244 = $596;$245 = $597;
  } else {
   break;
  }
 }
 $861 = $1;
 $862 = $861;
 $863 = HEAP32[$862>>2]|0;
 $864 = (($861) + 4)|0;
 $865 = $864;
 $866 = HEAP32[$865>>2]|0;
 $867 = (_i64Add(($863|0),($866|0),($857|0),($858|0))|0);
 $868 = tempRet0;
 $869 = $1;
 $870 = $869;
 HEAP32[$870>>2] = $867;
 $871 = (($869) + 4)|0;
 $872 = $871;
 HEAP32[$872>>2] = $868;
 $873 = $99;
 $874 = $873;
 $875 = HEAP32[$874>>2]|0;
 $876 = (($873) + 4)|0;
 $877 = $876;
 $878 = HEAP32[$877>>2]|0;
 $879 = (_i64Add(($875|0),($878|0),($770|0),($771|0))|0);
 $880 = tempRet0;
 $881 = $99;
 $882 = $881;
 HEAP32[$882>>2] = $879;
 $883 = (($881) + 4)|0;
 $884 = $883;
 HEAP32[$884>>2] = $880;
 $885 = $106;
 $886 = $885;
 $887 = HEAP32[$886>>2]|0;
 $888 = (($885) + 4)|0;
 $889 = $888;
 $890 = HEAP32[$889>>2]|0;
 $891 = (_i64Add(($887|0),($890|0),($683|0),($684|0))|0);
 $892 = tempRet0;
 $893 = $106;
 $894 = $893;
 HEAP32[$894>>2] = $891;
 $895 = (($893) + 4)|0;
 $896 = $895;
 HEAP32[$896>>2] = $892;
 $897 = $113;
 $898 = $897;
 $899 = HEAP32[$898>>2]|0;
 $900 = (($897) + 4)|0;
 $901 = $900;
 $902 = HEAP32[$901>>2]|0;
 $903 = (_i64Add(($899|0),($902|0),($596|0),($597|0))|0);
 $904 = tempRet0;
 $905 = $113;
 $906 = $905;
 HEAP32[$906>>2] = $903;
 $907 = (($905) + 4)|0;
 $908 = $907;
 HEAP32[$908>>2] = $904;
 $909 = $120;
 $910 = $909;
 $911 = HEAP32[$910>>2]|0;
 $912 = (($909) + 4)|0;
 $913 = $912;
 $914 = HEAP32[$913>>2]|0;
 $915 = (_i64Add(($911|0),($914|0),($855|0),($856|0))|0);
 $916 = tempRet0;
 $917 = $120;
 $918 = $917;
 HEAP32[$918>>2] = $915;
 $919 = (($917) + 4)|0;
 $920 = $919;
 HEAP32[$920>>2] = $916;
 $921 = $127;
 $922 = $921;
 $923 = HEAP32[$922>>2]|0;
 $924 = (($921) + 4)|0;
 $925 = $924;
 $926 = HEAP32[$925>>2]|0;
 $927 = (_i64Add(($923|0),($926|0),($768|0),($769|0))|0);
 $928 = tempRet0;
 $929 = $127;
 $930 = $929;
 HEAP32[$930>>2] = $927;
 $931 = (($929) + 4)|0;
 $932 = $931;
 HEAP32[$932>>2] = $928;
 $933 = $134;
 $934 = $933;
 $935 = HEAP32[$934>>2]|0;
 $936 = (($933) + 4)|0;
 $937 = $936;
 $938 = HEAP32[$937>>2]|0;
 $939 = (_i64Add(($935|0),($938|0),($681|0),($682|0))|0);
 $940 = tempRet0;
 $941 = $134;
 $942 = $941;
 HEAP32[$942>>2] = $939;
 $943 = (($941) + 4)|0;
 $944 = $943;
 HEAP32[$944>>2] = $940;
 $945 = $141;
 $946 = $945;
 $947 = HEAP32[$946>>2]|0;
 $948 = (($945) + 4)|0;
 $949 = $948;
 $950 = HEAP32[$949>>2]|0;
 $951 = (_i64Add(($947|0),($950|0),($594|0),($595|0))|0);
 $952 = tempRet0;
 $953 = $141;
 $954 = $953;
 HEAP32[$954>>2] = $951;
 $955 = (($953) + 4)|0;
 $956 = $955;
 HEAP32[$956>>2] = $952;
 STACKTOP = sp;return;
}
function _sph_dec64be_aligned($0) {
 $0 = $0|0;
 var $1 = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $2 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0;
 var $28 = 0, $29 = 0, $3 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $4 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0;
 var $46 = 0, $47 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $1 = HEAP8[$0>>0]|0;
 $2 = $1&255;
 $3 = (_bitshift64Shl(($2|0),0,56)|0);
 $4 = tempRet0;
 $5 = ((($0)) + 1|0);
 $6 = HEAP8[$5>>0]|0;
 $7 = $6&255;
 $8 = (_bitshift64Shl(($7|0),0,48)|0);
 $9 = tempRet0;
 $10 = $8 | $3;
 $11 = $9 | $4;
 $12 = ((($0)) + 2|0);
 $13 = HEAP8[$12>>0]|0;
 $14 = $13&255;
 $15 = (_bitshift64Shl(($14|0),0,40)|0);
 $16 = tempRet0;
 $17 = $10 | $15;
 $18 = $11 | $16;
 $19 = ((($0)) + 3|0);
 $20 = HEAP8[$19>>0]|0;
 $21 = $20&255;
 $22 = $18 | $21;
 $23 = ((($0)) + 4|0);
 $24 = HEAP8[$23>>0]|0;
 $25 = $24&255;
 $26 = (_bitshift64Shl(($25|0),0,24)|0);
 $27 = tempRet0;
 $28 = $17 | $26;
 $29 = $22 | $27;
 $30 = ((($0)) + 5|0);
 $31 = HEAP8[$30>>0]|0;
 $32 = $31&255;
 $33 = (_bitshift64Shl(($32|0),0,16)|0);
 $34 = tempRet0;
 $35 = $28 | $33;
 $36 = $29 | $34;
 $37 = ((($0)) + 6|0);
 $38 = HEAP8[$37>>0]|0;
 $39 = $38&255;
 $40 = (_bitshift64Shl(($39|0),0,8)|0);
 $41 = tempRet0;
 $42 = $35 | $40;
 $43 = $36 | $41;
 $44 = ((($0)) + 7|0);
 $45 = HEAP8[$44>>0]|0;
 $46 = $45&255;
 $47 = $42 | $46;
 tempRet0 = ($43);
 return ($47|0);
}
function _sha384_close($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var label = 0, sp = 0;
 sp = STACKTOP;
 _sha384_addbits_and_close($0,0,0,$1,$2);
 return;
}
function _sha384_addbits_and_close($0,$1,$2,$3,$4) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 $3 = $3|0;
 $4 = $4|0;
 var $$035 = 0, $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0;
 var $29 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0, $46 = 0, $47 = 0, $48 = 0;
 var $49 = 0, $5 = 0, $50 = 0, $51 = 0, $52 = 0, $53 = 0, $54 = 0, $55 = 0, $56 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, $exitcond = 0, dest = 0, label = 0, sp = 0, stop = 0;
 sp = STACKTOP;
 $5 = ((($0)) + 192|0);
 $6 = $5;
 $7 = $6;
 $8 = HEAP32[$7>>2]|0;
 $9 = (($6) + 4)|0;
 $10 = $9;
 $11 = HEAP32[$10>>2]|0;
 $12 = $8 & 127;
 $13 = 128 >>> $2;
 $14 = (0 - ($13))|0;
 $15 = $14 & $1;
 $16 = $15 | $13;
 $17 = $16&255;
 $18 = (($12) + 1)|0;
 $19 = (($0) + ($12)|0);
 HEAP8[$19>>0] = $17;
 $20 = ($12>>>0)>(111);
 $21 = (($0) + ($18)|0);
 if ($20) {
  $22 = $12 ^ 127;
  _memset(($21|0),0,($22|0))|0;
  $23 = ((($0)) + 128|0);
  _sha3_round($0,$23);
  dest=$0; stop=dest+112|0; do { HEAP32[dest>>2]=0|0; dest=dest+4|0; } while ((dest|0) < (stop|0));
 } else {
  $24 = (111 - ($12))|0;
  _memset(($21|0),0,($24|0))|0;
 }
 $25 = ((($0)) + 112|0);
 $26 = $5;
 $27 = $26;
 $28 = HEAP32[$27>>2]|0;
 $29 = (($26) + 4)|0;
 $30 = $29;
 $31 = HEAP32[$30>>2]|0;
 $32 = (_bitshift64Lshr(($28|0),($31|0),61)|0);
 $33 = tempRet0;
 _sph_enc64be_aligned($25,$32,$33);
 $34 = ((($0)) + 120|0);
 $35 = $5;
 $36 = $35;
 $37 = HEAP32[$36>>2]|0;
 $38 = (($35) + 4)|0;
 $39 = $38;
 $40 = HEAP32[$39>>2]|0;
 $41 = (_bitshift64Shl(($37|0),($40|0),3)|0);
 $42 = tempRet0;
 $43 = (_i64Add(($41|0),($42|0),($2|0),0)|0);
 $44 = tempRet0;
 _sph_enc64be_aligned($34,$43,$44);
 $45 = ((($0)) + 128|0);
 _sha3_round($0,$45);
 $46 = ($4|0)==(0);
 if ($46) {
  return;
 } else {
  $$035 = 0;
 }
 while(1) {
  $47 = $$035 << 3;
  $48 = (($3) + ($47)|0);
  $49 = (($45) + ($$035<<3)|0);
  $50 = $49;
  $51 = $50;
  $52 = HEAP32[$51>>2]|0;
  $53 = (($50) + 4)|0;
  $54 = $53;
  $55 = HEAP32[$54>>2]|0;
  _sph_enc64be($48,$52,$55);
  $56 = (($$035) + 1)|0;
  $exitcond = ($56|0)==($4|0);
  if ($exitcond) {
   break;
  } else {
   $$035 = $56;
  }
 }
 return;
}
function _sph_enc64be_aligned($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0, $29 = 0;
 var $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $3 = (_bitshift64Lshr(($1|0),($2|0),56)|0);
 $4 = tempRet0;
 $5 = $3&255;
 HEAP8[$0>>0] = $5;
 $6 = (_bitshift64Lshr(($1|0),($2|0),48)|0);
 $7 = tempRet0;
 $8 = $6&255;
 $9 = ((($0)) + 1|0);
 HEAP8[$9>>0] = $8;
 $10 = (_bitshift64Lshr(($1|0),($2|0),40)|0);
 $11 = tempRet0;
 $12 = $10&255;
 $13 = ((($0)) + 2|0);
 HEAP8[$13>>0] = $12;
 $14 = $2&255;
 $15 = ((($0)) + 3|0);
 HEAP8[$15>>0] = $14;
 $16 = (_bitshift64Lshr(($1|0),($2|0),24)|0);
 $17 = tempRet0;
 $18 = $16&255;
 $19 = ((($0)) + 4|0);
 HEAP8[$19>>0] = $18;
 $20 = (_bitshift64Lshr(($1|0),($2|0),16)|0);
 $21 = tempRet0;
 $22 = $20&255;
 $23 = ((($0)) + 5|0);
 HEAP8[$23>>0] = $22;
 $24 = (_bitshift64Lshr(($1|0),($2|0),8)|0);
 $25 = tempRet0;
 $26 = $24&255;
 $27 = ((($0)) + 6|0);
 HEAP8[$27>>0] = $26;
 $28 = $1&255;
 $29 = ((($0)) + 7|0);
 HEAP8[$29>>0] = $28;
 return;
}
function _sph_enc64be($0,$1,$2) {
 $0 = $0|0;
 $1 = $1|0;
 $2 = $2|0;
 var $10 = 0, $11 = 0, $12 = 0, $13 = 0, $14 = 0, $15 = 0, $16 = 0, $17 = 0, $18 = 0, $19 = 0, $20 = 0, $21 = 0, $22 = 0, $23 = 0, $24 = 0, $25 = 0, $26 = 0, $27 = 0, $28 = 0, $29 = 0;
 var $3 = 0, $4 = 0, $5 = 0, $6 = 0, $7 = 0, $8 = 0, $9 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $3 = (_bitshift64Lshr(($1|0),($2|0),56)|0);
 $4 = tempRet0;
 $5 = $3&255;
 HEAP8[$0>>0] = $5;
 $6 = (_bitshift64Lshr(($1|0),($2|0),48)|0);
 $7 = tempRet0;
 $8 = $6&255;
 $9 = ((($0)) + 1|0);
 HEAP8[$9>>0] = $8;
 $10 = (_bitshift64Lshr(($1|0),($2|0),40)|0);
 $11 = tempRet0;
 $12 = $10&255;
 $13 = ((($0)) + 2|0);
 HEAP8[$13>>0] = $12;
 $14 = $2&255;
 $15 = ((($0)) + 3|0);
 HEAP8[$15>>0] = $14;
 $16 = (_bitshift64Lshr(($1|0),($2|0),24)|0);
 $17 = tempRet0;
 $18 = $16&255;
 $19 = ((($0)) + 4|0);
 HEAP8[$19>>0] = $18;
 $20 = (_bitshift64Lshr(($1|0),($2|0),16)|0);
 $21 = tempRet0;
 $22 = $20&255;
 $23 = ((($0)) + 5|0);
 HEAP8[$23>>0] = $22;
 $24 = (_bitshift64Lshr(($1|0),($2|0),8)|0);
 $25 = tempRet0;
 $26 = $24&255;
 $27 = ((($0)) + 6|0);
 HEAP8[$27>>0] = $26;
 $28 = $1&255;
 $29 = ((($0)) + 7|0);
 HEAP8[$29>>0] = $28;
 return;
}
function _sph_sha512_close($0,$1) {
 $0 = $0|0;
 $1 = $1|0;
 var label = 0, sp = 0;
 sp = STACKTOP;
 _sha384_close($0,$1,8);
 _sph_sha512_init($0);
 return;
}
function _malloc($0) {
 $0 = $0|0;
 var $$$0172$i = 0, $$$0173$i = 0, $$$4236$i = 0, $$$4329$i = 0, $$$i = 0, $$0 = 0, $$0$i = 0, $$0$i$i = 0, $$0$i$i$i = 0, $$0$i20$i = 0, $$0172$lcssa$i = 0, $$01724$i = 0, $$0173$lcssa$i = 0, $$01733$i = 0, $$0192 = 0, $$0194 = 0, $$0201$i$i = 0, $$0202$i$i = 0, $$0206$i$i = 0, $$0207$i$i = 0;
 var $$024367$i = 0, $$0260$i$i = 0, $$0261$i$i = 0, $$0262$i$i = 0, $$0268$i$i = 0, $$0269$i$i = 0, $$0320$i = 0, $$0322$i = 0, $$0323$i = 0, $$0325$i = 0, $$0331$i = 0, $$0336$i = 0, $$0337$$i = 0, $$0337$i = 0, $$0339$i = 0, $$0340$i = 0, $$0345$i = 0, $$1176$i = 0, $$1178$i = 0, $$124466$i = 0;
 var $$1264$i$i = 0, $$1266$i$i = 0, $$1321$i = 0, $$1326$i = 0, $$1341$i = 0, $$1347$i = 0, $$1351$i = 0, $$2234243136$i = 0, $$2247$ph$i = 0, $$2253$ph$i = 0, $$2333$i = 0, $$3$i = 0, $$3$i$i = 0, $$3$i199 = 0, $$3328$i = 0, $$3349$i = 0, $$4$lcssa$i = 0, $$4$ph$i = 0, $$4236$i = 0, $$4329$lcssa$i = 0;
 var $$43298$i = 0, $$4335$$4$i = 0, $$4335$ph$i = 0, $$43357$i = 0, $$49$i = 0, $$723947$i = 0, $$748$i = 0, $$pre = 0, $$pre$i = 0, $$pre$i$i = 0, $$pre$i17$i = 0, $$pre$i195 = 0, $$pre$i207 = 0, $$pre$phi$i$iZ2D = 0, $$pre$phi$i18$iZ2D = 0, $$pre$phi$i208Z2D = 0, $$pre$phi$iZ2D = 0, $$pre$phiZ2D = 0, $$sink1$i = 0, $$sink1$i$i = 0;
 var $$sink12$i = 0, $$sink2$i = 0, $$sink2$i202 = 0, $$sink3$i = 0, $1 = 0, $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0;
 var $113 = 0, $114 = 0, $115 = 0, $116 = 0, $117 = 0, $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0;
 var $131 = 0, $132 = 0, $133 = 0, $134 = 0, $135 = 0, $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0;
 var $15 = 0, $150 = 0, $151 = 0, $152 = 0, $153 = 0, $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $159 = 0, $16 = 0, $160 = 0, $161 = 0, $162 = 0, $163 = 0, $164 = 0, $165 = 0, $166 = 0, $167 = 0;
 var $168 = 0, $169 = 0, $17 = 0, $170 = 0, $171 = 0, $172 = 0, $173 = 0, $174 = 0, $175 = 0, $176 = 0, $177 = 0, $178 = 0, $179 = 0, $18 = 0, $180 = 0, $181 = 0, $182 = 0, $183 = 0, $184 = 0, $185 = 0;
 var $186 = 0, $187 = 0, $188 = 0, $189 = 0, $19 = 0, $190 = 0, $191 = 0, $192 = 0, $193 = 0, $194 = 0, $195 = 0, $196 = 0, $197 = 0, $198 = 0, $199 = 0, $2 = 0, $20 = 0, $200 = 0, $201 = 0, $202 = 0;
 var $203 = 0, $204 = 0, $205 = 0, $206 = 0, $207 = 0, $208 = 0, $209 = 0, $21 = 0, $210 = 0, $211 = 0, $212 = 0, $213 = 0, $214 = 0, $215 = 0, $216 = 0, $217 = 0, $218 = 0, $219 = 0, $22 = 0, $220 = 0;
 var $221 = 0, $222 = 0, $223 = 0, $224 = 0, $225 = 0, $226 = 0, $227 = 0, $228 = 0, $229 = 0, $23 = 0, $230 = 0, $231 = 0, $232 = 0, $233 = 0, $234 = 0, $235 = 0, $236 = 0, $237 = 0, $238 = 0, $239 = 0;
 var $24 = 0, $240 = 0, $241 = 0, $242 = 0, $243 = 0, $244 = 0, $245 = 0, $246 = 0, $247 = 0, $248 = 0, $249 = 0, $25 = 0, $250 = 0, $251 = 0, $252 = 0, $253 = 0, $254 = 0, $255 = 0, $256 = 0, $257 = 0;
 var $258 = 0, $259 = 0, $26 = 0, $260 = 0, $261 = 0, $262 = 0, $263 = 0, $264 = 0, $265 = 0, $266 = 0, $267 = 0, $268 = 0, $269 = 0, $27 = 0, $270 = 0, $271 = 0, $272 = 0, $273 = 0, $274 = 0, $275 = 0;
 var $276 = 0, $277 = 0, $278 = 0, $279 = 0, $28 = 0, $280 = 0, $281 = 0, $282 = 0, $283 = 0, $284 = 0, $285 = 0, $286 = 0, $287 = 0, $288 = 0, $289 = 0, $29 = 0, $290 = 0, $291 = 0, $292 = 0, $293 = 0;
 var $294 = 0, $295 = 0, $296 = 0, $297 = 0, $298 = 0, $299 = 0, $3 = 0, $30 = 0, $300 = 0, $301 = 0, $302 = 0, $303 = 0, $304 = 0, $305 = 0, $306 = 0, $307 = 0, $308 = 0, $309 = 0, $31 = 0, $310 = 0;
 var $311 = 0, $312 = 0, $313 = 0, $314 = 0, $315 = 0, $316 = 0, $317 = 0, $318 = 0, $319 = 0, $32 = 0, $320 = 0, $321 = 0, $322 = 0, $323 = 0, $324 = 0, $325 = 0, $326 = 0, $327 = 0, $328 = 0, $329 = 0;
 var $33 = 0, $330 = 0, $331 = 0, $332 = 0, $333 = 0, $334 = 0, $335 = 0, $336 = 0, $337 = 0, $338 = 0, $339 = 0, $34 = 0, $340 = 0, $341 = 0, $342 = 0, $343 = 0, $344 = 0, $345 = 0, $346 = 0, $347 = 0;
 var $348 = 0, $349 = 0, $35 = 0, $350 = 0, $351 = 0, $352 = 0, $353 = 0, $354 = 0, $355 = 0, $356 = 0, $357 = 0, $358 = 0, $359 = 0, $36 = 0, $360 = 0, $361 = 0, $362 = 0, $363 = 0, $364 = 0, $365 = 0;
 var $366 = 0, $367 = 0, $368 = 0, $369 = 0, $37 = 0, $370 = 0, $371 = 0, $372 = 0, $373 = 0, $374 = 0, $375 = 0, $376 = 0, $377 = 0, $378 = 0, $379 = 0, $38 = 0, $380 = 0, $381 = 0, $382 = 0, $383 = 0;
 var $384 = 0, $385 = 0, $386 = 0, $387 = 0, $388 = 0, $389 = 0, $39 = 0, $390 = 0, $391 = 0, $392 = 0, $393 = 0, $394 = 0, $395 = 0, $396 = 0, $397 = 0, $398 = 0, $399 = 0, $4 = 0, $40 = 0, $400 = 0;
 var $401 = 0, $402 = 0, $403 = 0, $404 = 0, $405 = 0, $406 = 0, $407 = 0, $408 = 0, $409 = 0, $41 = 0, $410 = 0, $411 = 0, $412 = 0, $413 = 0, $414 = 0, $415 = 0, $416 = 0, $417 = 0, $418 = 0, $419 = 0;
 var $42 = 0, $420 = 0, $421 = 0, $422 = 0, $423 = 0, $424 = 0, $425 = 0, $426 = 0, $427 = 0, $428 = 0, $429 = 0, $43 = 0, $430 = 0, $431 = 0, $432 = 0, $433 = 0, $434 = 0, $435 = 0, $436 = 0, $437 = 0;
 var $438 = 0, $439 = 0, $44 = 0, $440 = 0, $441 = 0, $442 = 0, $443 = 0, $444 = 0, $445 = 0, $446 = 0, $447 = 0, $448 = 0, $449 = 0, $45 = 0, $450 = 0, $451 = 0, $452 = 0, $453 = 0, $454 = 0, $455 = 0;
 var $456 = 0, $457 = 0, $458 = 0, $459 = 0, $46 = 0, $460 = 0, $461 = 0, $462 = 0, $463 = 0, $464 = 0, $465 = 0, $466 = 0, $467 = 0, $468 = 0, $469 = 0, $47 = 0, $470 = 0, $471 = 0, $472 = 0, $473 = 0;
 var $474 = 0, $475 = 0, $476 = 0, $477 = 0, $478 = 0, $479 = 0, $48 = 0, $480 = 0, $481 = 0, $482 = 0, $483 = 0, $484 = 0, $485 = 0, $486 = 0, $487 = 0, $488 = 0, $489 = 0, $49 = 0, $490 = 0, $491 = 0;
 var $492 = 0, $493 = 0, $494 = 0, $495 = 0, $496 = 0, $497 = 0, $498 = 0, $499 = 0, $5 = 0, $50 = 0, $500 = 0, $501 = 0, $502 = 0, $503 = 0, $504 = 0, $505 = 0, $506 = 0, $507 = 0, $508 = 0, $509 = 0;
 var $51 = 0, $510 = 0, $511 = 0, $512 = 0, $513 = 0, $514 = 0, $515 = 0, $516 = 0, $517 = 0, $518 = 0, $519 = 0, $52 = 0, $520 = 0, $521 = 0, $522 = 0, $523 = 0, $524 = 0, $525 = 0, $526 = 0, $527 = 0;
 var $528 = 0, $529 = 0, $53 = 0, $530 = 0, $531 = 0, $532 = 0, $533 = 0, $534 = 0, $535 = 0, $536 = 0, $537 = 0, $538 = 0, $539 = 0, $54 = 0, $540 = 0, $541 = 0, $542 = 0, $543 = 0, $544 = 0, $545 = 0;
 var $546 = 0, $547 = 0, $548 = 0, $549 = 0, $55 = 0, $550 = 0, $551 = 0, $552 = 0, $553 = 0, $554 = 0, $555 = 0, $556 = 0, $557 = 0, $558 = 0, $559 = 0, $56 = 0, $560 = 0, $561 = 0, $562 = 0, $563 = 0;
 var $564 = 0, $565 = 0, $566 = 0, $567 = 0, $568 = 0, $569 = 0, $57 = 0, $570 = 0, $571 = 0, $572 = 0, $573 = 0, $574 = 0, $575 = 0, $576 = 0, $577 = 0, $578 = 0, $579 = 0, $58 = 0, $580 = 0, $581 = 0;
 var $582 = 0, $583 = 0, $584 = 0, $585 = 0, $586 = 0, $587 = 0, $588 = 0, $589 = 0, $59 = 0, $590 = 0, $591 = 0, $592 = 0, $593 = 0, $594 = 0, $595 = 0, $596 = 0, $597 = 0, $598 = 0, $599 = 0, $6 = 0;
 var $60 = 0, $600 = 0, $601 = 0, $602 = 0, $603 = 0, $604 = 0, $605 = 0, $606 = 0, $607 = 0, $608 = 0, $609 = 0, $61 = 0, $610 = 0, $611 = 0, $612 = 0, $613 = 0, $614 = 0, $615 = 0, $616 = 0, $617 = 0;
 var $618 = 0, $619 = 0, $62 = 0, $620 = 0, $621 = 0, $622 = 0, $623 = 0, $624 = 0, $625 = 0, $626 = 0, $627 = 0, $628 = 0, $629 = 0, $63 = 0, $630 = 0, $631 = 0, $632 = 0, $633 = 0, $634 = 0, $635 = 0;
 var $636 = 0, $637 = 0, $638 = 0, $639 = 0, $64 = 0, $640 = 0, $641 = 0, $642 = 0, $643 = 0, $644 = 0, $645 = 0, $646 = 0, $647 = 0, $648 = 0, $649 = 0, $65 = 0, $650 = 0, $651 = 0, $652 = 0, $653 = 0;
 var $654 = 0, $655 = 0, $656 = 0, $657 = 0, $658 = 0, $659 = 0, $66 = 0, $660 = 0, $661 = 0, $662 = 0, $663 = 0, $664 = 0, $665 = 0, $666 = 0, $667 = 0, $668 = 0, $669 = 0, $67 = 0, $670 = 0, $671 = 0;
 var $672 = 0, $673 = 0, $674 = 0, $675 = 0, $676 = 0, $677 = 0, $678 = 0, $679 = 0, $68 = 0, $680 = 0, $681 = 0, $682 = 0, $683 = 0, $684 = 0, $685 = 0, $686 = 0, $687 = 0, $688 = 0, $689 = 0, $69 = 0;
 var $690 = 0, $691 = 0, $692 = 0, $693 = 0, $694 = 0, $695 = 0, $696 = 0, $697 = 0, $698 = 0, $699 = 0, $7 = 0, $70 = 0, $700 = 0, $701 = 0, $702 = 0, $703 = 0, $704 = 0, $705 = 0, $706 = 0, $707 = 0;
 var $708 = 0, $709 = 0, $71 = 0, $710 = 0, $711 = 0, $712 = 0, $713 = 0, $714 = 0, $715 = 0, $716 = 0, $717 = 0, $718 = 0, $719 = 0, $72 = 0, $720 = 0, $721 = 0, $722 = 0, $723 = 0, $724 = 0, $725 = 0;
 var $726 = 0, $727 = 0, $728 = 0, $729 = 0, $73 = 0, $730 = 0, $731 = 0, $732 = 0, $733 = 0, $734 = 0, $735 = 0, $736 = 0, $737 = 0, $738 = 0, $739 = 0, $74 = 0, $740 = 0, $741 = 0, $742 = 0, $743 = 0;
 var $744 = 0, $745 = 0, $746 = 0, $747 = 0, $748 = 0, $749 = 0, $75 = 0, $750 = 0, $751 = 0, $752 = 0, $753 = 0, $754 = 0, $755 = 0, $756 = 0, $757 = 0, $758 = 0, $759 = 0, $76 = 0, $760 = 0, $761 = 0;
 var $762 = 0, $763 = 0, $764 = 0, $765 = 0, $766 = 0, $767 = 0, $768 = 0, $769 = 0, $77 = 0, $770 = 0, $771 = 0, $772 = 0, $773 = 0, $774 = 0, $775 = 0, $776 = 0, $777 = 0, $778 = 0, $779 = 0, $78 = 0;
 var $780 = 0, $781 = 0, $782 = 0, $783 = 0, $784 = 0, $785 = 0, $786 = 0, $787 = 0, $788 = 0, $789 = 0, $79 = 0, $790 = 0, $791 = 0, $792 = 0, $793 = 0, $794 = 0, $795 = 0, $796 = 0, $797 = 0, $798 = 0;
 var $799 = 0, $8 = 0, $80 = 0, $800 = 0, $801 = 0, $802 = 0, $803 = 0, $804 = 0, $805 = 0, $806 = 0, $807 = 0, $808 = 0, $809 = 0, $81 = 0, $810 = 0, $811 = 0, $812 = 0, $813 = 0, $814 = 0, $815 = 0;
 var $816 = 0, $817 = 0, $818 = 0, $819 = 0, $82 = 0, $820 = 0, $821 = 0, $822 = 0, $823 = 0, $824 = 0, $825 = 0, $826 = 0, $827 = 0, $828 = 0, $829 = 0, $83 = 0, $830 = 0, $831 = 0, $832 = 0, $833 = 0;
 var $834 = 0, $835 = 0, $836 = 0, $837 = 0, $838 = 0, $839 = 0, $84 = 0, $840 = 0, $841 = 0, $842 = 0, $843 = 0, $844 = 0, $845 = 0, $846 = 0, $847 = 0, $848 = 0, $849 = 0, $85 = 0, $850 = 0, $851 = 0;
 var $852 = 0, $853 = 0, $854 = 0, $855 = 0, $856 = 0, $857 = 0, $858 = 0, $859 = 0, $86 = 0, $860 = 0, $861 = 0, $862 = 0, $863 = 0, $864 = 0, $865 = 0, $866 = 0, $867 = 0, $868 = 0, $869 = 0, $87 = 0;
 var $870 = 0, $871 = 0, $872 = 0, $873 = 0, $874 = 0, $875 = 0, $876 = 0, $877 = 0, $878 = 0, $879 = 0, $88 = 0, $880 = 0, $881 = 0, $882 = 0, $883 = 0, $884 = 0, $885 = 0, $886 = 0, $887 = 0, $888 = 0;
 var $889 = 0, $89 = 0, $890 = 0, $891 = 0, $892 = 0, $893 = 0, $894 = 0, $895 = 0, $896 = 0, $897 = 0, $898 = 0, $899 = 0, $9 = 0, $90 = 0, $900 = 0, $901 = 0, $902 = 0, $903 = 0, $904 = 0, $905 = 0;
 var $906 = 0, $907 = 0, $908 = 0, $909 = 0, $91 = 0, $910 = 0, $911 = 0, $912 = 0, $913 = 0, $914 = 0, $915 = 0, $916 = 0, $917 = 0, $918 = 0, $919 = 0, $92 = 0, $920 = 0, $921 = 0, $922 = 0, $923 = 0;
 var $924 = 0, $925 = 0, $926 = 0, $927 = 0, $928 = 0, $929 = 0, $93 = 0, $930 = 0, $931 = 0, $932 = 0, $933 = 0, $934 = 0, $935 = 0, $936 = 0, $937 = 0, $938 = 0, $939 = 0, $94 = 0, $940 = 0, $941 = 0;
 var $942 = 0, $943 = 0, $944 = 0, $945 = 0, $946 = 0, $947 = 0, $948 = 0, $949 = 0, $95 = 0, $950 = 0, $951 = 0, $952 = 0, $953 = 0, $954 = 0, $955 = 0, $956 = 0, $957 = 0, $958 = 0, $959 = 0, $96 = 0;
 var $960 = 0, $961 = 0, $962 = 0, $963 = 0, $964 = 0, $965 = 0, $966 = 0, $967 = 0, $968 = 0, $969 = 0, $97 = 0, $970 = 0, $971 = 0, $98 = 0, $99 = 0, $cond$i = 0, $cond$i$i = 0, $cond$i206 = 0, $not$$i = 0, $not$3$i = 0;
 var $or$cond$i = 0, $or$cond$i200 = 0, $or$cond1$i = 0, $or$cond1$i198 = 0, $or$cond10$i = 0, $or$cond11$i = 0, $or$cond11$not$i = 0, $or$cond12$i = 0, $or$cond2$i = 0, $or$cond49$i = 0, $or$cond5$i = 0, $or$cond50$i = 0, $or$cond7$i = 0, label = 0, sp = 0;
 sp = STACKTOP;
 STACKTOP = STACKTOP + 16|0;
 $1 = sp;
 $2 = ($0>>>0)<(245);
 do {
  if ($2) {
   $3 = ($0>>>0)<(11);
   $4 = (($0) + 11)|0;
   $5 = $4 & -8;
   $6 = $3 ? 16 : $5;
   $7 = $6 >>> 3;
   $8 = HEAP32[8128]|0;
   $9 = $8 >>> $7;
   $10 = $9 & 3;
   $11 = ($10|0)==(0);
   if (!($11)) {
    $12 = $9 & 1;
    $13 = $12 ^ 1;
    $14 = (($13) + ($7))|0;
    $15 = $14 << 1;
    $16 = (32552 + ($15<<2)|0);
    $17 = ((($16)) + 8|0);
    $18 = HEAP32[$17>>2]|0;
    $19 = ((($18)) + 8|0);
    $20 = HEAP32[$19>>2]|0;
    $21 = ($20|0)==($16|0);
    if ($21) {
     $22 = 1 << $14;
     $23 = $22 ^ -1;
     $24 = $8 & $23;
     HEAP32[8128] = $24;
    } else {
     $25 = ((($20)) + 12|0);
     HEAP32[$25>>2] = $16;
     HEAP32[$17>>2] = $20;
    }
    $26 = $14 << 3;
    $27 = $26 | 3;
    $28 = ((($18)) + 4|0);
    HEAP32[$28>>2] = $27;
    $29 = (($18) + ($26)|0);
    $30 = ((($29)) + 4|0);
    $31 = HEAP32[$30>>2]|0;
    $32 = $31 | 1;
    HEAP32[$30>>2] = $32;
    $$0 = $19;
    STACKTOP = sp;return ($$0|0);
   }
   $33 = HEAP32[(32520)>>2]|0;
   $34 = ($6>>>0)>($33>>>0);
   if ($34) {
    $35 = ($9|0)==(0);
    if (!($35)) {
     $36 = $9 << $7;
     $37 = 2 << $7;
     $38 = (0 - ($37))|0;
     $39 = $37 | $38;
     $40 = $36 & $39;
     $41 = (0 - ($40))|0;
     $42 = $40 & $41;
     $43 = (($42) + -1)|0;
     $44 = $43 >>> 12;
     $45 = $44 & 16;
     $46 = $43 >>> $45;
     $47 = $46 >>> 5;
     $48 = $47 & 8;
     $49 = $48 | $45;
     $50 = $46 >>> $48;
     $51 = $50 >>> 2;
     $52 = $51 & 4;
     $53 = $49 | $52;
     $54 = $50 >>> $52;
     $55 = $54 >>> 1;
     $56 = $55 & 2;
     $57 = $53 | $56;
     $58 = $54 >>> $56;
     $59 = $58 >>> 1;
     $60 = $59 & 1;
     $61 = $57 | $60;
     $62 = $58 >>> $60;
     $63 = (($61) + ($62))|0;
     $64 = $63 << 1;
     $65 = (32552 + ($64<<2)|0);
     $66 = ((($65)) + 8|0);
     $67 = HEAP32[$66>>2]|0;
     $68 = ((($67)) + 8|0);
     $69 = HEAP32[$68>>2]|0;
     $70 = ($69|0)==($65|0);
     if ($70) {
      $71 = 1 << $63;
      $72 = $71 ^ -1;
      $73 = $8 & $72;
      HEAP32[8128] = $73;
      $90 = $73;
     } else {
      $74 = ((($69)) + 12|0);
      HEAP32[$74>>2] = $65;
      HEAP32[$66>>2] = $69;
      $90 = $8;
     }
     $75 = $63 << 3;
     $76 = (($75) - ($6))|0;
     $77 = $6 | 3;
     $78 = ((($67)) + 4|0);
     HEAP32[$78>>2] = $77;
     $79 = (($67) + ($6)|0);
     $80 = $76 | 1;
     $81 = ((($79)) + 4|0);
     HEAP32[$81>>2] = $80;
     $82 = (($67) + ($75)|0);
     HEAP32[$82>>2] = $76;
     $83 = ($33|0)==(0);
     if (!($83)) {
      $84 = HEAP32[(32532)>>2]|0;
      $85 = $33 >>> 3;
      $86 = $85 << 1;
      $87 = (32552 + ($86<<2)|0);
      $88 = 1 << $85;
      $89 = $90 & $88;
      $91 = ($89|0)==(0);
      if ($91) {
       $92 = $90 | $88;
       HEAP32[8128] = $92;
       $$pre = ((($87)) + 8|0);
       $$0194 = $87;$$pre$phiZ2D = $$pre;
      } else {
       $93 = ((($87)) + 8|0);
       $94 = HEAP32[$93>>2]|0;
       $$0194 = $94;$$pre$phiZ2D = $93;
      }
      HEAP32[$$pre$phiZ2D>>2] = $84;
      $95 = ((($$0194)) + 12|0);
      HEAP32[$95>>2] = $84;
      $96 = ((($84)) + 8|0);
      HEAP32[$96>>2] = $$0194;
      $97 = ((($84)) + 12|0);
      HEAP32[$97>>2] = $87;
     }
     HEAP32[(32520)>>2] = $76;
     HEAP32[(32532)>>2] = $79;
     $$0 = $68;
     STACKTOP = sp;return ($$0|0);
    }
    $98 = HEAP32[(32516)>>2]|0;
    $99 = ($98|0)==(0);
    if ($99) {
     $$0192 = $6;
    } else {
     $100 = (0 - ($98))|0;
     $101 = $98 & $100;
     $102 = (($101) + -1)|0;
     $103 = $102 >>> 12;
     $104 = $103 & 16;
     $105 = $102 >>> $104;
     $106 = $105 >>> 5;
     $107 = $106 & 8;
     $108 = $107 | $104;
     $109 = $105 >>> $107;
     $110 = $109 >>> 2;
     $111 = $110 & 4;
     $112 = $108 | $111;
     $113 = $109 >>> $111;
     $114 = $113 >>> 1;
     $115 = $114 & 2;
     $116 = $112 | $115;
     $117 = $113 >>> $115;
     $118 = $117 >>> 1;
     $119 = $118 & 1;
     $120 = $116 | $119;
     $121 = $117 >>> $119;
     $122 = (($120) + ($121))|0;
     $123 = (32816 + ($122<<2)|0);
     $124 = HEAP32[$123>>2]|0;
     $125 = ((($124)) + 4|0);
     $126 = HEAP32[$125>>2]|0;
     $127 = $126 & -8;
     $128 = (($127) - ($6))|0;
     $129 = ((($124)) + 16|0);
     $130 = HEAP32[$129>>2]|0;
     $131 = ($130|0)==(0|0);
     $$sink12$i = $131&1;
     $132 = (((($124)) + 16|0) + ($$sink12$i<<2)|0);
     $133 = HEAP32[$132>>2]|0;
     $134 = ($133|0)==(0|0);
     if ($134) {
      $$0172$lcssa$i = $124;$$0173$lcssa$i = $128;
     } else {
      $$01724$i = $124;$$01733$i = $128;$136 = $133;
      while(1) {
       $135 = ((($136)) + 4|0);
       $137 = HEAP32[$135>>2]|0;
       $138 = $137 & -8;
       $139 = (($138) - ($6))|0;
       $140 = ($139>>>0)<($$01733$i>>>0);
       $$$0173$i = $140 ? $139 : $$01733$i;
       $$$0172$i = $140 ? $136 : $$01724$i;
       $141 = ((($136)) + 16|0);
       $142 = HEAP32[$141>>2]|0;
       $143 = ($142|0)==(0|0);
       $$sink1$i = $143&1;
       $144 = (((($136)) + 16|0) + ($$sink1$i<<2)|0);
       $145 = HEAP32[$144>>2]|0;
       $146 = ($145|0)==(0|0);
       if ($146) {
        $$0172$lcssa$i = $$$0172$i;$$0173$lcssa$i = $$$0173$i;
        break;
       } else {
        $$01724$i = $$$0172$i;$$01733$i = $$$0173$i;$136 = $145;
       }
      }
     }
     $147 = (($$0172$lcssa$i) + ($6)|0);
     $148 = ($147>>>0)>($$0172$lcssa$i>>>0);
     if ($148) {
      $149 = ((($$0172$lcssa$i)) + 24|0);
      $150 = HEAP32[$149>>2]|0;
      $151 = ((($$0172$lcssa$i)) + 12|0);
      $152 = HEAP32[$151>>2]|0;
      $153 = ($152|0)==($$0172$lcssa$i|0);
      do {
       if ($153) {
        $158 = ((($$0172$lcssa$i)) + 20|0);
        $159 = HEAP32[$158>>2]|0;
        $160 = ($159|0)==(0|0);
        if ($160) {
         $161 = ((($$0172$lcssa$i)) + 16|0);
         $162 = HEAP32[$161>>2]|0;
         $163 = ($162|0)==(0|0);
         if ($163) {
          $$3$i = 0;
          break;
         } else {
          $$1176$i = $162;$$1178$i = $161;
         }
        } else {
         $$1176$i = $159;$$1178$i = $158;
        }
        while(1) {
         $164 = ((($$1176$i)) + 20|0);
         $165 = HEAP32[$164>>2]|0;
         $166 = ($165|0)==(0|0);
         if (!($166)) {
          $$1176$i = $165;$$1178$i = $164;
          continue;
         }
         $167 = ((($$1176$i)) + 16|0);
         $168 = HEAP32[$167>>2]|0;
         $169 = ($168|0)==(0|0);
         if ($169) {
          break;
         } else {
          $$1176$i = $168;$$1178$i = $167;
         }
        }
        HEAP32[$$1178$i>>2] = 0;
        $$3$i = $$1176$i;
       } else {
        $154 = ((($$0172$lcssa$i)) + 8|0);
        $155 = HEAP32[$154>>2]|0;
        $156 = ((($155)) + 12|0);
        HEAP32[$156>>2] = $152;
        $157 = ((($152)) + 8|0);
        HEAP32[$157>>2] = $155;
        $$3$i = $152;
       }
      } while(0);
      $170 = ($150|0)==(0|0);
      do {
       if (!($170)) {
        $171 = ((($$0172$lcssa$i)) + 28|0);
        $172 = HEAP32[$171>>2]|0;
        $173 = (32816 + ($172<<2)|0);
        $174 = HEAP32[$173>>2]|0;
        $175 = ($$0172$lcssa$i|0)==($174|0);
        if ($175) {
         HEAP32[$173>>2] = $$3$i;
         $cond$i = ($$3$i|0)==(0|0);
         if ($cond$i) {
          $176 = 1 << $172;
          $177 = $176 ^ -1;
          $178 = $98 & $177;
          HEAP32[(32516)>>2] = $178;
          break;
         }
        } else {
         $179 = ((($150)) + 16|0);
         $180 = HEAP32[$179>>2]|0;
         $181 = ($180|0)!=($$0172$lcssa$i|0);
         $$sink2$i = $181&1;
         $182 = (((($150)) + 16|0) + ($$sink2$i<<2)|0);
         HEAP32[$182>>2] = $$3$i;
         $183 = ($$3$i|0)==(0|0);
         if ($183) {
          break;
         }
        }
        $184 = ((($$3$i)) + 24|0);
        HEAP32[$184>>2] = $150;
        $185 = ((($$0172$lcssa$i)) + 16|0);
        $186 = HEAP32[$185>>2]|0;
        $187 = ($186|0)==(0|0);
        if (!($187)) {
         $188 = ((($$3$i)) + 16|0);
         HEAP32[$188>>2] = $186;
         $189 = ((($186)) + 24|0);
         HEAP32[$189>>2] = $$3$i;
        }
        $190 = ((($$0172$lcssa$i)) + 20|0);
        $191 = HEAP32[$190>>2]|0;
        $192 = ($191|0)==(0|0);
        if (!($192)) {
         $193 = ((($$3$i)) + 20|0);
         HEAP32[$193>>2] = $191;
         $194 = ((($191)) + 24|0);
         HEAP32[$194>>2] = $$3$i;
        }
       }
      } while(0);
      $195 = ($$0173$lcssa$i>>>0)<(16);
      if ($195) {
       $196 = (($$0173$lcssa$i) + ($6))|0;
       $197 = $196 | 3;
       $198 = ((($$0172$lcssa$i)) + 4|0);
       HEAP32[$198>>2] = $197;
       $199 = (($$0172$lcssa$i) + ($196)|0);
       $200 = ((($199)) + 4|0);
       $201 = HEAP32[$200>>2]|0;
       $202 = $201 | 1;
       HEAP32[$200>>2] = $202;
      } else {
       $203 = $6 | 3;
       $204 = ((($$0172$lcssa$i)) + 4|0);
       HEAP32[$204>>2] = $203;
       $205 = $$0173$lcssa$i | 1;
       $206 = ((($147)) + 4|0);
       HEAP32[$206>>2] = $205;
       $207 = (($147) + ($$0173$lcssa$i)|0);
       HEAP32[$207>>2] = $$0173$lcssa$i;
       $208 = ($33|0)==(0);
       if (!($208)) {
        $209 = HEAP32[(32532)>>2]|0;
        $210 = $33 >>> 3;
        $211 = $210 << 1;
        $212 = (32552 + ($211<<2)|0);
        $213 = 1 << $210;
        $214 = $8 & $213;
        $215 = ($214|0)==(0);
        if ($215) {
         $216 = $8 | $213;
         HEAP32[8128] = $216;
         $$pre$i = ((($212)) + 8|0);
         $$0$i = $212;$$pre$phi$iZ2D = $$pre$i;
        } else {
         $217 = ((($212)) + 8|0);
         $218 = HEAP32[$217>>2]|0;
         $$0$i = $218;$$pre$phi$iZ2D = $217;
        }
        HEAP32[$$pre$phi$iZ2D>>2] = $209;
        $219 = ((($$0$i)) + 12|0);
        HEAP32[$219>>2] = $209;
        $220 = ((($209)) + 8|0);
        HEAP32[$220>>2] = $$0$i;
        $221 = ((($209)) + 12|0);
        HEAP32[$221>>2] = $212;
       }
       HEAP32[(32520)>>2] = $$0173$lcssa$i;
       HEAP32[(32532)>>2] = $147;
      }
      $222 = ((($$0172$lcssa$i)) + 8|0);
      $$0 = $222;
      STACKTOP = sp;return ($$0|0);
     } else {
      $$0192 = $6;
     }
    }
   } else {
    $$0192 = $6;
   }
  } else {
   $223 = ($0>>>0)>(4294967231);
   if ($223) {
    $$0192 = -1;
   } else {
    $224 = (($0) + 11)|0;
    $225 = $224 & -8;
    $226 = HEAP32[(32516)>>2]|0;
    $227 = ($226|0)==(0);
    if ($227) {
     $$0192 = $225;
    } else {
     $228 = (0 - ($225))|0;
     $229 = $224 >>> 8;
     $230 = ($229|0)==(0);
     if ($230) {
      $$0336$i = 0;
     } else {
      $231 = ($225>>>0)>(16777215);
      if ($231) {
       $$0336$i = 31;
      } else {
       $232 = (($229) + 1048320)|0;
       $233 = $232 >>> 16;
       $234 = $233 & 8;
       $235 = $229 << $234;
       $236 = (($235) + 520192)|0;
       $237 = $236 >>> 16;
       $238 = $237 & 4;
       $239 = $238 | $234;
       $240 = $235 << $238;
       $241 = (($240) + 245760)|0;
       $242 = $241 >>> 16;
       $243 = $242 & 2;
       $244 = $239 | $243;
       $245 = (14 - ($244))|0;
       $246 = $240 << $243;
       $247 = $246 >>> 15;
       $248 = (($245) + ($247))|0;
       $249 = $248 << 1;
       $250 = (($248) + 7)|0;
       $251 = $225 >>> $250;
       $252 = $251 & 1;
       $253 = $252 | $249;
       $$0336$i = $253;
      }
     }
     $254 = (32816 + ($$0336$i<<2)|0);
     $255 = HEAP32[$254>>2]|0;
     $256 = ($255|0)==(0|0);
     L74: do {
      if ($256) {
       $$2333$i = 0;$$3$i199 = 0;$$3328$i = $228;
       label = 57;
      } else {
       $257 = ($$0336$i|0)==(31);
       $258 = $$0336$i >>> 1;
       $259 = (25 - ($258))|0;
       $260 = $257 ? 0 : $259;
       $261 = $225 << $260;
       $$0320$i = 0;$$0325$i = $228;$$0331$i = $255;$$0337$i = $261;$$0340$i = 0;
       while(1) {
        $262 = ((($$0331$i)) + 4|0);
        $263 = HEAP32[$262>>2]|0;
        $264 = $263 & -8;
        $265 = (($264) - ($225))|0;
        $266 = ($265>>>0)<($$0325$i>>>0);
        if ($266) {
         $267 = ($265|0)==(0);
         if ($267) {
          $$43298$i = 0;$$43357$i = $$0331$i;$$49$i = $$0331$i;
          label = 61;
          break L74;
         } else {
          $$1321$i = $$0331$i;$$1326$i = $265;
         }
        } else {
         $$1321$i = $$0320$i;$$1326$i = $$0325$i;
        }
        $268 = ((($$0331$i)) + 20|0);
        $269 = HEAP32[$268>>2]|0;
        $270 = $$0337$i >>> 31;
        $271 = (((($$0331$i)) + 16|0) + ($270<<2)|0);
        $272 = HEAP32[$271>>2]|0;
        $273 = ($269|0)==(0|0);
        $274 = ($269|0)==($272|0);
        $or$cond1$i198 = $273 | $274;
        $$1341$i = $or$cond1$i198 ? $$0340$i : $269;
        $275 = ($272|0)==(0|0);
        $not$3$i = $275 ^ 1;
        $276 = $not$3$i&1;
        $$0337$$i = $$0337$i << $276;
        if ($275) {
         $$2333$i = $$1341$i;$$3$i199 = $$1321$i;$$3328$i = $$1326$i;
         label = 57;
         break;
        } else {
         $$0320$i = $$1321$i;$$0325$i = $$1326$i;$$0331$i = $272;$$0337$i = $$0337$$i;$$0340$i = $$1341$i;
        }
       }
      }
     } while(0);
     if ((label|0) == 57) {
      $277 = ($$2333$i|0)==(0|0);
      $278 = ($$3$i199|0)==(0|0);
      $or$cond$i200 = $277 & $278;
      if ($or$cond$i200) {
       $279 = 2 << $$0336$i;
       $280 = (0 - ($279))|0;
       $281 = $279 | $280;
       $282 = $226 & $281;
       $283 = ($282|0)==(0);
       if ($283) {
        $$0192 = $225;
        break;
       }
       $284 = (0 - ($282))|0;
       $285 = $282 & $284;
       $286 = (($285) + -1)|0;
       $287 = $286 >>> 12;
       $288 = $287 & 16;
       $289 = $286 >>> $288;
       $290 = $289 >>> 5;
       $291 = $290 & 8;
       $292 = $291 | $288;
       $293 = $289 >>> $291;
       $294 = $293 >>> 2;
       $295 = $294 & 4;
       $296 = $292 | $295;
       $297 = $293 >>> $295;
       $298 = $297 >>> 1;
       $299 = $298 & 2;
       $300 = $296 | $299;
       $301 = $297 >>> $299;
       $302 = $301 >>> 1;
       $303 = $302 & 1;
       $304 = $300 | $303;
       $305 = $301 >>> $303;
       $306 = (($304) + ($305))|0;
       $307 = (32816 + ($306<<2)|0);
       $308 = HEAP32[$307>>2]|0;
       $$4$ph$i = 0;$$4335$ph$i = $308;
      } else {
       $$4$ph$i = $$3$i199;$$4335$ph$i = $$2333$i;
      }
      $309 = ($$4335$ph$i|0)==(0|0);
      if ($309) {
       $$4$lcssa$i = $$4$ph$i;$$4329$lcssa$i = $$3328$i;
      } else {
       $$43298$i = $$3328$i;$$43357$i = $$4335$ph$i;$$49$i = $$4$ph$i;
       label = 61;
      }
     }
     if ((label|0) == 61) {
      while(1) {
       label = 0;
       $310 = ((($$43357$i)) + 4|0);
       $311 = HEAP32[$310>>2]|0;
       $312 = $311 & -8;
       $313 = (($312) - ($225))|0;
       $314 = ($313>>>0)<($$43298$i>>>0);
       $$$4329$i = $314 ? $313 : $$43298$i;
       $$4335$$4$i = $314 ? $$43357$i : $$49$i;
       $315 = ((($$43357$i)) + 16|0);
       $316 = HEAP32[$315>>2]|0;
       $317 = ($316|0)==(0|0);
       $$sink2$i202 = $317&1;
       $318 = (((($$43357$i)) + 16|0) + ($$sink2$i202<<2)|0);
       $319 = HEAP32[$318>>2]|0;
       $320 = ($319|0)==(0|0);
       if ($320) {
        $$4$lcssa$i = $$4335$$4$i;$$4329$lcssa$i = $$$4329$i;
        break;
       } else {
        $$43298$i = $$$4329$i;$$43357$i = $319;$$49$i = $$4335$$4$i;
        label = 61;
       }
      }
     }
     $321 = ($$4$lcssa$i|0)==(0|0);
     if ($321) {
      $$0192 = $225;
     } else {
      $322 = HEAP32[(32520)>>2]|0;
      $323 = (($322) - ($225))|0;
      $324 = ($$4329$lcssa$i>>>0)<($323>>>0);
      if ($324) {
       $325 = (($$4$lcssa$i) + ($225)|0);
       $326 = ($325>>>0)>($$4$lcssa$i>>>0);
       if (!($326)) {
        $$0 = 0;
        STACKTOP = sp;return ($$0|0);
       }
       $327 = ((($$4$lcssa$i)) + 24|0);
       $328 = HEAP32[$327>>2]|0;
       $329 = ((($$4$lcssa$i)) + 12|0);
       $330 = HEAP32[$329>>2]|0;
       $331 = ($330|0)==($$4$lcssa$i|0);
       do {
        if ($331) {
         $336 = ((($$4$lcssa$i)) + 20|0);
         $337 = HEAP32[$336>>2]|0;
         $338 = ($337|0)==(0|0);
         if ($338) {
          $339 = ((($$4$lcssa$i)) + 16|0);
          $340 = HEAP32[$339>>2]|0;
          $341 = ($340|0)==(0|0);
          if ($341) {
           $$3349$i = 0;
           break;
          } else {
           $$1347$i = $340;$$1351$i = $339;
          }
         } else {
          $$1347$i = $337;$$1351$i = $336;
         }
         while(1) {
          $342 = ((($$1347$i)) + 20|0);
          $343 = HEAP32[$342>>2]|0;
          $344 = ($343|0)==(0|0);
          if (!($344)) {
           $$1347$i = $343;$$1351$i = $342;
           continue;
          }
          $345 = ((($$1347$i)) + 16|0);
          $346 = HEAP32[$345>>2]|0;
          $347 = ($346|0)==(0|0);
          if ($347) {
           break;
          } else {
           $$1347$i = $346;$$1351$i = $345;
          }
         }
         HEAP32[$$1351$i>>2] = 0;
         $$3349$i = $$1347$i;
        } else {
         $332 = ((($$4$lcssa$i)) + 8|0);
         $333 = HEAP32[$332>>2]|0;
         $334 = ((($333)) + 12|0);
         HEAP32[$334>>2] = $330;
         $335 = ((($330)) + 8|0);
         HEAP32[$335>>2] = $333;
         $$3349$i = $330;
        }
       } while(0);
       $348 = ($328|0)==(0|0);
       do {
        if ($348) {
         $431 = $226;
        } else {
         $349 = ((($$4$lcssa$i)) + 28|0);
         $350 = HEAP32[$349>>2]|0;
         $351 = (32816 + ($350<<2)|0);
         $352 = HEAP32[$351>>2]|0;
         $353 = ($$4$lcssa$i|0)==($352|0);
         if ($353) {
          HEAP32[$351>>2] = $$3349$i;
          $cond$i206 = ($$3349$i|0)==(0|0);
          if ($cond$i206) {
           $354 = 1 << $350;
           $355 = $354 ^ -1;
           $356 = $226 & $355;
           HEAP32[(32516)>>2] = $356;
           $431 = $356;
           break;
          }
         } else {
          $357 = ((($328)) + 16|0);
          $358 = HEAP32[$357>>2]|0;
          $359 = ($358|0)!=($$4$lcssa$i|0);
          $$sink3$i = $359&1;
          $360 = (((($328)) + 16|0) + ($$sink3$i<<2)|0);
          HEAP32[$360>>2] = $$3349$i;
          $361 = ($$3349$i|0)==(0|0);
          if ($361) {
           $431 = $226;
           break;
          }
         }
         $362 = ((($$3349$i)) + 24|0);
         HEAP32[$362>>2] = $328;
         $363 = ((($$4$lcssa$i)) + 16|0);
         $364 = HEAP32[$363>>2]|0;
         $365 = ($364|0)==(0|0);
         if (!($365)) {
          $366 = ((($$3349$i)) + 16|0);
          HEAP32[$366>>2] = $364;
          $367 = ((($364)) + 24|0);
          HEAP32[$367>>2] = $$3349$i;
         }
         $368 = ((($$4$lcssa$i)) + 20|0);
         $369 = HEAP32[$368>>2]|0;
         $370 = ($369|0)==(0|0);
         if ($370) {
          $431 = $226;
         } else {
          $371 = ((($$3349$i)) + 20|0);
          HEAP32[$371>>2] = $369;
          $372 = ((($369)) + 24|0);
          HEAP32[$372>>2] = $$3349$i;
          $431 = $226;
         }
        }
       } while(0);
       $373 = ($$4329$lcssa$i>>>0)<(16);
       do {
        if ($373) {
         $374 = (($$4329$lcssa$i) + ($225))|0;
         $375 = $374 | 3;
         $376 = ((($$4$lcssa$i)) + 4|0);
         HEAP32[$376>>2] = $375;
         $377 = (($$4$lcssa$i) + ($374)|0);
         $378 = ((($377)) + 4|0);
         $379 = HEAP32[$378>>2]|0;
         $380 = $379 | 1;
         HEAP32[$378>>2] = $380;
        } else {
         $381 = $225 | 3;
         $382 = ((($$4$lcssa$i)) + 4|0);
         HEAP32[$382>>2] = $381;
         $383 = $$4329$lcssa$i | 1;
         $384 = ((($325)) + 4|0);
         HEAP32[$384>>2] = $383;
         $385 = (($325) + ($$4329$lcssa$i)|0);
         HEAP32[$385>>2] = $$4329$lcssa$i;
         $386 = $$4329$lcssa$i >>> 3;
         $387 = ($$4329$lcssa$i>>>0)<(256);
         if ($387) {
          $388 = $386 << 1;
          $389 = (32552 + ($388<<2)|0);
          $390 = HEAP32[8128]|0;
          $391 = 1 << $386;
          $392 = $390 & $391;
          $393 = ($392|0)==(0);
          if ($393) {
           $394 = $390 | $391;
           HEAP32[8128] = $394;
           $$pre$i207 = ((($389)) + 8|0);
           $$0345$i = $389;$$pre$phi$i208Z2D = $$pre$i207;
          } else {
           $395 = ((($389)) + 8|0);
           $396 = HEAP32[$395>>2]|0;
           $$0345$i = $396;$$pre$phi$i208Z2D = $395;
          }
          HEAP32[$$pre$phi$i208Z2D>>2] = $325;
          $397 = ((($$0345$i)) + 12|0);
          HEAP32[$397>>2] = $325;
          $398 = ((($325)) + 8|0);
          HEAP32[$398>>2] = $$0345$i;
          $399 = ((($325)) + 12|0);
          HEAP32[$399>>2] = $389;
          break;
         }
         $400 = $$4329$lcssa$i >>> 8;
         $401 = ($400|0)==(0);
         if ($401) {
          $$0339$i = 0;
         } else {
          $402 = ($$4329$lcssa$i>>>0)>(16777215);
          if ($402) {
           $$0339$i = 31;
          } else {
           $403 = (($400) + 1048320)|0;
           $404 = $403 >>> 16;
           $405 = $404 & 8;
           $406 = $400 << $405;
           $407 = (($406) + 520192)|0;
           $408 = $407 >>> 16;
           $409 = $408 & 4;
           $410 = $409 | $405;
           $411 = $406 << $409;
           $412 = (($411) + 245760)|0;
           $413 = $412 >>> 16;
           $414 = $413 & 2;
           $415 = $410 | $414;
           $416 = (14 - ($415))|0;
           $417 = $411 << $414;
           $418 = $417 >>> 15;
           $419 = (($416) + ($418))|0;
           $420 = $419 << 1;
           $421 = (($419) + 7)|0;
           $422 = $$4329$lcssa$i >>> $421;
           $423 = $422 & 1;
           $424 = $423 | $420;
           $$0339$i = $424;
          }
         }
         $425 = (32816 + ($$0339$i<<2)|0);
         $426 = ((($325)) + 28|0);
         HEAP32[$426>>2] = $$0339$i;
         $427 = ((($325)) + 16|0);
         $428 = ((($427)) + 4|0);
         HEAP32[$428>>2] = 0;
         HEAP32[$427>>2] = 0;
         $429 = 1 << $$0339$i;
         $430 = $431 & $429;
         $432 = ($430|0)==(0);
         if ($432) {
          $433 = $431 | $429;
          HEAP32[(32516)>>2] = $433;
          HEAP32[$425>>2] = $325;
          $434 = ((($325)) + 24|0);
          HEAP32[$434>>2] = $425;
          $435 = ((($325)) + 12|0);
          HEAP32[$435>>2] = $325;
          $436 = ((($325)) + 8|0);
          HEAP32[$436>>2] = $325;
          break;
         }
         $437 = HEAP32[$425>>2]|0;
         $438 = ($$0339$i|0)==(31);
         $439 = $$0339$i >>> 1;
         $440 = (25 - ($439))|0;
         $441 = $438 ? 0 : $440;
         $442 = $$4329$lcssa$i << $441;
         $$0322$i = $442;$$0323$i = $437;
         while(1) {
          $443 = ((($$0323$i)) + 4|0);
          $444 = HEAP32[$443>>2]|0;
          $445 = $444 & -8;
          $446 = ($445|0)==($$4329$lcssa$i|0);
          if ($446) {
           label = 97;
           break;
          }
          $447 = $$0322$i >>> 31;
          $448 = (((($$0323$i)) + 16|0) + ($447<<2)|0);
          $449 = $$0322$i << 1;
          $450 = HEAP32[$448>>2]|0;
          $451 = ($450|0)==(0|0);
          if ($451) {
           label = 96;
           break;
          } else {
           $$0322$i = $449;$$0323$i = $450;
          }
         }
         if ((label|0) == 96) {
          HEAP32[$448>>2] = $325;
          $452 = ((($325)) + 24|0);
          HEAP32[$452>>2] = $$0323$i;
          $453 = ((($325)) + 12|0);
          HEAP32[$453>>2] = $325;
          $454 = ((($325)) + 8|0);
          HEAP32[$454>>2] = $325;
          break;
         }
         else if ((label|0) == 97) {
          $455 = ((($$0323$i)) + 8|0);
          $456 = HEAP32[$455>>2]|0;
          $457 = ((($456)) + 12|0);
          HEAP32[$457>>2] = $325;
          HEAP32[$455>>2] = $325;
          $458 = ((($325)) + 8|0);
          HEAP32[$458>>2] = $456;
          $459 = ((($325)) + 12|0);
          HEAP32[$459>>2] = $$0323$i;
          $460 = ((($325)) + 24|0);
          HEAP32[$460>>2] = 0;
          break;
         }
        }
       } while(0);
       $461 = ((($$4$lcssa$i)) + 8|0);
       $$0 = $461;
       STACKTOP = sp;return ($$0|0);
      } else {
       $$0192 = $225;
      }
     }
    }
   }
  }
 } while(0);
 $462 = HEAP32[(32520)>>2]|0;
 $463 = ($462>>>0)<($$0192>>>0);
 if (!($463)) {
  $464 = (($462) - ($$0192))|0;
  $465 = HEAP32[(32532)>>2]|0;
  $466 = ($464>>>0)>(15);
  if ($466) {
   $467 = (($465) + ($$0192)|0);
   HEAP32[(32532)>>2] = $467;
   HEAP32[(32520)>>2] = $464;
   $468 = $464 | 1;
   $469 = ((($467)) + 4|0);
   HEAP32[$469>>2] = $468;
   $470 = (($465) + ($462)|0);
   HEAP32[$470>>2] = $464;
   $471 = $$0192 | 3;
   $472 = ((($465)) + 4|0);
   HEAP32[$472>>2] = $471;
  } else {
   HEAP32[(32520)>>2] = 0;
   HEAP32[(32532)>>2] = 0;
   $473 = $462 | 3;
   $474 = ((($465)) + 4|0);
   HEAP32[$474>>2] = $473;
   $475 = (($465) + ($462)|0);
   $476 = ((($475)) + 4|0);
   $477 = HEAP32[$476>>2]|0;
   $478 = $477 | 1;
   HEAP32[$476>>2] = $478;
  }
  $479 = ((($465)) + 8|0);
  $$0 = $479;
  STACKTOP = sp;return ($$0|0);
 }
 $480 = HEAP32[(32524)>>2]|0;
 $481 = ($480>>>0)>($$0192>>>0);
 if ($481) {
  $482 = (($480) - ($$0192))|0;
  HEAP32[(32524)>>2] = $482;
  $483 = HEAP32[(32536)>>2]|0;
  $484 = (($483) + ($$0192)|0);
  HEAP32[(32536)>>2] = $484;
  $485 = $482 | 1;
  $486 = ((($484)) + 4|0);
  HEAP32[$486>>2] = $485;
  $487 = $$0192 | 3;
  $488 = ((($483)) + 4|0);
  HEAP32[$488>>2] = $487;
  $489 = ((($483)) + 8|0);
  $$0 = $489;
  STACKTOP = sp;return ($$0|0);
 }
 $490 = HEAP32[8246]|0;
 $491 = ($490|0)==(0);
 if ($491) {
  HEAP32[(32992)>>2] = 4096;
  HEAP32[(32988)>>2] = 4096;
  HEAP32[(32996)>>2] = -1;
  HEAP32[(33000)>>2] = -1;
  HEAP32[(33004)>>2] = 0;
  HEAP32[(32956)>>2] = 0;
  $492 = $1;
  $493 = $492 & -16;
  $494 = $493 ^ 1431655768;
  HEAP32[8246] = $494;
  $498 = 4096;
 } else {
  $$pre$i195 = HEAP32[(32992)>>2]|0;
  $498 = $$pre$i195;
 }
 $495 = (($$0192) + 48)|0;
 $496 = (($$0192) + 47)|0;
 $497 = (($498) + ($496))|0;
 $499 = (0 - ($498))|0;
 $500 = $497 & $499;
 $501 = ($500>>>0)>($$0192>>>0);
 if (!($501)) {
  $$0 = 0;
  STACKTOP = sp;return ($$0|0);
 }
 $502 = HEAP32[(32952)>>2]|0;
 $503 = ($502|0)==(0);
 if (!($503)) {
  $504 = HEAP32[(32944)>>2]|0;
  $505 = (($504) + ($500))|0;
  $506 = ($505>>>0)<=($504>>>0);
  $507 = ($505>>>0)>($502>>>0);
  $or$cond1$i = $506 | $507;
  if ($or$cond1$i) {
   $$0 = 0;
   STACKTOP = sp;return ($$0|0);
  }
 }
 $508 = HEAP32[(32956)>>2]|0;
 $509 = $508 & 4;
 $510 = ($509|0)==(0);
 L167: do {
  if ($510) {
   $511 = HEAP32[(32536)>>2]|0;
   $512 = ($511|0)==(0|0);
   L169: do {
    if ($512) {
     label = 118;
    } else {
     $$0$i20$i = (32960);
     while(1) {
      $513 = HEAP32[$$0$i20$i>>2]|0;
      $514 = ($513>>>0)>($511>>>0);
      if (!($514)) {
       $515 = ((($$0$i20$i)) + 4|0);
       $516 = HEAP32[$515>>2]|0;
       $517 = (($513) + ($516)|0);
       $518 = ($517>>>0)>($511>>>0);
       if ($518) {
        break;
       }
      }
      $519 = ((($$0$i20$i)) + 8|0);
      $520 = HEAP32[$519>>2]|0;
      $521 = ($520|0)==(0|0);
      if ($521) {
       label = 118;
       break L169;
      } else {
       $$0$i20$i = $520;
      }
     }
     $544 = (($497) - ($480))|0;
     $545 = $544 & $499;
     $546 = ($545>>>0)<(2147483647);
     if ($546) {
      $547 = (_sbrk(($545|0))|0);
      $548 = HEAP32[$$0$i20$i>>2]|0;
      $549 = HEAP32[$515>>2]|0;
      $550 = (($548) + ($549)|0);
      $551 = ($547|0)==($550|0);
      if ($551) {
       $552 = ($547|0)==((-1)|0);
       if ($552) {
        $$2234243136$i = $545;
       } else {
        $$723947$i = $545;$$748$i = $547;
        label = 135;
        break L167;
       }
      } else {
       $$2247$ph$i = $547;$$2253$ph$i = $545;
       label = 126;
      }
     } else {
      $$2234243136$i = 0;
     }
    }
   } while(0);
   do {
    if ((label|0) == 118) {
     $522 = (_sbrk(0)|0);
     $523 = ($522|0)==((-1)|0);
     if ($523) {
      $$2234243136$i = 0;
     } else {
      $524 = $522;
      $525 = HEAP32[(32988)>>2]|0;
      $526 = (($525) + -1)|0;
      $527 = $526 & $524;
      $528 = ($527|0)==(0);
      $529 = (($526) + ($524))|0;
      $530 = (0 - ($525))|0;
      $531 = $529 & $530;
      $532 = (($531) - ($524))|0;
      $533 = $528 ? 0 : $532;
      $$$i = (($533) + ($500))|0;
      $534 = HEAP32[(32944)>>2]|0;
      $535 = (($$$i) + ($534))|0;
      $536 = ($$$i>>>0)>($$0192>>>0);
      $537 = ($$$i>>>0)<(2147483647);
      $or$cond$i = $536 & $537;
      if ($or$cond$i) {
       $538 = HEAP32[(32952)>>2]|0;
       $539 = ($538|0)==(0);
       if (!($539)) {
        $540 = ($535>>>0)<=($534>>>0);
        $541 = ($535>>>0)>($538>>>0);
        $or$cond2$i = $540 | $541;
        if ($or$cond2$i) {
         $$2234243136$i = 0;
         break;
        }
       }
       $542 = (_sbrk(($$$i|0))|0);
       $543 = ($542|0)==($522|0);
       if ($543) {
        $$723947$i = $$$i;$$748$i = $522;
        label = 135;
        break L167;
       } else {
        $$2247$ph$i = $542;$$2253$ph$i = $$$i;
        label = 126;
       }
      } else {
       $$2234243136$i = 0;
      }
     }
    }
   } while(0);
   do {
    if ((label|0) == 126) {
     $553 = (0 - ($$2253$ph$i))|0;
     $554 = ($$2247$ph$i|0)!=((-1)|0);
     $555 = ($$2253$ph$i>>>0)<(2147483647);
     $or$cond7$i = $555 & $554;
     $556 = ($495>>>0)>($$2253$ph$i>>>0);
     $or$cond10$i = $556 & $or$cond7$i;
     if (!($or$cond10$i)) {
      $566 = ($$2247$ph$i|0)==((-1)|0);
      if ($566) {
       $$2234243136$i = 0;
       break;
      } else {
       $$723947$i = $$2253$ph$i;$$748$i = $$2247$ph$i;
       label = 135;
       break L167;
      }
     }
     $557 = HEAP32[(32992)>>2]|0;
     $558 = (($496) - ($$2253$ph$i))|0;
     $559 = (($558) + ($557))|0;
     $560 = (0 - ($557))|0;
     $561 = $559 & $560;
     $562 = ($561>>>0)<(2147483647);
     if (!($562)) {
      $$723947$i = $$2253$ph$i;$$748$i = $$2247$ph$i;
      label = 135;
      break L167;
     }
     $563 = (_sbrk(($561|0))|0);
     $564 = ($563|0)==((-1)|0);
     if ($564) {
      (_sbrk(($553|0))|0);
      $$2234243136$i = 0;
      break;
     } else {
      $565 = (($561) + ($$2253$ph$i))|0;
      $$723947$i = $565;$$748$i = $$2247$ph$i;
      label = 135;
      break L167;
     }
    }
   } while(0);
   $567 = HEAP32[(32956)>>2]|0;
   $568 = $567 | 4;
   HEAP32[(32956)>>2] = $568;
   $$4236$i = $$2234243136$i;
   label = 133;
  } else {
   $$4236$i = 0;
   label = 133;
  }
 } while(0);
 if ((label|0) == 133) {
  $569 = ($500>>>0)<(2147483647);
  if ($569) {
   $570 = (_sbrk(($500|0))|0);
   $571 = (_sbrk(0)|0);
   $572 = ($570|0)!=((-1)|0);
   $573 = ($571|0)!=((-1)|0);
   $or$cond5$i = $572 & $573;
   $574 = ($570>>>0)<($571>>>0);
   $or$cond11$i = $574 & $or$cond5$i;
   $575 = $571;
   $576 = $570;
   $577 = (($575) - ($576))|0;
   $578 = (($$0192) + 40)|0;
   $579 = ($577>>>0)>($578>>>0);
   $$$4236$i = $579 ? $577 : $$4236$i;
   $or$cond11$not$i = $or$cond11$i ^ 1;
   $580 = ($570|0)==((-1)|0);
   $not$$i = $579 ^ 1;
   $581 = $580 | $not$$i;
   $or$cond49$i = $581 | $or$cond11$not$i;
   if (!($or$cond49$i)) {
    $$723947$i = $$$4236$i;$$748$i = $570;
    label = 135;
   }
  }
 }
 if ((label|0) == 135) {
  $582 = HEAP32[(32944)>>2]|0;
  $583 = (($582) + ($$723947$i))|0;
  HEAP32[(32944)>>2] = $583;
  $584 = HEAP32[(32948)>>2]|0;
  $585 = ($583>>>0)>($584>>>0);
  if ($585) {
   HEAP32[(32948)>>2] = $583;
  }
  $586 = HEAP32[(32536)>>2]|0;
  $587 = ($586|0)==(0|0);
  do {
   if ($587) {
    $588 = HEAP32[(32528)>>2]|0;
    $589 = ($588|0)==(0|0);
    $590 = ($$748$i>>>0)<($588>>>0);
    $or$cond12$i = $589 | $590;
    if ($or$cond12$i) {
     HEAP32[(32528)>>2] = $$748$i;
    }
    HEAP32[(32960)>>2] = $$748$i;
    HEAP32[(32964)>>2] = $$723947$i;
    HEAP32[(32972)>>2] = 0;
    $591 = HEAP32[8246]|0;
    HEAP32[(32548)>>2] = $591;
    HEAP32[(32544)>>2] = -1;
    HEAP32[(32564)>>2] = (32552);
    HEAP32[(32560)>>2] = (32552);
    HEAP32[(32572)>>2] = (32560);
    HEAP32[(32568)>>2] = (32560);
    HEAP32[(32580)>>2] = (32568);
    HEAP32[(32576)>>2] = (32568);
    HEAP32[(32588)>>2] = (32576);
    HEAP32[(32584)>>2] = (32576);
    HEAP32[(32596)>>2] = (32584);
    HEAP32[(32592)>>2] = (32584);
    HEAP32[(32604)>>2] = (32592);
    HEAP32[(32600)>>2] = (32592);
    HEAP32[(32612)>>2] = (32600);
    HEAP32[(32608)>>2] = (32600);
    HEAP32[(32620)>>2] = (32608);
    HEAP32[(32616)>>2] = (32608);
    HEAP32[(32628)>>2] = (32616);
    HEAP32[(32624)>>2] = (32616);
    HEAP32[(32636)>>2] = (32624);
    HEAP32[(32632)>>2] = (32624);
    HEAP32[(32644)>>2] = (32632);
    HEAP32[(32640)>>2] = (32632);
    HEAP32[(32652)>>2] = (32640);
    HEAP32[(32648)>>2] = (32640);
    HEAP32[(32660)>>2] = (32648);
    HEAP32[(32656)>>2] = (32648);
    HEAP32[(32668)>>2] = (32656);
    HEAP32[(32664)>>2] = (32656);
    HEAP32[(32676)>>2] = (32664);
    HEAP32[(32672)>>2] = (32664);
    HEAP32[(32684)>>2] = (32672);
    HEAP32[(32680)>>2] = (32672);
    HEAP32[(32692)>>2] = (32680);
    HEAP32[(32688)>>2] = (32680);
    HEAP32[(32700)>>2] = (32688);
    HEAP32[(32696)>>2] = (32688);
    HEAP32[(32708)>>2] = (32696);
    HEAP32[(32704)>>2] = (32696);
    HEAP32[(32716)>>2] = (32704);
    HEAP32[(32712)>>2] = (32704);
    HEAP32[(32724)>>2] = (32712);
    HEAP32[(32720)>>2] = (32712);
    HEAP32[(32732)>>2] = (32720);
    HEAP32[(32728)>>2] = (32720);
    HEAP32[(32740)>>2] = (32728);
    HEAP32[(32736)>>2] = (32728);
    HEAP32[(32748)>>2] = (32736);
    HEAP32[(32744)>>2] = (32736);
    HEAP32[(32756)>>2] = (32744);
    HEAP32[(32752)>>2] = (32744);
    HEAP32[(32764)>>2] = (32752);
    HEAP32[(32760)>>2] = (32752);
    HEAP32[(32772)>>2] = (32760);
    HEAP32[(32768)>>2] = (32760);
    HEAP32[(32780)>>2] = (32768);
    HEAP32[(32776)>>2] = (32768);
    HEAP32[(32788)>>2] = (32776);
    HEAP32[(32784)>>2] = (32776);
    HEAP32[(32796)>>2] = (32784);
    HEAP32[(32792)>>2] = (32784);
    HEAP32[(32804)>>2] = (32792);
    HEAP32[(32800)>>2] = (32792);
    HEAP32[(32812)>>2] = (32800);
    HEAP32[(32808)>>2] = (32800);
    $592 = (($$723947$i) + -40)|0;
    $593 = ((($$748$i)) + 8|0);
    $594 = $593;
    $595 = $594 & 7;
    $596 = ($595|0)==(0);
    $597 = (0 - ($594))|0;
    $598 = $597 & 7;
    $599 = $596 ? 0 : $598;
    $600 = (($$748$i) + ($599)|0);
    $601 = (($592) - ($599))|0;
    HEAP32[(32536)>>2] = $600;
    HEAP32[(32524)>>2] = $601;
    $602 = $601 | 1;
    $603 = ((($600)) + 4|0);
    HEAP32[$603>>2] = $602;
    $604 = (($$748$i) + ($592)|0);
    $605 = ((($604)) + 4|0);
    HEAP32[$605>>2] = 40;
    $606 = HEAP32[(33000)>>2]|0;
    HEAP32[(32540)>>2] = $606;
   } else {
    $$024367$i = (32960);
    while(1) {
     $607 = HEAP32[$$024367$i>>2]|0;
     $608 = ((($$024367$i)) + 4|0);
     $609 = HEAP32[$608>>2]|0;
     $610 = (($607) + ($609)|0);
     $611 = ($$748$i|0)==($610|0);
     if ($611) {
      label = 143;
      break;
     }
     $612 = ((($$024367$i)) + 8|0);
     $613 = HEAP32[$612>>2]|0;
     $614 = ($613|0)==(0|0);
     if ($614) {
      break;
     } else {
      $$024367$i = $613;
     }
    }
    if ((label|0) == 143) {
     $615 = ((($$024367$i)) + 12|0);
     $616 = HEAP32[$615>>2]|0;
     $617 = $616 & 8;
     $618 = ($617|0)==(0);
     if ($618) {
      $619 = ($607>>>0)<=($586>>>0);
      $620 = ($$748$i>>>0)>($586>>>0);
      $or$cond50$i = $620 & $619;
      if ($or$cond50$i) {
       $621 = (($609) + ($$723947$i))|0;
       HEAP32[$608>>2] = $621;
       $622 = HEAP32[(32524)>>2]|0;
       $623 = (($622) + ($$723947$i))|0;
       $624 = ((($586)) + 8|0);
       $625 = $624;
       $626 = $625 & 7;
       $627 = ($626|0)==(0);
       $628 = (0 - ($625))|0;
       $629 = $628 & 7;
       $630 = $627 ? 0 : $629;
       $631 = (($586) + ($630)|0);
       $632 = (($623) - ($630))|0;
       HEAP32[(32536)>>2] = $631;
       HEAP32[(32524)>>2] = $632;
       $633 = $632 | 1;
       $634 = ((($631)) + 4|0);
       HEAP32[$634>>2] = $633;
       $635 = (($586) + ($623)|0);
       $636 = ((($635)) + 4|0);
       HEAP32[$636>>2] = 40;
       $637 = HEAP32[(33000)>>2]|0;
       HEAP32[(32540)>>2] = $637;
       break;
      }
     }
    }
    $638 = HEAP32[(32528)>>2]|0;
    $639 = ($$748$i>>>0)<($638>>>0);
    if ($639) {
     HEAP32[(32528)>>2] = $$748$i;
    }
    $640 = (($$748$i) + ($$723947$i)|0);
    $$124466$i = (32960);
    while(1) {
     $641 = HEAP32[$$124466$i>>2]|0;
     $642 = ($641|0)==($640|0);
     if ($642) {
      label = 151;
      break;
     }
     $643 = ((($$124466$i)) + 8|0);
     $644 = HEAP32[$643>>2]|0;
     $645 = ($644|0)==(0|0);
     if ($645) {
      $$0$i$i$i = (32960);
      break;
     } else {
      $$124466$i = $644;
     }
    }
    if ((label|0) == 151) {
     $646 = ((($$124466$i)) + 12|0);
     $647 = HEAP32[$646>>2]|0;
     $648 = $647 & 8;
     $649 = ($648|0)==(0);
     if ($649) {
      HEAP32[$$124466$i>>2] = $$748$i;
      $650 = ((($$124466$i)) + 4|0);
      $651 = HEAP32[$650>>2]|0;
      $652 = (($651) + ($$723947$i))|0;
      HEAP32[$650>>2] = $652;
      $653 = ((($$748$i)) + 8|0);
      $654 = $653;
      $655 = $654 & 7;
      $656 = ($655|0)==(0);
      $657 = (0 - ($654))|0;
      $658 = $657 & 7;
      $659 = $656 ? 0 : $658;
      $660 = (($$748$i) + ($659)|0);
      $661 = ((($640)) + 8|0);
      $662 = $661;
      $663 = $662 & 7;
      $664 = ($663|0)==(0);
      $665 = (0 - ($662))|0;
      $666 = $665 & 7;
      $667 = $664 ? 0 : $666;
      $668 = (($640) + ($667)|0);
      $669 = $668;
      $670 = $660;
      $671 = (($669) - ($670))|0;
      $672 = (($660) + ($$0192)|0);
      $673 = (($671) - ($$0192))|0;
      $674 = $$0192 | 3;
      $675 = ((($660)) + 4|0);
      HEAP32[$675>>2] = $674;
      $676 = ($586|0)==($668|0);
      do {
       if ($676) {
        $677 = HEAP32[(32524)>>2]|0;
        $678 = (($677) + ($673))|0;
        HEAP32[(32524)>>2] = $678;
        HEAP32[(32536)>>2] = $672;
        $679 = $678 | 1;
        $680 = ((($672)) + 4|0);
        HEAP32[$680>>2] = $679;
       } else {
        $681 = HEAP32[(32532)>>2]|0;
        $682 = ($681|0)==($668|0);
        if ($682) {
         $683 = HEAP32[(32520)>>2]|0;
         $684 = (($683) + ($673))|0;
         HEAP32[(32520)>>2] = $684;
         HEAP32[(32532)>>2] = $672;
         $685 = $684 | 1;
         $686 = ((($672)) + 4|0);
         HEAP32[$686>>2] = $685;
         $687 = (($672) + ($684)|0);
         HEAP32[$687>>2] = $684;
         break;
        }
        $688 = ((($668)) + 4|0);
        $689 = HEAP32[$688>>2]|0;
        $690 = $689 & 3;
        $691 = ($690|0)==(1);
        if ($691) {
         $692 = $689 & -8;
         $693 = $689 >>> 3;
         $694 = ($689>>>0)<(256);
         L234: do {
          if ($694) {
           $695 = ((($668)) + 8|0);
           $696 = HEAP32[$695>>2]|0;
           $697 = ((($668)) + 12|0);
           $698 = HEAP32[$697>>2]|0;
           $699 = ($698|0)==($696|0);
           if ($699) {
            $700 = 1 << $693;
            $701 = $700 ^ -1;
            $702 = HEAP32[8128]|0;
            $703 = $702 & $701;
            HEAP32[8128] = $703;
            break;
           } else {
            $704 = ((($696)) + 12|0);
            HEAP32[$704>>2] = $698;
            $705 = ((($698)) + 8|0);
            HEAP32[$705>>2] = $696;
            break;
           }
          } else {
           $706 = ((($668)) + 24|0);
           $707 = HEAP32[$706>>2]|0;
           $708 = ((($668)) + 12|0);
           $709 = HEAP32[$708>>2]|0;
           $710 = ($709|0)==($668|0);
           do {
            if ($710) {
             $715 = ((($668)) + 16|0);
             $716 = ((($715)) + 4|0);
             $717 = HEAP32[$716>>2]|0;
             $718 = ($717|0)==(0|0);
             if ($718) {
              $719 = HEAP32[$715>>2]|0;
              $720 = ($719|0)==(0|0);
              if ($720) {
               $$3$i$i = 0;
               break;
              } else {
               $$1264$i$i = $719;$$1266$i$i = $715;
              }
             } else {
              $$1264$i$i = $717;$$1266$i$i = $716;
             }
             while(1) {
              $721 = ((($$1264$i$i)) + 20|0);
              $722 = HEAP32[$721>>2]|0;
              $723 = ($722|0)==(0|0);
              if (!($723)) {
               $$1264$i$i = $722;$$1266$i$i = $721;
               continue;
              }
              $724 = ((($$1264$i$i)) + 16|0);
              $725 = HEAP32[$724>>2]|0;
              $726 = ($725|0)==(0|0);
              if ($726) {
               break;
              } else {
               $$1264$i$i = $725;$$1266$i$i = $724;
              }
             }
             HEAP32[$$1266$i$i>>2] = 0;
             $$3$i$i = $$1264$i$i;
            } else {
             $711 = ((($668)) + 8|0);
             $712 = HEAP32[$711>>2]|0;
             $713 = ((($712)) + 12|0);
             HEAP32[$713>>2] = $709;
             $714 = ((($709)) + 8|0);
             HEAP32[$714>>2] = $712;
             $$3$i$i = $709;
            }
           } while(0);
           $727 = ($707|0)==(0|0);
           if ($727) {
            break;
           }
           $728 = ((($668)) + 28|0);
           $729 = HEAP32[$728>>2]|0;
           $730 = (32816 + ($729<<2)|0);
           $731 = HEAP32[$730>>2]|0;
           $732 = ($731|0)==($668|0);
           do {
            if ($732) {
             HEAP32[$730>>2] = $$3$i$i;
             $cond$i$i = ($$3$i$i|0)==(0|0);
             if (!($cond$i$i)) {
              break;
             }
             $733 = 1 << $729;
             $734 = $733 ^ -1;
             $735 = HEAP32[(32516)>>2]|0;
             $736 = $735 & $734;
             HEAP32[(32516)>>2] = $736;
             break L234;
            } else {
             $737 = ((($707)) + 16|0);
             $738 = HEAP32[$737>>2]|0;
             $739 = ($738|0)!=($668|0);
             $$sink1$i$i = $739&1;
             $740 = (((($707)) + 16|0) + ($$sink1$i$i<<2)|0);
             HEAP32[$740>>2] = $$3$i$i;
             $741 = ($$3$i$i|0)==(0|0);
             if ($741) {
              break L234;
             }
            }
           } while(0);
           $742 = ((($$3$i$i)) + 24|0);
           HEAP32[$742>>2] = $707;
           $743 = ((($668)) + 16|0);
           $744 = HEAP32[$743>>2]|0;
           $745 = ($744|0)==(0|0);
           if (!($745)) {
            $746 = ((($$3$i$i)) + 16|0);
            HEAP32[$746>>2] = $744;
            $747 = ((($744)) + 24|0);
            HEAP32[$747>>2] = $$3$i$i;
           }
           $748 = ((($743)) + 4|0);
           $749 = HEAP32[$748>>2]|0;
           $750 = ($749|0)==(0|0);
           if ($750) {
            break;
           }
           $751 = ((($$3$i$i)) + 20|0);
           HEAP32[$751>>2] = $749;
           $752 = ((($749)) + 24|0);
           HEAP32[$752>>2] = $$3$i$i;
          }
         } while(0);
         $753 = (($668) + ($692)|0);
         $754 = (($692) + ($673))|0;
         $$0$i$i = $753;$$0260$i$i = $754;
        } else {
         $$0$i$i = $668;$$0260$i$i = $673;
        }
        $755 = ((($$0$i$i)) + 4|0);
        $756 = HEAP32[$755>>2]|0;
        $757 = $756 & -2;
        HEAP32[$755>>2] = $757;
        $758 = $$0260$i$i | 1;
        $759 = ((($672)) + 4|0);
        HEAP32[$759>>2] = $758;
        $760 = (($672) + ($$0260$i$i)|0);
        HEAP32[$760>>2] = $$0260$i$i;
        $761 = $$0260$i$i >>> 3;
        $762 = ($$0260$i$i>>>0)<(256);
        if ($762) {
         $763 = $761 << 1;
         $764 = (32552 + ($763<<2)|0);
         $765 = HEAP32[8128]|0;
         $766 = 1 << $761;
         $767 = $765 & $766;
         $768 = ($767|0)==(0);
         if ($768) {
          $769 = $765 | $766;
          HEAP32[8128] = $769;
          $$pre$i17$i = ((($764)) + 8|0);
          $$0268$i$i = $764;$$pre$phi$i18$iZ2D = $$pre$i17$i;
         } else {
          $770 = ((($764)) + 8|0);
          $771 = HEAP32[$770>>2]|0;
          $$0268$i$i = $771;$$pre$phi$i18$iZ2D = $770;
         }
         HEAP32[$$pre$phi$i18$iZ2D>>2] = $672;
         $772 = ((($$0268$i$i)) + 12|0);
         HEAP32[$772>>2] = $672;
         $773 = ((($672)) + 8|0);
         HEAP32[$773>>2] = $$0268$i$i;
         $774 = ((($672)) + 12|0);
         HEAP32[$774>>2] = $764;
         break;
        }
        $775 = $$0260$i$i >>> 8;
        $776 = ($775|0)==(0);
        do {
         if ($776) {
          $$0269$i$i = 0;
         } else {
          $777 = ($$0260$i$i>>>0)>(16777215);
          if ($777) {
           $$0269$i$i = 31;
           break;
          }
          $778 = (($775) + 1048320)|0;
          $779 = $778 >>> 16;
          $780 = $779 & 8;
          $781 = $775 << $780;
          $782 = (($781) + 520192)|0;
          $783 = $782 >>> 16;
          $784 = $783 & 4;
          $785 = $784 | $780;
          $786 = $781 << $784;
          $787 = (($786) + 245760)|0;
          $788 = $787 >>> 16;
          $789 = $788 & 2;
          $790 = $785 | $789;
          $791 = (14 - ($790))|0;
          $792 = $786 << $789;
          $793 = $792 >>> 15;
          $794 = (($791) + ($793))|0;
          $795 = $794 << 1;
          $796 = (($794) + 7)|0;
          $797 = $$0260$i$i >>> $796;
          $798 = $797 & 1;
          $799 = $798 | $795;
          $$0269$i$i = $799;
         }
        } while(0);
        $800 = (32816 + ($$0269$i$i<<2)|0);
        $801 = ((($672)) + 28|0);
        HEAP32[$801>>2] = $$0269$i$i;
        $802 = ((($672)) + 16|0);
        $803 = ((($802)) + 4|0);
        HEAP32[$803>>2] = 0;
        HEAP32[$802>>2] = 0;
        $804 = HEAP32[(32516)>>2]|0;
        $805 = 1 << $$0269$i$i;
        $806 = $804 & $805;
        $807 = ($806|0)==(0);
        if ($807) {
         $808 = $804 | $805;
         HEAP32[(32516)>>2] = $808;
         HEAP32[$800>>2] = $672;
         $809 = ((($672)) + 24|0);
         HEAP32[$809>>2] = $800;
         $810 = ((($672)) + 12|0);
         HEAP32[$810>>2] = $672;
         $811 = ((($672)) + 8|0);
         HEAP32[$811>>2] = $672;
         break;
        }
        $812 = HEAP32[$800>>2]|0;
        $813 = ($$0269$i$i|0)==(31);
        $814 = $$0269$i$i >>> 1;
        $815 = (25 - ($814))|0;
        $816 = $813 ? 0 : $815;
        $817 = $$0260$i$i << $816;
        $$0261$i$i = $817;$$0262$i$i = $812;
        while(1) {
         $818 = ((($$0262$i$i)) + 4|0);
         $819 = HEAP32[$818>>2]|0;
         $820 = $819 & -8;
         $821 = ($820|0)==($$0260$i$i|0);
         if ($821) {
          label = 192;
          break;
         }
         $822 = $$0261$i$i >>> 31;
         $823 = (((($$0262$i$i)) + 16|0) + ($822<<2)|0);
         $824 = $$0261$i$i << 1;
         $825 = HEAP32[$823>>2]|0;
         $826 = ($825|0)==(0|0);
         if ($826) {
          label = 191;
          break;
         } else {
          $$0261$i$i = $824;$$0262$i$i = $825;
         }
        }
        if ((label|0) == 191) {
         HEAP32[$823>>2] = $672;
         $827 = ((($672)) + 24|0);
         HEAP32[$827>>2] = $$0262$i$i;
         $828 = ((($672)) + 12|0);
         HEAP32[$828>>2] = $672;
         $829 = ((($672)) + 8|0);
         HEAP32[$829>>2] = $672;
         break;
        }
        else if ((label|0) == 192) {
         $830 = ((($$0262$i$i)) + 8|0);
         $831 = HEAP32[$830>>2]|0;
         $832 = ((($831)) + 12|0);
         HEAP32[$832>>2] = $672;
         HEAP32[$830>>2] = $672;
         $833 = ((($672)) + 8|0);
         HEAP32[$833>>2] = $831;
         $834 = ((($672)) + 12|0);
         HEAP32[$834>>2] = $$0262$i$i;
         $835 = ((($672)) + 24|0);
         HEAP32[$835>>2] = 0;
         break;
        }
       }
      } while(0);
      $960 = ((($660)) + 8|0);
      $$0 = $960;
      STACKTOP = sp;return ($$0|0);
     } else {
      $$0$i$i$i = (32960);
     }
    }
    while(1) {
     $836 = HEAP32[$$0$i$i$i>>2]|0;
     $837 = ($836>>>0)>($586>>>0);
     if (!($837)) {
      $838 = ((($$0$i$i$i)) + 4|0);
      $839 = HEAP32[$838>>2]|0;
      $840 = (($836) + ($839)|0);
      $841 = ($840>>>0)>($586>>>0);
      if ($841) {
       break;
      }
     }
     $842 = ((($$0$i$i$i)) + 8|0);
     $843 = HEAP32[$842>>2]|0;
     $$0$i$i$i = $843;
    }
    $844 = ((($840)) + -47|0);
    $845 = ((($844)) + 8|0);
    $846 = $845;
    $847 = $846 & 7;
    $848 = ($847|0)==(0);
    $849 = (0 - ($846))|0;
    $850 = $849 & 7;
    $851 = $848 ? 0 : $850;
    $852 = (($844) + ($851)|0);
    $853 = ((($586)) + 16|0);
    $854 = ($852>>>0)<($853>>>0);
    $855 = $854 ? $586 : $852;
    $856 = ((($855)) + 8|0);
    $857 = ((($855)) + 24|0);
    $858 = (($$723947$i) + -40)|0;
    $859 = ((($$748$i)) + 8|0);
    $860 = $859;
    $861 = $860 & 7;
    $862 = ($861|0)==(0);
    $863 = (0 - ($860))|0;
    $864 = $863 & 7;
    $865 = $862 ? 0 : $864;
    $866 = (($$748$i) + ($865)|0);
    $867 = (($858) - ($865))|0;
    HEAP32[(32536)>>2] = $866;
    HEAP32[(32524)>>2] = $867;
    $868 = $867 | 1;
    $869 = ((($866)) + 4|0);
    HEAP32[$869>>2] = $868;
    $870 = (($$748$i) + ($858)|0);
    $871 = ((($870)) + 4|0);
    HEAP32[$871>>2] = 40;
    $872 = HEAP32[(33000)>>2]|0;
    HEAP32[(32540)>>2] = $872;
    $873 = ((($855)) + 4|0);
    HEAP32[$873>>2] = 27;
    ;HEAP32[$856>>2]=HEAP32[(32960)>>2]|0;HEAP32[$856+4>>2]=HEAP32[(32960)+4>>2]|0;HEAP32[$856+8>>2]=HEAP32[(32960)+8>>2]|0;HEAP32[$856+12>>2]=HEAP32[(32960)+12>>2]|0;
    HEAP32[(32960)>>2] = $$748$i;
    HEAP32[(32964)>>2] = $$723947$i;
    HEAP32[(32972)>>2] = 0;
    HEAP32[(32968)>>2] = $856;
    $875 = $857;
    while(1) {
     $874 = ((($875)) + 4|0);
     HEAP32[$874>>2] = 7;
     $876 = ((($875)) + 8|0);
     $877 = ($876>>>0)<($840>>>0);
     if ($877) {
      $875 = $874;
     } else {
      break;
     }
    }
    $878 = ($855|0)==($586|0);
    if (!($878)) {
     $879 = $855;
     $880 = $586;
     $881 = (($879) - ($880))|0;
     $882 = HEAP32[$873>>2]|0;
     $883 = $882 & -2;
     HEAP32[$873>>2] = $883;
     $884 = $881 | 1;
     $885 = ((($586)) + 4|0);
     HEAP32[$885>>2] = $884;
     HEAP32[$855>>2] = $881;
     $886 = $881 >>> 3;
     $887 = ($881>>>0)<(256);
     if ($887) {
      $888 = $886 << 1;
      $889 = (32552 + ($888<<2)|0);
      $890 = HEAP32[8128]|0;
      $891 = 1 << $886;
      $892 = $890 & $891;
      $893 = ($892|0)==(0);
      if ($893) {
       $894 = $890 | $891;
       HEAP32[8128] = $894;
       $$pre$i$i = ((($889)) + 8|0);
       $$0206$i$i = $889;$$pre$phi$i$iZ2D = $$pre$i$i;
      } else {
       $895 = ((($889)) + 8|0);
       $896 = HEAP32[$895>>2]|0;
       $$0206$i$i = $896;$$pre$phi$i$iZ2D = $895;
      }
      HEAP32[$$pre$phi$i$iZ2D>>2] = $586;
      $897 = ((($$0206$i$i)) + 12|0);
      HEAP32[$897>>2] = $586;
      $898 = ((($586)) + 8|0);
      HEAP32[$898>>2] = $$0206$i$i;
      $899 = ((($586)) + 12|0);
      HEAP32[$899>>2] = $889;
      break;
     }
     $900 = $881 >>> 8;
     $901 = ($900|0)==(0);
     if ($901) {
      $$0207$i$i = 0;
     } else {
      $902 = ($881>>>0)>(16777215);
      if ($902) {
       $$0207$i$i = 31;
      } else {
       $903 = (($900) + 1048320)|0;
       $904 = $903 >>> 16;
       $905 = $904 & 8;
       $906 = $900 << $905;
       $907 = (($906) + 520192)|0;
       $908 = $907 >>> 16;
       $909 = $908 & 4;
       $910 = $909 | $905;
       $911 = $906 << $909;
       $912 = (($911) + 245760)|0;
       $913 = $912 >>> 16;
       $914 = $913 & 2;
       $915 = $910 | $914;
       $916 = (14 - ($915))|0;
       $917 = $911 << $914;
       $918 = $917 >>> 15;
       $919 = (($916) + ($918))|0;
       $920 = $919 << 1;
       $921 = (($919) + 7)|0;
       $922 = $881 >>> $921;
       $923 = $922 & 1;
       $924 = $923 | $920;
       $$0207$i$i = $924;
      }
     }
     $925 = (32816 + ($$0207$i$i<<2)|0);
     $926 = ((($586)) + 28|0);
     HEAP32[$926>>2] = $$0207$i$i;
     $927 = ((($586)) + 20|0);
     HEAP32[$927>>2] = 0;
     HEAP32[$853>>2] = 0;
     $928 = HEAP32[(32516)>>2]|0;
     $929 = 1 << $$0207$i$i;
     $930 = $928 & $929;
     $931 = ($930|0)==(0);
     if ($931) {
      $932 = $928 | $929;
      HEAP32[(32516)>>2] = $932;
      HEAP32[$925>>2] = $586;
      $933 = ((($586)) + 24|0);
      HEAP32[$933>>2] = $925;
      $934 = ((($586)) + 12|0);
      HEAP32[$934>>2] = $586;
      $935 = ((($586)) + 8|0);
      HEAP32[$935>>2] = $586;
      break;
     }
     $936 = HEAP32[$925>>2]|0;
     $937 = ($$0207$i$i|0)==(31);
     $938 = $$0207$i$i >>> 1;
     $939 = (25 - ($938))|0;
     $940 = $937 ? 0 : $939;
     $941 = $881 << $940;
     $$0201$i$i = $941;$$0202$i$i = $936;
     while(1) {
      $942 = ((($$0202$i$i)) + 4|0);
      $943 = HEAP32[$942>>2]|0;
      $944 = $943 & -8;
      $945 = ($944|0)==($881|0);
      if ($945) {
       label = 213;
       break;
      }
      $946 = $$0201$i$i >>> 31;
      $947 = (((($$0202$i$i)) + 16|0) + ($946<<2)|0);
      $948 = $$0201$i$i << 1;
      $949 = HEAP32[$947>>2]|0;
      $950 = ($949|0)==(0|0);
      if ($950) {
       label = 212;
       break;
      } else {
       $$0201$i$i = $948;$$0202$i$i = $949;
      }
     }
     if ((label|0) == 212) {
      HEAP32[$947>>2] = $586;
      $951 = ((($586)) + 24|0);
      HEAP32[$951>>2] = $$0202$i$i;
      $952 = ((($586)) + 12|0);
      HEAP32[$952>>2] = $586;
      $953 = ((($586)) + 8|0);
      HEAP32[$953>>2] = $586;
      break;
     }
     else if ((label|0) == 213) {
      $954 = ((($$0202$i$i)) + 8|0);
      $955 = HEAP32[$954>>2]|0;
      $956 = ((($955)) + 12|0);
      HEAP32[$956>>2] = $586;
      HEAP32[$954>>2] = $586;
      $957 = ((($586)) + 8|0);
      HEAP32[$957>>2] = $955;
      $958 = ((($586)) + 12|0);
      HEAP32[$958>>2] = $$0202$i$i;
      $959 = ((($586)) + 24|0);
      HEAP32[$959>>2] = 0;
      break;
     }
    }
   }
  } while(0);
  $961 = HEAP32[(32524)>>2]|0;
  $962 = ($961>>>0)>($$0192>>>0);
  if ($962) {
   $963 = (($961) - ($$0192))|0;
   HEAP32[(32524)>>2] = $963;
   $964 = HEAP32[(32536)>>2]|0;
   $965 = (($964) + ($$0192)|0);
   HEAP32[(32536)>>2] = $965;
   $966 = $963 | 1;
   $967 = ((($965)) + 4|0);
   HEAP32[$967>>2] = $966;
   $968 = $$0192 | 3;
   $969 = ((($964)) + 4|0);
   HEAP32[$969>>2] = $968;
   $970 = ((($964)) + 8|0);
   $$0 = $970;
   STACKTOP = sp;return ($$0|0);
  }
 }
 $971 = (___errno_location()|0);
 HEAP32[$971>>2] = 12;
 $$0 = 0;
 STACKTOP = sp;return ($$0|0);
}
function _free($0) {
 $0 = $0|0;
 var $$0195$i = 0, $$0195$in$i = 0, $$0348 = 0, $$0349 = 0, $$0361 = 0, $$0368 = 0, $$1 = 0, $$1347 = 0, $$1352 = 0, $$1355 = 0, $$1363 = 0, $$1367 = 0, $$2 = 0, $$3 = 0, $$3365 = 0, $$pre = 0, $$pre$phiZ2D = 0, $$sink3 = 0, $$sink5 = 0, $1 = 0;
 var $10 = 0, $100 = 0, $101 = 0, $102 = 0, $103 = 0, $104 = 0, $105 = 0, $106 = 0, $107 = 0, $108 = 0, $109 = 0, $11 = 0, $110 = 0, $111 = 0, $112 = 0, $113 = 0, $114 = 0, $115 = 0, $116 = 0, $117 = 0;
 var $118 = 0, $119 = 0, $12 = 0, $120 = 0, $121 = 0, $122 = 0, $123 = 0, $124 = 0, $125 = 0, $126 = 0, $127 = 0, $128 = 0, $129 = 0, $13 = 0, $130 = 0, $131 = 0, $132 = 0, $133 = 0, $134 = 0, $135 = 0;
 var $136 = 0, $137 = 0, $138 = 0, $139 = 0, $14 = 0, $140 = 0, $141 = 0, $142 = 0, $143 = 0, $144 = 0, $145 = 0, $146 = 0, $147 = 0, $148 = 0, $149 = 0, $15 = 0, $150 = 0, $151 = 0, $152 = 0, $153 = 0;
 var $154 = 0, $155 = 0, $156 = 0, $157 = 0, $158 = 0, $159 = 0, $16 = 0, $160 = 0, $161 = 0, $162 = 0, $163 = 0, $164 = 0, $165 = 0, $166 = 0, $167 = 0, $168 = 0, $169 = 0, $17 = 0, $170 = 0, $171 = 0;
 var $172 = 0, $173 = 0, $174 = 0, $175 = 0, $176 = 0, $177 = 0, $178 = 0, $179 = 0, $18 = 0, $180 = 0, $181 = 0, $182 = 0, $183 = 0, $184 = 0, $185 = 0, $186 = 0, $187 = 0, $188 = 0, $189 = 0, $19 = 0;
 var $190 = 0, $191 = 0, $192 = 0, $193 = 0, $194 = 0, $195 = 0, $196 = 0, $197 = 0, $198 = 0, $199 = 0, $2 = 0, $20 = 0, $200 = 0, $201 = 0, $202 = 0, $203 = 0, $204 = 0, $205 = 0, $206 = 0, $207 = 0;
 var $208 = 0, $209 = 0, $21 = 0, $210 = 0, $211 = 0, $212 = 0, $213 = 0, $214 = 0, $215 = 0, $216 = 0, $217 = 0, $218 = 0, $219 = 0, $22 = 0, $220 = 0, $221 = 0, $222 = 0, $223 = 0, $224 = 0, $225 = 0;
 var $226 = 0, $227 = 0, $228 = 0, $229 = 0, $23 = 0, $230 = 0, $231 = 0, $232 = 0, $233 = 0, $234 = 0, $235 = 0, $236 = 0, $237 = 0, $238 = 0, $239 = 0, $24 = 0, $240 = 0, $241 = 0, $242 = 0, $243 = 0;
 var $244 = 0, $245 = 0, $246 = 0, $247 = 0, $248 = 0, $249 = 0, $25 = 0, $250 = 0, $251 = 0, $252 = 0, $253 = 0, $254 = 0, $255 = 0, $256 = 0, $257 = 0, $258 = 0, $259 = 0, $26 = 0, $260 = 0, $27 = 0;
 var $28 = 0, $29 = 0, $3 = 0, $30 = 0, $31 = 0, $32 = 0, $33 = 0, $34 = 0, $35 = 0, $36 = 0, $37 = 0, $38 = 0, $39 = 0, $4 = 0, $40 = 0, $41 = 0, $42 = 0, $43 = 0, $44 = 0, $45 = 0;
 var $46 = 0, $47 = 0, $48 = 0, $49 = 0, $5 = 0, $50 = 0, $51 = 0, $52 = 0, $53 = 0, $54 = 0, $55 = 0, $56 = 0, $57 = 0, $58 = 0, $59 = 0, $6 = 0, $60 = 0, $61 = 0, $62 = 0, $63 = 0;
 var $64 = 0, $65 = 0, $66 = 0, $67 = 0, $68 = 0, $69 = 0, $7 = 0, $70 = 0, $71 = 0, $72 = 0, $73 = 0, $74 = 0, $75 = 0, $76 = 0, $77 = 0, $78 = 0, $79 = 0, $8 = 0, $80 = 0, $81 = 0;
 var $82 = 0, $83 = 0, $84 = 0, $85 = 0, $86 = 0, $87 = 0, $88 = 0, $89 = 0, $9 = 0, $90 = 0, $91 = 0, $92 = 0, $93 = 0, $94 = 0, $95 = 0, $96 = 0, $97 = 0, $98 = 0, $99 = 0, $cond373 = 0;
 var $cond374 = 0, label = 0, sp = 0;
 sp = STACKTOP;
 $1 = ($0|0)==(0|0);
 if ($1) {
  return;
 }
 $2 = ((($0)) + -8|0);
 $3 = HEAP32[(32528)>>2]|0;
 $4 = ((($0)) + -4|0);
 $5 = HEAP32[$4>>2]|0;
 $6 = $5 & -8;
 $7 = (($2) + ($6)|0);
 $8 = $5 & 1;
 $9 = ($8|0)==(0);
 do {
  if ($9) {
   $10 = HEAP32[$2>>2]|0;
   $11 = $5 & 3;
   $12 = ($11|0)==(0);
   if ($12) {
    return;
   }
   $13 = (0 - ($10))|0;
   $14 = (($2) + ($13)|0);
   $15 = (($10) + ($6))|0;
   $16 = ($14>>>0)<($3>>>0);
   if ($16) {
    return;
   }
   $17 = HEAP32[(32532)>>2]|0;
   $18 = ($17|0)==($14|0);
   if ($18) {
    $79 = ((($7)) + 4|0);
    $80 = HEAP32[$79>>2]|0;
    $81 = $80 & 3;
    $82 = ($81|0)==(3);
    if (!($82)) {
     $$1 = $14;$$1347 = $15;$87 = $14;
     break;
    }
    HEAP32[(32520)>>2] = $15;
    $83 = $80 & -2;
    HEAP32[$79>>2] = $83;
    $84 = $15 | 1;
    $85 = ((($14)) + 4|0);
    HEAP32[$85>>2] = $84;
    $86 = (($14) + ($15)|0);
    HEAP32[$86>>2] = $15;
    return;
   }
   $19 = $10 >>> 3;
   $20 = ($10>>>0)<(256);
   if ($20) {
    $21 = ((($14)) + 8|0);
    $22 = HEAP32[$21>>2]|0;
    $23 = ((($14)) + 12|0);
    $24 = HEAP32[$23>>2]|0;
    $25 = ($24|0)==($22|0);
    if ($25) {
     $26 = 1 << $19;
     $27 = $26 ^ -1;
     $28 = HEAP32[8128]|0;
     $29 = $28 & $27;
     HEAP32[8128] = $29;
     $$1 = $14;$$1347 = $15;$87 = $14;
     break;
    } else {
     $30 = ((($22)) + 12|0);
     HEAP32[$30>>2] = $24;
     $31 = ((($24)) + 8|0);
     HEAP32[$31>>2] = $22;
     $$1 = $14;$$1347 = $15;$87 = $14;
     break;
    }
   }
   $32 = ((($14)) + 24|0);
   $33 = HEAP32[$32>>2]|0;
   $34 = ((($14)) + 12|0);
   $35 = HEAP32[$34>>2]|0;
   $36 = ($35|0)==($14|0);
   do {
    if ($36) {
     $41 = ((($14)) + 16|0);
     $42 = ((($41)) + 4|0);
     $43 = HEAP32[$42>>2]|0;
     $44 = ($43|0)==(0|0);
     if ($44) {
      $45 = HEAP32[$41>>2]|0;
      $46 = ($45|0)==(0|0);
      if ($46) {
       $$3 = 0;
       break;
      } else {
       $$1352 = $45;$$1355 = $41;
      }
     } else {
      $$1352 = $43;$$1355 = $42;
     }
     while(1) {
      $47 = ((($$1352)) + 20|0);
      $48 = HEAP32[$47>>2]|0;
      $49 = ($48|0)==(0|0);
      if (!($49)) {
       $$1352 = $48;$$1355 = $47;
       continue;
      }
      $50 = ((($$1352)) + 16|0);
      $51 = HEAP32[$50>>2]|0;
      $52 = ($51|0)==(0|0);
      if ($52) {
       break;
      } else {
       $$1352 = $51;$$1355 = $50;
      }
     }
     HEAP32[$$1355>>2] = 0;
     $$3 = $$1352;
    } else {
     $37 = ((($14)) + 8|0);
     $38 = HEAP32[$37>>2]|0;
     $39 = ((($38)) + 12|0);
     HEAP32[$39>>2] = $35;
     $40 = ((($35)) + 8|0);
     HEAP32[$40>>2] = $38;
     $$3 = $35;
    }
   } while(0);
   $53 = ($33|0)==(0|0);
   if ($53) {
    $$1 = $14;$$1347 = $15;$87 = $14;
   } else {
    $54 = ((($14)) + 28|0);
    $55 = HEAP32[$54>>2]|0;
    $56 = (32816 + ($55<<2)|0);
    $57 = HEAP32[$56>>2]|0;
    $58 = ($57|0)==($14|0);
    if ($58) {
     HEAP32[$56>>2] = $$3;
     $cond373 = ($$3|0)==(0|0);
     if ($cond373) {
      $59 = 1 << $55;
      $60 = $59 ^ -1;
      $61 = HEAP32[(32516)>>2]|0;
      $62 = $61 & $60;
      HEAP32[(32516)>>2] = $62;
      $$1 = $14;$$1347 = $15;$87 = $14;
      break;
     }
    } else {
     $63 = ((($33)) + 16|0);
     $64 = HEAP32[$63>>2]|0;
     $65 = ($64|0)!=($14|0);
     $$sink3 = $65&1;
     $66 = (((($33)) + 16|0) + ($$sink3<<2)|0);
     HEAP32[$66>>2] = $$3;
     $67 = ($$3|0)==(0|0);
     if ($67) {
      $$1 = $14;$$1347 = $15;$87 = $14;
      break;
     }
    }
    $68 = ((($$3)) + 24|0);
    HEAP32[$68>>2] = $33;
    $69 = ((($14)) + 16|0);
    $70 = HEAP32[$69>>2]|0;
    $71 = ($70|0)==(0|0);
    if (!($71)) {
     $72 = ((($$3)) + 16|0);
     HEAP32[$72>>2] = $70;
     $73 = ((($70)) + 24|0);
     HEAP32[$73>>2] = $$3;
    }
    $74 = ((($69)) + 4|0);
    $75 = HEAP32[$74>>2]|0;
    $76 = ($75|0)==(0|0);
    if ($76) {
     $$1 = $14;$$1347 = $15;$87 = $14;
    } else {
     $77 = ((($$3)) + 20|0);
     HEAP32[$77>>2] = $75;
     $78 = ((($75)) + 24|0);
     HEAP32[$78>>2] = $$3;
     $$1 = $14;$$1347 = $15;$87 = $14;
    }
   }
  } else {
   $$1 = $2;$$1347 = $6;$87 = $2;
  }
 } while(0);
 $88 = ($87>>>0)<($7>>>0);
 if (!($88)) {
  return;
 }
 $89 = ((($7)) + 4|0);
 $90 = HEAP32[$89>>2]|0;
 $91 = $90 & 1;
 $92 = ($91|0)==(0);
 if ($92) {
  return;
 }
 $93 = $90 & 2;
 $94 = ($93|0)==(0);
 if ($94) {
  $95 = HEAP32[(32536)>>2]|0;
  $96 = ($95|0)==($7|0);
  if ($96) {
   $97 = HEAP32[(32524)>>2]|0;
   $98 = (($97) + ($$1347))|0;
   HEAP32[(32524)>>2] = $98;
   HEAP32[(32536)>>2] = $$1;
   $99 = $98 | 1;
   $100 = ((($$1)) + 4|0);
   HEAP32[$100>>2] = $99;
   $101 = HEAP32[(32532)>>2]|0;
   $102 = ($$1|0)==($101|0);
   if (!($102)) {
    return;
   }
   HEAP32[(32532)>>2] = 0;
   HEAP32[(32520)>>2] = 0;
   return;
  }
  $103 = HEAP32[(32532)>>2]|0;
  $104 = ($103|0)==($7|0);
  if ($104) {
   $105 = HEAP32[(32520)>>2]|0;
   $106 = (($105) + ($$1347))|0;
   HEAP32[(32520)>>2] = $106;
   HEAP32[(32532)>>2] = $87;
   $107 = $106 | 1;
   $108 = ((($$1)) + 4|0);
   HEAP32[$108>>2] = $107;
   $109 = (($87) + ($106)|0);
   HEAP32[$109>>2] = $106;
   return;
  }
  $110 = $90 & -8;
  $111 = (($110) + ($$1347))|0;
  $112 = $90 >>> 3;
  $113 = ($90>>>0)<(256);
  do {
   if ($113) {
    $114 = ((($7)) + 8|0);
    $115 = HEAP32[$114>>2]|0;
    $116 = ((($7)) + 12|0);
    $117 = HEAP32[$116>>2]|0;
    $118 = ($117|0)==($115|0);
    if ($118) {
     $119 = 1 << $112;
     $120 = $119 ^ -1;
     $121 = HEAP32[8128]|0;
     $122 = $121 & $120;
     HEAP32[8128] = $122;
     break;
    } else {
     $123 = ((($115)) + 12|0);
     HEAP32[$123>>2] = $117;
     $124 = ((($117)) + 8|0);
     HEAP32[$124>>2] = $115;
     break;
    }
   } else {
    $125 = ((($7)) + 24|0);
    $126 = HEAP32[$125>>2]|0;
    $127 = ((($7)) + 12|0);
    $128 = HEAP32[$127>>2]|0;
    $129 = ($128|0)==($7|0);
    do {
     if ($129) {
      $134 = ((($7)) + 16|0);
      $135 = ((($134)) + 4|0);
      $136 = HEAP32[$135>>2]|0;
      $137 = ($136|0)==(0|0);
      if ($137) {
       $138 = HEAP32[$134>>2]|0;
       $139 = ($138|0)==(0|0);
       if ($139) {
        $$3365 = 0;
        break;
       } else {
        $$1363 = $138;$$1367 = $134;
       }
      } else {
       $$1363 = $136;$$1367 = $135;
      }
      while(1) {
       $140 = ((($$1363)) + 20|0);
       $141 = HEAP32[$140>>2]|0;
       $142 = ($141|0)==(0|0);
       if (!($142)) {
        $$1363 = $141;$$1367 = $140;
        continue;
       }
       $143 = ((($$1363)) + 16|0);
       $144 = HEAP32[$143>>2]|0;
       $145 = ($144|0)==(0|0);
       if ($145) {
        break;
       } else {
        $$1363 = $144;$$1367 = $143;
       }
      }
      HEAP32[$$1367>>2] = 0;
      $$3365 = $$1363;
     } else {
      $130 = ((($7)) + 8|0);
      $131 = HEAP32[$130>>2]|0;
      $132 = ((($131)) + 12|0);
      HEAP32[$132>>2] = $128;
      $133 = ((($128)) + 8|0);
      HEAP32[$133>>2] = $131;
      $$3365 = $128;
     }
    } while(0);
    $146 = ($126|0)==(0|0);
    if (!($146)) {
     $147 = ((($7)) + 28|0);
     $148 = HEAP32[$147>>2]|0;
     $149 = (32816 + ($148<<2)|0);
     $150 = HEAP32[$149>>2]|0;
     $151 = ($150|0)==($7|0);
     if ($151) {
      HEAP32[$149>>2] = $$3365;
      $cond374 = ($$3365|0)==(0|0);
      if ($cond374) {
       $152 = 1 << $148;
       $153 = $152 ^ -1;
       $154 = HEAP32[(32516)>>2]|0;
       $155 = $154 & $153;
       HEAP32[(32516)>>2] = $155;
       break;
      }
     } else {
      $156 = ((($126)) + 16|0);
      $157 = HEAP32[$156>>2]|0;
      $158 = ($157|0)!=($7|0);
      $$sink5 = $158&1;
      $159 = (((($126)) + 16|0) + ($$sink5<<2)|0);
      HEAP32[$159>>2] = $$3365;
      $160 = ($$3365|0)==(0|0);
      if ($160) {
       break;
      }
     }
     $161 = ((($$3365)) + 24|0);
     HEAP32[$161>>2] = $126;
     $162 = ((($7)) + 16|0);
     $163 = HEAP32[$162>>2]|0;
     $164 = ($163|0)==(0|0);
     if (!($164)) {
      $165 = ((($$3365)) + 16|0);
      HEAP32[$165>>2] = $163;
      $166 = ((($163)) + 24|0);
      HEAP32[$166>>2] = $$3365;
     }
     $167 = ((($162)) + 4|0);
     $168 = HEAP32[$167>>2]|0;
     $169 = ($168|0)==(0|0);
     if (!($169)) {
      $170 = ((($$3365)) + 20|0);
      HEAP32[$170>>2] = $168;
      $171 = ((($168)) + 24|0);
      HEAP32[$171>>2] = $$3365;
     }
    }
   }
  } while(0);
  $172 = $111 | 1;
  $173 = ((($$1)) + 4|0);
  HEAP32[$173>>2] = $172;
  $174 = (($87) + ($111)|0);
  HEAP32[$174>>2] = $111;
  $175 = HEAP32[(32532)>>2]|0;
  $176 = ($$1|0)==($175|0);
  if ($176) {
   HEAP32[(32520)>>2] = $111;
   return;
  } else {
   $$2 = $111;
  }
 } else {
  $177 = $90 & -2;
  HEAP32[$89>>2] = $177;
  $178 = $$1347 | 1;
  $179 = ((($$1)) + 4|0);
  HEAP32[$179>>2] = $178;
  $180 = (($87) + ($$1347)|0);
  HEAP32[$180>>2] = $$1347;
  $$2 = $$1347;
 }
 $181 = $$2 >>> 3;
 $182 = ($$2>>>0)<(256);
 if ($182) {
  $183 = $181 << 1;
  $184 = (32552 + ($183<<2)|0);
  $185 = HEAP32[8128]|0;
  $186 = 1 << $181;
  $187 = $185 & $186;
  $188 = ($187|0)==(0);
  if ($188) {
   $189 = $185 | $186;
   HEAP32[8128] = $189;
   $$pre = ((($184)) + 8|0);
   $$0368 = $184;$$pre$phiZ2D = $$pre;
  } else {
   $190 = ((($184)) + 8|0);
   $191 = HEAP32[$190>>2]|0;
   $$0368 = $191;$$pre$phiZ2D = $190;
  }
  HEAP32[$$pre$phiZ2D>>2] = $$1;
  $192 = ((($$0368)) + 12|0);
  HEAP32[$192>>2] = $$1;
  $193 = ((($$1)) + 8|0);
  HEAP32[$193>>2] = $$0368;
  $194 = ((($$1)) + 12|0);
  HEAP32[$194>>2] = $184;
  return;
 }
 $195 = $$2 >>> 8;
 $196 = ($195|0)==(0);
 if ($196) {
  $$0361 = 0;
 } else {
  $197 = ($$2>>>0)>(16777215);
  if ($197) {
   $$0361 = 31;
  } else {
   $198 = (($195) + 1048320)|0;
   $199 = $198 >>> 16;
   $200 = $199 & 8;
   $201 = $195 << $200;
   $202 = (($201) + 520192)|0;
   $203 = $202 >>> 16;
   $204 = $203 & 4;
   $205 = $204 | $200;
   $206 = $201 << $204;
   $207 = (($206) + 245760)|0;
   $208 = $207 >>> 16;
   $209 = $208 & 2;
   $210 = $205 | $209;
   $211 = (14 - ($210))|0;
   $212 = $206 << $209;
   $213 = $212 >>> 15;
   $214 = (($211) + ($213))|0;
   $215 = $214 << 1;
   $216 = (($214) + 7)|0;
   $217 = $$2 >>> $216;
   $218 = $217 & 1;
   $219 = $218 | $215;
   $$0361 = $219;
  }
 }
 $220 = (32816 + ($$0361<<2)|0);
 $221 = ((($$1)) + 28|0);
 HEAP32[$221>>2] = $$0361;
 $222 = ((($$1)) + 16|0);
 $223 = ((($$1)) + 20|0);
 HEAP32[$223>>2] = 0;
 HEAP32[$222>>2] = 0;
 $224 = HEAP32[(32516)>>2]|0;
 $225 = 1 << $$0361;
 $226 = $224 & $225;
 $227 = ($226|0)==(0);
 do {
  if ($227) {
   $228 = $224 | $225;
   HEAP32[(32516)>>2] = $228;
   HEAP32[$220>>2] = $$1;
   $229 = ((($$1)) + 24|0);
   HEAP32[$229>>2] = $220;
   $230 = ((($$1)) + 12|0);
   HEAP32[$230>>2] = $$1;
   $231 = ((($$1)) + 8|0);
   HEAP32[$231>>2] = $$1;
  } else {
   $232 = HEAP32[$220>>2]|0;
   $233 = ($$0361|0)==(31);
   $234 = $$0361 >>> 1;
   $235 = (25 - ($234))|0;
   $236 = $233 ? 0 : $235;
   $237 = $$2 << $236;
   $$0348 = $237;$$0349 = $232;
   while(1) {
    $238 = ((($$0349)) + 4|0);
    $239 = HEAP32[$238>>2]|0;
    $240 = $239 & -8;
    $241 = ($240|0)==($$2|0);
    if ($241) {
     label = 73;
     break;
    }
    $242 = $$0348 >>> 31;
    $243 = (((($$0349)) + 16|0) + ($242<<2)|0);
    $244 = $$0348 << 1;
    $245 = HEAP32[$243>>2]|0;
    $246 = ($245|0)==(0|0);
    if ($246) {
     label = 72;
     break;
    } else {
     $$0348 = $244;$$0349 = $245;
    }
   }
   if ((label|0) == 72) {
    HEAP32[$243>>2] = $$1;
    $247 = ((($$1)) + 24|0);
    HEAP32[$247>>2] = $$0349;
    $248 = ((($$1)) + 12|0);
    HEAP32[$248>>2] = $$1;
    $249 = ((($$1)) + 8|0);
    HEAP32[$249>>2] = $$1;
    break;
   }
   else if ((label|0) == 73) {
    $250 = ((($$0349)) + 8|0);
    $251 = HEAP32[$250>>2]|0;
    $252 = ((($251)) + 12|0);
    HEAP32[$252>>2] = $$1;
    HEAP32[$250>>2] = $$1;
    $253 = ((($$1)) + 8|0);
    HEAP32[$253>>2] = $251;
    $254 = ((($$1)) + 12|0);
    HEAP32[$254>>2] = $$0349;
    $255 = ((($$1)) + 24|0);
    HEAP32[$255>>2] = 0;
    break;
   }
  }
 } while(0);
 $256 = HEAP32[(32544)>>2]|0;
 $257 = (($256) + -1)|0;
 HEAP32[(32544)>>2] = $257;
 $258 = ($257|0)==(0);
 if ($258) {
  $$0195$in$i = (32968);
 } else {
  return;
 }
 while(1) {
  $$0195$i = HEAP32[$$0195$in$i>>2]|0;
  $259 = ($$0195$i|0)==(0|0);
  $260 = ((($$0195$i)) + 8|0);
  if ($259) {
   break;
  } else {
   $$0195$in$i = $260;
  }
 }
 HEAP32[(32544)>>2] = -1;
 return;
}
function ___errno_location() {
 var label = 0, sp = 0;
 sp = STACKTOP;
 return (33008|0);
}
function runPostSets() {
}
function ___muldsi3($a, $b) {
    $a = $a | 0;
    $b = $b | 0;
    var $1 = 0, $2 = 0, $3 = 0, $6 = 0, $8 = 0, $11 = 0, $12 = 0;
    $1 = $a & 65535;
    $2 = $b & 65535;
    $3 = Math_imul($2, $1) | 0;
    $6 = $a >>> 16;
    $8 = ($3 >>> 16) + (Math_imul($2, $6) | 0) | 0;
    $11 = $b >>> 16;
    $12 = Math_imul($11, $1) | 0;
    return (tempRet0 = (($8 >>> 16) + (Math_imul($11, $6) | 0) | 0) + ((($8 & 65535) + $12 | 0) >>> 16) | 0, 0 | ($8 + $12 << 16 | $3 & 65535)) | 0;
}
function ___muldi3($a$0, $a$1, $b$0, $b$1) {
    $a$0 = $a$0 | 0;
    $a$1 = $a$1 | 0;
    $b$0 = $b$0 | 0;
    $b$1 = $b$1 | 0;
    var $x_sroa_0_0_extract_trunc = 0, $y_sroa_0_0_extract_trunc = 0, $1$0 = 0, $1$1 = 0, $2 = 0;
    $x_sroa_0_0_extract_trunc = $a$0;
    $y_sroa_0_0_extract_trunc = $b$0;
    $1$0 = ___muldsi3($x_sroa_0_0_extract_trunc, $y_sroa_0_0_extract_trunc) | 0;
    $1$1 = tempRet0;
    $2 = Math_imul($a$1, $y_sroa_0_0_extract_trunc) | 0;
    return (tempRet0 = ((Math_imul($b$1, $x_sroa_0_0_extract_trunc) | 0) + $2 | 0) + $1$1 | $1$1 & 0, 0 | $1$0 & -1) | 0;
}
function _bitshift64Ashr(low, high, bits) {
    low = low|0; high = high|0; bits = bits|0;
    var ander = 0;
    if ((bits|0) < 32) {
      ander = ((1 << bits) - 1)|0;
      tempRet0 = high >> bits;
      return (low >>> bits) | ((high&ander) << (32 - bits));
    }
    tempRet0 = (high|0) < 0 ? -1 : 0;
    return (high >> (bits - 32))|0;
}
function _bitshift64Lshr(low, high, bits) {
    low = low|0; high = high|0; bits = bits|0;
    var ander = 0;
    if ((bits|0) < 32) {
      ander = ((1 << bits) - 1)|0;
      tempRet0 = high >>> bits;
      return (low >>> bits) | ((high&ander) << (32 - bits));
    }
    tempRet0 = 0;
    return (high >>> (bits - 32))|0;
}
function _bitshift64Shl(low, high, bits) {
    low = low|0; high = high|0; bits = bits|0;
    var ander = 0;
    if ((bits|0) < 32) {
      ander = ((1 << bits) - 1)|0;
      tempRet0 = (high << bits) | ((low&(ander << (32 - bits))) >>> (32 - bits));
      return low << bits;
    }
    tempRet0 = low << (bits - 32);
    return 0;
}
function _i64Add(a, b, c, d) {
    /*
      x = a + b*2^32
      y = c + d*2^32
      result = l + h*2^32
    */
    a = a|0; b = b|0; c = c|0; d = d|0;
    var l = 0, h = 0;
    l = (a + c)>>>0;
    h = (b + d + (((l>>>0) < (a>>>0))|0))>>>0; // Add carry from low word to high word on overflow.
    return ((tempRet0 = h,l|0)|0);
}
function _i64Subtract(a, b, c, d) {
    a = a|0; b = b|0; c = c|0; d = d|0;
    var l = 0, h = 0;
    l = (a - c)>>>0;
    h = (b - d)>>>0;
    h = (b - d - (((c>>>0) > (a>>>0))|0))>>>0; // Borrow one from high word to low word on underflow.
    return ((tempRet0 = h,l|0)|0);
}
function _memcpy(dest, src, num) {
    dest = dest|0; src = src|0; num = num|0;
    var ret = 0;
    var aligned_dest_end = 0;
    var block_aligned_dest_end = 0;
    var dest_end = 0;
    // Test against a benchmarked cutoff limit for when HEAPU8.set() becomes faster to use.
    if ((num|0) >=
      8192
    ) {
      return _emscripten_memcpy_big(dest|0, src|0, num|0)|0;
    }

    ret = dest|0;
    dest_end = (dest + num)|0;
    if ((dest&3) == (src&3)) {
      // The initial unaligned < 4-byte front.
      while (dest & 3) {
        if ((num|0) == 0) return ret|0;
        HEAP8[((dest)>>0)]=((HEAP8[((src)>>0)])|0);
        dest = (dest+1)|0;
        src = (src+1)|0;
        num = (num-1)|0;
      }
      aligned_dest_end = (dest_end & -4)|0;
      block_aligned_dest_end = (aligned_dest_end - 64)|0;
      while ((dest|0) <= (block_aligned_dest_end|0) ) {
        HEAP32[((dest)>>2)]=((HEAP32[((src)>>2)])|0);
        HEAP32[(((dest)+(4))>>2)]=((HEAP32[(((src)+(4))>>2)])|0);
        HEAP32[(((dest)+(8))>>2)]=((HEAP32[(((src)+(8))>>2)])|0);
        HEAP32[(((dest)+(12))>>2)]=((HEAP32[(((src)+(12))>>2)])|0);
        HEAP32[(((dest)+(16))>>2)]=((HEAP32[(((src)+(16))>>2)])|0);
        HEAP32[(((dest)+(20))>>2)]=((HEAP32[(((src)+(20))>>2)])|0);
        HEAP32[(((dest)+(24))>>2)]=((HEAP32[(((src)+(24))>>2)])|0);
        HEAP32[(((dest)+(28))>>2)]=((HEAP32[(((src)+(28))>>2)])|0);
        HEAP32[(((dest)+(32))>>2)]=((HEAP32[(((src)+(32))>>2)])|0);
        HEAP32[(((dest)+(36))>>2)]=((HEAP32[(((src)+(36))>>2)])|0);
        HEAP32[(((dest)+(40))>>2)]=((HEAP32[(((src)+(40))>>2)])|0);
        HEAP32[(((dest)+(44))>>2)]=((HEAP32[(((src)+(44))>>2)])|0);
        HEAP32[(((dest)+(48))>>2)]=((HEAP32[(((src)+(48))>>2)])|0);
        HEAP32[(((dest)+(52))>>2)]=((HEAP32[(((src)+(52))>>2)])|0);
        HEAP32[(((dest)+(56))>>2)]=((HEAP32[(((src)+(56))>>2)])|0);
        HEAP32[(((dest)+(60))>>2)]=((HEAP32[(((src)+(60))>>2)])|0);
        dest = (dest+64)|0;
        src = (src+64)|0;
      }
      while ((dest|0) < (aligned_dest_end|0) ) {
        HEAP32[((dest)>>2)]=((HEAP32[((src)>>2)])|0);
        dest = (dest+4)|0;
        src = (src+4)|0;
      }
    } else {
      // In the unaligned copy case, unroll a bit as well.
      aligned_dest_end = (dest_end - 4)|0;
      while ((dest|0) < (aligned_dest_end|0) ) {
        HEAP8[((dest)>>0)]=((HEAP8[((src)>>0)])|0);
        HEAP8[(((dest)+(1))>>0)]=((HEAP8[(((src)+(1))>>0)])|0);
        HEAP8[(((dest)+(2))>>0)]=((HEAP8[(((src)+(2))>>0)])|0);
        HEAP8[(((dest)+(3))>>0)]=((HEAP8[(((src)+(3))>>0)])|0);
        dest = (dest+4)|0;
        src = (src+4)|0;
      }
    }
    // The remaining unaligned < 4 byte tail.
    while ((dest|0) < (dest_end|0)) {
      HEAP8[((dest)>>0)]=((HEAP8[((src)>>0)])|0);
      dest = (dest+1)|0;
      src = (src+1)|0;
    }
    return ret|0;
}
function _memmove(dest, src, num) {
    dest = dest|0; src = src|0; num = num|0;
    var ret = 0;
    if (((src|0) < (dest|0)) & ((dest|0) < ((src + num)|0))) {
      // Unlikely case: Copy backwards in a safe manner
      ret = dest;
      src = (src + num)|0;
      dest = (dest + num)|0;
      while ((num|0) > 0) {
        dest = (dest - 1)|0;
        src = (src - 1)|0;
        num = (num - 1)|0;
        HEAP8[((dest)>>0)]=((HEAP8[((src)>>0)])|0);
      }
      dest = ret;
    } else {
      _memcpy(dest, src, num) | 0;
    }
    return dest | 0;
}
function _memset(ptr, value, num) {
    ptr = ptr|0; value = value|0; num = num|0;
    var end = 0, aligned_end = 0, block_aligned_end = 0, value4 = 0;
    end = (ptr + num)|0;

    value = value & 0xff;
    if ((num|0) >= 67 /* 64 bytes for an unrolled loop + 3 bytes for unaligned head*/) {
      while ((ptr&3) != 0) {
        HEAP8[((ptr)>>0)]=value;
        ptr = (ptr+1)|0;
      }

      aligned_end = (end & -4)|0;
      block_aligned_end = (aligned_end - 64)|0;
      value4 = value | (value << 8) | (value << 16) | (value << 24);

      while((ptr|0) <= (block_aligned_end|0)) {
        HEAP32[((ptr)>>2)]=value4;
        HEAP32[(((ptr)+(4))>>2)]=value4;
        HEAP32[(((ptr)+(8))>>2)]=value4;
        HEAP32[(((ptr)+(12))>>2)]=value4;
        HEAP32[(((ptr)+(16))>>2)]=value4;
        HEAP32[(((ptr)+(20))>>2)]=value4;
        HEAP32[(((ptr)+(24))>>2)]=value4;
        HEAP32[(((ptr)+(28))>>2)]=value4;
        HEAP32[(((ptr)+(32))>>2)]=value4;
        HEAP32[(((ptr)+(36))>>2)]=value4;
        HEAP32[(((ptr)+(40))>>2)]=value4;
        HEAP32[(((ptr)+(44))>>2)]=value4;
        HEAP32[(((ptr)+(48))>>2)]=value4;
        HEAP32[(((ptr)+(52))>>2)]=value4;
        HEAP32[(((ptr)+(56))>>2)]=value4;
        HEAP32[(((ptr)+(60))>>2)]=value4;
        ptr = (ptr + 64)|0;
      }

      while ((ptr|0) < (aligned_end|0) ) {
        HEAP32[((ptr)>>2)]=value4;
        ptr = (ptr+4)|0;
      }
    }
    // The remaining bytes.
    while ((ptr|0) < (end|0)) {
      HEAP8[((ptr)>>0)]=value;
      ptr = (ptr+1)|0;
    }
    return (end-num)|0;
}
function _sbrk(increment) {
    increment = increment|0;
    var oldDynamicTop = 0;
    var oldDynamicTopOnChange = 0;
    var newDynamicTop = 0;
    var totalMemory = 0;
    oldDynamicTop = HEAP32[DYNAMICTOP_PTR>>2]|0;
    newDynamicTop = oldDynamicTop + increment | 0;

    if (((increment|0) > 0 & (newDynamicTop|0) < (oldDynamicTop|0)) // Detect and fail if we would wrap around signed 32-bit int.
      | (newDynamicTop|0) < 0) { // Also underflow, sbrk() should be able to be used to subtract.
      abortOnCannotGrowMemory()|0;
      ___setErrNo(12);
      return -1;
    }

    HEAP32[DYNAMICTOP_PTR>>2] = newDynamicTop;
    totalMemory = getTotalMemory()|0;
    if ((newDynamicTop|0) > (totalMemory|0)) {
      if ((enlargeMemory()|0) == 0) {
        HEAP32[DYNAMICTOP_PTR>>2] = oldDynamicTop;
        ___setErrNo(12);
        return -1;
      }
    }
    return oldDynamicTop|0;
}

  


// EMSCRIPTEN_END_FUNCS


  return { ___errno_location: ___errno_location, ___muldi3: ___muldi3, _bitshift64Ashr: _bitshift64Ashr, _bitshift64Lshr: _bitshift64Lshr, _bitshift64Shl: _bitshift64Shl, _crypto_sign_ed25519_ref10_ge_scalarmult_base: _crypto_sign_ed25519_ref10_ge_scalarmult_base, _curve25519_donna: _curve25519_donna, _curve25519_sign: _curve25519_sign, _curve25519_verify: _curve25519_verify, _free: _free, _i64Add: _i64Add, _i64Subtract: _i64Subtract, _malloc: _malloc, _memcpy: _memcpy, _memmove: _memmove, _memset: _memset, _sbrk: _sbrk, _sph_sha512_init: _sph_sha512_init, establishStackSpace: establishStackSpace, getTempRet0: getTempRet0, runPostSets: runPostSets, setTempRet0: setTempRet0, setThrew: setThrew, stackAlloc: stackAlloc, stackRestore: stackRestore, stackSave: stackSave };
})
// EMSCRIPTEN_END_ASM
(Module.asmGlobalArg, Module.asmLibraryArg, buffer);

var ___errno_location = Module["___errno_location"] = asm["___errno_location"];
var ___muldi3 = Module["___muldi3"] = asm["___muldi3"];
var _bitshift64Ashr = Module["_bitshift64Ashr"] = asm["_bitshift64Ashr"];
var _bitshift64Lshr = Module["_bitshift64Lshr"] = asm["_bitshift64Lshr"];
var _bitshift64Shl = Module["_bitshift64Shl"] = asm["_bitshift64Shl"];
var _crypto_sign_ed25519_ref10_ge_scalarmult_base = Module["_crypto_sign_ed25519_ref10_ge_scalarmult_base"] = asm["_crypto_sign_ed25519_ref10_ge_scalarmult_base"];
var _curve25519_donna = Module["_curve25519_donna"] = asm["_curve25519_donna"];
var _curve25519_sign = Module["_curve25519_sign"] = asm["_curve25519_sign"];
var _curve25519_verify = Module["_curve25519_verify"] = asm["_curve25519_verify"];
var _free = Module["_free"] = asm["_free"];
var _i64Add = Module["_i64Add"] = asm["_i64Add"];
var _i64Subtract = Module["_i64Subtract"] = asm["_i64Subtract"];
var _malloc = Module["_malloc"] = asm["_malloc"];
var _memcpy = Module["_memcpy"] = asm["_memcpy"];
var _memmove = Module["_memmove"] = asm["_memmove"];
var _memset = Module["_memset"] = asm["_memset"];
var _sbrk = Module["_sbrk"] = asm["_sbrk"];
var _sph_sha512_init = Module["_sph_sha512_init"] = asm["_sph_sha512_init"];
var establishStackSpace = Module["establishStackSpace"] = asm["establishStackSpace"];
var getTempRet0 = Module["getTempRet0"] = asm["getTempRet0"];
var runPostSets = Module["runPostSets"] = asm["runPostSets"];
var setTempRet0 = Module["setTempRet0"] = asm["setTempRet0"];
var setThrew = Module["setThrew"] = asm["setThrew"];
var stackAlloc = Module["stackAlloc"] = asm["stackAlloc"];
var stackRestore = Module["stackRestore"] = asm["stackRestore"];
var stackSave = Module["stackSave"] = asm["stackSave"];
;



// === Auto-generated postamble setup entry stuff ===

Module['asm'] = asm;




































































if (memoryInitializer) {
  if (!isDataURI(memoryInitializer)) {
    if (typeof Module['locateFile'] === 'function') {
      memoryInitializer = Module['locateFile'](memoryInitializer);
    } else if (Module['memoryInitializerPrefixURL']) {
      memoryInitializer = Module['memoryInitializerPrefixURL'] + memoryInitializer;
    }
  }
  if (ENVIRONMENT_IS_NODE || ENVIRONMENT_IS_SHELL) {
    var data = Module['readBinary'](memoryInitializer);
    HEAPU8.set(data, GLOBAL_BASE);
  } else {
    addRunDependency('memory initializer');
    var applyMemoryInitializer = function(data) {
      if (data.byteLength) data = new Uint8Array(data);
      HEAPU8.set(data, GLOBAL_BASE);
      // Delete the typed array that contains the large blob of the memory initializer request response so that
      // we won't keep unnecessary memory lying around. However, keep the XHR object itself alive so that e.g.
      // its .status field can still be accessed later.
      if (Module['memoryInitializerRequest']) delete Module['memoryInitializerRequest'].response;
      removeRunDependency('memory initializer');
    }
    function doBrowserLoad() {
      Module['readAsync'](memoryInitializer, applyMemoryInitializer, function() {
        throw 'could not load memory initializer ' + memoryInitializer;
      });
    }
    var memoryInitializerBytes = tryParseAsDataURI(memoryInitializer);
    if (memoryInitializerBytes) {
      applyMemoryInitializer(memoryInitializerBytes.buffer);
    } else
    if (Module['memoryInitializerRequest']) {
      // a network request has already been created, just use that
      function useRequest() {
        var request = Module['memoryInitializerRequest'];
        var response = request.response;
        if (request.status !== 200 && request.status !== 0) {
          var data = tryParseAsDataURI(Module['memoryInitializerRequestURL']);
          if (data) {
            response = data.buffer;
          } else {
            // If you see this warning, the issue may be that you are using locateFile or memoryInitializerPrefixURL, and defining them in JS. That
            // means that the HTML file doesn't know about them, and when it tries to create the mem init request early, does it to the wrong place.
            // Look in your browser's devtools network console to see what's going on.
            console.warn('a problem seems to have happened with Module.memoryInitializerRequest, status: ' + request.status + ', retrying ' + memoryInitializer);
            doBrowserLoad();
            return;
          }
        }
        applyMemoryInitializer(response);
      }
      if (Module['memoryInitializerRequest'].response) {
        setTimeout(useRequest, 0); // it's already here; but, apply it asynchronously
      } else {
        Module['memoryInitializerRequest'].addEventListener('load', useRequest); // wait for it
      }
    } else {
      // fetch it from the network ourselves
      doBrowserLoad();
    }
  }
}



/**
 * @constructor
 * @extends {Error}
 * @this {ExitStatus}
 */
function ExitStatus(status) {
  this.name = "ExitStatus";
  this.message = "Program terminated with exit(" + status + ")";
  this.status = status;
};
ExitStatus.prototype = new Error();
ExitStatus.prototype.constructor = ExitStatus;

var initialStackTop;
var calledMain = false;

dependenciesFulfilled = function runCaller() {
  // If run has never been called, and we should call run (INVOKE_RUN is true, and Module.noInitialRun is not false)
  if (!Module['calledRun']) run();
  if (!Module['calledRun']) dependenciesFulfilled = runCaller; // try this again later, after new deps are fulfilled
}





/** @type {function(Array=)} */
function run(args) {
  args = args || Module['arguments'];

  if (runDependencies > 0) {
    return;
  }


  preRun();

  if (runDependencies > 0) return; // a preRun added a dependency, run will be called later
  if (Module['calledRun']) return; // run may have just been called through dependencies being fulfilled just in this very frame

  function doRun() {
    if (Module['calledRun']) return; // run may have just been called while the async setStatus time below was happening
    Module['calledRun'] = true;

    if (ABORT) return;

    ensureInitRuntime();

    preMain();

    if (Module['onRuntimeInitialized']) Module['onRuntimeInitialized']();


    postRun();
  }

  if (Module['setStatus']) {
    Module['setStatus']('Running...');
    setTimeout(function() {
      setTimeout(function() {
        Module['setStatus']('');
      }, 1);
      doRun();
    }, 1);
  } else {
    doRun();
  }
}
Module['run'] = run;


function exit(status, implicit) {

  // if this is just main exit-ing implicitly, and the status is 0, then we
  // don't need to do anything here and can just leave. if the status is
  // non-zero, though, then we need to report it.
  // (we may have warned about this earlier, if a situation justifies doing so)
  if (implicit && Module['noExitRuntime'] && status === 0) {
    return;
  }

  if (Module['noExitRuntime']) {
  } else {

    ABORT = true;
    EXITSTATUS = status;
    STACKTOP = initialStackTop;

    exitRuntime();

    if (Module['onExit']) Module['onExit'](status);
  }

  if (ENVIRONMENT_IS_NODE) {
    process['exit'](status);
  }
  Module['quit'](status, new ExitStatus(status));
}
Module['exit'] = exit;

var abortDecorators = [];

function abort(what) {
  if (Module['onAbort']) {
    Module['onAbort'](what);
  }

  if (what !== undefined) {
    Module.print(what);
    Module.printErr(what);
    what = JSON.stringify(what)
  } else {
    what = '';
  }

  ABORT = true;
  EXITSTATUS = 1;

  throw 'abort(' + what + '). Build with -s ASSERTIONS=1 for more info.';
}
Module['abort'] = abort;

// {{PRE_RUN_ADDITIONS}}

if (Module['preInit']) {
  if (typeof Module['preInit'] == 'function') Module['preInit'] = [Module['preInit']];
  while (Module['preInit'].length > 0) {
    Module['preInit'].pop()();
  }
}


Module["noExitRuntime"] = true;

run();

// {{POST_RUN_ADDITIONS}}





// {{MODULE_ADDITIONS}}




/* vim: ts=4:sw=4:expandtab */
var Internal = Internal || {};

(function() {
    'use strict';

    // Insert some bytes into the emscripten memory and return a pointer
    function _allocate(bytes) {
        var address = Module._malloc(bytes.length);
        Module.HEAPU8.set(bytes, address);

        return address;
    }

    function _readBytes(address, length, array) {
        array.set(Module.HEAPU8.subarray(address, address + length));
    }

    var basepoint = new Uint8Array(32);
    basepoint[0] = 9;

    Internal.curve25519 = {
        keyPair: function(privKey) {
            var priv = new Uint8Array(privKey);
            priv[0]  &= 248;
            priv[31] &= 127;
            priv[31] |= 64;

            // Where to store the result
            var publicKey_ptr = Module._malloc(32);

            // Get a pointer to the private key
            var privateKey_ptr = _allocate(priv);

            // The basepoint for generating public keys
            var basepoint_ptr = _allocate(basepoint);

            // The return value is just 0, the operation is done in place
            var err = Module._curve25519_donna(publicKey_ptr,
                                            privateKey_ptr,
                                            basepoint_ptr);

            var res = new Uint8Array(32);
            _readBytes(publicKey_ptr, 32, res);

            Module._free(publicKey_ptr);
            Module._free(privateKey_ptr);
            Module._free(basepoint_ptr);

            return { pubKey: res.buffer, privKey: priv.buffer };
        },
        sharedSecret: function(pubKey, privKey) {
            // Where to store the result
            var sharedKey_ptr = Module._malloc(32);

            // Get a pointer to our private key
            var privateKey_ptr = _allocate(new Uint8Array(privKey));

            // Get a pointer to their public key, the basepoint when you're
            // generating a shared secret
            var basepoint_ptr = _allocate(new Uint8Array(pubKey));

            // Return value is 0 here too of course
            var err = Module._curve25519_donna(sharedKey_ptr,
                                               privateKey_ptr,
                                               basepoint_ptr);

            var res = new Uint8Array(32);
            _readBytes(sharedKey_ptr, 32, res);

            Module._free(sharedKey_ptr);
            Module._free(privateKey_ptr);
            Module._free(basepoint_ptr);

            return res.buffer;
        },
        sign: function(privKey, message) {
            // Where to store the result
            var signature_ptr = Module._malloc(64);

            // Get a pointer to our private key
            var privateKey_ptr = _allocate(new Uint8Array(privKey));

            // Get a pointer to the message
            var message_ptr = _allocate(new Uint8Array(message));

            var err = Module._curve25519_sign(signature_ptr,
                                              privateKey_ptr,
                                              message_ptr,
                                              message.byteLength);

            var res = new Uint8Array(64);
            _readBytes(signature_ptr, 64, res);

            Module._free(signature_ptr);
            Module._free(privateKey_ptr);
            Module._free(message_ptr);

            return res.buffer;
        },
        verify: function(pubKey, message, sig) {
            // Get a pointer to their public key
            var publicKey_ptr = _allocate(new Uint8Array(pubKey));

            // Get a pointer to the signature
            var signature_ptr = _allocate(new Uint8Array(sig));

            // Get a pointer to the message
            var message_ptr = _allocate(new Uint8Array(message));

            var res = Module._curve25519_verify(signature_ptr,
                                                publicKey_ptr,
                                                message_ptr,
                                                message.byteLength);

            Module._free(publicKey_ptr);
            Module._free(signature_ptr);
            Module._free(message_ptr);

            return res !== 0;
        }
    };

    Internal.curve25519_async = {
        keyPair: function(privKey) {
            return new Promise(function(resolve) {
                resolve(Internal.curve25519.keyPair(privKey));
            });
        },
        sharedSecret: function(pubKey, privKey) {
            return new Promise(function(resolve) {
                resolve(Internal.curve25519.sharedSecret(pubKey, privKey));
            });
        },
        sign: function(privKey, message) {
            return new Promise(function(resolve) {
                resolve(Internal.curve25519.sign(privKey, message));
            });
        },
        verify: function(pubKey, message, sig) {
            return new Promise(function(resolve, reject) {
                if (Internal.curve25519.verify(pubKey, message, sig)) {
                    reject(new Error("Invalid signature"));
                } else {
                    resolve();
                }
            });
        },
    };

})();

var Internal = Internal || {};
// I am the worker
this.onmessage = function(e) {
    Internal.curve25519_async[e.data.methodName].apply(null, e.data.args).then(function(result) {
        postMessage({ id: e.data.id, result: result });
    }).catch(function(error) {
        postMessage({ id: e.data.id, error: error.message });
    });
};

})();