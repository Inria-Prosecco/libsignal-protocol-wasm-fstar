
// To be loaded by main.js
var my_js_files = [];
var my_modules = ["WasmSupport", "FStar", "C_Endianness", "C_String", "TestLib", "Hacl_Hash_SHA2", "Hacl_Impl_AES_256_CBC", "Hacl_Curve25519_51", "Hacl_Ed25519", "Impl_Signal_Crypto", "Impl_Signal_Core", "Test_Impl_Signal"];
var my_debug = false;

if (typeof module !== "undefined")
  module.exports = {
    my_js_files: my_js_files,
    my_modules: my_modules,
    my_debug: my_debug
  }
