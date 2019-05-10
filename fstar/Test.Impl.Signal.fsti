module Test.Impl.Signal

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer


val main : unit -> Stack C.exit_code (requires (fun h -> True)) (ensures (fun h0 _ h1 -> modifies0 h0 h1))
