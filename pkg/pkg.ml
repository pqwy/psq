#!/usr/bin/env ocaml
#use "topfind"
#require "topkg"
open Topkg

let speed = Conf.(key ~doc:"Build benchmarks" "benchmarks" bool ~absent:false)

let () =
  Pkg.describe "psq" @@ fun c ->
  let speed = Conf.value c speed in
  Ok [ Pkg.mllib ~api:["Psq"] "src/psq.mllib";
       Pkg.test "test/test";
       Pkg.test ~cond:speed ~run:false "test/bench"; ]
