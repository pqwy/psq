(* Copyright (c) 2016 David Kaloper Meršinjak. All rights reserved.
   See LICENSE.md *)

let shuffle arr =
  let n = Array.length arr in
  for i = 0 to n - 2 do
    let j = Random.int (n - i) + i in
    let t = arr.(i) in
    arr.(i) <- arr.(j); arr.(j) <- t
  done

let permutation n =
  let arr = Array.init n (fun x -> x) in
  shuffle arr;
  Array.to_list arr

module type S = sig
  type t
  val add     : int -> int -> t -> t
  val find    : int -> t -> int option
  val remove  : int -> t -> t
  val of_list : (int * int) list -> t
end
module I = struct type t = int let compare (a: int) b = compare a b end
let q = (module Psq.Make (I) (I): S)
let m = (module struct
  module M = Map.Make (I)
  type t = int M.t
  let find, add, remove = M.(find_opt, add, remove)
  let of_list xs = List.fold_left (fun m (k, v) -> M.add k v m) M.empty xs
end: S)

open Unmark

let runs ((module M: S)) size =
  let xs = permutation size |> List.map (fun x -> x, x) in
  let q  = M.of_list xs
  and q' = List.map (fun (k, p) -> (k * 2, p * 2)) xs |> M.of_list in
  group (Fmt.strf "x%d" size) [
    bench "find" (fun () -> M.find (Random.int size) q)
  ; bench "add" (fun () -> let k = Random.int size + 1 in M.add k k q')
  ; bench "remove" (fun () -> M.remove (Random.int size) q)
  ]

let _ = Unmark_cli.main "psq" [
    bench "Random.int" (fun () -> Random.int 1000)
  ; group "map" [runs m 10; runs m 100; runs m 1000]
  ; group "psq" [runs q 10; runs q 100; runs q 1000]
  ]
