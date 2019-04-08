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

let r_bindings n = permutation n |> List.rev_map (fun x -> x, x)

module type S = sig
  type t
  val add     : int -> int -> t -> t
  val find    : int -> t -> int option
  val remove  : int -> t -> t
  val of_list : (int * int) list -> t
end
module I = struct type t = int let compare (a: int) b = compare a b end
module Q = Psq.Make (I)(I)
let q = (module Q: S)
let m = (module struct
  module M = Map.Make (I)
  type t = int M.t
  let find, add, remove = M.(find_opt, add, remove)
  let of_list xs = List.fold_left (fun m (k, v) -> M.add k v m) M.empty xs
end: S)

open Unmark

let runs ((module M: S)) size =
  let xs = r_bindings size in
  let q  = M.of_list xs
  and q' = List.rev_map (fun (k, p) -> (k * 2, p * 2)) xs |> M.of_list in
  group (Fmt.strf "x%d" size) [
    bench "find" (fun () -> M.find (Random.int size) q)
  ; bench "add" (fun () -> let k = Random.int size + 1 in M.add k k q')
  ; bench "remove" (fun () -> M.remove (Random.int size) q)
  ]

let runs1 size =
  let xs = r_bindings size in
  let q = Q.of_list xs in
  group (Fmt.strf "x%d" size) [
    group "of_" [
      bench "of_sorted_list" (fun () -> Q.of_sorted_list xs)
    ; bench "of_list" (fun () -> Q.of_list xs)
    ; bench "of_seq" (fun () -> Q.of_seq (List.to_seq xs))
    ; bench "add_seq" (fun () -> Q.(add_seq (List.to_seq xs) empty))
    ];
    group "to_" [
      bench "to_p_list" (fun () -> Q.to_priority_list q)
    ; bench "to_seq" (fun () -> Q.to_seq q |> Seq.iter ignore)
    ; bench "to_list" (fun () -> Q.to_list q)
    ]
  ]

let arg = Cmdliner.Arg.(
  value @@ opt (list int) [10; 100; 1000] @@ info ["sizes"])
let _ = Unmark_cli.main_ext "psq" ~arg @@ fun ns -> [
    bench "Random.int" (fun () -> Random.int 1000)
  ; group "map" (List.map (runs m) ns)
  ; group "psq" (List.map (runs q) ns)
  ; group "psq1" (List.map runs1 ns)
]
