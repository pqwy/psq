(* Copyright (c) 2016 David Kaloper Meršinjak. All rights reserved.
   See LICENSE.md *)

module I = struct type t = int let compare (a: int) b = compare a b end
module Q = Psq.Make (I) (I)
module M = Map.Make (I)

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

let runs name ~of_list ~add ~find ~remove size =
  let (n, measure) = (1000, `Cputime_ns) in
  let xs = permutation size |> List.map (fun x -> x, x) in
  let q  = of_list xs
  and q' = List.map (fun (k, p) -> (k * 2, p * 2)) xs |> of_list in
  Format.printf "\n%s / %d\n%!" name size;
  Unmark.time ~tag:"find" ~measure ~n
    (fun () -> for i = 0 to size - 1 do find i q done);
  Unmark.time ~tag:"add" ~measure ~n (fun () ->
    for i = 0 to size - 1 do let k = i * 2 + 1 in add k k q' done);
  Unmark.time ~tag:"remove" ~measure ~n
    (fun () -> for i = 0 to size - 1 do remove i q done);
  ()

let m_of_list xs =
  List.fold_left (fun m (k, v) -> M.add k v m) M.empty xs

let () =
  Unmark.warmup ();
  let (of_list, add, find, remove) = M.(m_of_list, add, find, remove) in
  runs "map" ~of_list ~add ~find ~remove 10;
  runs "map" ~of_list ~add ~find ~remove 100;
  runs "map" ~of_list ~add ~find ~remove 1000;
  let (of_list, add, find, remove) = Q.(of_list, add, find, remove) in
  runs "psq" ~of_list ~add ~find ~remove 10;
  runs "psq" ~of_list ~add ~find ~remove 100;
  runs "psq" ~of_list ~add ~find ~remove 1000;
  ()

