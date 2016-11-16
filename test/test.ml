(* Copyright (c) 2016 David Kaloper Meršinjak. All rights reserved.
   See LICENSE.md *)

module At = Alcotest
module I = struct type t = int let compare (a: int) b = compare a b end
module Q = Psq.Make (I) (I)

let pp = Q.pp_dump Format.pp_print_int Format.pp_print_int

let lsort = List.sort (fun (k1, _) (k2, _) -> compare k1 k2)

let uniq (type a) ?(cmp=compare) xs =
  let module S = Set.Make (struct type t = a let compare = cmp end) in
  let rec sieve s = function
    | []                   -> []
    | x::xs when S.mem x s -> sieve s xs
    | x::xs                -> x :: sieve (S.add x s) xs in
  sieve S.empty xs

let init f n =
  let rec go i =
    if i >= n then [] else
      let x = f i in x :: go (succ i) in
  go 0

let randoms n = init (fun _ -> Random.int n) n |> uniq

let balanced q =
  let (n, d) = Q.(size q, depth q) in
  n <= 1 || float d < log (float n) *. log 10. *. 3.75

let ck_balance q =
  if not (balanced q) then
    At.fail (Format.asprintf "not balanced:@;%a\n%!" pp q)

let mk ?(sort = false) n =
  let xs = randoms n |> List.map (fun x -> (x, x)) in
  if sort then
    let xs = lsort xs in (xs, Q.of_list xs)
  else (xs, Q.of_list xs)

let t_of_sorted n () =
  let xs = randoms n |> List.map (fun x -> (x, x)) |> lsort in
  let q  = Q.of_sorted_list xs in
  ck_balance q;
  At.(check (list (pair int int))) "sorted ctor -> ordered" xs (Q.to_list q)

let t_ctor ?sort n () =
  let (xs, q) = mk ?sort n in
  At.(check (list (pair int int))) "to_list" (lsort xs) (Q.to_list q);
  ck_balance q

let t_find ?sort n () =
  let (xs, q) = mk ?sort n in
  xs |> List.iter @@ fun (k, p) ->
    At.(check (option int)) "find" (Some p) (Q.find k q)

let t_remove ?sort n () =
  let (xs, q) = mk ?sort n in
  let f q (k, p) =
    let s  = Q.size q in
    let q' = Q.remove k q in
    ck_balance q';
    At.(check (option int)) "present" (Some p) (Q.find k q);
    At.(check (option int)) "removed" None (Q.find k q');
    At.(check int) "smaller" (s - 1) (Q.size q');
    q' in
  List.fold_left f q xs |> ignore

let t_prio ?sort n () =
  let rec drain q = match Q.pop q with
    | None         -> []
    | Some (kp, q) -> kp :: drain q in
  let (xs, q) = mk ?sort n in
  let ys = drain q in
  At.(check (list (pair int int))) "ascending" (lsort xs) ys

let t_replace ?sort n () =
  let (xs, q) = mk ?sort n in
  let f q (k, _) = ck_balance q; Q.add k (k * 13) q in
  let q' = List.fold_left f q xs in
  At.(check int) "same size" (Q.size q) (Q.size q');
  At.(check (list (pair int int))) "new bindings"
    (List.map (fun (k, _) -> (k, k * 13)) xs |> lsort)
    (Q.to_list q')

let t_adjust ?sort n () =
  let (xs, q) = mk ?sort n in
  let f q (k, _) =
    ck_balance q; Q.adjust succ k q in
  let q' = List.fold_left f q xs in
  At.(check int) "same size" (Q.size q) (Q.size q');
  At.(check (list (pair int int))) "new bindings"
    (List.map (fun (k, p) -> (k, succ p)) xs |> lsort)
    (Q.to_list q')

let t_balance ?sort n () = mk ?sort n |> snd |> ck_balance

let suite ~sort n = [
  "of_list", `Quick, t_ctor    ~sort n;
  "find"   , `Quick, t_find    ~sort n;
  "rem"    , `Quick, t_remove  ~sort n;
  "prio"   , `Quick, t_prio    ~sort n;
  "replace", `Quick, t_replace ~sort n;
  "adjust" , `Quick, t_adjust  ~sort n;
  "balance", `Quick, t_balance ~sort n;
]

let () = Random.self_init ()
let () = At.run "psq" [
  "random", suite ~sort:false 1000;
  "asc"   , suite ~sort:true  1000;
  "asc+"  , [
    "of_sorted", `Quick, t_of_sorted 1000
  ]
]
