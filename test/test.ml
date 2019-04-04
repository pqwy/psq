(* Copyright (c) 2016 David Kaloper Meršinjak. All rights reserved.
   See LICENSE.md *)

let id x = x
let (%) f g x = f (g x)

module I = struct type t = int let compare (a: int) b = compare a b end
module Q = Psq.Make (I) (I)


let g_asc_uniq (type a) cmp gen n s = (* at most *)
  let module S = Set.Make (struct type t = a let compare = cmp end) in
  let rec go acc = function
    0 -> S.elements acc
  | n -> go (S.add (gen s) acc) (n - 1) in
  go S.empty n

let g_uniq (type a) cmp gen n s =
  let module S = Set.Make (struct type t = a let compare = cmp end) in
  let rec go acc = function
    0 -> []
  | n -> let x = gen s in
         if S.mem x acc then go acc (n - 1) else x :: go (S.add x acc) (n - 1) in
  go S.empty n

let list_of_iter_2 i =
  let xs = ref [] in i (fun a b -> xs := (a, b) :: !xs); List.rev !xs

let rec list_eq eq xs ys = match xs, ys with
  [], [] -> true
| x::xs, y::ys -> eq x y && list_eq eq xs ys
| _ -> false

let pp_bds = Fmt.(Dump.(list (pair int int)))
let pp_q ppf q =
  let sep ppf () = Fmt.pf ppf ";@ "
  and kp = Fmt.(Dump.pair int int) in
  Fmt.pf ppf "of_sorted_list [@[%a@]]" (Q.pp ~sep kp) q

let rec to_priorities q = match Q.pop q with
  Some (kp, q) -> kp :: to_priorities q
| None         -> []
let cmpi (a: int) b = compare a b
let cmp_k (k1, _) (k2, _) = cmpi k1 k2
let cmp_p (_, p1) (_, p2) = cmpi p1 p2
let sorted_by_k xs = List.sort cmp_k xs
let sorted_by_p xs = List.sort cmp_p xs
let (=|=) = list_eq (fun b1 b2 -> cmp_k b1 b2 = 0 && cmp_p b1 b2 = 0)
let (=~=) q1 q2 = Q.to_list q1 =|= Q.to_list q2

let g_binding = QCheck.Gen.(pair small_nat small_nat)
let g_bindings = QCheck.Gen.list g_binding
let g_uniq_bindings = QCheck.Gen.sized @@ fun n s ->
  g_uniq cmp_k g_binding n s
let g_uniq_asc_bindings = QCheck.Gen.sized @@ fun n s ->
  g_asc_uniq cmp_k g_binding n s
let bindings, uniq_bindings, uniq_asc_bindings =
  let print = Fmt.(to_to_string pp_bds)
  and shrink = QCheck.Shrink.list in
  QCheck.(make ~print ~shrink g_bindings,
          make ~print ~shrink g_uniq_bindings,
          make ~print ~shrink g_uniq_asc_bindings)
let psq = QCheck.(
  map ~rev:Q.to_list Q.of_sorted_list uniq_asc_bindings |>
    set_print Fmt.(to_to_string pp_q))
let psq_w_any_key = QCheck.(pair psq small_nat)


let balanced q =
  let (n, d) = Q.(size q, depth q) in
  n <= 1 || float d < log (float n) *. log 10. *. 3.75

let test name gen p =
  QCheck.Test.make ~name gen p |> QCheck_alcotest.to_alcotest

let () = Alcotest.run "psq" [

  "of_sorted_list", [
    test "k-order" uniq_asc_bindings
      Q.(fun xs -> to_list (of_sorted_list xs) = xs);
    test "p-order" uniq_asc_bindings
      Q.(fun xs -> to_priorities (of_sorted_list xs) = sorted_by_p xs);
    test "balance" uniq_asc_bindings (balanced % Q.of_sorted_list);
  ];

  "of_list", [
    test "k-order" uniq_bindings
      Q.(fun xs -> to_list (of_list xs) = sorted_by_k xs);
    test "p-order" uniq_bindings
      Q.(fun xs -> to_priorities (of_list xs) = sorted_by_p xs);
    test "balance" uniq_bindings (balanced % Q.of_list);
    test "k-uniqueness" bindings
      (fun xs ->
        Q.(to_list (of_list xs) |> List.map fst)
          = List.(map fst xs |> sort_uniq cmpi));
  ];

  "add", [
    test "k-order" psq_w_any_key
      (fun (q, k) ->
        Q.(to_list (add k k q)) =|=
          ((k, k) :: List.remove_assoc k (Q.to_list q) |> sorted_by_k));
    (* test "p-order" psq_w_any_key *)
    (*   (fun (q, k) -> *)
    (*     to_priorities (Q.add k k q) =|= *)
    (*       ((k, k) :: List.remove_assoc k (to_priorities q) |> sorted_by_p)); *)
    test "p-order" psq_w_any_key
      (fun (q, k) ->
        (Q.add k k q |> to_priorities |> List.map snd) =
          List.(k :: (remove_assoc k (to_priorities q) |> map snd) |> sort cmpi));
    test "balance" psq_w_any_key (fun (q, k) -> balanced (Q.add k k q));
    test "mem" psq_w_any_key (fun (q, k) -> Q.(add k k q |> mem k));
    test "find" psq_w_any_key (fun (q, k) -> Q.(add k k q |> find k) = Some k);
    test "size" psq_w_any_key
      Q.(fun (q, k) -> size (add k k q) = size q + if mem k q then 0 else 1);
  ];

  "mem", [
    test "all" psq
      (fun q -> Q.to_list q |> List.for_all
        (fun (k, _) -> Q.mem k q));
    test "=> find" psq_w_any_key
      (fun (q, k) -> QCheck.assume Q.(mem k q); Q.find k q <> None);
  ];

  "find", [
    test "all" psq
      (fun q -> Q.to_list q |> List.for_all
        (fun (k, p) -> Q.find k q = Some p));
    test "=> mem" psq_w_any_key
      (fun (q, k) -> QCheck.assume (Q.find k q <> None); Q.mem k q);
  ];

  "remove", [
    test "all" psq
      (fun q -> Q.to_list q |>
        List.for_all (fun (k, _) -> not Q.(remove k q |> mem k)));
    test "mem" psq_w_any_key (fun (q, k) -> not Q.(remove k q |> mem k));
    test "size" psq_w_any_key
      (fun (q, k) ->
        Q.(remove k q |> size) = Q.size q - if Q.mem k q then 1 else 0);
    test "balance" psq_w_any_key (fun (q, k) -> Q.(remove k q |> balanced));
  ];

  "adjust", [
    test "all" psq
      (fun q -> Q.to_list q |> List.for_all (fun (k, p) ->
        let q' = Q.adjust succ k q in
        Q.find k q' = Some (p + 1) && Q.size q = Q.size q'));
    test "find" psq_w_any_key
      (fun (q, k) ->
        Q.(adjust succ k q |> find k)
          = (match Q.find k q with Some p -> Some (p + 1) | _ -> None));
  ];

  "minimum", [
    test "pop = (min, rest)" psq
      (fun q ->
        QCheck.assume (not (Q.is_empty q));
        match Q.(pop q, min q, rest q) with
          Some (kp1, q1), Some kp2, Some q2 -> kp1 = kp2 && q1 =~= q2
        | _ -> false);
    test "min + rest" psq
      (fun q -> q =~=
        Q.(match pop q with Some ((k, p), q) -> add k p q | _ -> empty));
  ];

  "at_most", [
    test "<= p" psq_w_any_key
      (fun (q, p0) -> Q.fold_at_most p0 (fun _ p acc -> p <= p0 && acc) true q);
    test "ordered" psq_w_any_key
      (fun (q, p0) ->
        let xs = Q.fold_at_most p0 (fun k _ xs -> k::xs) [] q in
        xs = List.sort cmpi xs);
    test "fold = iter" psq_w_any_key
      (fun (q, p0) ->
        Q.fold_at_most p0 (fun k p xs -> (k, p)::xs) [] q
          =|= list_of_iter_2 (fun f -> Q.iter_at_most p0 f q));
    test "seq = fold" psq_w_any_key
      (fun (q, p0) ->
        (Q.seq_at_most p0 q |> List.of_seq)
          =|= Q.fold_at_most p0 (fun k p xs -> (k, p) :: xs) [] q);
  ];

  "aggregate", [
    test "to_list = fold" psq
      (fun q -> Q.to_list q =|= Q.fold (fun k p xs -> (k, p) :: xs) [] q);
    test "to_list = iter" psq
      (fun q -> Q.to_list q =|= list_of_iter_2 (fun f -> Q.iter f q));
    test "to_list = to_seq" psq
      (fun q -> Q.to_list q =|= (Q.to_seq q |> List.of_seq));
  ];

  "p selection",
  let f x k p = (k + p) / 2 < x in
  let wf q0 f q =
    (Q.to_list q |> List.for_all (fun (k, p) -> f k p)) &&
    balanced q &&
    Q.size q <= Q.size q0 in
  [ test "filter wf" psq_w_any_key
      (fun (q0, k0) -> let p = f k0 in Q.filter p q0 |> wf q0 p);
    test "partition wf" psq_w_any_key
      (fun (q0, k0) ->
        let p = f k0 in let (q1, q2) = Q.partition p q0 in
        wf q0 p q1 && wf q0 (fun x -> not % p x) q2);
    test "partition = filter" psq_w_any_key
      (fun (q, k) -> Q.(partition (f k) q |> fst) =~= Q.(filter (f k) q));
    test "partition inverse" psq_w_any_key
      (fun (q, k) ->
        let (q1, q2) = Q.partition (f k) q in
        q =~= Q.(to_list q1 @ to_list q2 |> of_list))
  ]
]
