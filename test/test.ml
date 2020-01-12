(* Copyright (c) 2016 David Kaloper Meršinjak. All rights reserved.
   See LICENSE.md *)

let id x = x
let (%) f g x = f (g x)

module I = struct type t = int let compare (a: int) b = compare a b end
module Q = Psq.Make (I) (I)

let list_of_iter_2 i =
  let xs = ref [] in i (fun a b -> xs := (a, b) :: !xs); List.rev !xs
let rec unfold f s = match f s with Some (x, s) -> x :: unfold f s | _ -> []

let cmpi (a: int) b = compare a b
let (%%) f g a b = f (g a) (g b)
let (=>) cmp1 cmp2 a b = match cmp1 a b with 0 -> cmp2 a b | r -> r
let k_order xs = List.sort (cmpi %% fst) xs
let pk_order xs = List.sort (cmpi %% snd => cmpi %% fst) xs
let k_order_uniq xs =
  let cmp_kp = cmpi %% fst => cmpi %% snd and cmp_k = cmpi %% fst in
  match List.sort_uniq cmp_kp xs with
  | [] -> []
  | kp0::kps ->
      let f kp xs kp0 = if cmp_k kp kp0 = 0 then xs kp0 else kp :: xs kp in
      kp0 :: List.fold_right f kps (fun _ -> []) kp0

let is_balanced q =
  let (n, d) = Q.(size q, depth q) in
  n <= 1 || float d < log (float n) *. log 10. *. 3.75

let (!) q = `Sem (Q.to_list q)
let sem xs = `Sem (k_order_uniq xs)

let g_size = QCheck.Gen.(small_nat >|= fun x -> x mod 1_000)
let bindings = QCheck.(
  make Gen.(list_size g_size (pair small_nat small_nat))
    ~print:Fmt.(to_to_string Dump.(pair int int |> list))
    ~shrink:Shrink.list)
let psq = QCheck.(
  map Q.of_list bindings ~rev:Q.to_list |>
    set_print Fmt.(to_to_string (Q.pp_dump int int)))
let kv = QCheck.small_nat
let psq_w arb = QCheck.pair psq arb
let psq_w_any_key = psq_w kv

let test name gen p =
  QCheck.Test.make ~count:200 ~name gen p |> QCheck_alcotest.to_alcotest

let () = Alcotest.run "psq" [

  "of_list", [
    test "sem" bindings (fun xs -> !(Q.of_list xs) = sem xs);
    test "of_sorted_list sem" bindings
      (fun xs -> !(Q.of_sorted_list (k_order_uniq xs)) = sem xs);
    test "bal" bindings (fun xs -> is_balanced (Q.of_list xs));
  ];

  "to_list", [
    test "order" psq (fun q -> Q.to_list q = k_order (Q.to_list q));
  ];

  "to_priority_list", [
    test "sem" psq (fun q -> Q.to_priority_list q = pk_order (Q.to_list q))
  ];

  "size", [
    test "sem" psq (fun q -> Q.size q = List.length (Q.to_list q));
  ];

  "sg", [
    test "sem" kv (fun x -> !Q.(sg x x) = sem [x, x]);
  ];

  "(++)", [
    test "sem" QCheck.(pair bindings bindings)
      (fun (xs1, xs2) -> !Q.(of_list xs1 ++ of_list xs2) = sem (xs1 @ xs2));
    test "comm" QCheck.(pair psq psq)
      (fun (q1, q2) -> !Q.(q1 ++ q2) = !Q.(q2 ++ q1));
    test "assoc" QCheck.(pair psq psq |> pair psq)
      (fun (q1, (q2, q3)) -> !Q.((q1 ++ q2) ++ q3) = !Q.(q1 ++ (q2 ++ q3)));
  ];

  "split_at", [
    test "sem" psq_w_any_key (fun (q, k) ->
      let q1, q2 = Q.split_at k q
      and xs1, xs2 = List.partition (fun (k1, _) -> k1 <= k) (Q.to_list q) in
      !q1 = sem xs1 && !q2 = sem xs2);
    test "inv" psq_w_any_key (fun (q, k) ->
      let q1, q2 = Q.split_at k q in !q = !Q.(q1 ++ q2));
  ];

  "membership", [
    test "find sem" psq_w_any_key
      (fun (q, x) -> Q.find x q = List.assoc_opt x (Q.to_list q));
    test "mem ==> find" psq_w_any_key
      (fun (q, k) -> QCheck.assume Q.(mem k q); Q.find k q <> None);
    test "find ==> mem" psq_w_any_key
      (fun (q, k) -> QCheck.assume (Q.find k q <> None); Q.mem k q);
  ];

  "update", [
    test "sem" (psq_w QCheck.(pair kv (option kv)))
      (fun (q, (x, yy)) ->
        let kp = match yy with Some y -> [x, y] | _ -> [] in
        !(Q.update x (fun _ -> yy) q) =
          sem (kp @ List.remove_assoc x (Q.to_list q)));
    test "bal" (psq_w QCheck.(pair kv (option kv)))
      (fun (q, (x, yy)) -> is_balanced (Q.update x (fun _ -> yy) q));
    test "phys" psq_w_any_key (fun (q, x) -> Q.update x id q == q);
  ];

  "add", [
    test "sem" psq_w_any_key
      (fun (q, x) ->
        !(Q.add x x q) = sem ((x, x) :: List.remove_assoc x (Q.to_list q)));
    test "bal" psq_w_any_key (fun (q, k) -> is_balanced (Q.add k k q));
  ];

  "push", [
    test "sem" psq_w_any_key
      (fun (q, x) ->
        let p = match List.assoc_opt x (Q.to_list q) with
        | Some p0 -> min x p0
        | None -> x in
        !(Q.push x x q) = sem ((x, p) :: List.remove_assoc x (Q.to_list q)));
    test "mono" psq_w_any_key
       (fun (q, x) ->
         QCheck.assume (Q.mem x q);
         Q.find x (Q.push x x q) <= Q.find x q);
    test "comm" (psq_w (QCheck.pair kv kv))
      (fun (q, (x, y)) ->
        !Q.(q |> push x x |> push x y) = !Q.(q |> push x y |> push x x));
    test "= of_list" bindings
      (fun xs ->
        !(Q.of_list xs) =
          !(List.fold_left (fun q (k, p) -> Q.push k p q) Q.empty xs));
  ];

  "remove", [
    test "sem" psq_w_any_key
      (fun (q, k) ->
        !(Q.remove k q) = sem (List.remove_assoc k (Q.to_list q)));
    test "phys" psq_w_any_key
      (fun (q, k) -> QCheck.assume (not (Q.mem k q)); Q.remove k q == q);
    test "bal" psq_w_any_key (fun (q, k) -> Q.(remove k q |> is_balanced));
  ];

  "adjust", [
    test "sem" psq_w_any_key
      (fun (q, x) ->
        !(Q.adjust x succ q) =
          sem (Q.to_list q |>
            List.map (fun (k, p) -> (k, if k = x then succ p else p))));
  ];

  "pop", [
    test "sem1" psq (fun q -> unfold Q.pop q = pk_order (Q.to_list q));
    test "sem2" psq (fun q -> unfold Q.pop q = Q.to_priority_list q);
    test "min, rest" psq
      (fun q ->
        QCheck.assume (not (Q.is_empty q));
        match Q.(pop q, min q, rest q) with
          Some (kp1, q1), Some kp2, Some q2 -> kp1 = kp2 && !q1 = !q2
        | _ -> false);
  ];

  "at_most", [
    test "sem" psq_w_any_key
      (fun (q, x) ->
        List.of_seq (Q.to_seq_at_most x q) =
          List.filter (fun kp -> snd kp <= x) (Q.to_list q));
    test "seq = fold" psq_w_any_key
      (fun (q, x) ->
        List.of_seq (Q.to_seq_at_most x q) =
          Q.fold_at_most x (fun k p xs -> (k, p)::xs) [] q);
    test "seq = iter" psq_w_any_key
      (fun (q, x) ->
        List.of_seq (Q.to_seq_at_most x q) =
          list_of_iter_2 (fun f -> Q.iter_at_most x f q));
  ];

  "to_stuff", [
    test "to_list = to_seq" psq
      (fun q -> Q.to_list q = (Q.to_seq q |> List.of_seq));
    test "to_list = fold" psq
      (fun q -> Q.to_list q = Q.fold (fun k p xs -> (k, p) :: xs) [] q);
    test "to_list = iter" psq
      (fun q -> Q.to_list q = list_of_iter_2 (fun f -> Q.iter f q));
    test "to_priority_seq" psq
      (fun q -> Q.to_priority_list q = List.of_seq (Q.to_priority_seq q));
  ];

  "filter", [
    test "sem" psq_w_any_key
      (fun (q, k0) ->
        !(Q.filter (fun k _ -> k <= k0) q) =
          sem (List.filter (fun (k, _) -> k <= k0) (Q.to_list q)));
    test "bal" psq_w_any_key
      (fun (q, k0) -> is_balanced (Q.filter (fun k _ -> k <= k0) q));
  ];
]
