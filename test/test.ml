(* Copyright (c) 2016 David Kaloper Meršinjak. All rights reserved.
   See LICENSE.md *)

let id x = x
let (%) f g x = f (g x)

module I = struct type t = int let compare (a: int) b = compare a b end
module Q = Psq.Make (I) (I)

let list_of_iter_2 i =
  let xs = ref [] in i (fun a b -> xs := (a, b) :: !xs); List.rev !xs
let sort_uniq_r (type a) cmp xs =
  let module S = Set.Make (struct type t = a let compare = cmp end) in
  List.fold_right S.add xs S.empty |> S.elements
let rec unfold f s = match f s with Some (x, s) -> x :: unfold f s | _ -> []

let cmpi (a: int) b = compare a b
let cmp_k (k1, _) (k2, _) = cmpi k1 k2
let cmp_p (_, p1) (_, p2) = cmpi p1 p2
let sorted_by_k xs = List.sort cmp_k xs
let sorted_by_p = List.sort @@ fun b1 b2 ->
  match cmp_p b1 b2 with 0 -> cmp_k b1 b2 | x -> x

let balanced q =
  let (n, d) = Q.(size q, depth q) in
  n <= 1 || float d < log (float n) *. log 10. *. 3.75

let (!) q = `Sem Q.(to_list q, to_priority_list q, size q)
let sem xs =
  let xs = sort_uniq_r cmp_k xs in
  `Sem (xs, sorted_by_p xs, List.length xs)

let size = QCheck.Gen.(small_nat >|= fun x -> x mod 1_000)
let bindings = QCheck.(
  make Gen.(list_size size (pair small_nat small_nat))
    ~print:Fmt.(to_to_string Fmt.(Dump.(list (pair int int))))
    ~shrink:Shrink.list)
let psq = QCheck.(
  map Q.of_list bindings ~rev:Q.to_list |>
    set_print Fmt.(to_to_string (Q.pp_dump int int)))
let psq_w_any_key = QCheck.(pair psq small_nat)

let test name gen p =
  QCheck.Test.make ~count:200 ~name gen p |> QCheck_alcotest.to_alcotest

let () = Alcotest.run "psq" [

  "of_list", [
    test "sem" bindings
      (fun xs -> !(Q.of_list xs) = sem xs);
    test "of_sorted_list sem" bindings
      (fun xs -> !(Q.of_sorted_list (sort_uniq_r cmp_k xs)) = sem xs);
    test "bal" bindings (fun xs -> balanced (Q.of_list xs));
    test "of_sorted_list bal" bindings
      (fun xs -> balanced (Q.of_sorted_list xs));
  ];

  "sg", [
    test "sem" QCheck.small_nat (fun x -> !Q.(sg x x) = sem [x, x]);
  ];

  "(++)", [
    test "sem" QCheck.(pair bindings bindings)
      (fun (xs1, xs2) -> !Q.(of_list xs1 ++ of_list xs2) = sem (xs1 @ xs2));
  ];

  "size", [
    test "sem" psq (fun q -> Q.size q = List.length (Q.to_list q));
  ];

  "membership", [
    test "find sem" psq_w_any_key
      (fun (q, x) -> Q.find x q = List.assoc_opt x (Q.to_list q));
    test "mem ==> find" psq_w_any_key
      (fun (q, k) -> QCheck.assume Q.(mem k q); Q.find k q <> None);
    test "find ==> mem" psq_w_any_key
      (fun (q, k) -> QCheck.assume (Q.find k q <> None); Q.mem k q);
  ];

  "add", [
    test "sem" psq_w_any_key
      (fun (q, x) ->
        !(Q.add x x q) = sem ((x, x) :: List.remove_assoc x (Q.to_list q)));
    test "= of_list" bindings
      (fun xs ->
        !(Q.of_list xs) =
          !(List.fold_left (fun q (k, p) -> Q.add k p q) Q.empty xs));
    test "bal" psq_w_any_key (fun (q, k) -> balanced (Q.add k k q));
  ];

  "remove", [
    test "sem" psq_w_any_key
      (fun (q, k) ->
        !(Q.remove k q) = sem (List.remove_assoc k (Q.to_list q)));
    test "phys" psq_w_any_key
      (fun (q, k) -> QCheck.assume (not (Q.mem k q)); Q.remove k q == q);
    test "bal" psq_w_any_key (fun (q, k) -> Q.(remove k q |> balanced));
  ];

  "adjust", [
    test "sem" psq_w_any_key
      (fun (q, x) ->
        !(Q.adjust x succ q) =
          sem (Q.to_list q |>
            List.map (fun (k, p) -> (k, if k = x then succ p else p))));
  ];

  "pop", [
    test "sem" psq (fun q -> Q.to_priority_list q = unfold Q.pop q);
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
      (fun (q, k0) -> balanced (Q.filter (fun k _ -> k <= k0) q));
  ];
]
