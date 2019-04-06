(* Copyright (c) 2016 David Kaloper Meršinjak. All rights reserved.
   See LICENSE.md *)

type 'a fmt = Format.formatter -> 'a -> unit

let pf = Format.fprintf

module type Ordered = sig type t val compare : t -> t -> int end

module type S = sig
  type t
  type k
  type p
  val empty : t
  val sg : k -> p -> t
  val is_empty : t -> bool
  val size : t -> int
  val mem : k -> t -> bool
  val find : k -> t -> p option
  val add : k -> p -> t -> t
  val remove : k -> t -> t
  val adjust: (p -> p) -> k -> t -> t
  val min : t -> (k * p) option
  val rest : t -> t option
  val pop : t -> ((k * p) * t) option
  val fold_at_most : p -> (k -> p -> 'a -> 'a) -> 'a -> t -> 'a
  val iter_at_most : p -> (k -> p -> unit) -> t -> unit
  val seq_at_most : p -> t -> (k * p) Seq.t
  val fold : (k -> p -> 'a -> 'a) -> 'a -> t -> 'a
  val filter : (k -> p -> bool) -> t -> t
  val partition : (k -> p -> bool) -> t -> t * t
  val iter : (k -> p -> unit) -> t -> unit
  val to_list : t -> (k * p) list
  val of_list : (k * p) list -> t
  val of_sorted_list : (k * p) list -> t
  val to_seq : t -> (k * p) Seq.t
  val of_seq : (k * p) Seq.t -> t
  val pp : ?sep:(unit fmt) -> (k * p) fmt -> t fmt
  val depth : t -> int
  val pp_dump : k fmt -> p fmt -> t fmt
end

module L = struct
  include List
  let rec take n = function
    x::xs when n > 0 -> x :: take (pred n) xs | _ -> []
  let rec drop n = function
    _::xs when n > 0 -> drop (pred n) xs | xs -> xs
end

module Make (K: Ordered) (P: Ordered) :
S with type k = K.t and type p = P.t = struct

  type k = K.t
  type p = P.t

  type t = (* SEARCH PENNANTS *)
      N
    | T of (k * p) * k * tree

  and tree = (* LOSER TREES, OH MY *)
      Lf
    | NdL of (k * p) * tree * k * tree * int
    | NdR of (k * p) * tree * k * tree * int

  let empty = N
  let sg (k, _ as kp) = T (kp, k, Lf)

  let is_empty = function N -> true | _ -> false

  let size_t = function
    | Lf -> 0
    | NdL (_, _, _, _, w)
    | NdR (_, _, _, _, w) -> w

  let size = function N -> 0 | T (_, _, t) -> size_t t + 1

  let nd_l kp t1 sk t2 = NdL (kp, t1, sk, t2, size_t t1 + size_t t2 + 1)
  let nd_r kp t1 sk t2 = NdR (kp, t1, sk, t2, size_t t1 + size_t t2 + 1)

  let nd (k, _ as kp) t1 sk t2 =
    if K.compare k sk <= 0 then nd_l kp t1 sk t2 else nd_r kp t1 sk t2


  let outweighs s1 s2 = s1 * 100 > s2 * 375

  let (@<=@) (k1, p1) (k2, p2) =
    let c = P.compare p1 p2 in
    if c = 0 then K.compare k1 k2 <= 0 else c < 0 [@@inline]

  let rot_l kp1 t1 sk1 = function
    | NdL (kp2, t2, sk2, t3, _) when kp1 @<=@ kp2 ->
        nd kp1 (nd kp2 t1 sk1 t2) sk2 t3
    | NdL (kp2, t2, sk2, t3, _) | NdR (kp2, t2, sk2, t3, _) ->
        nd kp2 (nd kp1 t1 sk1 t2) sk2 t3
    | Lf -> assert false

  let rot_r kp1 tt sk2 t3 = match tt with
    | NdR (kp2, t1, sk1, t2, _) when kp1 @<=@ kp2 ->
        nd kp1 t1 sk1 (nd kp2 t2 sk2 t3)
    | NdL (kp2, t1, sk1, t2, _) | NdR (kp2, t1, sk1, t2, _) ->
        nd kp2 t1 sk1 (nd kp1 t2 sk2 t3)
    | Lf -> assert false

  let rot_ll kp1 t1 sk1 = function
    | NdL (kp2, t2, sk2, t3, _) | NdR (kp2, t2, sk2, t3, _) ->
        rot_l kp1 t1 sk1 (rot_r kp2 t2 sk2 t3)
    | Lf -> assert false

  let rot_rr kp1 tt sk2 t3 = match tt with
    | NdL (kp2, t1, sk1, t2, _) | NdR (kp2, t1, sk1, t2, _) ->
        rot_r kp1 (rot_l kp2 t1 sk1 t2) sk2 t3
    | Lf -> assert false

  (* Precond: at most one of t1, t2 is at most 1 away from a balanced
     configuration. *)
  let nd_bal kp t1 sk t2 =
    let s1 = size_t t1 and s2 = size_t t2 in
    match (t1, t2) with
    | ((NdL (_, t11, _, t12, _) | NdR (_, t11, _, t12, _)), _)
      when s1 > 1 && outweighs s1 s2 ->
        if size_t t11 > size_t t12 then
          rot_r kp t1 sk t2
        else rot_rr kp t1 sk t2
    | (_, (NdL (_, t21, _, t22, _) | NdR (_, t21, _, t22, _)))
      when s2 > 1 && outweighs s2 s1 ->
        if size_t t21 < size_t t22 then
          rot_l kp t1 sk t2
        else rot_ll kp t1 sk t2
    | _ -> nd kp t1 sk t2

  let (><) t1 t2 = match (t1, t2) with
    | (N, t) | (t, N) -> t
    | (T (kp1, sk1, t1), T (kp2, sk2, t2)) ->
        if kp1 @<=@ kp2 then
          T (kp1, sk2, nd_bal kp2 t1 sk1 t2)
        else T (kp2, sk2, nd_bal kp1 t1 sk1 t2)

  (* XXX repetition, parameterise (w/ inlining) *)
  let (>|<) t1 t2 = match (t1, t2) with
    | (N, t) | (t, N) -> t
    | (T (kp1, sk1, t1), T (kp2, sk2, t2)) ->
        if kp1 @<=@ kp2 then
          T (kp1, sk2, nd_r kp2 t1 sk1 t2)
        else T (kp2, sk2, nd_l kp1 t1 sk1 t2)

  let rec promote sk0 = function
    | Lf -> N
    | NdL (kp, t1, sk, t2, _) -> T (kp, sk, t1) >< promote sk0 t2
    | NdR (kp, t1, sk, t2, _) -> promote sk t1 >< T (kp, sk0, t2)

  let min = function N -> None | T (kp, _, _) -> Some kp
  let rest = function N -> None | T (_, sk, t) -> Some (promote sk t)
  let pop = function N -> None | T (kp, sk, t) -> Some (kp, promote sk t)

  let find k0 t =
    let rec go k0 = function
      | Lf -> None
      | NdL ((k, p), t1, sk, t2, _)
      | NdR ((k, p), t1, sk, t2, _) ->
          if K.compare k0 k = 0 then Some p else
            if K.compare k0 sk <= 0 then go k0 t1 else
              go k0 t2 in
    match t with
    | N -> None
    | T ((k, p), _, t) -> if K.compare k0 k = 0 then Some p else go k0 t

  let mem k0 t =
    let rec go k0 = function
      | Lf -> false
      | NdL ((k, _), t1, sk, t2, _)
      | NdR ((k, _), t1, sk, t2, _) ->
          K.compare k0 k = 0 ||
          if K.compare k0 sk <= 0 then go k0 t1 else go k0 t2 in
    match t with N -> false | T ((k, _), _, t) -> K.compare k0 k = 0 || go k0 t

  let foldr_at_most p0 f t z =
    let rec f1 p0 (_, p as kp) f z t =
      if P.compare p p0 <= 0 then f2 p0 kp f z t else z ()
    and f2 p0 kp0 f z = function
      Lf -> f kp0 z
    | NdL (kp, t1, _, t2, _) -> f1 p0 kp f (fun () -> f2 p0 kp0 f z t2) t1
    | NdR (kp, t1, _, t2, _) -> f2 p0 kp0 f (fun () -> f1 p0 kp f z t2) t1 in
    match t with T (kp0, _, t) -> f1 p0 kp0 f z t | _ -> z ()

  let fold_at_most p0 f z t =
    foldr_at_most p0 (fun (k, p) a -> f k p (a ())) t (fun () -> z)

  let iter_at_most p0 f t =
    foldr_at_most p0 (fun (k, p) i -> f k p; i ()) t ignore

  let seq_at_most p0 t () =
    foldr_at_most p0 (fun kp seq -> Seq.Cons (kp, seq)) t Seq.empty

  (* XXX FIXME:
     Splitting the pennant while going down. Make add/remove/adjust work on bare
     trees to avoid thrashing the GC during traversal. *)

  type view = Nv | Sgv of (k * p) | Binv of t * K.t * t

  let view = function
    | N -> Nv
    | T (kp, _, Lf) -> Sgv kp
    | T (kp1, sk1, NdL (kp2, t1, sk2, t2, _)) ->
        Binv (T (kp2, sk2, t1), sk2, T (kp1, sk1, t2))
    | T (kp1, sk1, NdR (kp2, t1, sk2, t2, _)) ->
        Binv (T (kp1, sk2, t1), sk2, T (kp2, sk1, t2))

  (* let rec add (k0, _ as kp0) t = match view t with *)
  (*   | Nv -> sg kp0 *)
  (*   | Sgv (k, _) -> *)
  (*       let c = K.compare k0 k and t' = sg kp0 in *)
  (*       if c < 0 then t' >< t else if c > 0 then t >< t' else t' *)
  (*   | Binv (t1, sk, t2) -> *)
  (*       if K.compare k0 sk <= 0 then add kp0 t1 >< t2 else t1 >< add kp0 t2 *)

  (* XXX This hand-inlining of [view] is just sad. *)
  let rec add (k0, _ as kp0) = function
    | N -> sg kp0
    | T ((k, _), _, Lf) as t ->
        let t0 = sg kp0 and c = K.compare k0 k in
        if c < 0 then t0 >|< t else if c > 0 then t >|< t0 else t0
    | T (kp1, sk1, NdL (kp2, t1, sk2, t2, _)) ->
        let t = T (kp2, sk2, t1) and t' = T (kp1, sk1, t2) in
        if K.compare k0 sk2 <= 0 then add kp0 t >< t' else t >< add kp0 t'
    | T (kp1, sk1, NdR (kp2, t1, sk2, t2, _)) ->
        let t = T (kp1, sk2, t1) and t' = T (kp2, sk1, t2) in
        if K.compare k0 sk2 <= 0 then add kp0 t >< t' else t >< add kp0 t'

  let remove k0 t =
    let rec go k0 t = match view t with
      | Binv (t1, sk, t2) ->
          if K.compare k0 sk <= 0 then go k0 t1 >< t2 else t1 >< go k0 t2
      | Sgv (k, _) when K.compare k k0 = 0 -> N
      | Sgv _ | Nv -> raise_notrace Exit in
    try go k0 t with Exit -> t

  let adjust f k0 t =
    let rec go f k0 t = match view t with
      | Binv (t1, sk, t2) ->
          if K.compare k0 sk <= 0 then go f k0 t1 >|< t2 else t1 >|< go f k0 t2
      | Sgv (k, p) when K.compare k k0 = 0 -> sg (k, f p)
      | Sgv _ | Nv -> raise_notrace Exit in
    try go f k0 t with Exit -> t

  let rec filter pf t = match view t with
    | Nv -> N
    | Sgv (k, p as kp) -> if pf k p then sg kp else N
    | Binv (t1, _, t2) -> filter pf t1 >< filter pf t2

  let rec partition pf t = match view t with
    | Nv -> (N, N)
    | Sgv (k, p as kp) -> if pf k p then (sg kp, N) else (N, sg kp)
    | Binv (t1, _, t2) ->
        let (y1, n1) = partition pf t1
        and (y2, n2) = partition pf t2 in
        (y1 >< y2, n1 >< n2)


  let of_sorted_list xs =
    let rec go n = function
      | []        -> N
      | [x]       -> sg x
      | [x;y]     -> sg x >|< sg y
      | [x;y;z]   -> (sg x >|< sg y) >|< sg z
      | [x;y;z;w] -> (sg x >|< sg y) >|< (sg z >|< sg w)
      | xs -> let m = n / 2 in go m L.(take m xs) >|< go (n - m) L.(drop m xs)
    in go (L.length xs) xs

  let of_list xs =
    let cmp (k1, _) (k2, _) = K.compare k1 k2 in
    List.sort_uniq cmp xs |> of_sorted_list

  (* XXX List.of_seq can avoid reversing the list, but needs 4.7. *)
  let of_seq xs = Seq.fold_left (fun xs a -> a::xs) [] xs |> List.rev |> of_list

  let iter f t =
    let rec go (p0, k0 as pk0) f = function
      Lf -> f p0 k0
    | NdL (pk, t1, _, t2, _) -> go pk f t1; go pk0 f t2
    | NdR (pk, t1, _, t2, _) -> go pk0 f t1; go pk f t2 in
    match t with N -> () | T (pk, _, t) -> go pk f t

  let foldr f t z =
    let rec go kp0 f z = function
      Lf -> f kp0 z
    | NdL (kp, t1, _, t2, _) -> go kp f (fun () -> go kp0 f z t2) t1
    | NdR (kp, t1, _, t2, _) -> go kp0 f (fun () -> go kp f z t2) t1 in
    match t with T (kp, _, t) -> go kp f z t | N -> z ()

  let nil () = []
  let fold f z t = foldr (fun (k, p) z -> f k p (z ())) t (fun () -> z)
  let to_list t = foldr (fun kp xs -> kp :: xs ()) t nil
  let to_seq t () = foldr (fun kp xs -> Seq.Cons (kp, xs)) t Seq.empty

  let add k p = add (k, p)
  let sg k p = sg (k, p)

  let depth t =
    let rec go = function
      | Lf -> 0
      | NdL (_, t1, _, t2, _) | NdR (_, t1, _, t2, _) ->
          max (go t1) (go t2) + 1 in
    match t with N -> 0 | T (_, _, t) -> go t + 1

  let pp ?(sep = Format.pp_print_space) pp ppf t =
    let rec go pk0 cont ppf = function
      | Lf -> pf ppf "@[%a@]" pp pk0; if cont then sep ppf ()
      | NdL (pk, t1, _, t2, _) -> go pk  true ppf t1; go pk0 cont ppf t2
      | NdR (pk, t1, _, t2, _) -> go pk0 true ppf t1; go pk  cont ppf t2 in
    match t with N -> () | T (pk, _, t) -> pf ppf "@[%a@]" (go pk false) t

  let pp_dump ppk ppp ppf t =
    let rec go ppf = function
      | Lf -> Format.pp_print_string ppf "*"
      | NdL ((k, p), t1, sk, t2, w)
      | NdR ((k, p), t1, sk, t2, w) ->
          pf ppf "  @[<v>%a@]@,%a/%a -> %a #%d@,  @[<v>%a@]"
            go t1 ppk k ppk sk ppp p w go t2 in
    match t with
    | N -> ()
    | T ((k, p), sk, t1) ->
        pf ppf "%a/%a -> %a@,  @[<v>%a@]" ppk k ppk sk ppp p go t1
end
