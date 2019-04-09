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
  val (++) : t -> t -> t
  val is_empty : t -> bool
  val size : t -> int
  val mem : k -> t -> bool
  val find : k -> t -> p option
  val add : k -> p -> t -> t
  val remove : k -> t -> t
  val adjust : k -> (p -> p) -> t -> t
  val update : k -> (p option -> p option) -> t -> t
  val min : t -> (k * p) option
  val rest : t -> t option
  val pop : t -> ((k * p) * t) option
  val fold_at_most : p -> (k -> p -> 'a -> 'a) -> 'a -> t -> 'a
  val iter_at_most : p -> (k -> p -> unit) -> t -> unit
  val to_seq_at_most : p -> t -> (k * p) Seq.t
  val of_list : (k * p) list -> t
  val of_sorted_list : (k * p) list -> t
  val of_seq : (k * p) Seq.t -> t
  val add_seq : (k * p) Seq.t -> t -> t
  val to_list : t -> (k * p) list
  val to_seq : t -> (k * p) Seq.t
  val fold : (k -> p -> 'a -> 'a) -> 'a -> t -> 'a
  val iter : (k -> p -> unit) -> t -> unit
  val to_priority_list : t -> (k * p) list
  val to_priority_seq : t -> (k * p) Seq.t
  val filter : (k -> p -> bool) -> t -> t
  val partition : (k -> p -> bool) -> t -> t * t
  val pp : ?sep:(unit fmt) -> (k * p) fmt -> t fmt
  val pp_dump : k fmt -> p fmt -> t fmt
  val depth : t -> int
end

module L = struct
  include List
  let rec take n = function
    x::xs when n > 0 -> x :: take (pred n) xs | _ -> []
  let rec drop n = function
    _::xs when n > 0 -> drop (pred n) xs | xs -> xs
end

module Make (K: Ordered) (P: Ordered) :
  S with type k = K.t and type p = P.t =
struct

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
    Lf -> 0
  | NdL (_, _, _, _, w)
  | NdR (_, _, _, _, w) -> w

  let size = function N -> 0 | T (_, _, t) -> size_t t + 1

  let nd_l kp t1 sk t2 = NdL (kp, t1, sk, t2, size_t t1 + size_t t2 + 1)
  let nd_r kp t1 sk t2 = NdR (kp, t1, sk, t2, size_t t1 + size_t t2 + 1)

  let nd (k, _ as kp) t1 sk t2 =
    if K.compare k sk <= 0 then nd_l kp t1 sk t2 else nd_r kp t1 sk t2


  let outweighs s1 s2 = s1 * 100 > s2 * 375

  let (@<=@) (k1, p1) (k2, p2) =
    match P.compare p1 p2 with 0 -> K.compare k1 k2 <= 0 | c -> c < 0
  [@@inline]

  let rot_l kp1 t1 sk1 = function
    NdL (kp2, t2, sk2, t3, _) when kp1 @<=@ kp2 ->
      nd kp1 (nd kp2 t1 sk1 t2) sk2 t3
  | NdL (kp2, t2, sk2, t3, _) | NdR (kp2, t2, sk2, t3, _) ->
      nd kp2 (nd kp1 t1 sk1 t2) sk2 t3
  | Lf -> assert false

  let rot_r kp1 tt sk2 t3 = match tt with
    NdR (kp2, t1, sk1, t2, _) when kp1 @<=@ kp2 ->
      nd kp1 t1 sk1 (nd kp2 t2 sk2 t3)
  | NdL (kp2, t1, sk1, t2, _) | NdR (kp2, t1, sk1, t2, _) ->
      nd kp2 t1 sk1 (nd kp1 t2 sk2 t3)
  | Lf -> assert false

  let rot_ll kp1 t1 sk1 = function
    NdL (kp2, t2, sk2, t3, _) | NdR (kp2, t2, sk2, t3, _) ->
      rot_l kp1 t1 sk1 (rot_r kp2 t2 sk2 t3)
  | Lf -> assert false

  let rot_rr kp1 tt sk2 t3 = match tt with
    NdL (kp2, t1, sk1, t2, _) | NdR (kp2, t1, sk1, t2, _) ->
      rot_r kp1 (rot_l kp2 t1 sk1 t2) sk2 t3
  | Lf -> assert false

  (* Precond: at most one of t1, t2 is at most 1 away from a balanced
     configuration. *)
  let nd_bal kp t1 sk t2 =
    let s1 = size_t t1 and s2 = size_t t2 in
    match (t1, t2) with
      ((NdL (_, t11, _, t12, _) | NdR (_, t11, _, t12, _)), _)
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
    (N, t) | (t, N) -> t
  | (T (kp1, sk1, t1), T (kp2, sk2, t2)) ->
      if kp1 @<=@ kp2 then
        T (kp1, sk2, nd_bal kp2 t1 sk1 t2)
      else T (kp2, sk2, nd_bal kp1 t1 sk1 t2)
  [@@inline]

  let (>|<) (k1, _ as kp1) (k2, _ as kp2) =
    if kp1 @<=@ kp2 then
      T (kp1, k2, NdR (kp2, Lf, k1, Lf, 1))
    else T (kp2, k2, NdL (kp1, Lf, k1, Lf, 1))
  [@@inline]

  let rec promote sk0 = function
    Lf -> N
  | NdL (kp, t1, sk, t2, _) -> T (kp, sk, t1) >< promote sk0 t2
  | NdR (kp, t1, sk, t2, _) -> promote sk t1 >< T (kp, sk0, t2)

  let min = function N -> None | T (kp, _, _) -> Some kp
  let rest = function N -> None | T (_, sk, t) -> Some (promote sk t)
  let pop = function N -> None | T (kp, sk, t) -> Some (kp, promote sk t)

  let find k0 t =
    let rec go k0 = function
      Lf -> None
    | NdL ((k, p), t1, sk, t2, _)
    | NdR ((k, p), t1, sk, t2, _) ->
        if K.compare k0 k = 0 then Some p else
          if K.compare k0 sk <= 0 then go k0 t1 else go k0 t2 in
    match t with
      N -> None
    | T ((k, p), _, t) -> if K.compare k0 k = 0 then Some p else go k0 t

  let mem k0 t =
    let rec go k0 = function
      Lf -> false
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

  let to_seq_at_most p0 t () =
    foldr_at_most p0 (fun kp seq -> Seq.Cons (kp, seq)) t Seq.empty

  (* type view = Nv | Sgv of (k * p) | Binv of t * K.t * t *)

  (* let view = function *)
  (*   N -> Nv *)
  (* | T (kp, _, Lf) -> Sgv kp *)
  (* | T (kp1, sk1, NdL (kp2, t1, sk2, t2, _)) -> *)
  (*     Binv (T (kp2, sk2, t1), sk2, T (kp1, sk1, t2)) *)
  (* | T (kp1, sk1, NdR (kp2, t1, sk2, t2, _)) -> *)
  (*     Binv (T (kp1, sk2, t1), sk2, T (kp2, sk1, t2)) *)

  (* let rec add (k0, _ as kp0) t = match view t with *)
  (*   | Nv -> sg kp0 *)
  (*   | Sgv (k, _) -> *)
  (*       let c = K.compare k0 k and t' = sg kp0 in *)
  (*       if c < 0 then t' >< t else if c > 0 then t >< t' else t' *)
  (*   | Binv (t1, sk, t2) -> *)
  (*       if K.compare k0 sk <= 0 then add kp0 t1 >< t2 else t1 >< add kp0 t2 *)

  (* let remove k0 t = *)
  (*   let rec go k0 t = match view t with *)
  (*     Binv (t1, sk, t2) -> *)
  (*       if K.compare k0 sk <= 0 then go k0 t1 >< t2 else t1 >< go k0 t2 *)
  (*   | Sgv (k, _) when K.compare k k0 = 0 -> N *)
  (*   | Sgv _ | Nv -> raise_notrace Exit in *)
  (*   try go k0 t with Exit -> t *)

  (* let adjust k0 f t = *)
  (*   let rec go f k0 t = match view t with *)
  (*     Binv (t1, sk, t2) -> *)
  (*       if K.compare k0 sk <= 0 then go f k0 t1 >|< t2 else t1 >|< go f k0 t2 *)
  (*   | Sgv (k, p) when K.compare k k0 = 0 -> sg (k, f p) *)
  (*   | Sgv _ | Nv -> raise_notrace Exit in *)
  (*   try go f k0 t with Exit -> t *)

  (* let rec filter pf t = match view t with *)
  (*   Nv -> N *)
  (* | Sgv (k, p as kp) -> if pf k p then sg kp else N *)
  (* | Binv (t1, _, t2) -> filter pf t1 >< filter pf t2 *)

  let update k0 f t =
    let node f k0 p = match f p with
      Some p -> sg (k0, p) | None -> N [@@inline] in
    let rec go k0 f (k1, p1 as kp1) sk1 = function
      Lf ->
        let c = K.compare k0 k1 in
        if c = 0 then node f k0 (Some p1) else
        ( match f None with
            Some p -> if c < 0 then (k0, p) >|< kp1 else kp1 >|< (k0, p)
          | None   -> raise_notrace Exit )
    | NdL (kp2, t1, sk2, t2, _) ->
        if K.compare k0 sk2 <= 0 then
          go k0 f kp2 sk2 t1 >< T (kp1, sk1, t2)
        else T (kp2, sk2, t1) >< go k0 f kp1 sk1 t2
    | NdR (kp2, t1, sk2, t2, _) ->
        if K.compare k0 sk2 <= 0 then
          go k0 f kp1 sk2 t1 >< T (kp2, sk1, t2)
        else T (kp1, sk2, t1) >< go k0 f kp2 sk1 t2 in
    match t with
      N -> node f k0 None
    | T (kp, sk, t1) -> try go k0 f kp sk t1 with Exit -> t

  let add k p t = update k (fun _ -> Some p) t
  let remove k t = update k (fun _ -> None) t
  let adjust k f t = update k (function Some p -> Some (f p) | _ -> None) t

  let filter pf t =
    let rec go pf kp1 sk1 = function
      Lf -> if pf (fst kp1) (snd kp1) then sg kp1 else N
    | NdL (kp2, t1, sk2, t2, _) -> go pf kp2 sk2 t1 >< go pf kp1 sk1 t2
    | NdR (kp2, t1, sk2, t2, _) -> go pf kp1 sk2 t1 >< go pf kp2 sk1 t2 in
    match t with N -> N | T (kp, sk, t) -> go pf kp sk t

  let partition pf t = (filter pf t, filter (fun k p -> not (pf k p)) t)

  let of_sorted_list xs =
    let rec go n = function
      []        -> N
    | [x]       -> sg x
    | [x;y]     -> x >|< y
    | [x;y;z]   -> (x >|< y) >< sg z
    | [x;y;z;w] -> (x >|< y) >< (z >|< w)
    | xs -> let m = n / 2 in go m L.(take m xs) >< go (n - m) L.(drop m xs) in
    go (L.length xs) xs

  let cmp_k (k1, _) (k2, _) = K.compare k1 k2

  let of_list xs = Psq_list.sort_uniq cmp_k xs |> of_sorted_list

  let of_seq xs = Seq.fold_left (fun xs a -> a::xs) [] xs |> of_list

  let add_seq xs q = Seq.fold_left (fun q (k, p) -> add k p q) q xs

  let iter f t =
    let rec go (p0, k0 as pk0) f = function
      Lf -> f p0 k0
    | NdL (pk, t1, _, t2, _) -> go pk f t1; go pk0 f t2
    | NdR (pk, t1, _, t2, _) -> go pk0 f t1; go pk f t2 in
    match t with N -> () | T (pk, _, t) -> go pk f t

  let foldr f z t =
    let rec go kp0 f z = function
      Lf -> f kp0 z
    | NdL (kp, t1, _, t2, _) -> go kp f (go kp0 f z t2) t1
    | NdR (kp, t1, _, t2, _) -> go kp0 f (go kp f z t2) t1 in
    match t with N -> z | T (kp, _, t) -> go kp f z t

  let lfoldr f t z =
    let rec go kp0 f z = function
      Lf -> f kp0 z
    | NdL (kp, t1, _, t2, _) -> go kp f (fun () -> go kp0 f z t2) t1
    | NdR (kp, t1, _, t2, _) -> go kp0 f (fun () -> go kp f z t2) t1 in
    match t with T (kp, _, t) -> go kp f z t | N -> z ()

  let (++) q1 q2 = foldr (fun (k, p) q -> add k p q) q1 q2
  let fold f z t = foldr (fun (k, p) z -> f k p z) z t
  let to_list t = foldr (fun kp xs -> kp :: xs) [] t
  let to_seq t () = lfoldr (fun kp xs -> Seq.Cons (kp, xs)) t Seq.empty

  let to_priority_list t =
    let rec (--) xs ys = match xs, ys with
      [], l | l, [] -> l
    | x::xt, y::yt -> if x @<=@ y then x :: (xt -- ys) else y :: (xs -- yt) in
    let rec go = function
      Lf -> []
    | NdL (kp2, t1, _, t2, _) -> (kp2 :: go t1) -- go t2
    | NdR (kp2, t1, _, t2, _) -> go t1 -- (kp2 :: go t2) in
    match t with N -> [] | T (kp, _, t) -> kp :: go t

  let to_priority_seq t () =
    let open Seq in
    let rec (--) n1 n2 = match n1, n2 with
      Nil, n | n, Nil -> n
    | Cons (x, xt), Cons (y, yt) ->
        if x @<=@ y then
          Cons (x, fun _ -> xt () -- n2)
        else Cons (y, fun _ -> n1 -- yt ()) in
    let rec go = function
      Lf -> Nil
    | NdL (kp2, t1, _, t2, _) -> Cons (kp2, fun _ -> go t1) -- go t2
    | NdR (kp2, t1, _, t2, _) -> go t1 -- Cons (kp2, fun _ -> go t2) in
    match t with N -> Nil | T (kp, _, t) -> Cons (kp, fun _ -> go t)

  let sg k p = sg (k, p)

  let depth t =
    let rec go = function
      Lf -> 0
    | NdL (_, t1, _, t2, _) | NdR (_, t1, _, t2, _) ->
        max (go t1) (go t2) + 1 in
    match t with N -> 0 | T (_, _, t) -> go t + 1

  let pp ?(sep = Format.pp_print_space) pp ppf t =
    let first = ref true in
    let k ppf = iter @@ fun k p ->
      ( match !first with true -> first := false | _ -> sep ppf ());
      pp ppf (k, p) in
    pf ppf "@[%a@]" k t

  let pp_dump ppk ppp ppf =
    let sep ppf () = pf ppf ";@ "
    and ppkp ppf (k, p) = pf ppf "(@[%a,@ %a@])" ppk k ppp p in
    pf ppf "of_sorted_list [%a]" (pp ~sep ppkp)
end
