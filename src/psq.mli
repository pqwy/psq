(* Copyright (c) 2016 David Kaloper Meršinjak. All rights reserved.
   See LICENSE.md *)

(** Functional Priority Search Queues

    [Psq] provides a functional structure that behaves as both a finite map and
    a priority queue.

    {ul
    {- The structure contains a collection of bindings [k -> p], and allows
       efficient {{!S.add}addition}, {{!S.find}lookup} and {{!S.remove}removal}
       of bindings by key.}
    {- It additionally supports {{!S.min}access} to, and {{!S.rest}removal} of
       the binding [k -> p] with the least [p].}}

    The implementation is backed by a weight-balanced semi-heap. Access by key
    is [O(log n)]. Access to the minimal [p] is [O(1)], and its removal is
    [O(log n)].

    {b References}
    {ul
    {- Ralf Hinze.
    {{:https://www.cs.ox.ac.uk/ralf.hinze/publications/ICFP01.pdf} A Simple
    Implementation Technique for Priority Search Queues}. 2001.}}

    {e %%VERSION%% — {{:%%PKG_HOMEPAGE%% }homepage}} *)

(** {1 Psq} *)

(** Signature of priority search queues. *)
module type S = sig

  (** {1 Priority Search Queue} *)

  type t
  (** A search queue. *)

  type k
  (** Keys in {{!t}[t]}. *)

  type p
  (** Priorities in {{!t}[t]}. *)

  val empty : t
  (** [empty] is the search queue that contains no bindings. *)

  val sg : k -> p -> t
  (** [sg k p] is the singleton search queue, containing only the
      binding [k -> p]. *)

  val is_empty : t -> bool
  (** [is_empty t] is [true] iff [t] is {{!empty}[empty]}. *)

  val size : t -> int
  (** [size t] is the number of distinct bindings in [t]. *)

  (** {1 Access by [k]} *)

  val mem : k -> t -> bool
  (** [find k t] is [true] iff [k] is bound in [t]. *)

  val find : k -> t -> p option
  (** [find k t] is [Some p] if [t] contains the binding [k -> p], or [None]
      otherwise. *)

  val add : k -> p -> t -> t
  (** [add k p t] is [t] with the binding [k -> p]. If [k] is already bound in
      [t], that binding is replaced. *)

  val remove : k -> t -> t
  (** [remove k t] is [t] without the binding for [k], or [t], if [k] is not
      bound in [t]. *)

  val adjust: (p -> p) -> k -> t -> t
  (** [adjust f k t] is [t] with the binding [k -> p] replaced by [k -> f p].
      When [k] is not bound in [t], the result is [t]. *)

  (** {1 Access by min [p]} *)

  val min : t -> (k * p) option
  (** [min t] is the binding [Some (k, p)] where [p] is minimal in [t], or
      [None] if [t] is {{!empty}[empty]}. *)

  val rest : t -> t option
  (** [rest t] is [t] without the binding [min t], or [None]. *)

  val pop : t -> ((k * p) * t) option
  (** [pop t] is [(min t, rest t)], or [None]. *)

  val fold_at_most : p -> (k -> p -> 'a -> 'a) -> 'a -> t -> 'a
  (** [fold_at_most p0 f z q] folds [f] over bindings [k -> p] where [p] is not
      larger than [p0], in key-ascending order. *)

  val iter_at_most : p -> (k -> p -> unit) -> t -> unit
  (** [iter_at_most p0 f q] applies [f] to the bindings [k -> p] where [p] is
      not larger than [p0], in key-ascending order. *)

  (** {1 Aggregate access} *)

  val fold : (k -> p -> 'a -> 'a) -> 'a -> t -> 'a
  (** [fold f z t] is [f k0 p0 (f k1 p1 ... (f kn pn z))]. Bindings are folded
      over in key-ascending order. *)

  val filter : (k -> p -> bool) -> t -> t
  (** [filter p t] is the search queue with exactly the bindings in [t] which
      satisfy the predicate [p]. *)

  val partition : (k -> p -> bool) -> t -> t * t
  (** [partition p t] splits [t] into [(t1, t2)], where [t1] contains the
      bindings in [t] which satisfy the predicate [p], and [t2] contains those
      that don't. *)

  val iter : (k -> p -> unit) -> t -> unit
  (** [iter f t] applies [f] to all bindings in [t] in key-ascending order. *)

  (** {1 Conversions} *)

  val to_list : t -> (k * p) list
  (** [to_list t] are all the bindings in [t] in key-ascending order. *)

  val of_list : (k * p) list -> t
  (** [of_list kps] is a [t] with the bindings from [kps]. When there are
      multiple bindings for a given [k], it is unspecified which one is chosen. *)

  val of_sorted_list : (k * p) list -> t
  (** [of_sorted_list kps] is [t] with the bindings in [kps]. This operation is
      generally faster than {{!of_list}[of_list]}. [kps] must contain the
      bindings in key-ascending order without repetitions. When this is not the
      case, the result is undefined. *)

  (** {1 Pretty-printing} *)

  open Format

  val pp : ?sep:(formatter -> unit -> unit) -> (formatter -> k * p -> unit) ->
           formatter -> t -> unit
  (** [pp ?sep pp_kp ppf t] pretty-prints [t] to [ppf], using [pp_kp] to print
      the bindings and [~sep] to separate them. [~sep] defaults to
      {!Format.print_space}. *)

  (**/**)

  (* Debug. *)
  val depth : t -> int
  val pp_dump : (formatter -> k -> unit) -> (formatter -> p -> unit) ->
                formatter -> t -> unit
  (**/**)
end

(** Signature of ordered types. *)
module type Ordered = sig
  type t
  val compare : t -> t -> int
  (** [compare] is a total order on {{!t}[t]}. *)
end

(** [Make(K)(P)] is the {{!S}priority search queue} with bindings [K.t -> P.t]. *)
module Make (K: Ordered) (P: Ordered):
  S with type k = K.t and type p = P.t
