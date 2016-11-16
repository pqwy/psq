(* Copyright (c) 2016 David Kaloper Meršinjak. All rights reserved.
   See LICENSE.md *)

let rec mem ?(cmp=compare) a = function
  | [] -> false | x::xs -> cmp a x = 0 || mem ~cmp a xs

let rec add ?(cmp=compare) a = function
  | []    -> [a]
  | x::xs ->
      match cmp a x with -1 -> a::x::xs | 1 -> x::add ~cmp a xs | _ -> x::xs

let astar (type a) ?(cmp=compare) start graph h sat =
  let module K = struct type t = a let compare = cmp end in
  let module P = struct
    type t = int * a list
    let compare (a: t) b = compare (fst a) (fst b)
  end in
  let module Q = Psq.Make(K)(P) in
  let rec go q = match Q.pop q with
    | Some ((a, (dist, path)), q) ->
        if sat a then Some (dist, a, List.rev path) else
          let f q (w, b) =
            let d' = w + h b in
            if mem ~cmp b path then q else
              match Q.find b q with
              | Some (d, _) when d <= d' -> q
              | _ -> Q.add b (d', a::path) q in
          go @@ List.fold_left f q @@ graph a
    | None -> None in
  go Q.(sg start (0, []))

let labyrinth p0 (pn_m, pn_n as pn) grid =
  let (m0, n0) = Array.(length grid, length grid.(0)) in
  let h (m, n) = abs (pn_m - m) + abs (pn_n - n)
  and sat mn = mn = pn
  and graph (m, n) =
    (if m > 0    && grid.(m-1).(n) = `o then [1, (m-1, n)] else []) @
    (if m < m0-1 && grid.(m+1).(n) = `o then [1, (m+1, n)] else []) @
    (if n > 0    && grid.(m).(n-1) = `o then [1, (m, n-1)] else []) @
    (if n < n0-1 && grid.(m).(n+1) = `o then [1, (m, n+1)] else []) in
  match astar ~cmp:compare p0 graph h sat with
  | None -> Fmt.pr "not found\n%!"
  | Some (dist, (m, n), path) ->
      Fmt.(pr "@[(%d, %d), dist: %d@;steps: %a@]\n%!"
        m n dist (Dump.(list (pair int int))) path)

let l : [`X|`o] array array =
[|[| `o; `X; `o; `o; `o; `o; |];
  [| `o; `X; `X; `X; `o; `o; |];
  [| `o; `o; `o; `o; `X; `o; |];
  [| `o; `X; `X; `X; `o; `o; |];
  [| `o; `X; `o; `o; `o; `o; |];
  [| `o; `o; `o; `X; `X; `o; |]|]

let () = labyrinth (0, 0) (5, 5) l
