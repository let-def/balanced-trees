type (+'a, +'b) t =
  | Leaf
  | Node of int * ('a, 'b) t * 'a * 'b * ('a, 'b) t

let size = function
  | Node (s, _, _, _, _) -> s
  | Leaf -> 0

let item_size = function
  | Node (s, l, _, _, r) -> s - size l - size r
  | Leaf -> 0

(** {1 Balance criteria}
  Functions are not symmetric.
  The first argument should always be of the same power of two or smaller
  (guaranteed by construction). *)

(** [smaller_ell smin smax] iff
    - [smin] is less than [smax]
    - [smin] and [smax] differs by less than two magnitude orders, i.e
      msbs(smin) >= msbs(smax) - 1
    where msbs is the index of the most significant bit set *)
let smaller_ell smin smax = (smin < smax) && ((smin land smax) lsl 1 < smax)

(** [disbalanced smin smax] check if two sub-trees of size [smin] and [smax],
    are disbalanced. That is, msbs(smin) < msbs(smax) - 1 *)
let disbalanced smin smax = smaller_ell smin (smax lsr 1)

(** {1 Smart but not too much constructors} *)

(** Construct node and check balance *)
let node_ l w x0 x1 r =
  let sl = size l and sr = size r in
  assert (w > 0);
  (* Incorrect invariant :/
    if sl < sr then
      assert (not (disbalanced sl sr))
    else
      assert (not (disbalanced sr sl));*)
  Node (sl + w + sr, l, x0, x1, r)

(** Construct Node *)
let node_ l w x0 x1 r = Node (size l + w + size r, l, x0, x1, r)

(** Rotations *)
let rot_left l w x0 x1 r k = match r with
  | Node (_, rl, y0, y1, rr) as node ->
    k (node_ l w x0 x1 rl) (item_size node) y0 y1 rr
  | _ -> assert false

let rot_right l w y0 y1 r k = match l with
  | Node (_, ll, x0, x1, lr) as node ->
    k ll (item_size node) x0 x1 (node_ lr w y0 y1 r)
  | _ -> assert false

(** Balancing *)
let smaller_ell a b = (a < b) && ((a land b) lsl 1 < b)

let inc_left l w x0 x1 r k =
  let r = match r with
    | Node (_, rl, y0, y1, rr) when smaller_ell (size rr) (size rl) ->
      rot_right rl (item_size r) y0 y1 rr node_
    | _ -> r
  in
  rot_left l w x0 x1 r k

let inc_right l w y0 y1 r k =
  let l = match l with
    | Node (_, ll, x0, x1, lr) when smaller_ell (size ll) (size lr) ->
      rot_left ll (item_size l) x0 x1 lr node_
    | _ -> l
  in
  rot_right l w y0 y1 r k

(** Balance trees leaning to the right *)
let rec node_left l w x0 x1 r =
  if disbalanced (size l) (size r) then
    inc_left l w x0 x1 r node_left
  else
    node_ l w x0 x1 r

(** Balance trees leaning to the left *)
let rec node_right l w y0 y1 r =
  if disbalanced (size r) (size l) then
    inc_right l w y0 y1 r node_right
  else
    node_ l w y0 y1 r

(** Public interface *)

let leaf = Leaf

let node l w x0 x1 r = match l, r with
  | Leaf, Leaf -> node_ leaf w x0 x1 leaf
  | l, r when size l < size r ->
    node_left l w x0 x1 r
  | l, r ->
    node_right l w x0 x1 r

let rec join l r = match l, r with
  | Leaf, t | t, Leaf -> t
  | Node (sl, ll, x0, x1, lr), Node (sr, rl, y0, y1, rr) ->
    if sl <= sr then
      node (join l rl) (item_size r) y0 y1 rr
    else
      node ll (item_size r) x0 x1 (join lr r)

let rec rank n = function
  | Leaf -> raise Not_found
  | Node (s, l, x0, x1, r) ->
    let sl = size l and sr = size r in
    if n < sl then
      rank n l
    else
      let s' = s - sr in
      if n < s' then
        n - sl, x0, x1
      else
        rank (n - s') r
