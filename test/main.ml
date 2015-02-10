module Balanced_set (Ord : Set.OrderedType) : Set.S with type elt = Ord.t =
struct
  type elt = Ord.t
  type t = elt Bt_1.t
  open Bt_1

  let empty = leaf

  let is_empty = function
    | Leaf -> true
    | _ -> false

  let rec mem elt = function
    | Leaf -> false
    | Node (_, l, elt', r) ->
      let c = Ord.compare elt elt' in
      if c = 0 then true
      else if c < 0 then
        mem elt l
      else
        mem elt r

  let singleton elt = node leaf elt leaf

  let rec add elt = function
    | Leaf -> singleton elt
    | Node (_, l, elt', r) as n ->
      let c = Ord.compare elt elt' in
      if c = 0 then n
      else if c < 0 then
        let l' = add elt l in
        begin
          if l == l' then
            n
          else
            node l' elt' r
        end
      else
        let r' = add elt r in
        begin
          if r == r' then
            n
          else
            node l elt' r'
        end

  let rec remove elt n = match n with
    | Leaf -> n
    | Node (_, l, elt', r) ->
      let c = Ord.compare elt elt' in
      if c < 0 then
        let l' = remove elt l in
        begin
          if l == l' then
            n
          else
            node l' elt' r
        end
      else if c > 0 then
        let r' = remove elt r in
        begin
          if r == r' then
            n
          else
            node l elt' r'
        end
      else join l r

  let union _ = failwith "TODO"
  let inter _ = failwith "TODO"
  let diff _ = failwith "TODO"
  let compare _ = failwith "TODO"
  let equal _ = failwith "TODO"
  let subset _ = failwith "TODO"
  let iter _ = failwith "TODO"
  let fold _ = failwith "TODO"
  let for_all _ = failwith "TODO"
  let exists _ = failwith "TODO"
  let filter _ = failwith "TODO"
  let partition _ = failwith "TODO"
  let cardinal = size
  let elements _ = failwith "TODO"
  let min_elt _ = failwith "TODO"
  let max_elt _ = failwith "TODO"
  let choose _ = failwith "TODO"
  let split _ = failwith "TODO"
  let find _ = failwith "TODO"
  let of_list _ = failwith "TODO"
end

module Balanced_map (Ord : Set.OrderedType) : Map.S with type key = Ord.t =
struct
  type key = Ord.t

  type 'a t = (key,'a) Bt_2.t

  open Bt_2

  let empty = leaf

  let is_empty = function
    | Leaf -> true
    | _ -> false

  let rec mem key = function
    | Leaf -> false
    | Node (_, l, key', _, r) ->
      let c = Ord.compare key key' in
      if c = 0 then true
      else if c < 0 then
        mem key l
      else
        mem key r

  let singleton k v = node leaf k v leaf

  let rec add k v = function
    | Leaf -> singleton k v
    | Node (_, l, k', v', r) ->
      let c = Ord.compare k k' in
      if c = 0 then node l k v r
      else if c < 0 then
        node (add k v l) k' v' r
      else
        node l k' v' (add k v r)

  let rec remove k n = match n with
    | Leaf -> n
    | Node (_, l, k', v', r) ->
      let c = Ord.compare k k' in
      if c = 0 then join l r
      else if c < 0 then
        let l' = remove k l in
        begin
          if l == l' then
            n
          else
            node l' k' v' r
        end
      else
        let r' = remove k r in
        begin
          if r == r' then
            n
          else
            node l k' v' r'
        end

  let merge _ = failwith "TODO"
  let compare _ = failwith "TODO"
  let equal _ = failwith "TODO"
  let iter _ = failwith "TODO"
  let fold _ = failwith "TODO"
  let for_all _ = failwith "TODO"
  let exists _ = failwith "TODO"
  let filter _ = failwith "TODO"
  let partition _ = failwith "TODO"
  let cardinal = size
  let bindings _ = failwith "TODO"
  let min_binding _ = failwith "TODO"
  let max_binding _ = failwith "TODO"
  let choose _ = failwith "TODO"
  let split _ = failwith "TODO"
  let find _ = failwith "TODO"
  let map _ = failwith "TODO"
  let mapi _ = failwith "TODO"
end

module Balanced_wset (Ord : Set.OrderedType) (*Set.S with type elt = Ord.t*) =
struct
  type elt = Ord.t
  type t = elt Btw_1.t
  open Btw_1

  let empty = leaf

  let is_empty = function
    | Leaf -> true
    | _ -> false

  let rec mem elt = function
    | Leaf -> false
    | Node (_, l, elt', r) ->
      let c = Ord.compare elt elt' in
      if c = 0 then true
      else if c < 0 then
        mem elt l
      else
        mem elt r

  let singleton w elt = node leaf w elt leaf

  let rec add w elt = function
    | Leaf -> singleton w elt
    | Node (_, l, elt', r) as n ->
      let c = Ord.compare elt elt' in
      if c = 0 then n
      else if c < 0 then
        let l' = add w elt l in
        begin
          if l == l' then
            n
          else
            node l' (item_size n) elt' r
        end
      else
        let r' = add w elt r in
        begin
          if r == r' then
            n
          else
            node l (item_size n) elt' r'
        end

  let rec remove elt n = match n with
    | Leaf -> n
    | Node (_, l, elt', r) ->
      let c = Ord.compare elt elt' in
      if c = 0 then join l r
      else if c < 0 then
        let l' = remove elt l in
        begin
          if l == l' then
            n
          else
            node l' 1 elt' r
        end
      else
        let r' = remove elt r in
        begin
          if r == r' then
            n
          else
            node l 1 elt' r'
        end

  let union _ = failwith "TODO"
  let inter _ = failwith "TODO"
  let diff _ = failwith "TODO"
  let compare _ = failwith "TODO"
  let equal _ = failwith "TODO"
  let subset _ = failwith "TODO"
  let iter _ = failwith "TODO"
  let fold _ = failwith "TODO"
  let for_all _ = failwith "TODO"
  let exists _ = failwith "TODO"
  let filter _ = failwith "TODO"
  let partition _ = failwith "TODO"
  let cardinal _ = failwith "TODO"
  let elements _ = failwith "TODO"
  let min_elt _ = failwith "TODO"
  let max_elt _ = failwith "TODO"
  let choose _ = failwith "TODO"
  let split _ = failwith "TODO"
  let find _ = failwith "TODO"
  let of_list _ = failwith "TODO"
end

module Balanced_wmap (Ord : Set.OrderedType) : Map.S with type key = Ord.t =
struct
  type key = Ord.t

  type 'a t = (key,'a) Btw_2.t

  open Btw_2

  let empty = leaf

  let is_empty = function
    | Leaf -> true
    | _ -> false

  let rec mem key = function
    | Leaf -> false
    | Node (_, l, key', _, r) ->
      let c = Ord.compare key key' in
      if c = 0 then true
      else if c < 0 then
        mem key l
      else
        mem key r

  let singleton k v = node leaf 1 k v leaf

  let rec add k v = function
    | Leaf -> singleton k v
    | Node (_, l, k', v', r) ->
      let c = Ord.compare k k' in
      if c = 0 then node l 1 k v r
      else if c < 0 then
        node (add k v l) 1 k' v' r
      else
        node l 1 k' v' (add k v r)

  let rec remove k n = match n with
    | Leaf -> n
    | Node (_, l, k', v', r) ->
      let c = Ord.compare k k' in
      if c = 0 then join l r
      else if c < 0 then
        let l' = remove k l in
        begin
          if l == l' then
            n
          else
            node l' 1 k' v' r
        end
      else
        let r' = remove k r in
        begin
          if r == r' then
            n
          else
            node l 1 k' v' r'
        end

  let merge _ = failwith "TODO"
  let compare _ = failwith "TODO"
  let equal _ = failwith "TODO"
  let iter _ = failwith "TODO"
  let fold _ = failwith "TODO"
  let for_all _ = failwith "TODO"
  let exists _ = failwith "TODO"
  let filter _ = failwith "TODO"
  let partition _ = failwith "TODO"
  let cardinal _ = failwith "TODO"
  let bindings _ = failwith "TODO"
  let min_binding _ = failwith "TODO"
  let max_binding _ = failwith "TODO"
  let choose _ = failwith "TODO"
  let split _ = failwith "TODO"
  let find _ = failwith "TODO"
  let map _ = failwith "TODO"
  let mapi _ = failwith "TODO"
end

module Int = struct
  type t = int
  let compare (a : int) (b : int) = a - b
end

module IntSet0 = Set.Make(Int)
module IntSet1 = Balanced_set(Int)
module IntSet1w = Balanced_wset(Int)

module IntMap0 = Map.Make(Int)
module IntMap1 = Balanced_map(Int)
module IntMap1w = Balanced_wmap(Int)

let count = 1_000_000

let shuf n = (n * 2654435761) land 0xFFFFFFFF

let test_set init add rem =
  Gc.full_major ();
  let m = ref init in
  let time = Sys.time () in
  for i = 1 to count do
    let i = shuf i in
    m := add (shuf i) i !m
  done;
  let minor = (Gc.stat ()).Gc.minor_words in
  for i = 1 to count do
    let i = shuf i in
    m := rem i !m;
    (*if (counter !m mod 1531 = 0) then
    (  print_int (counter !m); print_newline ());*)
  done;
  let time = Sys.time () -. time in
  let mem = (Gc.stat ()).Gc.minor_words -. minor in
  time, mem

let test_map init add rem =
  Gc.full_major ();
  let m = ref init in
  let time = Sys.time () in
  for i = 1 to count do
    let i = shuf i in
    m := add i i !m
  done;
  let minor = (Gc.stat ()).Gc.minor_words in
  for i = count downto 1 do
    let i = shuf i in
    m := rem i !m
  done;
  let time = Sys.time () -. time in
  let mem = (Gc.stat ()).Gc.minor_words -. minor in
  time, mem


let main () =
  List.iter
    (fun (name, result) ->
       let lazy (time, mem) = result in
       Printf.printf "\t%s: time:%f memory:%f \n%!" name time mem;
    )
    [
      "Set.Make", lazy IntSet0.(test_set empty (fun _ -> add) remove);
      "Balanced_set", lazy IntSet1.(test_set empty (fun _ -> add) remove);
      "Balanced_wset", lazy IntSet1w.(test_set empty add remove);
      "Map.Make", lazy IntMap0.(test_map empty add remove);
      "Balanced_map", lazy IntMap1.(test_map empty add remove);
      "Balanced_wmap", lazy IntMap1w.(test_map empty add remove);
    ]

let () = main (); main ()
