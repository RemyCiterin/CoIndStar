module IdxTree

module Classical = FStar.Classical
open IdxPFunctor
open FStar.FunctionalExtensionality
open ParamCoindProof
open FStar.Tactics.Builtins
open FStar.Tactics.Derived
open Utils

type direction: eqtype = | Left | Right
type node_ty : Type = 
  | LeafTy | NodeTy : int -> node_ty

let dir_from_node (node:node_ty) : Type = match node with
  | NodeTy _ -> direction
  | LeafTy -> empty

unopteq type tree_apply (a:Type) =
  | Node : a -> int -> a -> tree_apply a
  | Leaf : tree_apply a

let tree_pf : idx_pf unit  =
  {
    command = (fun _ -> node_ty);
    response = (fun _ node -> dir_from_node node);
    next = (fun _ _ _ -> ())
  }

// there is a natural isomorphism between tree_apply (f ()) and idx_apply tree_pf f
let pfapply_to_tree (#f:unit -> Type)
  (x:idx_apply tree_pf () f) : tree_apply (f ()) =
  match x.node with
  | NodeTy i -> Node (x.children Left) i (x.children Right)
  | LeafTy -> Leaf

let tree_to_pfapply (#f:unit -> Type)
  (x:tree_apply (f ())) : idx_apply tree_pf () f =
  match x with
  | Node l i r -> {node=NodeTy i; children=on_dom _ (fun d -> match d with | Left -> l | Right -> r)}
  | Leaf -> {node=LeafTy; children = on_dom _ (fun e -> match e with)}

let tree = m_type tree_pf ()

let tree_destruct (t:tree) : tree_apply tree =
  pfapply_to_tree (m_destruct t)

let tree_destruct_thm (t t':tree) :
  Lemma
    (requires tree_destruct t == tree_destruct t')
    (ensures t == t')
  [SMTPat (t == t')] =
  assert(feq (m_children t) (m_children t'));
  idx_apply_equals (m_destruct t) (m_destruct t');
  m_bisim_thm (fun _ t t' -> m_destruct t == m_destruct t') t t'

let isNode (t:tree) : bool =
  Node? (tree_destruct t)

let isLeaf (t:tree) : bool =
  Leaf? (tree_destruct t)

unfold let tree_val (t:tree) : Pure
  int (requires isNode t) (fun _ -> True) =
  match tree_destruct t with
  | Node  _ i _ -> i

unfold let tree_left (t:tree) :
  Pure tree (requires isNode t) (fun _ -> True) =
  match tree_destruct t with
  | Node l _ _ -> l

unfold let tree_right (t:tree) :
  Pure tree (requires isNode t) (fun _ -> True) =
  match tree_destruct t with
  | Node  _ _ r -> r


let tree_corec (#state:Type) (f:state -> tree_apply state) (s0:state) : tree =
  m_corec (fun _ st -> tree_to_pfapply (f st)) s0

let tree_bisim_thm (r:tree -> tree -> prop) (t t':tree) :
  Lemma
    (requires r t t' /\ (forall (x y:tree). r x y ==> (
      (isLeaf x /\ isLeaf y) \/
      (isNode x /\ isNode y /\
        tree_val x == tree_val y /\
        r (tree_left x) (tree_left y) /\
        r (tree_right x) (tree_right y))
    )))
    (ensures t == t')
  = m_bisim_thm (fun _ x y -> r x y) t t'


let tree_destruct_corec_thm (#state:Type) (f:state -> tree_apply state) (s0:state) :
  Lemma (ensures tree_destruct (tree_corec f s0) == (match f s0 with
    | Leaf -> Leaf
    | Node l i r -> Node (tree_corec f l) i (tree_corec f r)
  )) [SMTPat (tree_destruct (tree_corec f s0))] =
  m_destruct_corec_thm (fun _ s -> tree_to_pfapply (f s)) s0

let tree_leaf = m_construct (tree_to_pfapply Leaf)

let tree_leaf_thm1 (t:tree{isLeaf t}) :
  Lemma (ensures t == tree_leaf) [SMTPat (isLeaf t)] =
  tree_bisim_thm (fun t t' -> isLeaf t /\ isLeaf t') tree_leaf t


// definition of tree equality using m_equals

(*
let tree_equals (t t':tree) = m_equals #unit #tree_pf t t'

unopteq type tree_equals_apply (f:(tree -> tree -> Type)) (t1 t2: tree) : Type =
| EQNode :
  squash(isNode t1) ->
  squash(isNode t2) ->
  squash(tree_val t1 == tree_val t2) ->
  f (tree_left t1) (tree_left t2) ->
  f (tree_right t1) (tree_right t2) ->
  tree_equals_apply f t1 t2
| EQLeaf :
  squash(isLeaf t1) ->
  squash(isLeaf t2) ->
  tree_equals_apply f t1 t2

let tree_equals_pf_left_thm (f:(_:unit & (tree * tree) -> Type))
  (t1 t2:tree) : Lemma
    (requires m_node t1 == m_node t2 /\ isNode t1)
    (ensures
      idx_apply_ch_out (m_equals_pf (tree_pf)) (|(), (t1, t2)|) f () Left ==
      f (|(), (tree_left t1, tree_left t2)|)
    )
  = assert(
    (m_equals_pf (tree_pf)).next (|(), (t1, t2)|) () Left ==
    (|(), (tree_left t1, tree_left t2)|)
  );
  assert(
    idx_apply_ch_out (m_equals_pf (tree_pf)) (|(), (t1, t2)|) f () Left ==
    f ((m_equals_pf (tree_pf)).next (|(), (t1, t2)|) () Left)
  );
  ()


let tree_equals_pf_right_thm (f:(_:unit & (tree * tree) -> Type))
  (t1 t2:tree) : Lemma
    (requires m_node t1 == m_node t2 /\ isNode t1)
    (ensures
      idx_apply_ch_out (m_equals_pf (tree_pf)) (|(), (t1, t2)|) f () Right ==
      f (|(), (tree_right t1, tree_right t2)|)
    )
  = assert(
    (m_equals_pf (tree_pf)).next (|(), (t1, t2)|) () Right ==
    (|(), (tree_right t1, tree_right t2)|)
  );
  assert(
    idx_apply_ch_out (m_equals_pf (tree_pf)) (|(), (t1, t2)|) f () Right ==
    f ((m_equals_pf (tree_pf)).next (|(), (t1, t2)|) () Right)
  );
  ()


let m_equals_apply_to_tree (f:(_:unit & (tree * tree)) -> Type)
  (t1 t2:tree) (pf:idx_apply (m_equals_pf tree_pf) (|(), (t1, t2)|) f) :
  tree_equals_apply (fun t t' -> f (|(), (t, t')|)) t1 t2 =
  let x:squash(m_node t1 == m_node t2) = pf.node in 
  assert(m_node t1 == m_node t2);

  match tree_destruct t1, tree_destruct t2 with
  | Node l1 i1 r1, Node l2 i2 r2 ->
    tree_equals_pf_left_thm f t1 t2;
    tree_equals_pf_right_thm f t1 t2;
    EQNode () () () (coerce_eq () (pf.children Left)) (coerce_eq () (pf.children Right))
  | Leaf, Leaf -> EQLeaf () ()

let m_equals_tree_to_apply (f:(_:unit & (tree * tree)) -> Type)
  (t1 t2: tree) (pf: tree_equals_apply (fun t t' -> f (|(), (t, t')|)) t1 t2) :
  idx_apply (m_equals_pf tree_pf) (|(), (t1, t2)|) f =
  match pf with
  | EQNode n1 n2 val_eq l r ->
    {node = val_eq; children = on_dom _ (fun d ->
      tree_equals_pf_left_thm f t1 t2;
      tree_equals_pf_right_thm f t1 t2;
      match d with
      | Left -> coerce_eq () l
      | Right -> coerce_eq () r
    )}
  | EQLeaf l1 l2 -> {node = (); children = on_dom _ (fun e -> match e with)}

let tree_equals_destruct (t t':tree) (t_eq:tree_equals t t') :
  tree_equals_apply tree_equals t t' =
  m_equals_apply_to_tree _ t t' (m_destruct t_eq)

let tree_equals_corec (#state:tree -> tree -> Type)
  (f:(t:tree) -> (t':tree) -> state t t' -> tree_equals_apply state t t')
  (t t':tree) (s0:state t t') : tree_equals t t' =
  let state' : (_:unit & (tree * tree)) -> Type =
    fun (|_, (t, t')|) -> state t t'
  in

  let f' : (o:(_:unit & (tree * tree))) -> state' o ->
    idx_apply (m_equals_pf tree_pf) o state' =
    fun (|_, (t, t')|) s -> m_equals_tree_to_apply _ t t' (coerce_eq () (f t t' s))
  in

  m_corec #_ #_ #_ #state' f' s0
*)

let tree_equals_with (f:tree * tree ^-> prop) :
  (tree * tree ^-> prop) = on _ #prop (fun (t1, t2) ->
    match tree_destruct t1, tree_destruct t2 with
    | Leaf, Leaf -> True
    | Node l1 x1 r1, Node l2 x2 r2 ->
     x1 == x2 /\ f (l1, l2) /\ f (r1, r2)
    | _, _ -> False
  )

let tree_equals (t1 t2:tree) : prop = gfp tree_equals_with (t1, t2)



// definition of a binary search tree

type int_inf =
  | Int of int
  | PInf
  | MInf

let (-<=-) (x y:int_inf) : bool =
  match x, y with
  | MInf, _ -> true
  | _, PInf -> true
  | PInf, _ -> false
  | _, MInf -> false
  | Int i, Int j -> i <= j

type bounds =
  | Empty
  | Interval : (min:int_inf) -> (max:int_inf{min -<=- max}) -> bounds

let min_bounds (b:bounds{Interval? b}) : int_inf =
  match b with | Interval min _ -> min

let max_bounds (b:bounds{Interval? b}) : int_inf =
  match b with | Interval _ max -> max

let in_bounds (i:int_inf) (b:bounds) : bool =
  match b with
  | Empty -> false
  | Interval min max -> i -<=- max && min -<=- i

let sub_bounds (b1 b2:bounds) : bool =
  match b1 with
  | Empty -> true
  | Interval min max -> min `in_bounds` b2 && max `in_bounds` b2

let inter_bounds (b1 b2:bounds) : bounds =
  match b1, b2 with
  | Empty, _ -> Empty
  | _, Empty -> Empty
  | Interval min1 max1, Interval min2 max2 ->
    let res = match min1 -<=- min2, max1 -<=- max2 with
    | false, false ->
      if min1 -<=- max2 then Interval min1 max2 else Empty
    | true, true ->
      if min2 -<=- max1 then Interval min2 max1 else Empty
    | false, true -> b1
    | true, false -> b2
    in
    assert(res `sub_bounds` b1 /\ res `sub_bounds` b2);
    res


let split_bounds (i:int) (b:bounds{Int i `in_bounds` b}) : bounds * bounds =
  (
    inter_bounds b (Interval MInf (Int (i-1))),
    inter_bounds b (Interval (Int (i+1)) PInf)
  )

let split_bounds_sub (i:int) (b:bounds{Int i `in_bounds` b}) (b':bounds{b `sub_bounds` b'})
  : Lemma (
      let lb, rb = split_bounds i b in
      let lb', rb' = split_bounds i b' in
      lb `sub_bounds` lb' /\ rb `sub_bounds` rb'
  ) = ()

// show that split_bounds have the correct behaviour
let bounds_split_example (i j:int) (b:bounds) :
  Lemma
    (requires Int i `in_bounds` b /\ Int j `in_bounds` b)
    (ensures True)
  =
  let p1 =  j == i in
  let p2 = Int j `in_bounds` (split_bounds i b)._1 in
  let p3 = Int j `in_bounds` (split_bounds i b)._2 in
  assert(p1 \/ p2 \/ p3);
  assert(p1 ==> (~p2 /\ ~p3));
  assert(p2 ==> (~p1 /\ ~p3));
  assert(p3 ==> (~p1 /\ ~p2))
  

let is_bst_with (aux:tree * bounds ^-> prop) : (tree * bounds ^-> prop) =
  on _ #prop (fun (t, b) -> match tree_destruct t with
    | Node l i r ->
     Int i `in_bounds` b /\ (
        let lb, rb = split_bounds i b in
        aux (l, lb) /\ aux (r, rb)
      )
    | Leaf -> True
  )

let is_bst = gfp is_bst_with

let is_bst_increasing (t:tree) (b1 b2:bounds) :
  Lemma
    (requires is_bst (t, b1) /\ 
      b1 `sub_bounds` b2
    )
    (ensures is_bst (t, b2))
  = let p : (tree * bounds ^-> prop) = 
    on _ #prop (fun (t, b2) ->
      exists b1. is_bst (t, b1) /\ b1 `sub_bounds` b2
    )
  in 

  let aux (t:tree) (b:bounds) :
    Lemma
      (requires p (t, b))
      (ensures is_bst_with p (t, b))
    =
    eliminate exists b'. is_bst (t, b') /\ b' `sub_bounds` b
    returns is_bst_with p (t, b)
    with _. begin
      assert(is_bst (t, b'));
      unfold_gfp is_bst_with (t, b');
      match tree_destruct t with
      | Node l i r -> begin
        let lb, rb = split_bounds i b in
        let lb', rb' = split_bounds i b' in
        split_bounds_sub i b' b;
        assert(lb' `sub_bounds` lb);
        assert(rb' `sub_bounds` rb);
        ()
      end
      | Leaf -> ()
    end
  in
  Classical.forall_intro_2 (Classical.move_requires_2 aux);
  
  tarski is_bst_with p;
  assert(p (t, b2))


let height_tree_with : monotone_fun (tree * nat) = fun aux ->
  on (tree * nat) #prop (fun (t, h) -> match tree_destruct t with
    | Node l i r -> h > 0 /\ //(exists h'. h' < h /\ (forall h''. h'' >= h' ==>
      aux (l, h-1) /\ aux (r, h-1)
      //))
    | Leaf -> True
  )

let height_tree = gfp height_tree_with
(*
let height_tree_ge (t:tree) (h' h:nat) :
  Lemma
    (requires h' >= h /\ height_tree (t, h))
    (ensures height_tree (t, h'))
  = match tree_destruct t with
  | Node l i r ->
    unfold_gfp height_tree_with (t, h);
    fold_gfp height_tree_with (t, h')
  | Leaf ->
    fold_gfp height_tree_with (t, h')
*)
let rec less_index (h:nat) (t:tree{height_tree (t, h)}) :
  Tot (option int) = // (decreases h) =
  match tree_destruct t with
  | Node l i r -> begin
    unfold_gfp height_tree_with (t, h);
    //Classical.forall_intro (Classical.move_requires (height_tree_ge t (h-1)));
    match less_index (h-1) l with
    | None -> Some i
    | Some j -> Some j
  end
  | Leaf -> None

#push-options "--z3rlimit 100"
let bst_is_sized (i:int) (j:int{j >= i}) (t:tree)
  : Lemma
    (requires is_bst (t, Interval (Int i) (Int j)))
    (ensures height_tree (t, 1 + j - i))
  = let rel (t:tree) (h:nat) (i j:int) =
    Leaf? (tree_destruct t) \/ (
      i <= j /\ h == 1 + j - i /\
      is_bst (t, Interval (Int i) (Int j))
    )
  in
  
  let p : (tree * nat ^-> prop) =
    on (tree * nat) #prop (fun (t, h) ->
      exists i j. rel t h i j
    )
  in
  let aux (pair:tree * nat) : 
    Lemma
      (requires p pair)
      (ensures height_tree_with p pair)
    =
    let (t, h) = pair in
    match tree_destruct t with
    | Node l x r ->
      begin eliminate exists i j. rel t h i j
      returns height_tree_with p pair
      with _.
      if Leaf? (tree_destruct t) then
        ()
      else begin

        let b = Interval (Int i) (Int j) in
        unfold_gfp is_bst_with (t, b);
        let lb, rb = split_bounds x b in


        //is_bst_increasing l lb (Interval (Int li) (Int lj));
        if i = j then begin 
          unfold_gfp is_bst_with (l, lb);
          unfold_gfp is_bst_with (r, rb);
          assert(Leaf? (tree_destruct l));
          assert(Leaf? (tree_destruct r));
          assert(rel l 0 0 0);
          assert(rel r 0 0 0);
          ()
        end else begin
          let li, lj = i, j-1 in
          let ri, rj = i+1, j in
          is_bst_increasing l lb (Interval (Int li) (Int lj));
          is_bst_increasing r rb (Interval (Int ri) (Int rj));
          assert(rel l (h-1) li lj);
          assert(rel r (h-1) ri rj);
          ()
        end
      end
    end
    | Leaf -> ()
  in
  Classical.forall_intro (Classical.move_requires aux);
  assert(forall pair. p pair ==> height_tree_with p pair);
  tarski height_tree_with p;
  assert(rel t (j-i+1) i j);
  assert(p (t, 1+j-i))

// polynomial functor to represent that a tree is a binary search tree
(*
let is_bst_command : tree * bounds -> Type = fun (t, b) ->
  match tree_destruct t with
  | Node _ i _ -> squash(Int i `in_bounds` b)
  | Leaf -> unit

let is_bst_response : (p:(tree * bounds)) -> is_bst_command p -> Type =
  fun (t, b) _ -> match tree_destruct t with
  | Node _ _ _ -> direction
  | Leaf -> empty

let is_bst_next : (p:(tree * bounds)) -> (c:is_bst_command p) -> is_bst_response p c -> tree * bounds =
  fun (t, b) _ dir -> match tree_destruct t with
  | Node l i r -> begin
    let (l_b, r_b) = split_bounds i b in
    let dir: direction = dir in
    match dir with
    | Left -> (l, l_b)
    | Right -> (r, r_b)
  end
  | Leaf -> match dir with


let is_bst_pf : idx_pf (tree * bounds) =
  {
    command = is_bst_command;
    response = is_bst_response;
    next = is_bst_next
  }

unopteq type bst_apply : (tree*bounds) -> (tree*bounds -> Type) -> Type =
  | BSTNode : (#f:(tree*bounds -> Type)) ->
    (#b:bounds) -> (#t:tree{isNode t /\ Int (tree_val t) `in_bounds` b}) ->
    f (tree_left t, (tree_val t `split_bounds` b)._1) ->
    f (tree_right t, (tree_val t `split_bounds` b)._2) ->
    bst_apply (t, b) f
  | BSTLeaf : (#f:(tree * bounds -> Type)) ->
    (#b:bounds) -> bst_apply (tree_leaf, b) f


let bst (t:tree) (b:bounds) : Type = m_type is_bst_pf (t, b)

*)

