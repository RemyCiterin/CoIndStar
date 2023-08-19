module IdxStream

module Classical = FStar.Classical
module Paco = ParamCoindProof
module Paco2 = CoindProofApprox
open IdxPFunctor
open FStar.FunctionalExtensionality
module PropExt = FStar.PropositionalExtensionality
open Utils

open FStar.Tactics

// definition of a stream

let stream_pf (a:Type) : idx_pf unit =
  {
    command = (fun _ -> a);
    response = (fun _ _ -> unit);
    next = (fun o _ _ -> o)
  }


let stream_apply (a out:Type) = a * out

let stream (a:Type) = m_type #unit (stream_pf a) ()

let from_unit (#a:Type) (x:a) (_:unit) : a = x

let head (#a:Type) (s:stream a) : a =
  (m_destruct s).node

let tail (#a:Type) (s:stream a) : stream a =
  (m_destruct s).children ()

let stream_eq_thm (#a:Type) (s s':stream a) :
  Lemma
    (requires head s == head s' /\ tail s == tail s')
    (ensures s == s')
  [SMTPat (s == s')]
  = assert(feq (m_destruct s).children (m_destruct s').children);
  idx_apply_equals (m_destruct s) (m_destruct s');
  m_bisim_thm (fun _ s s' -> m_destruct s == m_destruct s') s s'

let idx_apply_from_pair (#a #out:Type) (pair:a * out) : idx_apply (stream_pf a) () (from_unit out) =
  {node = pair._1; children = on_dom _ (fun _ -> pair._2)}

let stream_corec (#a #state:Type) (f:state -> a * state) (s0:state) : stream a =
  m_corec (fun _ st -> idx_apply_from_pair (f st)) s0

let stream_head_corec_thm (#a #state:Type) (f:state -> a * state) (s0:state) :
  Lemma (head (stream_corec f s0) == (f s0)._1) [SMTPat (head (stream_corec f s0))] =
  m_destruct_corec_thm (fun _ st -> idx_apply_from_pair (f st)) s0

let stream_tail_corec_thm (#a #state: Type) (f:state -> a * state) (s0:state) :
  Lemma (tail (stream_corec f s0) == stream_corec f (f s0)._2) [SMTPat (tail (stream_corec f s0))] =
  m_destruct_corec_thm (fun _ st -> idx_apply_from_pair (f st)) s0

let stream_bisim_thm (#a: Type) (r:stream a -> stream a -> prop) (s s':stream a) :
  Lemma (requires r s s' /\ (forall s s'.{:pattern r s s'} r s s' ==> (
    head s == head s' /\ r (tail s) (tail s')
  )))
  (ensures s == s')
  =
  m_bisim_thm (fun _ s s' -> r s s') s s'

let stream_cons (#a:Type) (hd:a) (tl:stream a) : stream a =
  // let f : m_type (stream_pf a) = fun _ -> tl in
  m_construct {node=hd; children = on_dom unit (fun _ -> tl)}

let stream_cons_head (#a:Type) (hd:a) (tl:stream a) :
  Lemma (ensures head (stream_cons hd tl) == hd)
  [SMTPat (head (stream_cons hd tl))] =
  m_destruct_construct_thm #unit #(stream_pf a) {node=hd; children= on_dom unit (fun _ -> tl)}

let stream_cons_tail (#a:Type) (hd:a) (tl:stream a) :
  Lemma (ensures tail (stream_cons hd tl) == tl)
  [SMTPat (tail (stream_cons hd tl))] =
  m_destruct_construct_thm #unit #(stream_pf a) {node=hd; children = on_dom unit (fun _ -> tl)}

let stream_head_tail_cons (#a:Type) (s:stream a) :
  Lemma (stream_cons (head s) (tail s) == s)
  [SMTPat (stream_cons (head s) (tail s))] =
  let s' = stream_cons (head s) (tail s) in
  assert(tail s' == tail s);
  assert(head s' == head s);
  stream_eq_thm s s'

// defintion of a stream bellow between two stream
let stream_below_pf : idx_pf (stream int * stream int) =
  {
    command = (fun (m1, m2) -> squash(head m1 <= head m2));
    response = (fun (m1, m2) _ -> if head m1 = head m2 then unit else empty);
    next = (fun (m1, m2) _ _ -> (tail m1, tail m2))
  }

let stream_below (s1 s2: stream int) : Type = m_type stream_below_pf (s1, s2)

let stream_mul (s1 s2: stream int) : stream int =
  stream_corec #int #(stream int * stream int)
    (fun (s1, s2) -> (op_Multiply (head s1) (head s2), (tail s1, tail s2))) (s1, s2)

let stream_add (s1 s2:stream int) : stream int =
  stream_corec #int #(stream int * stream int)
    (fun (s1, s2) ->(head s1 + head s2, (tail s1, tail s2))) (s1, s2)

let square_mul_tail (s1 s2:stream int) : 
  Lemma (tail (stream_mul s1 s2) == stream_mul (tail s1) (tail s2))
  [SMTPat (tail (stream_mul s1 s2))] =
  ()

let square_mul_head (s1 s2:stream int) :
  Lemma (head (stream_mul s1 s2) == op_Multiply (head s1) (head s2))
  [SMTPat (head (stream_mul s1 s2))] =
  ()

// à cause des restricted_t il faut être explicite sur le type de f+
let stream_mul_below_thm (s:stream int) : stream_below s (stream_mul s s) =
  m_corec #_ #stream_below_pf #_ #(fun (s1, s2) -> squash(s2 == stream_mul s1 s1)) (fun (s1, s2) _ ->
    let f (_:(if head s1 = head s2 then unit else empty)) :
      squash(tail s2 == stream_mul (tail s1) (tail s1)) = () in
    {node = (); children = on_dom _ f}
  ) ()

let stream_assoc_equals (s1 s2 s3:stream int) :
  m_equals
    (stream_add (stream_add s1 s2) s3)
    (stream_add s1 (stream_add s2 s3)) =
  let state (sl sr:stream int) =
    s:(stream int * stream int * stream int) {
      sr == stream_add s._1 (stream_add s._2 s._3) /\
      sl == stream_add (stream_add s._1 s._2) s._3
    }
  in


  m_corec #_ #_ #_ //  #_ #(m_equals_pf (stream_pf int)) #_
    #(fun (| _, (sl, sr)|) -> state sl sr)
    (fun (|_, (sl, sr)|) (s1, s2, s3) ->
      let f (_:unit) : (state (tail sl) ( tail sr)) =
        (tail #int s1, tail #int s2, tail #int s3)
      in
      {node = (); children = on_dom _ f}
    ) (s1, s2, s3)

let stream_assoc (s1 s2 s3:stream int) :
  Lemma (stream_add (stream_add s1 s2) s3 == stream_add s1 (stream_add s2 s3))
  = m_equals_thm _ _ (stream_assoc_equals s1 s2 s3)

(*
#push-options "--z3rlimit 100 --query_stats"
let stream_assoc2 (s1 s2 s3:stream int) :
  Lemma (stream_add (stream_add s1 s2) s3 == stream_add s1 (stream_add s2 s3)) =

  let p (sl sr:stream int) (s:stream int * stream int * stream int): prop =
    sl == stream_add (stream_add s._1 s._2) s._3 /\
    sr == stream_add s._1 (stream_add s._2 s._3)
  in

  let r (sl sr:stream int): prop = squash(exists s. p sl sr s) in

  let lemma1 (sl sr:stream int) :
    Lemma (requires r sl sr)
    (ensures r (tail sl) (tail sr)) =
    let x : squash(exists s. p sl sr s) = () in
    Classical.exists_elim (r (tail sl) (tail sr)) #_ #(p sl sr) x (fun (s1, s2, s3) ->
      Classical.move_requires (fun _ -> Classical.exists_intro (p (tail sl) (tail sr)) 
      (tail s1, tail s2, tail s3)) ()
    )
  in
  Classical.forall_intro_2 (Classical.move_requires_2 lemma1);
  assert(forall sl sr.{:pattern r sl sr} r sl sr ==> r (tail sl) (tail sr));

  let lemma2 (sl sr:stream int) :
    Lemma (requires r sl sr)
    (ensures head sl == head sr) =
    let x : r sl sr = () in
    Classical.exists_elim (head sl == head sr) #_ #(p sl sr) x (fun (s1, s2, s3) -> ())
  in
  Classical.forall_intro_2 (Classical.move_requires_2 lemma2);

  assert(forall sl sr.{:pattern r sl sr} r sl sr ==> head sl == head sr);

  let sl = stream_add (stream_add s1 s2) s3 in
  let sr = stream_add s1 (stream_add s2 s3) in

  Classical.exists_intro (p sl sr) (s1, s2, s3);
  
  assert(r (stream_add (stream_add s1 s2) s3) (stream_add s1 (stream_add s2 s3)));

  stream_bisim_thm r (stream_add (stream_add s1 s2) s3) (stream_add s1 (stream_add s2 s3))

*)

// definition of pointwise property
let stream_pw_pf (#a:Type) (p:a -> prop) : idx_pf (stream a) =
  {
    command = (fun s -> squash(p (head s)));
    response = (fun s _ -> unit);
    next = (fun s _ _ -> tail s)
  }

let stream_pw (#a:Type) (p:a -> prop) (s:stream a) =
  m_type (stream_pw_pf p) s

let pw_head (#a:Type) (#p:a -> prop) (#s:stream a) (pw:stream_pw p s) :
  Lemma (p (head s)) = m_node pw

let pw_tail (#a:Type) (#p:a -> prop) (#s:stream a) (pw:stream_pw p s) :
  stream_pw p (tail s) = m_children pw ()

// construction of pointwise property on stream using invariant
let pw_invariant (#a:Type) (p:a -> prop) (#state:Type)
  (f:state -> a * state) (s0:state)

  (inv:state -> prop)

  : Pure (stream_pw p (stream_corec f s0))
    (requires
      (forall x. inv x ==> inv (f x)._2) /\
      (forall x. inv x ==> p (f x)._1) /\
      inv s0
    )
    (ensures fun _ -> True) =
    let new_state (s:stream a) = 
      x:state{s == stream_corec f x /\ inv x}
    in

    let get_node (s:stream a) (x:new_state s) :
      Lemma (p (head s)) =
      assert(inv x);
      assert(p (f x)._1)
    in

    let get_children (s:stream a) (x:new_state s) (_:unit)
      : new_state (tail s) =
      assert(tail s == stream_corec f (f x)._2);
      (f x)._2
    in
    
    m_corec #_ #_ #_ #new_state (fun s x -> 
      {node = get_node s x; children = on_dom _ (get_children s x)}
    ) s0

let rec k_ind_aux (#a:Type) (p:a -> prop) (#state:Type)
  (f:state -> a * state) (s0:state) (k:nat) (x:state) :
  Tot (state * prop) (decreases k) =
  if k = 0 then (s0, x == s0) else
  let (x', p) = k_ind_aux p f s0 (k-1) x in
  let x'' = (f x')._2 in
  (x'', (x == x'' \/ p))


let k_ind_invariant (#a:Type) (p:a -> prop) (#state:Type)
  (f:state -> a * state) (s0:state) (k:nat) (x:state) :
  Tot prop (decreases k) =

  (k_ind_aux p f s0 k x)._2
  
  //if k = 0 then squash(x == s0) else
  //  squash(x == s0 \/ (exists x'. k_ind_invariant p f s0 (k-1) x' /\ x == (f x')._2))


let exemple1 : unit =
  let n = 120 in
  let f : int -> int * int =
    fun x -> (x, (if x >= n then 0 else x+1))
  in

  let inv (x:int) : prop = squash(0 <= x /\ x <= n) in
  let safe (x:int) : prop = inv x in

  let k = 120 in

  let inv' = k_ind_invariant safe f 0 k in
  assert(inv' 0) by (norm [primops; iota; delta; zeta; nbe]);
  assert(forall x. inv' x ==> safe x) by (norm [primops; iota; delta; zeta; nbe]);
  assert(forall x. inv' x ==> inv' (f x)._2) by (norm [primops; iota; delta; zeta; nbe]);

  let _ = pw_invariant safe f 0 inv' in
  let _ = pw_invariant safe f 0 inv in
  ()

(*
example: check the property x != 101 in the program:
l0: int x = 0;
l1: while (x < 100) {
l2:   x += 1;
l3: } x = 200;
*)
let example2 : unit =
  let n = 100 in

  let f : (int * int) -> int * (int * int) = fun (line, x) ->
    let line, y = match line with
    | 0 -> (1, 0)
    | 1 -> if x < n then (2, x) else (3, x)
    | 2 -> (1, x+1)
    | 3 -> (3, n + n)
    | _ -> (line, x)
    in (x, (line, y))
  in
  let inv : (int * int) -> prop = fun (line, x) ->
    match line with
    | 0 -> squash(x == 0)
    | 1 -> squash(x <= n)
    | 2 -> squash(x < n)
    | 3 -> squash(x == n+n \/ x == n)
    | _ -> False
  in

  let safe (x:int) : prop = squash(x <> n+1) in

  assert(inv (0, 0));
  assert(forall p. inv p ==> safe (f p)._1);
  assert(forall p. inv p ==> inv (f p)._2);

  let inv' = k_ind_invariant safe f (0, 0) 205 in
  assert(inv' (0, 0)) by (norm [primops; iota; delta; zeta; nbe]);
  assert(forall p. inv' p ==> safe (f p)._1) by (norm [primops; iota; delta; zeta; nbe]);
  assert(forall p. inv' p ==> inv' (f p)._2) by (norm [primops; iota; delta; zeta; nbe]);

  let _ = pw_invariant #int safe f (0, 0) inv' in
  let _ = pw_invariant #int safe f (0, 0) inv in
  ()


let paco_stream_eq_with (#a:Type) :
  Paco.monotone_fun (stream a * stream a) =
  fun aux -> on _ #prop (fun (s1, s2) ->
    head s1 == head s2 /\ aux (tail s1, tail s2)
  )

[@@"opaque_to_smt"]
let paco_stream_eq (#a:Type) (s1 s2:stream a) =
  Paco.gfp paco_stream_eq_with (s1, s2)

let paco_stream_eq_thm (#a:Type) (s1 s2:stream a) :
  Lemma (requires paco_stream_eq s1 s2)
    (ensures s1 == s2)
  = //Classical.forall_intro_2 (paco_stream_eq_def #a);
  reveal_opaque (`%paco_stream_eq) (paco_stream_eq #a);
  stream_bisim_thm paco_stream_eq s1 s2

// prove that a certain relation is an sub equality-relation
let assoc_add_property_with (s1 s2 s3: stream int) :
  stream int * stream int -> prop = fun (s, s') ->
    s  == stream_add s1 (stream_add s2 s3) /\
    s' == stream_add (stream_add s1 s2) s3

let assoc_add_property : (stream int * stream int ^-> prop) =
  on _ #prop (fun (s, s') -> exists (s1 s2 s3:stream int).
    assoc_add_property_with s1 s2 s3 (s, s')
  )

#push-options "--z3rlimit 100"
let assoc_add_thm (_:unit) :
  Lemma
    (forall p. assoc_add_property p ==> paco_stream_eq_with assoc_add_property p)
  = let aux : (p:(stream int * stream int)) ->
    Lemma
      (requires assoc_add_property p)
      (ensures paco_stream_eq_with assoc_add_property p) =
    fun (s, s') -> eliminate exists s1 s2 s3.
      s  == stream_add s1 (stream_add s2 s3) /\
      s' == stream_add (stream_add s1 s2) s3
    returns head s == head s' /\ (assoc_add_property (tail s, tail s'))
    with _. begin
      Classical.forall_intro (Classical.move_requires (
        Paco.unfold_gfp #(stream int * stream int) paco_stream_eq_with
      ));
      Classical.forall_intro (Classical.move_requires (
        Paco.fold_gfp #(stream int * stream int) paco_stream_eq_with
      ));
      assert(head s == head s');
      assert(assoc_add_property_with
        (tail s1) (tail s2) (tail s3) (tail s, tail s'))
    end
  in
  Classical.forall_intro (Classical.move_requires aux)
#pop-options

let ts_f (#a #b:Type) (#state:Type)
  (f:b -> state -> a * state) :
  (stream b * state) -> a * (stream b * state) =
  fun (s, x0) ->
    let out, x1 = f (head s) x0 in
    (out, (tail s, x1))

let pw_invariant2 (#a #b:Type) (p:a -> prop) (#state:Type)
  (input:stream b) (f:b -> state -> a * state)
  (s0: state)
  
  (inv: state -> prop)

  : Pure (stream_pw p (stream_corec (ts_f f) (input, s0)))
    (requires
      (forall x s. inv s ==> p (f x s)._1) /\
      (forall x s. inv s ==> inv (f x s)._2) /\
      inv s0
    )

    (ensures
      fun _ -> True
    )
  = 
  let new_state (s:stream a) =
    x:(stream b & state){s == stream_corec (ts_f f) x /\ inv x._2}
  in

  let get_node (s:stream a) (st:new_state s) :
    Lemma (p (head s)) =
    ()
  in

  let get_children (s:stream a) (st:new_state s) (_:unit) :
    new_state (tail s) = 
    let (i, s) : (stream b & state) = st in
    (tail i, (f (head i) s)._2)
  in
  
  m_corec #_ #_ #_ #new_state (fun s x ->
    {node = get_node s x; children = on_dom _ (get_children s x)}
  ) (input, s0)

let tactic_nbe (_:unit) : Tac unit =
  norm [primops; iota; delta; zeta; nbe]

let rec k_ind_invariant2 (#a #b:Type) (#state:Type) (p:a -> prop)
  (f:b -> state -> a * state) (s0:state) (k:nat) (x:state) : Tot prop (decreases k) =
  if k = 0 then x == s0 else
    x == s0 \/ (exists b x'.
      x == (f b x')._2 /\ k_ind_invariant2 p f s0 (k-1) x'
    )

#push-options "--z3rlimit 50 --log_queries --query_stats"
let exemple3 : unit =
  let n = 5 in
  let b = k:nat{k < 2} in
  let f : b -> int -> int * int =
    fun i x -> (x, (if x >= n then 0 else x+i))
  in

  let f_b (x:b) : b * b = (x, (if x = 0 then 1 else 0)) in
  let input : stream b = stream_corec f_b 0 in

  let inv (x:int) : prop = squash(0 <= x /\ x <= n) in

  let safe (x:int) : prop = inv x in

  let _ = pw_invariant2 safe input f 0 inv in

  let k = 10 in
  let inv' = k_ind_invariant2 safe f 0 k in
  assert(inv' 0) by (tactic_nbe ());
  assert(forall i x. inv' x ==> safe (f i x)._1) by tactic_nbe ();
  assert(forall i x. inv' x ==> inv' (f i x)._2) by tactic_nbe ();
  let _ = pw_invariant2 safe input f 0 inv' in

  ()
#pop-options




let stream_eq_aux2' (a:Type) : 
  (((stream a * stream a) ^-> prop)
  -> (stream a * stream a) ^-> prop) =
  fun aux -> on _ #prop (fun (s1, s2) ->
    head s1 == head s2 /\ aux (tail s1, tail s2)
  )

let stream_eq_aux2_monotonic (a:Type) :
  Lemma (Paco2.monotone (stream_eq_aux2' a))
  = assert(Paco2.monotone (stream_eq_aux2' a))

#push-options "--fuel 0 --ifuel 1"
let stream_eq_aux2_scott_c (a:Type) :
  Lemma (Paco2.scott_continuous (stream_eq_aux2' a))
  =
  let aux p x :
    Lemma
      (requires forall n. stream_eq_aux2' a (p n) x)
      (ensures stream_eq_aux2' a (Paco2.limit p) x)
    = 
    let (s1, s2) = x in
    assert(forall n. head s1 == head s2 /\ p n (tail s1, tail s2));
    assert(stream_eq_aux2' a (p 0) x);
    FStar.PropositionalExtensionality.axiom();
    assert(head s1 == head s2 /\ (forall n. p n (tail s1, tail s2)));
    assert(head s1 == head s2 /\ Paco2.limit p (tail s1, tail s2))
      by (unfold_def (`Paco2.limit); assumption ());
    assert(stream_eq_aux2' a (Paco2.limit p) x) by
      (unfold_def (`stream_eq_aux2'); smt ())
  in
  Classical.forall_intro_2 (
    Classical.move_requires_2 aux)
#pop-options

let stream_eq_aux2 (a:Type) :
  Paco2.monotone_fun (stream a * stream a) =
  stream_eq_aux2_monotonic a;
  stream_eq_aux2_scott_c a;
  stream_eq_aux2' a


let rec test (x:(stream int * stream int)) (y:(stream int * (stream int * stream int))) (n:nat) :
  Lemma
    (requires x._1 == stream_add y._1 (stream_add y._2._1 y._2._2) /\
      x._2 == stream_add (stream_add y._1 y._2._1) y._2._2)
    (ensures Paco2.gfp_approx (stream_eq_aux2 int) n x)
    (decreases n)
  = if n = 0 then () else begin
    let s, s' = x in
    let s1, (s2, s3) = y in
    assert(head s == head s');
    test (tail s, tail s') (tail s1, (tail s2, tail s3)) (n-1);
    assert(Paco2.gfp_approx (stream_eq_aux2 int) (n-1) (tail s, tail s'));
    assert(head s == head s' /\ Paco2.gfp_approx (stream_eq_aux2 int) (n-1) (tail s, tail s'));
    assert(stream_eq_aux2 int (Paco2.gfp_approx (stream_eq_aux2 int) (n-1)) (s, s'));
    ()
  end
