module CoIndList

open PFunctor
open OnDomain
module Classical = FStar.Classical
open FStar.List.Tot.Base
open FStar.List.Tot.Properties
open FStar.Tactics.Typeclasses
open FStar.Tactics.Builtins
open FStar.Tactics.Derived
open FStar.Tactics

let p_stream (a:Type) : pfunctor =
  {
    index = a;
    target = fun _ -> unit
  }

let stream_apply (a out:Type) = a * out

let from_pf_apply (#a #out:Type) (x:pf_apply (p_stream a) out) : stream_apply a out =
  (x.node, to_fun x.children ())

let to_pf_apply (#a #out:Type) (x:stream_apply a out) : pf_apply (p_stream a) out =
  let (x, y) = x in
  {node = x; children = from_fun (fun _ -> y)}

let stream (a:Type) = m_type (p_stream a)

let head (#a:Type) (s:stream a) : a =
  let (h, _) = from_pf_apply (m_destruct s) in h

let tail (#a:Type) (s:stream a) : stream a =
  let (_, t) = from_pf_apply (m_destruct s) in t

let stream_corec (#a #state:Type) (f:state -> a * state) (s0:state) : stream a =
  m_corec (fun s -> to_pf_apply (f s)) s0

let stream_head_corec_thm (#a #state:Type) (f:state -> a * state) (s0:state) :
  Lemma (ensures
    head (stream_corec f s0) == (f s0)._1
  ) = ()

let stream_tail_corec_thm (#a #state: Type) (f:state -> a * state) (s0:state) :
  Lemma (ensures
    tail (stream_corec f s0) == stream_corec f (f s0)._2
  ) = ()

let stream_destruct_head (#a:Type) (s:stream a) :
  Lemma ((m_destruct s).node == head s)
  [SMTPat (m_destruct s).node]
  = ()

let stream_destruct_tail (#a:Type) (s:stream a) (arg:unit) :
  Lemma (to_fun (m_destruct s).children arg == tail s)
  [SMTPat (to_fun (m_destruct s).children arg)]
  = ()


let stream_bisim (#a:Type) (r:stream a -> stream a -> prop) (s s':stream a) :
  Lemma
  (requires r s s' /\ (forall (x y:stream a).{:pattern r x y} r x y ==> (
    head x == head y /\ r (tail x) (tail y)
  )))
  (ensures s == s') =
  m_type_bisim r s s'

let stream_feq (#a:Type) (f g:stream a -> stream a) (s:stream a) :
  Lemma
    (requires
      (forall x. head (f x) == head (g x))
      /\ (forall x. tail (f x) == f (tail x))
      /\ (forall x. tail (g x) == g (tail x))
    )
    (ensures f s == g s) =
    let r : stream a -> stream a -> prop =
      fun s s' -> exists x. s == f x /\ s' == g x
    in

    stream_bisim r (f s) (g s)

let stream_injective_function (#a:Type) (f:stream a -> stream a) (s s':stream a) :
  Lemma
    (requires f s == f s' /\ (forall x y. f x == f y ==> (head x == head y /\ f (tail x) == f (tail y))))
    (ensures f s == f s')
  = stream_bisim (fun s s' -> f s == f s') s s'

let stream_corec_feq (#a #state:Type) (f g:state -> a * state) (s0:state) :
  Lemma
    (requires forall x. f x == g x)
    (ensures stream_corec f s0 == stream_corec g s0)
  = stream_bisim (fun m m' ->
    exists s. m == stream_corec f s /\ m' == stream_corec g s
  ) (stream_corec f s0) (stream_corec g s0)

let stream_construct_automaton (#a:Type) (h:a) (t:stream a)
  (state: option (stream a)) : a * option (stream a) =
  match state with
  | Some s -> (head s, Some (tail s))
  | None -> (h, Some t)

let stream_construct (#a:Type) (h:a) (t:stream a) : stream a =
  stream_corec (stream_construct_automaton h t) None

// example of proof using bisim: identity on stream using corec
let stream_id (#a:Type) (s:stream a) : stream a =
  stream_corec #a #(stream a) (fun s -> (head s, tail s)) s

let stream_id_thm (#a:Type) (s:stream a) :
  Lemma (stream_id s == s) =
  let s' = stream_id s in
  stream_bisim (fun s s' -> stream_id s == s') s s'

let stream_construct_lemma1 (#a:Type) (h h':a) (t t':stream a) (s:stream a) :
  Lemma (
    stream_corec (stream_construct_automaton h t) (Some s) == 
    stream_corec (stream_construct_automaton h' t') (Some s))
  =
  stream_feq
    (fun s -> stream_corec (stream_construct_automaton h t) (Some s))
    (fun s -> stream_corec (stream_construct_automaton h' t') (Some s))
    s

let stream_construct_lemma2 (#a:Type) (h:a) (t:stream a) :
  Lemma (
    tail (stream_corec (stream_construct_automaton h t) None) ==
    stream_corec (stream_construct_automaton (head t) (tail t)) None
  ) =

  let t1 = stream_corec (stream_construct_automaton h t) None in
  let t2 = stream_corec (stream_construct_automaton h t) (Some t) in
  let t3 = stream_corec (stream_construct_automaton (head t) (tail t)) None in
  let t4 = stream_corec (stream_construct_automaton (head t) (tail t)) (Some t) in

  assert(tail t1 == t2);
  stream_construct_lemma1 h (head t) t (tail t) t;
  assert(t2 == t4);

  assert(tail t3 == tail t4);
  assert(head t3 == head t4);
  stream_bisim (fun s s' -> head s == head s' /\ tail s == tail s') t3 t4;
  assert(t3 == t4)

let stream_construct_thm (#a:Type) (s:stream a) :
  Lemma
    (ensures stream_construct (head s) (tail s) == s) =

  Classical.forall_intro_2 (stream_construct_lemma2 #a);
  stream_feq (fun s -> stream_construct (head s) (tail s)) (fun s -> s) s


let stream_construct_head_thm (#a:Type) (h:a) (t:stream a) :
  Lemma (h == head (stream_construct h t)) =
  ()

let stream_construct_tail_thm (#a:Type) (h:a) (t:stream a) :
  Lemma (t == tail (stream_construct h t)) =
  Classical.forall_intro_2 (stream_construct_lemma2 #a);
  stream_feq (fun s -> tail (stream_construct h s)) (fun s -> s) t

let rec stream_nth (#a:Type) (s:stream a) (i:nat) : Tot a (decreases i) =
  if i = 0 then head s else stream_nth (tail s) (i-1)

let rec stream_nth_thm (#a:Type) (s:stream a) (i:nat) :
  Lemma (ensures stream_nth (tail s) i == stream_nth s (i+1)) (decreases i)
  [SMTPat (stream_nth (tail s) i)]
  = if i = 0 then () else stream_nth_thm (tail s) (i-1)

let stream_from_index_automaton (#a:Type) (f:nat -> a) (n:nat) :
  a * nat = (f n, n+1)

let stream_from_index (#a:Type) (f:nat -> a) : stream a =
  stream_corec (stream_from_index_automaton f) 0

let add_one (#a:Type) (f:nat -> a) (n:nat) : a = f (n+1)

let stream_from_index_thm (#a:Type) (f:nat -> a) (i:nat) :
  Lemma (ensures (
    stream_corec (stream_from_index_automaton f) (i+1) == 
    stream_corec (stream_from_index_automaton (add_one f)) i
  )) [SMTPat (stream_corec (stream_from_index_automaton f) (i+1))] =
  let aux = stream_from_index_automaton f in

  let aux' = stream_from_index_automaton (add_one f) in

  stream_bisim (fun m m' -> exists i.
    m == stream_corec aux (i+1) /\
    m' == stream_corec aux' i
  ) (stream_corec aux (i+1)) (stream_corec aux' i)

let stream_from_index_thm_at0 (#a:Type) (f:nat -> a) :
  Lemma (
    ensures stream_corec (stream_from_index_automaton f) 1 == stream_corec (stream_from_index_automaton (add_one f)) 0
  ) [SMTPat (stream_corec (stream_from_index_automaton f) 1)] =
  stream_from_index_thm f 0


let stream_nth_from_index (#b:Type) (m:stream b) :
  Lemma (stream_from_index (stream_nth m) == m) =

  let f (m:stream b) = stream_from_index (stream_nth m) in
  let g (m:stream b) : nat -> (b * nat) = stream_from_index_automaton (stream_nth m) in

  assert(forall (m:stream b).
    head m == head (f m)
  );

  assert_norm(forall (m:stream b).{:pattern f m}
    f m == stream_corec (fun (n:nat) -> (stream_nth m n, n+1)) 0
  );

  assert_norm(forall (m:stream b).{:pattern f (tail m)}
    f (tail m) == stream_corec (fun (n:nat) -> (stream_nth (tail m) n, n+1)) 0
  );

  assert(forall n (m:stream b).{:pattern stream_nth (tail m) n}
    stream_nth (tail m) n == stream_nth m (n+1)
  );

  let aux0 (m:stream b) : nat -> b * nat = stream_from_index_automaton (stream_nth m) in
  let aux1 (m:stream b) : nat -> b * nat = stream_from_index_automaton (stream_nth (tail m)) in
  let aux2 (m:stream b) : nat -> b * nat = stream_from_index_automaton (add_one (stream_nth m)) in

  let aux_thm1 (m:stream b) :
    Lemma (stream_corec (aux1 m) 0 == stream_corec (aux2 m) 0) =
    assert(forall (n:nat). aux1 m n == aux2 m n)
      by (unfold_def (`add_one); unfold_def (`stream_from_index_automaton); smt ());
    stream_corec_feq (aux1 m) (aux2 m) 0
  in

  let aux_thm2 (m:stream b) :
    Lemma (stream_corec (aux2 m) 0 == stream_corec (aux0 m) 1) =
    stream_from_index_thm_at0 (aux0 m);
    assert(stream_corec (aux0 m) 1 == stream_corec (aux2 m) 0)
  in

  Classical.forall_intro aux_thm1;

  assert_norm(forall (m:stream b).
    f (tail m) == stream_corec (aux1 m) 0
  );

  assert(forall (m:stream b).
    f (tail m) == stream_corec (aux0 m) 1
  );

  stream_tail_corec_thm (aux0 m) 0;

  let id (m:stream b) : stream b = m in
  assert(forall m. head (id m) == head (f m));
  assert(forall m. tail (id m) == id (tail m));

  assert(f (tail m) == tail (stream_corec (aux0 m) 0));
  assert(f (tail m) == tail (f m));
  
  stream_feq f id m

