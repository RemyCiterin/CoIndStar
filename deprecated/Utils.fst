module Utils

open IdxPFunctor
module Classical = FStar.Classical
open FStar.FunctionalExtensionality
open FStar.Tactics.Derived
open FStar.Tactics.Builtins

(* some utilities to deal with functions from m_type to m_type *)

let m_type_identity (#output:Type) (#p:idx_pf output) (#o:output)
  (f:(o:output) -> m_type p o -> m_type p o) (m:m_type p o) :
  Lemma
    (requires
      forall o x. m_node (f o x) == m_node x /\
      (forall i. m_children (f o x) i == f _ (m_children x i))
    )
    (ensures f o m == m) =
  m_bisim_thm (fun o m m' -> m == f o m') (f o m) m

let m_type_injective_function (#output:Type) (#p:idx_pf output)
  (f: (o:output) -> m_type p o -> m_type p o) (#o:output) (s s':m_type p o) :
  Lemma
    (requires f o s == f o s' /\ (forall o x y. f o x == f o y ==> (
      m_node x == m_node y /\ (forall i.
        f _ (m_children x i) == f _ (m_children y i)
    ))))
    (ensures s == s')
  = m_bisim_thm (fun o s s' -> f o s == f o s') s s'

(* defintion and properties about constructor *)



let m_construct_lemma1 (#output:Type) (#p:idx_pf output) (#o #o':output)
  (pm:idx_apply p o (m_type p)) (m:m_type p o') :
  Lemma (m_corec (m_construct_automaton o pm) (mc_state_from_some o o' m) == m) =
  m_type_identity (fun o' m -> m_corec (m_construct_automaton o pm) (mc_state_from_some o o' m)) m

let m_construct_lemma2 (#output:Type) (#p:idx_pf output) (o:output)
  (pm:idx_apply p o (m_type p)) arg :
  Lemma (
    m_construct (m_destruct (pm.children arg)) ==
    (m_destruct (m_construct pm)).children arg
  ) =
  let m = pm.children arg in
  let pm' = m_destruct m in

  let t1 = m_construct pm in
  let t2 = m_corec (m_construct_automaton o pm) (Some m) in
  let t3 = m_construct pm' in
  let t4 = m_corec (m_construct_automaton _ pm') (Some m) in

  assert(t2 == (m_destruct t1).children arg);
  m_construct_lemma1 pm m;
  m_construct_lemma1 pm' m;
  assert(t2 == t4);

  assert(m_node t3 == m_node t4);
  assert(feq (m_children t3) (m_children t4));
  idx_apply_equals (m_destruct t3) (m_destruct t4);

  m_bisim_thm (fun o x y -> m_destruct x == m_destruct y) t3 t4

let m_construct_destruct_thm (#output:Type) (#p:idx_pf output) (#o:output) (m:m_type p o) :
  Lemma
    (ensures m_construct (m_destruct m) == m)
    [SMTPat (m_construct (m_destruct m))]
  = Classical.forall_intro_3 (m_construct_lemma2 #output #p);
  m_type_identity (fun _ m -> m_construct (m_destruct m)) m


let m_destruct_construct_thm (#output:Type) (#p:idx_pf output) (#o:output)
  (pm:idx_apply p o (m_type p)) :
  Lemma
    (ensures m_destruct (m_construct pm) == pm)
    [SMTPat (m_destruct (m_construct pm))]
  =
  Classical.forall_intro_3 (m_construct_lemma2 #output #p);
  let pm' = m_destruct (m_construct pm) in
  assert(feq pm.children pm'.children);
  idx_apply_equals pm pm'

(* fonctions to deal with equality of m_type and bisim *)



let m_equals_thm (#output:Type) (#p:idx_pf output) (#o:output) (m1 m2:m_type p o)
  (m_eq: m_equals m1 m2) : Lemma (m1 == m2) =
  let r (o:output) (m1 m2:m_type p o) : prop = squash(m_equals m1 m2) in
  assert(r o m1 m2);

  // step 1: r o m1 m2 ==> (m_destruct m1).node == (m_destruct m2).node
  let aux0 (input:(o:output & (m_type p o * m_type p o))) :
    Lemma (requires r input._1 input._2._1 input._2._2)
    (ensures m_node input._2._1 == m_node input._2._2)
    = 
    let (|o, (m1, m2)|) = input in
    let x:squash(m_equals m1 m2) = () in
    FStar.Squash.bind_squash #_ #(m_node m1 == m_node m2) x
      m_node
  in
  let aux1 o m1 m2 : 
    Lemma (r o m1 m2 ==> m_node m1 == m_node m2)
    = Classical.move_requires aux0 (|o, (m1, m2)|)
  in
  Classical.forall_intro_3 aux1;
  assert(forall o m1 m2. r o m1 m2 ==> (m_destruct m1).node == (m_destruct m2).node);

  // step 2: r o m1 m2 ==> forall arg. (m_destruct m1).children arg == (m_destruct m2).children
  let aux2 (input:(o:output & (m_type p o * m_type p o))) :
    Lemma (requires r input._1 input._2._1 input._2._2)
    (ensures forall arg. m_node input._2._1 == m_node input._2._2 /\
      r _ 
        (m_children input._2._1 arg)
        (m_children input._2._2 arg)
    )
    = let (|o, (m1, m2)|) = input in
    let x:squash(m_equals m1 m2) = () in

    assert(m_node m1 == m_node m2);

    let aux4 (m_eq:m_equals m1 m2) :
      squash(forall arg. r _ (m_children m1 arg) (m_children m2 arg)) =
      let aux5 arg : Lemma (r _ (m_children m1 arg) (m_children m2 arg)) =
        let x: r _ (m_children m1 arg) (m_children m2 arg) =
          FStar.Squash.return_squash ((m_destruct m_eq).children arg) in
        ()
      in
      Classical.forall_intro aux5
    in
    
    FStar.Squash.bind_squash x aux4
  in

  let aux3 o m1 m2 :
    Lemma (r o m1 m2 ==> (forall arg. r _ (m_children m1 arg) (m_children m2 arg))) =
    Classical.move_requires aux2 (|o, (m1, m2)|)
  in
  Classical.forall_intro_3 aux3;

  m_bisim_thm r m1 m2


noeq type isomorphism (t1 t2:Type) = {
  hom: t1 -> t2;
  inv: t2 -> t1;
  inv_hom: (x:t1) ->
    Lemma (inv (hom x) == x) [SMTPat (inv (hom x))];
  hom_inv: (x:t2) ->
    Lemma (hom (inv x) == x) [SMTPat (hom (inv x))]
}

let iso_inv_hom_thm (#t1 #t2:Type) (iso:isomorphism t1 t2) (x:t1) :
  Lemma
    (ensures iso.inv (iso.hom x) == x)
    [SMTPat (iso.inv (iso.hom x))]
  = iso.inv_hom x

let iso_hom_inv_thm (#t1 #t2:Type) (iso:isomorphism t1 t2) (x:t2) :
  Lemma
    (ensures iso.hom (iso.inv x) == x)
    [SMTPat (iso.hom (iso.inv x))] =
  iso.hom_inv x

let fun_comp (#a #b #c:Type) (f:b -> c) (g:a -> b) (x:a) : c = f (g x)

let right_comp_hom
  (#t1 #t2:Type) (iso:isomorphism t1 t2)
  (f:t1 ^-> Type) : (t2 ^-> Type)
  = on_dom _ (fun_comp f iso.inv)

let right_comp_inv
  (#t1 #t2:Type) (iso:isomorphism t1 t2)
  (f:t2 ^-> Type) : (t1 ^-> Type)
  = on_dom _ (fun_comp f iso.hom)

let right_comp_inv_hom_thm
  (#t1 #t2:Type) (iso:isomorphism t1 t2)
  (f:t1 ^-> Type) :
  Lemma
    (f == right_comp_inv iso (right_comp_hom iso f))
    [SMTPat (right_comp_inv iso (right_comp_hom iso f))]
  = let aux (x:t1) :
    Lemma (f x == right_comp_inv iso (right_comp_hom iso f) x)
    = iso.inv_hom x
  in
  Classical.forall_intro aux;
  assert(feq f (right_comp_inv iso (right_comp_hom iso f)))

let right_comp_hom_inv_thm
  (#t1 #t2:Type) (iso:isomorphism t1 t2)
  (f: t2 ^-> Type) :
  Lemma
    (f == right_comp_hom iso (right_comp_inv iso f))
    [SMTPat (right_comp_hom iso (right_comp_inv iso f))]
  = let aux (x:t2) :
    Lemma (f x == right_comp_hom iso (right_comp_inv iso f) x)
    = iso.hom_inv x
  in
  Classical.forall_intro aux;
  assert(feq f (right_comp_hom iso (right_comp_inv iso f)))

// TODO:
// il faut definir des isomorphism naturels entre idx_apply p o f
// et new_apply (iso.hom o) (right_comp_hom f) et s'en servir pour reconstruire
// des versions isomorphe de m_destruct, m_corec, m_destruct_corec_thm et m_bisim_thm

//                   from_new_apply
// idx_apply pf o a <--------------> new_apply o' a'
//     |             from_idx_apply        |
//     | map f                             | new_map f'
//     |                                   |
//     v             from_idx_apply        v
// idx_apply pf o b <--------------> new_apply o' a'
//                   from_new_apply


noeq type apply_functor
  (#output1 #output2:Type)
  (iso: isomorphism output1 output2)
  (pf:idx_pf output1) =
  {
    new_apply: output2 -> (output2 ^-> Type) -> Type;

    new_map:
      (#a:(output2 ^-> Type)) ->
      (#b:(output2 ^-> Type)) ->
      (#o:output2) -> (f: ((o:output2) -> a o -> b o)) ->
      new_apply o a -> new_apply o b;
      

    from_idx_apply:
      (#o:output1) -> (#f:(output1 ^-> Type)) ->
      idx_apply pf o f ->
      new_apply (iso.hom o) (right_comp_hom iso f);

    from_new_apply:
      (#o:output2) -> (#f:(output2 ^-> Type)) ->
        new_apply o f ->
        idx_apply pf (iso.inv o) (right_comp_inv iso f);

    new_idx_thm:
      (#o:output1) -> (#f: (output1 ^-> Type)) ->
      (ia:idx_apply pf o f) ->
      Lemma
        (ia == from_new_apply (from_idx_apply ia));

    idx_new_thm:
      (#o:output2) -> (#f:(output2 ^-> Type)) ->
      (na:new_apply o f) ->
      Lemma
        (na == from_idx_apply (from_new_apply na))
  }
