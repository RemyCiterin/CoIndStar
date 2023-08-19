module Utils

open IdxPFunctor

unfold let m_node (#output:Type) (#p:idx_pf output) (#o:output) (m:m_type p o) =
  (m_destruct m).node

unfold let m_children (#output:Type) (#p:idx_pf output) (#o:output) (m:m_type p o) =
  (m_destruct m).children

val m_type_identity (#output:Type) (#p:idx_pf output) (#o:output)
  (f: (o:output) -> m_type p o -> m_type p o) (m:m_type p o) :
  Lemma (requires
    forall o x. m_node (f o x) == m_node x /\
    (forall i. m_children (f o x) i == f _ (m_children x i))
  )
  (ensures f o m == m)

val m_type_injective_function (#output:Type) (#p:idx_pf output)
  (f: (o:output) -> m_type p o -> m_type p o) (#o:output) (m m':m_type p o) :
  Lemma (requires f o m == f o m' /\ (forall o x y. f o x == f o y ==> (
    m_node x == m_node y /\ (forall i.
      f _ (m_children x i) == f _ (m_children y i)
  ))))
  (ensures m == m')

let m_construct_state (#output:Type) (#p:idx_pf output) (o o':output) =
  x:option (m_type p o'){None? x ==> o == o'}

let mc_state_from_some
  (#output:Type) (#p:idx_pf output) (o o':output) (m:m_type p o') :
  m_construct_state o o' = Some m

let m_construct_automaton (#output:Type) (#p:idx_pf output) (o:output)
  (pm:idx_apply p o (m_type p)) (o':output) (state: m_construct_state o o') :
  idx_apply p o' (m_construct_state o) =

  match state with
  | Some m -> map (mc_state_from_some o) (m_destruct m)
  | None -> map (mc_state_from_some o) pm

let m_construct (#output:Type) (#p:idx_pf output) (#o:output)
  (pm: idx_apply p o (m_type p)) : m_type p o =
  m_corec (m_construct_automaton o pm) None

val m_construct_destruct_thm (#output:Type) (#p:idx_pf output) (#o:output) (m:m_type p o) :
  Lemma
    (ensures m_construct (m_destruct m) == m)
    [SMTPat (m_construct (m_destruct m))]


val m_destruct_construct_thm (#output:Type) (#p:idx_pf output) (#o:output)
  (pm:idx_apply p o (m_type p)) :
  Lemma
    (ensures m_destruct (m_construct pm) == pm)
    [SMTPat (m_destruct (m_construct pm))]


let m_equals_pf (#output:Type) (p:idx_pf output) : idx_pf (o:output & (m_type p o * m_type p o)) =
  {
    command = (fun (|o, (m1, m2)|) -> squash(m_node m1 == m_node m2));
    response = (fun (|o, (m1, m2)|) _ -> p.response o (m_destruct m1).node);
    next = (fun (|o, (m1, m2)|) _ arg -> (|p.next o (m_destruct m1).node arg, 
      (m_children m1 arg, m_children m2 arg)|))
  }

let m_equals (#output:Type) (#p:idx_pf output) (#o:output) (m1 m2:m_type p o) : Type =
  m_type (m_equals_pf p) (|o, (m1, m2)|)


val m_equals_thm (#output:Type) (#p:idx_pf output) (#o:output) (m1 m2:m_type p o)
  (m_eq: m_equals m1 m2) : Lemma (m1 == m2)
