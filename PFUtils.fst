module PFUtils

open PFunctor

module Classical = FStar.Classical


module T = FStar.Tactics
open FStar.Tactics.Typeclasses
open OnDomain


let m_construct_automaton (#p:pfunctor) (pa:pf_apply p (m_type p))
  (state:option (m_type p)) =
  match state with
  | Some m -> map p Some (m_destruct m)
  | None -> map p Some pa

let m_construct (#p:pfunctor) (pa:pf_apply p (m_type p))
  = m_corec (m_construct_automaton pa) None

let m_construct_lemma1 (#p:pfunctor) (pa:pf_apply p (m_type p)) (m:m_type p) :
  Lemma (m_corec (m_construct_automaton pa) (Some m) == m)
  = m_bisim (fun m m' ->
    m' == m_corec (m_construct_automaton pa) (Some m)
  ) m (m_corec (m_construct_automaton pa) (Some m))

let m_construct_lemma2 (#p:pfunctor) (pa:pf_apply p (m_type p)) arg :
  Lemma (m_construct (m_destruct (to_fun pa.children arg)) ==
    to_fun (m_children (m_construct pa)) arg
  ) = 
  let m = to_fun pa.children arg in
  let pa' = m_destruct m in

  let t1 = m_construct pa in
  let t2 = m_corec (m_construct_automaton pa) (Some m) in
  let t3 = m_construct pa' in
  let t4 = m_corec (m_construct_automaton pa') (Some m) in

  assert(t2 == to_fun (m_children t1) arg);
  m_construct_lemma1 pa m;
  m_construct_lemma1 pa' m;
  assert(t2 == t4);
  m_bisim (fun x y -> m_destruct x == m_destruct y) t3 t4

let m_cons_dest (#p:pfunctor) (m:m_type p) :
  Lemma
    (ensures m_construct (m_destruct m) == m)
    [SMTPat (m_construct (m_destruct m))]
  = Classical.forall_intro_2 (m_construct_lemma2 #p);
  m_bisim (fun x y ->
    y == m_construct (m_destruct x)
  ) m (m_construct (m_destruct m))

let m_dest_cons (#p:pfunctor) (pa:pf_apply p (m_type p)) :
  Lemma
    (ensures m_destruct (m_construct pa) == pa)
    [SMTPat (m_destruct (m_construct pa))]
  =
  Classical.forall_intro_2 (m_construct_lemma2 #p);
  let pa' = m_destruct (m_construct pa) in
  assert(deq pa.children pa'.children)


