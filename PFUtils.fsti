(*
definition of useful functions to handle non-indexed coinductive types
*)

module PFUtils

open PFunctor
open OnDomain

#push-options "--print_universes"

// return the node of the destroyed object
unfold let m_node (#p:pfunctor) (m:m_type p) =
  (m_destruct m).node

// return the children of the destroyed object
unfold let m_children (#p:pfunctor) (m:m_type p) =
  (m_destruct m).children

// inverse of the m_destruct function, define using m_corec 
val m_construct (#p:pfunctor) :
  pf_apply p (m_type p) -> m_type p

val m_cons_dest (#p:pfunctor) (m:m_type p) :
  Lemma
    (m_construct (m_destruct m) == m)
    [SMTPat (m_construct (m_destruct m))]

val m_dest_cons (#p:pfunctor) (pa:pf_apply p (m_type p)) :
  Lemma
    (m_destruct (m_construct pa) == pa)
    [SMTPat (m_destruct (m_construct pa))]

(*
this section define a new interface to construct coinductive datatype
using custom functors and a natural isomorphism between the functor
and a polynomial functor instead of polynomial functors directly
*)
noeq type functor = {
  f:Type -> Type;
  fmap: (#a:Type) -> (#b:Type) -> (a -> b) -> f a -> f b
}

noeq type interface_iso (f:functor) = {
  pf: pfunctor;
  hom: (#t:Type) -> pf_apply pf t -> f.f t;
  inv: (#t:Type) -> f.f t -> pf_apply pf t;
  inv_hom: (#t:Type) -> squash(forall x. inv #t (hom x) == x);
  hom_inv: (#t:Type) -> squash(forall x. hom #t (inv x) == x);
  hom_map: (#a:Type) -> (#b:Type) -> (g:(a -> b)) -> (p:pf_apply pf a) ->
    squash(hom (map pf g p) == f.fmap g (hom p))
}

let m_iso_type (#f:functor) (iso:interface_iso f) : Type =
  m_type iso.pf

let m_iso_destruct (#f:functor) (#iso:interface_iso f) 
  (m:m_iso_type iso) : f.f (m_iso_type iso) =
  iso.hom (m_destruct m)

let m_iso_construct (#f:functor) (#iso:interface_iso f)
  (pa:f.f (m_iso_type iso)) : m_iso_type iso =
  m_construct (iso.inv pa)

let m_iso_cons_dest (#f:functor) (#iso:interface_iso f)
  (m:m_iso_type iso) :
  Lemma
    (ensures m_iso_construct (m_iso_destruct m) == m)
    [SMTPat (m_iso_construct (m_iso_destruct m))]
  = iso.inv_hom #(m_iso_type iso)

let m_iso_dest_cons (#f:functor) (#iso:interface_iso f)
  (pa:f.f (m_iso_type iso)) :
  Lemma
    (ensures m_iso_destruct (m_iso_construct pa) == pa)
    [SMTPat (m_iso_destruct (m_iso_construct pa))]
  = iso.hom_inv #(m_iso_type iso)

let m_iso_bisim (#f:functor) (#iso:interface_iso f)
  (r:m_iso_type iso -> m_iso_type iso -> prop) (m m':m_iso_type iso) :
  Lemma
    (requires r m m' /\ (forall m m'. r m m' ==> (
      let pa  = m_iso_destruct m  in
      let pa' = m_iso_destruct m' in
      (iso.inv pa).node == (iso.inv pa').node /\ (forall arg.
        r
          (to_fun (iso.inv pa).children arg)
          (to_fun (iso.inv pa').children arg)
    ))))
    (ensures m == m')
  = iso.hom_inv #(m_iso_type iso);
  iso.inv_hom #(m_iso_type iso);
  m_bisim (fun x y -> r x y) m m'

let m_iso_corec_automaton
  (#f:functor) (iso:interface_iso f) (#state:Type) 
  (trans:state -> f.f state) : state -> pf_apply iso.pf state =
  fun x -> iso.inv (trans x)

let m_iso_corec (#f:functor) (iso:interface_iso f)
  (#state:Type) (trans:state -> f.f state) : state -> m_iso_type iso =
  m_corec (m_iso_corec_automaton iso trans)


let m_iso_dest_corec (#f:functor) (#iso:interface_iso f)
  (#state:Type) (trans:state -> f.f state) (x:state) :
  Lemma (
    m_iso_destruct (m_iso_corec iso trans x)
    == f.fmap (m_iso_corec iso trans) (trans x)
  ) = 
  iso.hom_inv #state;
  iso.hom_map (m_iso_corec iso trans) (iso.inv (trans x));
  
  assert(m_iso_destruct (m_iso_corec iso trans x) == 
    iso.hom (
      map iso.pf (m_corec (m_iso_corec_automaton iso trans)) (iso.inv (trans x))
    )
  )
