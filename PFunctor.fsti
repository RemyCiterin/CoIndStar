(*
definition of coinductive datatype, this interface use OnDomain instead of
restricted_t from FStar.FunctionalExtensionality because fstar does not
properly unify universes with it
*)

module PFunctor

open OnDomain

// definition of polynomial functor interface (or container)
noeq type pfunctor = {command: Type; response: command -> Type}

// definition of the application of a polynomial functor, 
// coinductive datatype are greatest fixed point of it
unopteq type pf_apply (p:pfunctor) ([@@@strictly_positive]a:Type) : Type =
  { node: p.command; children: onDomain (p.response node) a}

// composition of onDomain function
let comp (#a #b #c: Type) (f:b -> c) (g:a -> b) : onDomain a c =
  from_fun (fun (x:a) -> f (g x))

let map (p:pfunctor) (#a #b:Type) (g:a -> b) (pa: pf_apply p a): pf_apply p b =
  {node = pa.node; children = comp g (to_fun pa.children)}

// definition of M-type or coninductive datatype without index
val m_type (p:pfunctor) : Type

// destructor of a M-type
val m_destruct (#p:pfunctor) (m:m_type p) : pf_apply p (m_type p)

// constructor of M-type, the argument `f` is a `generator automaton` of the
// resulting object, and `x` is its initial state
val m_corec (#p:pfunctor) (#a:Type) (f:a -> pf_apply p a) (x:a) : m_type p

val m_dest_corec (#a:Type) (#p:pfunctor) (f:a -> pf_apply p a) (x:a) :
  Lemma (m_destruct (m_corec f x) == map p (m_corec f) (f x))
  [SMTPat (m_destruct (m_corec f x))]

// bisimulation theorem, this version complicated to use but serves as a basis
// for simpler bisimulation theorems
val m_bisim (#p:pfunctor) (r: m_type p -> m_type p -> prop) (m m':m_type p)
  : Lemma (requires r m m' /\ (forall x y. r x y ==> (
    (m_destruct x).node == (m_destruct y).node /\
    (forall arg. r (to_fun (m_destruct x).children arg) (to_fun (m_destruct y).children arg))
  )))
  (ensures m == m')

