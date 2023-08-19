module OnDomain

open FStar.FunctionalExtensionality

noeq type onDomain (a:Type) ([@@@strictly_positive] b:Type) : Type =
  | OnDomain : (a ^-> b) -> onDomain a b

let from_fun (#a #b: Type) (f: a -> b) : onDomain a b = OnDomain (on a f)

let to_fun (#a #b: Type) (d: onDomain a b) : a -> b =
  match d with
  | OnDomain f -> f

let deq (#a #b: Type) (d1:onDomain a b) (d2:onDomain a b) : prop =
  forall x. to_fun d1 x == to_fun d2 x

let deq_lemma (#a #b: Type) (d1 d2:onDomain a b) :
  Lemma (requires (deq d1 d2)) (ensures d1 == d2) =
  match (d1, d2) with
  | OnDomain f1, OnDomain f2 ->
    assert(feq f1 f2)

let destructor_lemma (#a #b:Type) (d:onDomain a b) : Lemma (from_fun (to_fun d) == d) = ()

let application_lemma (#a #b: Type) (f:a -> b) : Lemma (forall x. to_fun (from_fun f) x == f x) = ()
