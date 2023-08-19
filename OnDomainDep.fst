module OnDomainDep

open FStar.FunctionalExtensionality

// dependent version of onDomain
noeq type onDomainDep (a:Type) ([@@@strictly_positive]b:a -> Type) =
  | OnDomainDep : restricted_t a b -> onDomainDep a b

let to_fun (#a:Type) (#b:a -> Type) (d:onDomainDep a b) : ((x:a) -> b x) =
  match d with
  | OnDomainDep f -> f

let from_fun (#a:Type) (#b:a->Type) (f: (x:a) -> b x) : onDomainDep a b =
  OnDomainDep (on_domain a f)

let deq (#a:Type) (#b:a -> Type) (d1 d2: onDomainDep a b) : prop =
  forall x. to_fun d1 x == to_fun d2 x

let deq_lemma (#a:Type) (#b:a -> Type) (d1 d2: onDomainDep a b) :
  Lemma (requires deq d1 d2)
  (ensures d1 == d2) =
  match (d1, d2) with
  | OnDomainDep f1, OnDomainDep f2 -> assert(feq f1 f2)

let destructor_lemma (#a:Type) (#b:a -> Type) (d:onDomainDep a b) :
  Lemma (from_fun (to_fun d) == d) = ()

let application_lemma (#a:Type) (#b:a -> Type) (f:(x:a) -> b x) :
  Lemma (forall x. to_fun (from_fun f) x == f x) = ()
