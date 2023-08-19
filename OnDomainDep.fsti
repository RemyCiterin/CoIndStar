(*
this interface is a wrapper on FStar.FunctionalExtensionality
*)
module OnDomainDep

val onDomainDep (a:Type) ([@@@strictly_positive]b:a -> Type) : Type

// construct an onDomainDep object from a function
val to_fun (#a:Type) (#b:a -> Type) : onDomainDep a b -> (x:a) -> b x

// construct a function from an onDomainDep object
val from_fun (#a:Type) (#b:a -> Type) : ((x:a) -> b x) -> onDomainDep a b

let deq (#a:Type) (#b:a -> Type) (d1 d2:onDomainDep a b) : prop =
  forall x. to_fun d1 x == to_fun d2 x

val deq_lemma (#a:Type) (#b:a -> Type) (d1 d2: onDomainDep a b) :
  Lemma (requires deq d1 d2) (ensures d1 == d2) [SMTPat (deq d1 d2)]

val destructor_lemma (#a:Type) (#b:a -> Type) (d:onDomainDep a b) :
  Lemma (from_fun (to_fun d) == d) [SMTPat (to_fun d)]

val application_lemma (#a:Type) (#b:a -> Type) (f:(x:a) -> b x) :
  Lemma (forall x. to_fun (from_fun f) x == f x) [SMTPat (from_fun f)]
