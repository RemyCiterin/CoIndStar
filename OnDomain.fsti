(*
this interface is a wrapper on FStar.FunctionalExtensionality
*)
module OnDomain

val onDomain (a: Type) ([@@@strictly_positive] b: Type) : Type

// construct an onDomain object using a function 
val from_fun (#a #b: Type) : (a -> b) -> onDomain a b

// construct a function usin an onDomain object
val to_fun (#a #b: Type) : onDomain a b -> a -> b

// equality on domain
let deq (#a #b: Type) (d1:onDomain a b) (d2:onDomain a b) : prop =
  forall x. to_fun d1 x == to_fun d2 x

val deq_lemma (#a #b: Type) (d1 d2: onDomain a b) :
  Lemma (requires (deq d1 d2)) (ensures d1 == d2) [SMTPat (deq d1 d2)]

val destructor_lemma (#a #b: Type) (d:onDomain a b) :
  Lemma (from_fun (to_fun d) == d) [SMTPat (to_fun d)]

val application_lemma (#a #b: Type) (f: a -> b) :
  Lemma (forall x. to_fun (from_fun f) x == f x) [SMTPat (from_fun #a #b f)]
