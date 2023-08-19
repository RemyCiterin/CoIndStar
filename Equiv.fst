(*
definition of equivalence relation
*)

module Equiv

let relation (a:Type) = a -> a -> prop
let predicate (a:Type) = a -> prop

let reflexivity (#a:Type) (r:relation a) : prop =
  forall x. r x x

let symmetry (#a:Type) (r:relation a) : prop =
  forall x y. r x y ==> r y x

let transitivity (#a:Type) (r:relation a) : prop =
  forall x y z. r x y /\ r y z ==> r x z

// equivalence relation property
let equivalence (#a:Type) (r:relation a) : prop =
  reflexivity r /\ symmetry r /\ transitivity r

// subtype of equivalence relation 
let equiv (a:Type) = 
  r:relation a{equivalence r}

// eliminate an equivalence relation with pattern
let elim_eq_laws #a (r:equiv a) :
  Lemma (
    (forall x.{:pattern r x x} r x x) /\
    (forall x y.{:pattern r x y} r x y ==> r y x) /\
    (forall x y z.{:pattern r x y; r y z} r x y /\ r y z ==> r x z)
  ) = ()

