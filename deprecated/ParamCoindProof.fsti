module ParamCoindProof

open FStar.FunctionalExtensionality

let monotone (#a:Type) (f: (a ^-> prop) -> a ^-> prop) : prop =
  forall (r1 r2:a ^-> prop). (forall x. r1 x ==> r2 x) ==> (forall x. f r1 x ==> f r2 x)

let monotone_fun (a:Type) = f:((a ^-> prop) -> a ^-> prop){monotone f}

let gfp (#a:Type) (f:monotone_fun a) :  (a ^-> prop) =
  on a #prop (fun x ->
    exists (r:a ^-> prop). r x /\ (forall y. r y ==> f r y)
  )

val tarski (#a:Type) (f:monotone_fun a) (p:a ^-> prop) :
  Lemma
    (requires forall x. p x ==> f p x)
    (ensures forall x. p x ==> gfp f x)

val unfold_gfp (#a:Type) (f:monotone_fun a) (x:a) :
  Lemma
    (requires gfp f x)
    (ensures f (gfp f) x)

val fold_gfp (#a:Type) (f:monotone_fun a) (x:a) :
  Lemma
    (requires f (gfp f) x)
    (ensures gfp f x)


let _or_ (#a:Type) (p q:a ^-> prop) : (a ^-> prop) =
  on _ #prop (fun x -> p x \/ q x)

let union_monotone (#a:Type) (f:monotone_fun a) (p:a ^-> prop) : monotone_fun a =
  fun (q:a ^-> prop) -> f (p `_or_` q)

val strong_coinduction_elim (#a:Type) (f:monotone_fun a) (p:a ^-> prop) :
  Lemma
    (requires forall x. p x ==> gfp f x)
    (ensures forall x. p x ==> union_monotone f p (gfp f) x)

val strong_coinduction_intro (#a:Type) (f:monotone_fun a) (p:a ^-> prop) :
  Lemma
    (requires forall x. p x ==> union_monotone f p (gfp f) x)
    (ensures forall x. p x ==> gfp f x)

let pgfp (#a:Type) (f:monotone_fun a) : monotone_fun a =
  let res (p:a ^-> prop) : (a ^-> prop) =
    gfp (union_monotone f p)
  in
  let aux (p q:a ^-> prop) :
    Lemma
      (requires forall x. p x ==> q x)
      (ensures forall x. res p x ==> res q x)
    = strong_coinduction_intro (union_monotone f q) (res p)
  in
  Classical.forall_intro_2 (Classical.move_requires_2 aux);
  res

val initialize_lemma (#a:Type) (f:monotone_fun a) (p:a ^-> prop) (x:a) :
  Lemma
    (requires forall x. ~(p x))
    (ensures pgfp f p x <==> gfp f x)

val unfold_lemma (#a:Type) (f:monotone_fun a) (p:a ^-> prop) :
  Lemma
    (ensures pgfp f p == union_monotone f p (pgfp f p))

val accumulate_lemma1 (#a:Type) (f:monotone_fun a) (p q:a ^-> prop) :
  Lemma
    (requires forall x. q x ==> pgfp f p x)
    (ensures forall x. q x ==> pgfp f (p `_or_` q) x)

val accumulate_lemma2 (#a:Type) (f:monotone_fun a) (p q:a ^-> prop) :
  Lemma
    (requires forall x. q x ==> pgfp f (p `_or_` q) x)
    (ensures forall x. q x ==> pgfp f p x)
