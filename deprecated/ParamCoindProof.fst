module ParamCoindProof

module Classical = FStar.Classical
open FStar.FunctionalExtensionality
open FStar.PropositionalExtensionality


let apply_monotonicity (#a:Type) (f:monotone_fun a) (r1 r2:a ^-> prop) :
  Lemma
    (requires forall x. r1 x ==> r2 x)
    (ensures forall x. f r1 x ==> f r2 x)
  = ()

let tarski (#a:Type) (f:monotone_fun a) (p:a ^-> prop) :
  Lemma
    (requires forall x. p x ==> f p x)
    (ensures forall x. p x ==> gfp f x)
  = ()

let unfold_gfp (#a:Type) (f:monotone_fun a) (x:a) :
  Lemma
    (requires gfp f x)
    (ensures f (gfp f) x)
  = ()

let fold_gfp (#a:Type) (f:monotone_fun a) (x:a) :
  Lemma
    (requires f (gfp f) x)
    (ensures gfp f x)
  = ()


let strong_coinduction_elim (#a:Type) (f:monotone_fun a) (p:a ^-> prop) :
  Lemma
    (requires forall x. p x ==> gfp f x)
    (ensures forall x. p x ==> union_monotone f p (gfp f) x)
  = ()


let strong_coinduction_intro (#a:Type) (f:monotone_fun a) (p:a ^-> prop) :
  Lemma
    (requires forall x. p x ==> union_monotone f p (gfp f) x)
    (ensures forall x. p x ==> gfp f x)
  = let r : a -> prop = p `_or_` (gfp f) in
  assert(forall x. f (gfp f) x ==> f r x);
  assert(forall x. r x ==> f r x);
  ()

let initialize_lemma (#a:Type) (f:monotone_fun a) (p:a ^-> prop) (x:a) :
  Lemma
    (requires forall x. ~(p x))
    (ensures pgfp f p x <==> gfp f x) =
  assert(forall x q. union_monotone f p q x <==> f q x);
  ()

let unfold_lemma1 (#a:Type) (f:monotone_fun a) (p:a ^-> prop) (x:a) :
  Lemma
    (requires pgfp f p x)
    (ensures union_monotone f p (pgfp f p) x)
  = ()


let unfold_lemma2 (#a:Type) (f:monotone_fun a) (p:a ^-> prop) (x:a) :
  Lemma
    (requires union_monotone f p (pgfp f p) x)
    (ensures pgfp f p x)
  = fold_gfp (union_monotone f p) x


let unfold_lemma (#a:Type) (f:monotone_fun a) (p:a ^-> prop) :
  Lemma
    (ensures pgfp f p == union_monotone f p (pgfp f p))
  = Classical.forall_intro (Classical.move_requires (unfold_lemma1 f p));
  Classical.forall_intro (Classical.move_requires (unfold_lemma2 f p));
  axiom ();
  assert(feq (pgfp f p) (union_monotone f p (pgfp f p)))


let accumulate_lemma1 (#a:Type) (f:monotone_fun a) (p q:a ^-> prop) :
  Lemma
    (requires forall x. q x ==> pgfp f p x)
    (ensures
      forall x. q x ==> pgfp f (p `_or_` q) x
    )
  = apply_monotonicity (pgfp f) p (p `_or_` q)


let accumulate_lemma2 (#a:Type) (f:monotone_fun a) (p q:a ^-> prop) :
  Lemma
    (requires forall x. q x ==> pgfp f (p `_or_` q) x)
    (ensures forall x. q x ==> pgfp f p x)
  = unfold_lemma f (p `_or_` q);
  assert(forall x. pgfp f (p `_or_` q) x ==> 
    union_monotone f p (pgfp f (p `_or_` q)) x);
  let g : monotone_fun a = fun q -> f (p `_or_` q) in
  assert(forall x. pgfp f (p `_or_` q) x ==>
    g (pgfp f (p `_or_` q)) x);
  assert(forall x. pgfp f (p `_or_` q) x ==>
    pgfp f p x)
