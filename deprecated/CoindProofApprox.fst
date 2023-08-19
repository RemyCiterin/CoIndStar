(*
definition of parametrized coinductive property (similar to the Paco Coq library), 
this version use finite approximation of coindcutive property as tarski theorem solution,
instead of the classical solution with an exists symbol. 

The problem of this implementation is the usage of scott continuity instead of monotonicity
*)

module CoindProofApprox

module Classical = FStar.Classical
//open FStar.FunctionalExtensionality
open FStar.PropositionalExtensionality


// construction of Paco-like property using approximation of size n
// instead of the traditional definition: 
// gfp f x <==> exists r. r x /\ (forall y. r y ==> f r y)
let monotone (#a:Type) (f:(a -> prop) -> a -> prop) : prop =
  forall (r1 r2:a -> prop) x. (forall y. r1 y ==> r2 y) ==> f r1 x ==> f r2 x

let prove_monotone (#a:Type) (f:(a -> prop) -> a -> prop) 
  (lemma:(r1:(a -> prop)) -> (r2:(a -> prop)) -> (x:a) ->
    Lemma
      (requires (forall y. r1 y ==> r2 y) /\ f r1 x)
      (ensures f r2 x)
  ) : Lemma (monotone f) = 
  Classical.forall_intro_3 (
    Classical.move_requires_3 lemma)


let limit (#a:Type) (p:nat -> a -> prop) : (a -> prop) =
  fun x -> forall n. p n x

let scott_continuous (#a:Type) (f:(a -> prop) -> a -> prop) : prop =
  forall p x. (forall n. f (p n) x) ==> f (limit p) x

// in most cases, just use
// prove_scott_continuous f (fun p x -> assert(f (p 0) x))
// is enough to prove that a function is scott continuous
let prove_scott_continuous (#a:Type) (f:(a -> prop) -> a -> prop)
  (lemma:(p:(nat -> a -> prop)) -> (x:a) ->
    Lemma
      (requires forall n. f (p n) x)
      (ensures f (limit p) x)
  ) : Lemma (scott_continuous f) =
  Classical.forall_intro_2 (
    Classical.move_requires_2 lemma)


let top (a:Type) : (a -> prop) = fun _ -> True
let bot (a:Type) : (a -> prop) = fun _ -> False
// definition of monotone function (in the sens of scott continuity)
let monotone_fun (a:Type) = f:((a -> prop) -> a -> prop){monotone f /\ scott_continuous f}

// eliminate the monotonicity of a function
let apply_monotonicity (#a:Type) (f:monotone_fun a) (r1 r2:a -> prop) (x:a) :
  Lemma
    (requires forall x. r1 x ==> r2 x)
    (ensures f r1 x ==> f r2 x)
  = ()

// eliminate the scott continuity of a function
let apply_scott_continuous (#a:Type) (f:monotone_fun a) (p:nat -> a -> prop) (x:a) :
  Lemma
    (requires forall n. f (p n) x)
    (ensures f (limit p) x)
  = ()

// composition of two monotone function is monotone
let comp_monotone (#a:Type) (f g:monotone_fun a) : monotone_fun a =
  let out p = f (g p) in
  assert(monotone out);

  let aux p x :
    Lemma
      (requires forall n. out (p n) x)
      (ensures out (limit p) x)
    = assert(forall n. f (g (p n)) x);
    let gp (n:nat) = g (p n) in
    assert(f (limit gp) x);
    assert(forall x. limit gp x <==> g (limit p) x);
    axiom (); // apply propositional extensionality
    //assert(feq (limit gp) (g (limit p)));
    assert(f (g (limit p)) x);
    assert(out (limit p) x)
  in

  Classical.forall_intro_2 (
    Classical.move_requires_2 aux);
  out

// fun n p x -> f^n p x 
let rec gfp_approx_with (#a:Type) (f:monotone_fun a) (n:nat) :
  Tot (monotone_fun a) (decreases n) =
  if n = 0 then id else
    comp_monotone f (gfp_approx_with f (n-1))

// fun n x -> f^n top x
let gfp_approx (#a:Type) (f:monotone_fun a) (n:nat) : (a -> prop) =
  gfp_approx_with f n (top a)

// return the limit of gfp_approx_with
let gfp_with (#a:Type) (f:monotone_fun a) : monotone_fun a =
  fun p -> fun x ->
    forall n. gfp_approx_with f n p x
  
// return the greatest fixed point of a monotone function
let gfp (#a:Type) (f:monotone_fun a) : (a -> prop) =
  limit (gfp_approx f)

// proof of tarski theorem
let tarski (#a:Type) (f:monotone_fun a) (p:a -> prop) :
  Lemma
    (requires forall x. p x ==> f p x)
    (ensures forall x. p x ==> gfp f x) =
  let rec aux (x:a) (n:nat) :
    Lemma
      (requires p x /\ (forall x. p x ==> f p x))
      (ensures (forall y. p y ==> gfp_approx_with f n p y) /\ gfp_approx f n x) =
    if n = 0 then () else begin
      aux x (n-1);
      apply_monotonicity f p (gfp_approx_with f (n-1) p) x
    end
  in
  Classical.forall_intro_2 (
    Classical.move_requires_2 aux
  )

let prove_using_tarski_pred (#a:Type) (f:monotone_fun a) (p:a -> prop) (x:a)
  (lemma: (x:a) -> Lemma (requires p x) (ensures f p x))
  : Lemma 
    (requires p x)
    (ensures gfp f x)
  = Classical.forall_intro (
    Classical.move_requires lemma);
  tarski f p

let prove_using_tarski_rel (#a:Type) (#b:a -> Type) 
  (f:monotone_fun a)  (r:(x:a) -> b x -> prop) (x:a) (y:b x)
  (lemma:(x:a) -> (y:b x) -> Lemma
    (requires r x y)
    (ensures f (fun x -> exists y. r x y) x))
  : Lemma
    (requires r x y)
    (ensures gfp f x)
  = prove_using_tarski_pred f (fun x -> exists y. r x y) x
    (fun x -> Classical.forall_intro (Classical.move_requires (lemma x)))


// induction on proof size
let size_ind_proof (#a:Type) (f:monotone_fun a) (p:a -> prop)
  (lemma: (x:a) -> (n:nat) -> Lemma (requires p x) (ensures gfp_approx f n x))
  : Lemma (forall x. p x ==> gfp f x) =
  Classical.forall_intro_2 
    (Classical.move_requires_2 lemma)

// induction on proof size for property of the form fun x -> exists y. r x y
let size_ind_proof_exists (#a:Type) (#b:a -> Type) (f:monotone_fun a)
  (r:(x:a) -> b x -> prop)
  (lemma: (x:a) -> (y:b x) -> (n:nat) -> Lemma (requires r x y) (ensures gfp_approx f n x)) :
  Lemma (forall x. (exists y. r x y) ==> gfp f x) = 
  Classical.forall_intro_3 (fun x y n ->
    Classical.move_requires_2 (lemma x) y n
  )

// optimization of size_ind_proof
// TODO: make p implicit, now fstar does not infer p
let prove_using_pred (#a:Type) (f:monotone_fun a) (p:a -> prop) (x:a)
  (lemma: (x:a) -> (n:nat) -> Lemma (requires p x) (ensures gfp_approx f n x))
  : Lemma (requires p x) (ensures gfp f x) =
  Classical.forall_intro_2 
    (Classical.move_requires_2 lemma)

// optimization of size_ind_proof_exists
// TODO: make r implicit, now fstar does not infer r from the lemma
let prove_using_rel (#a:Type) (#b:a -> Type) (f:monotone_fun a)
  (r:(x:a) -> b x -> prop) (x:a) (y:b x)
  (lemma: (x:a) -> (y:b x) -> (n:nat) -> Lemma (requires r x y) (ensures gfp_approx f n x)) :
  Lemma 
    (requires r x y)
    (ensures gfp f x) = 
  Classical.forall_intro_3 (fun x y n ->
    Classical.move_requires_2 (lemma x) y n
  )

let fold_gfp (#a:Type) (f:monotone_fun a) (x:a) :
  Lemma
    (requires f (gfp f) x)
    (ensures gfp f x) =
  Classical.forall_intro_2 (fun n x ->
    Classical.move_requires_3 (apply_monotonicity f) (gfp f) (gfp_approx f n) x
  );
  assert(forall (n:nat). gfp_approx f (n+1) x);
  assert(forall n. gfp_approx f n x)


let unfold_gfp (#a:Type) (f:monotone_fun a) (x:a) :
  Lemma
    (requires gfp f x)
    (ensures f (gfp f) x) =
  Classical.forall_intro (
    Classical.move_requires (apply_scott_continuous f (gfp_approx f)));
  assert(forall x. (forall n. f (gfp_approx f n) x) ==> f (limit (gfp_approx f)) x);
  assert(forall x. (forall n. f (gfp_approx f n) x) ==> f (gfp f) x);
  assert(forall (n:nat). gfp_approx f (n+1) x);
  assert(forall n. f (gfp_approx f n) x)


let or (#a:Type) (p q:a -> prop) : a -> prop =
  fun x -> p x \/ q x

let union_monotone (#a:Type) (f:monotone_fun a) (p:a -> prop) : 
  monotone_fun a =
  let out = fun q -> f (p `or` q) in

  let union_with q (n:nat) x : prop =
    p x \/ q n x
  in
  
  prove_scott_continuous out (
    fun q x ->
      apply_scott_continuous f (union_with q) x;
      assert(f (p `or` limit q) x)
  );
  out

let union_monotone_symm (#a:Type) (f:monotone_fun a) (p q:a -> prop) (x:a) :
  Lemma (requires union_monotone f p q x)
    (ensures union_monotone f q p x)
  = ()

let strong_coinduction_elim (#a:Type) (f:monotone_fun a) (p:a -> prop) :
  Lemma
    (requires forall x. p x ==> gfp f x)
    (ensures forall x. p x ==> union_monotone f p (gfp f) x)
  = Classical.forall_intro (Classical.move_requires_2 unfold_gfp f)

let strong_coinduction_intro (#a:Type) (f:monotone_fun a) (p:a -> prop) :
  Lemma
    (requires forall x. p x ==> union_monotone f p (gfp f) x)
    (ensures forall x. p x ==> gfp f x) =
  Classical.forall_intro (Classical.move_requires_2 unfold_gfp f);
  let r : a -> prop = p `or` (gfp f) in
  assert(forall x. f (gfp f) x ==> f r x);
  assert(forall x. r x ==> f r x);
  tarski f r

(*
this section define parametrized coinduction part of the library Paco and it's different lemmas
*)

// TODO: prove that this function is scott continious if it is
let pgfp (#a:Type) (f:monotone_fun a) : (a -> prop) -> a -> prop =
  fun p -> gfp (union_monotone f p)

let pgfp_approx (#a:Type) (f:monotone_fun a) (p:a -> prop) (n:nat) : a -> prop =
  gfp_approx (union_monotone f p) n

let pgfp_monotone (#a:Type) (f:monotone_fun a) :
  Lemma (monotone (pgfp f)) = 
  prove_monotone (pgfp f) (fun p q x ->
      Classical.forall_intro (Classical.move_requires_2 unfold_gfp (union_monotone f p));
      strong_coinduction_intro (union_monotone f q) (pgfp f p)
  )

let initialize_lemma (#a:Type) (f:monotone_fun a) (p:a -> prop) (x:a) :
  Lemma
    (ensures pgfp f (bot a) x <==> gfp f x) =
  Classical.forall_intro (Classical.move_requires_2 unfold_gfp (union_monotone f (bot a)));
  Classical.forall_intro (Classical.move_requires_2 unfold_gfp f);
  tarski f (gfp (union_monotone f (bot a)));
  tarski (union_monotone f (bot a)) (gfp f)

let unfold_pgfp (#a:Type) (f:monotone_fun a) (p:a -> prop) (x:a) :
  Lemma
    (requires pgfp f p x)
    (ensures union_monotone f p (pgfp f p) x)
  = unfold_gfp (union_monotone f p) x

let fold_pgfp (#a:Type) (f:monotone_fun a) (p:a -> prop) (x:a) :
  Lemma
    (requires union_monotone f p (pgfp f p) x)
    (ensures pgfp f p x)
  = fold_gfp (union_monotone f p) x


// there is an equivalence, applying the monotonicity of pgfp f
let accumulate_lemma (#a:Type) (f:monotone_fun a) (p q:a -> prop) :
  Lemma
    (requires forall x. q x ==> pgfp f (p `or` q) x)
    (ensures forall x. q x ==> pgfp f p x) =
  Classical.forall_intro (Classical.move_requires_3 unfold_pgfp f (p `or` q));
  tarski (union_monotone f p) (pgfp f (p `or` q))

// compositional rule for combining proofs in the rely guarantee style
let compose (#a:Type) (f:monotone_fun a) (g1 g2 r1 r2 r:a -> prop) :
  Lemma
    (requires
      (forall x. g1 x ==> pgfp f r1 x) /\
      (forall x. g2 x ==> pgfp f r2 x) /\
      (forall x. r1 x ==> (r `or` g1) x) /\
      (forall x. r2 x ==> (r `or` g2) x)
    )
    (ensures forall x. (g1 `or` g2) x ==> pgfp f r x) =
  Classical.forall_intro_2 (
    Classical.move_requires_3 accumulate_lemma f);
  pgfp_monotone f


let prove_pgfp_using_pred (#a:Type) (f:monotone_fun a) (p q:a -> prop) (x:a) 
  (lemma : (x:a) -> (n:nat) -> 
    Lemma
      (requires q x)
      (ensures pgfp_approx f p n x)
  ) : Lemma
    (requires q x)
    (ensures pgfp f p x)
  = prove_using_pred (union_monotone f p) q x lemma


let prove_pgfp_using_rel (#a:Type) (#b:a -> Type) (f:monotone_fun a) (p:a -> prop)
  (rel:(x:a) -> b x -> prop) (x:a) (y:b x) 
  (lemma : (x:a) -> (y:b x) -> (n:nat) ->
    Lemma
      (requires rel x y)
      (ensures pgfp_approx f p n x)
  ) : Lemma
    (requires rel x y)
    (ensures pgfp f p x)
  = prove_using_rel (union_monotone f p) rel x y lemma
