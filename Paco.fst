(*
this file define coinductive, inductive and parametrized coinductive properties of arity 1
*)

module Paco

open FStar.PropositionalExtensionality
module Classical = FStar.Classical
module T = FStar.Tactics

let top (a:Type) : a -> prop = fun _ -> True
let bot (a:Type) : a -> prop = fun _ -> False


let functor (a:Type) = (a -> prop) -> a -> prop

let monotone (#a:Type) (f:functor a) : prop =
  forall (r1 r2:a -> prop) x. (forall y. r1 y ==> r2 y) ==> f r1 x ==> f r2 x

let monotone_functor (a:Type) = f:functor a{monotone f}

let monotone_intro (#a:Type) (f:functor a)
  (lemma : (r1:(a -> prop)) -> (r2:(a -> prop)) -> (x:a) ->
    Lemma
      (requires f r1 x /\ (forall y. r1 y ==> r2 y))
      (ensures f r2 x)
  ) : Lemma (monotone f) =
  Classical.forall_intro_3
    (Classical.move_requires_3 lemma)

let monotone_elim (#a:Type) (f:monotone_functor a) (p q:a -> prop) (x:a) :
  Lemma
    (requires f p x /\ (forall x. p x ==> q x))
    (ensures f q x)
  = ()

let upper_bound (#a:Type) (p:nat -> a -> prop) : a -> prop =
  fun x -> exists n. p n x

let lower_bound (#a:Type) (p:nat -> a -> prop) : a -> prop =
  fun x -> forall n. p n x

// commute with lower bound
let commute_with_lb (#a:Type) (f:functor a) : prop =
  forall p x. (forall n. f (p n) x) ==> f (lower_bound p) x

// commute with upper bound
let commute_with_ub (#a:Type) (f:functor a) : prop =
  forall p x. f (upper_bound p) x ==> (exists n. f (p n) x)

let commute_with_lb_intro (#a:Type) (f:functor a) 
  (lemma: (p:(nat -> a -> prop)) -> (x:a) ->
    Lemma
      (requires forall n. f (p n) x)
      (ensures f (lower_bound p) x)
  ) : Lemma (commute_with_lb f)
  = Classical.forall_intro_2 (
    Classical.move_requires_2 lemma)

let commute_with_lb_elim (#a:Type) (f:functor a) (p:nat -> a -> prop) (x:a) :
  Lemma
    (requires commute_with_lb f /\ (forall n. f (p n) x))
    (ensures f (lower_bound p) x)
  = ()

let commute_with_ub_intro (#a:Type) (f:functor a)
  (lemma: (p:(nat -> a -> prop)) -> (x:a) ->
    Lemma
      (requires f (upper_bound p) x)
      (ensures exists n. f (p n) x)
  ) : Lemma (commute_with_ub f)
  = Classical.forall_intro_2 (
    Classical.move_requires_2 lemma)

let commute_with_ub_elim (#a:Type) (f:functor a) (p:nat -> a -> prop) (x:a) :
  Lemma
    (requires commute_with_ub f /\ f (upper_bound p) x)
    (ensures exists n. f (p n) x)
  = ()

let comp_monotone (#a:Type) (f g:monotone_functor a) : monotone_functor a =
  fun p -> f (g p)

let comp_monotone_commute_with_lb (#a:Type) (f g:monotone_functor a) :
  Lemma
    (requires commute_with_lb f /\ commute_with_lb g)
    (ensures commute_with_lb (comp_monotone f g))
    [SMTPat (commute_with_lb (comp_monotone f g))]
  = commute_with_lb_intro 
    (comp_monotone f g)
    (fun p x -> 
      assert(forall n. f (g (p n)) x);
      let gp (n:nat) = g (p n) in
      assert(f (lower_bound gp) x);
      assert(forall x. lower_bound gp x <==> g (lower_bound p) x);
      assert(f (g (lower_bound p)) x)
    )


let comp_monotone_commute_with_ub (#a:Type) (f g:monotone_functor a) :
  Lemma
    (requires commute_with_ub f /\ commute_with_ub g)
    (ensures commute_with_ub (comp_monotone f g))
    [SMTPat (commute_with_ub (comp_monotone f g))] =
  commute_with_ub_intro
    (comp_monotone f g)
    (fun p x ->
      assert(f (g (upper_bound p)) x);
      let gp (n:nat) = g (p n) in
      assert(f (upper_bound gp) x)
    )

// definition of approximation of fixed point
// lfp f x = exists n. lfp_approx f n x
// gfp f x = forall n. gfp_approx f n x

let rec fp_approx_with (#a:Type) (f:monotone_functor a) (n:nat) :
  Tot
    (monotone_functor a)
    (decreases n) =
  if n = 0 then id else
    comp_monotone f (fp_approx_with f (n-1))

let rec fp_approx_with_commute_with_lb (#a:Type) (f:monotone_functor a) (n:nat) :
  Lemma
    (requires commute_with_lb f)
    (ensures commute_with_lb (fp_approx_with f n))
    [SMTPat (commute_with_lb (fp_approx_with f n))]
  = if n = 0 then () else fp_approx_with_commute_with_lb f (n-1)

let rec fp_approx_with_commute_with_ub (#a:Type) (f:monotone_functor a) (n:nat) :
  Lemma
    (requires commute_with_ub f)
    (ensures commute_with_ub (fp_approx_with f n))
    [SMTPat (commute_with_ub (fp_approx_with f n))]
  = if n = 0 then () else fp_approx_with_commute_with_ub f (n-1)

let gfp_approx (#a:Type) (f:monotone_functor a{commute_with_lb f}) (n:nat) : a -> prop =
  fp_approx_with f n (top a)

let lfp_approx (#a:Type) (f:monotone_functor a{commute_with_ub f}) (n:nat) : a -> prop =
  fp_approx_with f n (bot a)

let gfp' (#a:Type) (f:monotone_functor a{commute_with_lb f}) : a -> prop =
  lower_bound (gfp_approx f)

let lfp' (#a:Type) (f:monotone_functor a{commute_with_ub f}) : a -> prop =
  upper_bound (lfp_approx f)

let unfold_gfp' (#a:Type) (f:monotone_functor a{commute_with_lb f}) (x:a) :
  Lemma
    (requires gfp' f x)
    (ensures f (gfp' f) x)
  = Classical.forall_intro (
    Classical.move_requires (commute_with_lb_elim f (gfp_approx f)));
  assert(forall x. (forall n. f (gfp_approx f n) x) ==> f (lower_bound (gfp_approx f)) x);
  assert(forall x. (forall n. f (gfp_approx f n) x) ==> f (gfp' f) x);
  assert(forall (n:nat). gfp_approx f (n+1) x);
  assert(forall n. (gfp_approx f n) x)

let tarski_gfp' (#a:Type) (f:monotone_functor a{commute_with_lb f}) (p:a -> prop) :
  Lemma
    (requires forall x. p x ==> f p x)
    (ensures forall x. p x ==> gfp' f x) =
  let rec aux (x:a) (n:nat) :
    Lemma
      (requires p x /\ (forall x. p x ==> f p x))
      (ensures (forall y. p y ==> fp_approx_with f n p y) /\ gfp_approx f n x) =
    if n = 0 then () else begin
      aux x (n-1)
    end
  in
  Classical.forall_intro_2 (
    Classical.move_requires_2 aux)

let fold_lfp' (#a:Type) (f:monotone_functor a{commute_with_ub f}) (x:a) :
  Lemma
    (requires f (lfp' f) x)
    (ensures lfp' f x)
  = assert(f (upper_bound (lfp_approx f)) x);
  commute_with_ub_elim f (lfp_approx f) x;
  assert(exists (n:nat). f (lfp_approx f n) x);
  assert(exists (n:nat). lfp_approx f (n+1) x)

let tarski_lfp' (#a:Type) (f:monotone_functor a{commute_with_ub f}) (p:a -> prop) :
  Lemma
    (requires forall x. f p x ==> p x)
    (ensures forall x. lfp' f x ==> p x)
  = let rec aux (x:a) (n:nat) :
    Lemma
      (requires lfp_approx f n x /\ (forall x. f p x ==> p x))
      (ensures f p x) (decreases n)
    = if n = 0 then () else begin
      let lemma x : Lemma(requires lfp_approx f (n-1) x) (ensures f p x) =
        aux x (n-1)
      in
      Classical.forall_intro (Classical.move_requires lemma);
      monotone_elim f (lfp_approx f (n-1)) (f p) x
    end
  in
  Classical.forall_intro_2 (
    Classical.move_requires_2 aux)

// definition of fixed point without approximation, and basic theorems of lfp/gfp

let lfp (#a:Type) (f:monotone_functor a) (x:a) : prop =
  forall (p:a -> prop). (forall x. f p x ==> p x) ==> p x

let gfp (#a:Type) (f:monotone_functor a) (x:a) : prop =
  exists (p:a -> prop). p x /\ (forall x. p x ==> f p x)

let fold_lfp (#a:Type) (f:monotone_functor a) (x:a) :
  Lemma
    (requires f (lfp f) x)
    (ensures lfp f x)
  = ()

let unfold_lfp (#a:Type) (f:monotone_functor a) (x:a) :
  Lemma
    (requires lfp f x)
    (ensures f (lfp f) x)
  = ()

let fold_gfp (#a:Type) (f:monotone_functor a) (x:a) :
  Lemma
    (requires f (gfp f) x)
    (ensures gfp f x)
  = ()

let unfold_gfp (#a:Type) (f:monotone_functor a) (x:a) :
  Lemma
    (requires gfp f x)
    (ensures f (gfp f) x)
  = ()

let tarski_lfp (#a:Type) (f:monotone_functor a) (p:a -> prop) :
  Lemma
    (requires forall x. f p x ==> p x)
    (ensures forall x. lfp f x ==> p x)
  = ()

let tarski_gfp (#a:Type) (f:monotone_functor a) (p:a -> prop) :
  Lemma
    (requires forall x. p x ==> f p x)
    (ensures forall x. p x ==> gfp f x)
  = ()

// syntactic sugar for tarski theorem

let coinduction_pred (#a:Type) (f:monotone_functor a) (p:a -> prop) (x:a)
  (lemma: (x:a) -> Lemma (requires p x) (ensures f p x))
  : Lemma (requires p x) (ensures gfp f x) =
  Classical.forall_intro
    (Classical.move_requires lemma);
  tarski_gfp f p

let induction_pred (#a:Type) (f:monotone_functor a) (p:a -> prop) (x:a)
  (lemma: (x:a) -> Lemma (requires f p x) (ensures p x))
  : Lemma (requires lfp f x) (ensures p x) =
  Classical.forall_intro (
    Classical.move_requires lemma);
  tarski_lfp f p

// induction with hypothesis
let induction_pred_with (#a:Type) (f:monotone_functor a) (p1 p2:a -> prop) (x:a)
  (lemma: (x:a) -> Lemma (requires f (fun x -> p1 x ==> p2 x) x /\ p1 x) (ensures p2 x))
  : Lemma (requires lfp f x /\ p1 x) (ensures p2 x) =
  Classical.forall_intro (
    Classical.move_requires lemma);
    tarski_lfp f (fun x -> p1 x ==> p2 x)

let coinduction_rel (#a:Type) (#b:a -> Type) (f:monotone_functor a) (r:(x:a) -> b x -> prop) (x:a) (y:b x)
  (lemma: (x:a) -> (y:b x) -> Lemma (requires r x y) (ensures f (fun x -> exists y. r x y) x))
  : Lemma (requires r x y) (ensures gfp f x) =
  let p x : prop = exists y. r x y in
  let lemma' (x:a) : Lemma (requires p x) (ensures f p x) =
    Classical.forall_intro (
      Classical.move_requires (lemma x))
  in coinduction_pred f p x lemma'

let induction_rel (#a:Type) (#b:a -> Type) (f:monotone_functor a) (r:(x:a) -> b x -> prop) (x:a) (y:b x)
  (lemma: (x:a) -> (y:b x) -> Lemma (requires f (fun x -> forall y. r x y) x) (ensures r x y))
  : Lemma (requires lfp f x) (ensures r x y) =
  let p x : prop = forall y. r x y in
  let lemma' (x:a) : Lemma (requires f p x) (ensures p x) =
    Classical.forall_intro (
      Classical.move_requires (lemma x))
  in induction_pred f p x lemma'

// induction with hypothesis
let induction_rel_with (#a:Type) (#b:a -> Type) (f:monotone_functor a) (r1 r2:(x:a) -> b x -> prop) (x:a) (y:b x)
  (lemma: (x:a) -> (y:b x) -> Lemma (requires f (fun x -> forall y. r1 x y ==> r2 x y) x /\ r1 x y) (ensures r2 x y))
  : Lemma (requires lfp f x /\ r1 x y) (ensures r2 x y) =
  let p x : prop = forall y. r1 x y ==> r2 x y in
  let lemma' (x:a) : Lemma (requires f p x) (ensures p x) =
    Classical.forall_intro (
      Classical.move_requires (lemma x))
  in induction_pred f p x lemma'

// prove that approximated fixed points and fixed point are equals

let lfp_iff_lfp' (#a:Type) (f:monotone_functor a{commute_with_ub f}) (x:a) :
  Lemma
    (ensures lfp f x <==> lfp' f x) = 
  Classical.forall_intro (Classical.move_requires_2 fold_lfp  f);
  Classical.forall_intro (Classical.move_requires_2 fold_lfp' f);
  tarski_lfp' f (lfp f);
  tarski_lfp  f (lfp' f)

let gfp_iff_gfp' (#a:Type) (f:monotone_functor a{commute_with_lb f}) (x:a) :
  Lemma
    (ensures gfp f x <==> gfp' f x) =
  Classical.forall_intro (Classical.move_requires_2 unfold_gfp  f);
  Classical.forall_intro (Classical.move_requires_2 unfold_gfp' f);
  tarski_gfp' f (gfp f);
  tarski_gfp  f (gfp' f)

// syntactic sugar for proving (l|g)fp using (l|g)fp'

let coinduction_approx_pred (#a:Type) (f:monotone_functor a{commute_with_lb f}) (p:a -> prop) (x:a)
  (lemma: (x:a) -> (n:nat) ->
    Lemma (requires p x) (ensures gfp_approx f n x)
  ) : Lemma
    (requires p x)
    (ensures gfp f x)
  = Classical.forall_intro_2 (
    Classical.move_requires_2 lemma);
  gfp_iff_gfp' f x

let induction_approx_pred (#a:Type) (f:monotone_functor a{commute_with_ub f}) (p:a -> prop) (x:a)
  (lemma: (x:a) -> (n:nat) ->
    Lemma (requires lfp_approx f n x) (ensures p x)
  ) : Lemma
    (requires lfp f x) (ensures p x) =
  Classical.forall_intro_2 (
    Classical.move_requires_2 lemma);
  lfp_iff_lfp' f x

let induction_approx_pred_with (#a:Type) (f:monotone_functor a{commute_with_ub f}) (p1 p2:a -> prop) (x:a)
  (lemma: (x:a) -> (n:nat) ->
    Lemma (requires lfp_approx f n x /\ p1 x) (ensures p2 x)
  ) : Lemma
    (requires lfp f x /\ p1 x) (ensures p2 x) =
  Classical.forall_intro_2 (
    Classical.move_requires_2 lemma);
  lfp_iff_lfp' f x

let coinduction_approx_rel (#a:Type) (#b:a -> Type) (f:monotone_functor a{commute_with_lb f}) 
  (r:(x:a) -> b x -> prop) (x:a) (y:b x)
  (lemma: (x:a) -> (y:b x) -> (n:nat) ->
    Lemma (requires r x y) (ensures gfp_approx f n x)
  ) : Lemma
    (requires r x y)
    (ensures gfp f x)
  = Classical.forall_intro_3 (fun x ->
    Classical.move_requires_2 (lemma x));
  gfp_iff_gfp' f x

let induction_approx_rel (#a:Type) (#b:a -> Type) (f:monotone_functor a{commute_with_ub f}) 
  (r:(x:a) -> b x -> prop) (x:a) (y:b x)
  (lemma: (x:a) -> (y:b x) -> (n:nat) ->
    Lemma (requires lfp_approx f n x) (ensures r x y)
  ) : Lemma
    (requires lfp f x) (ensures r x y) =
  Classical.forall_intro_3 (fun x ->
    Classical.move_requires_2 (lemma x));
  lfp_iff_lfp' f x

let induction_approx_rel_with (#a:Type) (#b:a -> Type) (f:monotone_functor a{commute_with_ub f}) 
  (r1 r2:(x:a) -> b x -> prop) (x:a) (y:b x)
  (lemma: (x:a) -> (y:b x) -> (n:nat) ->
    Lemma (requires lfp_approx f n x /\ r1 x y) (ensures r2 x y)
  ) : Lemma
    (requires lfp f x /\ r1 x y) (ensures r2 x y) =
  Classical.forall_intro_3 (fun x ->
    Classical.move_requires_2 (lemma x));
  lfp_iff_lfp' f x

// definition of strong coindcution

let or (#a:Type) (p q:a -> prop) : a -> prop = fun x -> p x \/ q x

let union_monotone (#a:Type) (f:monotone_functor a) (p:a -> prop) : monotone_functor a =
  fun q -> f (p `or` q)

let union_monotone_commute_with_lb (#a:Type) (f:monotone_functor a) (p:a -> prop) :
  Lemma 
    (requires commute_with_lb f)
    (ensures commute_with_lb (union_monotone f p)) 
    [SMTPat (commute_with_lb (union_monotone f p))] =
  commute_with_lb_intro (union_monotone f p) (fun q x ->
    let union_with n = p `or` q n in
    commute_with_lb_elim f union_with x;
    assert(f (p `or` lower_bound q) x)
    
  )

let strong_coinduction_pred (#a:Type) (f:monotone_functor a) (p:a -> prop) (x:a) 
  (lemma: (x:a) -> Lemma (requires p x) (ensures union_monotone f p (gfp f) x))
  : Lemma
    (requires p x)
    (ensures gfp f x)
  = Classical.forall_intro (
    Classical.move_requires lemma)

let strong_coinduction_rel (#a:Type) (b:a -> Type) (f:monotone_functor a)
  (r:(x:a) -> b x -> prop) (x:a) (y:b x)
  (lemma: (x:a) -> (y:b x) ->
    Lemma
      (requires r x y)
      (ensures union_monotone f (fun x -> exists y. r x y) (gfp f) x)
  ) : Lemma
    (requires r x y)
    (ensures gfp f x)
  = let p x : prop = exists y. r x y in
  let lemma' (x:a) : Lemma (requires p x) (ensures union_monotone f p (gfp f) x)
    = Classical.forall_intro (Classical.move_requires (lemma x))
  in strong_coinduction_pred f p x lemma'


// definition of parametrized coinduction

let pgfp (#a:Type) (f:monotone_functor a) : monotone_functor a =
  fun p -> gfp (union_monotone f p)

let initialize_lemma (#a:Type) (f:monotone_functor a) (x:a) :
  Lemma (ensures pgfp f (bot a) x <==> gfp f x) = ()

let unfold_pgfp (#a:Type) (f:monotone_functor a) (p:a -> prop) (x:a) : 
  Lemma
    (requires pgfp f p x)
    (ensures union_monotone f p (pgfp f p) x)
  = unfold_gfp (union_monotone f p) x

let fold_pgfp (#a:Type) (f:monotone_functor a) (p:a -> prop) (x:a) : 
  Lemma
    (requires union_monotone f p (pgfp f p) x)
    (ensures pgfp f p x)
  = fold_gfp (union_monotone f p) x

let accumulate_pred (#a:Type) (f:monotone_functor a) (p q:a -> prop) (x:a)
  (lemma: (x:a) ->
    Lemma
      (requires q x)
      (ensures pgfp f (p `or` q) x)
  ) : Lemma
    (requires q x)
    (ensures pgfp f p x) =
  Classical.forall_intro (
    Classical.move_requires lemma);
  Classical.forall_intro (
    Classical.move_requires_3 unfold_pgfp f (p `or` q));
  tarski_gfp (union_monotone f p) (pgfp f (p `or` q))

let accumulate_rel (#a:Type) (#b:a -> Type) (f:monotone_functor a)
  (p:a -> prop) (r:(x:a) -> b x -> prop) (x:a) (y:b x)
  (lemma: (x:a) -> (y:b x) ->
    Lemma
      (requires r x y)
      (ensures pgfp f (fun x -> p x \/ (exists y. r x y)) x)
  ) : Lemma
    (requires r x y)
    (ensures pgfp f p x) =
  let q x : prop = exists y. r x y in
  let lemma' (x:a) :
    Lemma
      (requires q x)
      (ensures pgfp f (p `or` q) x) =
    Classical.forall_intro (
      Classical.move_requires (lemma x))
  in
  accumulate_pred f p q x lemma'
  
let compose (#a:Type) (f:monotone_functor a) (g1 g2 r1 r2 r:a -> prop) (x:a)
  (h1: (x:a) -> Lemma (requires g1 x) (ensures pgfp f r1 x))
  (h2: (x:a) -> Lemma (requires g2 x) (ensures pgfp f r2 x)) :
  Lemma
    (requires 
      (g1 `or` g2) x /\
      (forall x. r1 x ==> (r `or` g1) x) /\
      (forall x. r2 x ==> (r `or` g2) x)
    ) (ensures pgfp f r x) =
  Classical.forall_intro (Classical.move_requires h1);
  Classical.forall_intro (Classical.move_requires h2);
  accumulate_pred f r (g1 `or` g2) x (fun x -> ())

let pgfp_approx (#a:Type) (f:monotone_functor a{commute_with_lb f}) (p:a -> prop) (n:nat) (x:a) : prop =
  gfp_approx (union_monotone f p) n x

let pcoinduction_approx_pred (#a:Type) (f:monotone_functor a{commute_with_lb f}) (p q:a -> prop) (x:a) 
  (lemma: (x:a) -> (n:nat) ->
    Lemma
      (requires q x)
      (ensures pgfp_approx f p n x)
  ) : Lemma
    (requires q x)
    (ensures pgfp f p x) =
  coinduction_approx_pred (union_monotone f p) q x lemma

let pcoinduction_approx_rel (#a:Type) (#b:a -> Type) (f:monotone_functor a{commute_with_lb f})
  (p:a -> prop) (r:(x:a) -> b x -> prop) (x:a) (y:b x) 
  (lemma: (x:a) -> (y:b x) -> (n:nat) ->
    Lemma
      (requires r x y)
      (ensures pgfp_approx f p n x)
  ) : Lemma
    (requires r x y)
    (ensures pgfp f p x) =
  coinduction_approx_rel (union_monotone f p) r x y lemma

