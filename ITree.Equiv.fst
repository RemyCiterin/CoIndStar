module ITree.Equiv

open PFUtils
open ITree.Basics
open OnDomain

let itree_equiv_functor (e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) :
  Paco.functor (itree e a & itree e b) =
  fun aux (t, t') -> match itree_destruct t, itree_destruct t' with
  | Vis x1 ex1 cont1, Vis x2 ex2 cont2 ->
    x1 == x2 /\ ex1 == ex2 /\ (
      forall arg. aux (to_fun cont1 arg, to_fun cont2 arg)
    )
  | Ret r1, Ret r2 -> rel r1 r2
  | Tau t, Tau t' -> aux (t, t')
  | _, _ -> False

let itree_equiv_functor_monotone (e:Type -> Type) (a b:Type) (rel:a -> b -> prop) :
  Lemma (Paco.monotone (itree_equiv_functor e rel))
  [SMTPat (Paco.monotone (itree_equiv_functor e rel))]
  = Paco.monotone_intro (itree_equiv_functor e rel) (
    fun p q x -> ()
  )

let itree_equiv_functor_commut_with_lb (e:Type -> Type) (a b:Type) (rel:a -> b -> prop) :
  Lemma (Paco.commute_with_lb (itree_equiv_functor e rel))
    [SMTPat (Paco.commute_with_lb (itree_equiv_functor e rel))]
  = Paco.commute_with_lb_intro (itree_equiv_functor e rel) (fun p x ->
    assert(itree_equiv_functor e rel (p 0) x)
  )

let itree_eq_functor (e:Type -> Type) (r:Type) =
  itree_equiv_functor e #r #r (fun x y -> x == y)

// strong bisimulation relation
let itree_equiv (#e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) (t:itree e a) (t':itree e b) =
  Paco.gfp (itree_equiv_functor e rel) (t, t')

let itree_eq (#e:Type -> Type) (#r:Type) (t t':itree e r) =
  Paco.gfp (itree_eq_functor e r) (t, t')

let itree_eq_refl (#e:Type -> Type) (#r:Type) (t:itree e r) :
  Lemma (ensures itree_eq t t) [SMTPat (itree_eq t t)] =
  let p (x:itree e r & itree e r) : prop = x._1 == x._2 in
  Paco.coinduction_pred (itree_eq_functor e r) p (t, t) (fun _ -> ())


let itree_bisim (#e:Type -> Type) (#r:Type) (rel:itree e r -> itree e r -> prop) (t t':itree e r) :
  Lemma
    (requires rel t t' /\ (
      forall t t'. rel t t' ==> itree_eq_functor e r (fun (t, t') -> rel t t') (t, t')
    ))
    (ensures t == t')
  = m_iso_bisim rel t t'

// proof of strong bisimulation theorem
let itree_eq_thm (#e:Type -> Type) (#r:Type) (t t':itree e r) :
  Lemma (requires itree_eq t t') (ensures t == t') =
  Classical.forall_intro (
    Classical.move_requires_2 Paco.unfold_gfp (itree_eq_functor e r));
  itree_bisim itree_eq t t'
