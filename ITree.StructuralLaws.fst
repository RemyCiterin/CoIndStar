module ITree.StructuralLaws

open OnDomain
open ITree.Basics
open ITree.Equiv
open ITree.Eutt
open Equiv

let structural_law1 (#e:Type -> Type) (#r:Type) (rel:r -> r -> prop) (t:itree e r) :
  Lemma (requires reflexivity rel) (ensures eutt rel t (tau t)) =
  let pred (t, t') : prop = t' == tau t in

  let rec lemma (x:itree e r & itree e r) (n:nat) :
    Lemma
      (requires pred x)
      (ensures Paco.gfp_approx (eutt_functor e rel) n x)
      (decreases n) = 
    //reveal_opaque (`%eutt_functor) (eutt_functor e rel);
    if n = 0 then () else let t, t' = x in
    match itree_destruct t with
    | Tau cont -> 
      lemma (cont, t) (n-1);
      eutt_functor_intro e rel (Paco.gfp_approx (eutt_functor e rel) (n-1)) t (tau t) 0
    | _ -> begin
      eutt_refl rel t; 
      Paco.gfp_iff_gfp' (eutt_functor e rel) (t, t);
      Paco.gfp_iff_gfp' (eutt_functor e rel) (t, t');
      assert(Paco.gfp_approx (eutt_functor e rel) (n+1) (t, t));
      reveal_opaque (`%eutt_functor) (eutt_functor e rel);
      eutt_functor_intro e rel (eutt' rel) t (tau t) 1
      
      (*match itree_destruct t with
      | Ret r -> ()
      | Vis x ex cont -> 
        assert(burn 1 t  == Vis x ex cont);
        assert(burn 1 t' == Vis x ex cont);
        let aux x : Lemma (Paco.gfp_approx (eutt_functor e rel) (n-1) (to_fun cont x, to_fun cont x)) =
          Paco.gfp_iff_gfp' (eutt_functor e rel) (to_fun cont x, to_fun cont x);
          eutt_refl rel (to_fun cont x)
        in
        Classical.forall_intro aux;
        eutt_functor_intro e rel (eutt' rel) t (tau t) 1*)
    end
  in
  Paco.coinduction_approx_pred (eutt_functor e rel) pred (t, tau t) lemma



let structural_law2 (#e:Type -> Type) (#r #s:Type) (t:itree e r) (k:r -> itree e s) :
  Lemma (bind (tau t) k == tau (bind t k)) =
  reveal_opaque (`%bind) (bind #e #r #s);
  assert(itree_destruct (bind (tau t) k) == Tau (bind t k));
  itree_bisim (fun t t' ->
    itree_destruct t == itree_destruct t'
  ) (bind (tau t) k) (tau (bind t k))


let structural_law3 (#e:Type -> Type) (#a #r #s:Type) (x: e a) (k1:a -> itree e r) (k2:r -> itree e s) :
  Lemma (bind (vis x k1) k2 == vis x (fun x -> bind (k1 x) k2)) =
  reveal_opaque (`%bind) (bind #e #r #s);
  itree_repr_equality 
    (itree_destruct (bind (vis x k1) k2))
    (itree_destruct (vis x (fun x -> bind (k1 x) k2)));

  itree_bisim (fun t t' ->
    itree_destruct t == itree_destruct t'
  ) (bind (vis x k1) k2) (vis x (fun x -> bind (k1 x) k2))
