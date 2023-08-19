module ITree.CongruenceLaws

open OnDomain
module Classical = FStar.Classical
open ITree.Basics
open ITree.Equiv
open ITree.Eutt
open ITree.MonadLaws
open ITree.StructuralLaws


let congruence_law_1 (#e:Type -> Type) (#r:Type) (t1 t2:itree e r) :
  Lemma
    (requires t1 == t2)
    (ensures tau t1 == tau t2)
  = itree_bisim (fun t t' -> itree_destruct t == itree_destruct t') (tau t1) (tau t2)

let congruence_law_2 (#e:Type->Type) (#r #s #a:Type) (rel:r -> s -> prop) (ea: e a) 
  (k1:a -> itree e r) (k2:a -> itree e s) : Lemma
    (requires forall x. eutt rel (k1 x) (k2 x))
    (ensures eutt rel (vis ea k1) (vis ea k2)) =
  eutt_functor_intro e rel (eutt' rel) (vis ea k1) (vis ea k2) 0;
  Paco.fold_gfp (eutt_functor e rel) (vis ea k1, vis ea k2)

let eutt_tau_l (#e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) (t:itree e a) (t':itree e b) :
  Lemma
    (requires eutt rel t t')
    (ensures eutt rel (tau t) t') =
  structural_law1 (fun x y -> x == y) t;
  eutt_symm (fun x y -> x == y) (tau t) t;
  eutt_monotone (inverse_binrel (fun x y -> x == y)) (fun x y -> x == y) (tau t) t;
  eutt_trans (fun x y -> x == y) rel (tau t) t t';
  eutt_monotone (compose_binrel (fun x y -> x == y) rel) rel (tau t) t'

let eutt_tau_r (#e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) (t:itree e a) (t':itree e b) :
  Lemma
    (requires eutt rel t t')
    (ensures eutt rel t (tau t')) =
  structural_law1 (fun x y -> x == y) t';
  eutt_trans rel (fun x y -> x == y) t t' (tau t');
  eutt_monotone (compose_binrel rel (fun x y -> x == y)) rel t (tau t')

let eutt_tau_lr (#e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) (t:itree e a) (t':itree e b) :
  Lemma
    (requires eutt rel t t')
    (ensures eutt rel (tau t) (tau t')) =
  eutt_tau_l rel t t';
  eutt_tau_r rel (tau t) t'

let eutt_inverse_tau_l (#e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) (t:itree e a) (t':itree e b) :
  Lemma
    (requires eutt rel (tau t) t')
    (ensures eutt rel t t') =
    structural_law1 (fun x y -> x == y) t;
    eutt_trans (fun x y -> x == y) rel t (tau t) t';
    eutt_monotone (compose_binrel (fun x y -> x == y) rel) (rel) t t'

let eutt_inverse_tau_r (#e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) (t:itree e a) (t':itree e b) :
  Lemma
    (requires eutt rel t (tau t'))
    (ensures eutt rel t t') =
    structural_law1 (fun x y -> x == y) t';
    eutt_symm (fun x y -> x == y) (tau t') t';
    eutt_monotone (inverse_binrel (fun x y -> x == y)) (fun x y -> x == y) (tau t') t';
    eutt_trans rel (fun x y -> x == y) t (tau t') t';
    eutt_monotone (compose_binrel rel (fun x y -> x == y)) rel t t'

let eutt_inverse_tau_lr (#e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) (t:itree e a) (t':itree e b) :
  Lemma
    (requires eutt rel (tau t) (tau t'))
    (ensures eutt rel t t') =
    eutt_inverse_tau_l rel t (tau t');
    eutt_inverse_tau_r rel t t'

let rec congruence_law_3_lemma0 (#e:Type -> Type) (#a #b #c #d:Type) (rel1:a -> c -> prop) (rel2:b -> d -> prop)
  (t1:itree e a) (t2:itree e c) (k1:a -> itree e b) (k2:c -> itree e d) (r1:a) (r2:c) (n:nat) :
  Lemma
    (requires 
      eutt rel1 t1 t2 /\ (forall r r'. rel1 r r' ==> eutt rel2 (k1 r) (k2 r')) /\
      burn n t1 == Ret r1 /\ burn n t2 == Ret r2
    )
    (ensures
      eutt rel2 (bind t1 k1) (bind t2 k2)
    ) (decreases n) = 
  if n = 0 then begin
    monad_law2 k1 r1;
    monad_law2 k2 r2;
    assert(bind t1 k1 == k1 r1);
    assert(bind t2 k2 == k2 r2);
    Paco.unfold_gfp (eutt_functor e rel1) (t1, t2);
    eutt_functor_elim e rel1 (eutt' rel1) t1 t2 (eutt rel2 (bind t1 k1) (bind t2 k2)) (fun n ->
      burn_composition 0 n t1;
      burn_composition 0 n t2;
      assert(rel1 r1 r2)
    )
  end else begin
    match itree_destruct t1, itree_destruct t2 with
    | Tau t, Tau t' ->
      burn_composition 1 n t1;
      burn_composition 1 n t2;
      eutt_inverse_tau_lr rel1 t t';
      congruence_law_3_lemma0 rel1 rel2 t t' k1 k2 r1 r2 (n-1);
      reveal_opaque (`%bind) (bind #e #a #b);
      reveal_opaque (`%bind) (bind #e #c #d);
      assert(itree_destruct (bind t1 k1) == Tau (bind t k1));
      assert(itree_destruct (bind t2 k2) == Tau (bind t' k2));
      eutt_tau_lr rel2 (bind t k1) (bind t' k2)
    | Tau t, _ ->
      burn_composition 1 n t1;
      burn_composition 0 n t2;
      eutt_inverse_tau_l rel1 t t2;
      congruence_law_3_lemma0 rel1 rel2 t t2 k1 k2 r1 r2 (n-1);
      reveal_opaque (`%bind) (bind #e #a #b);
      assert(itree_destruct (bind t1 k1) == Tau (bind t k1));
      eutt_tau_l rel2 (bind t k1) (bind t2 k2)
    | _, Tau t' ->
      burn_composition 1 n t2;
      burn_composition 0 n t1;
      eutt_inverse_tau_r rel1 t1 t';
      congruence_law_3_lemma0 rel1 rel2 t1 t' k1 k2 r1 r2 (n-1);
      reveal_opaque (`%bind) (bind #e #c #d);
      assert(itree_destruct (bind t2 k2) == Tau (bind t' k2));
      eutt_tau_r rel2 (bind t1 k1) (bind t' k2)
    | _, _ ->
      congruence_law_3_lemma0 rel1 rel2 t1 t2 k1 k2 r1 r2 0
  end

let congruence_law_3 (#e:Type -> Type) (#a #b #c #d:Type) (rel1:a -> c -> prop) (rel2:b -> d -> prop)
  (t1:itree e a) (t2:itree e c) (k1:a -> itree e b) (k2:c -> itree e d) : 
  Lemma
    (requires
      eutt rel1 t1 t2 /\ (forall x y. rel1 x y ==> eutt rel2 (k1 x) (k2 y))
    ) (ensures eutt rel2 (bind t1 k1) (bind t2 k2)) =
  reveal_opaque (`%bind) (bind #e #a #b);
  reveal_opaque (`%bind) (bind #e #c #d);

  let pred (x: itree e b & itree e d) (y:itree e a & itree e c) : prop =
    x._1 == bind y._1 k1 /\ x._2 == bind y._2 k2 /\ eutt' rel1 y
  in

  let aux = Paco.gfp_approx (eutt_functor e rel2) in

  let rec lemma (x:itree e b & itree e d) (y:itree e a & itree e c) (n:nat) : 
    Lemma
      (requires pred x y)
      (ensures Paco.gfp_approx (eutt_functor e rel2) n x) 
      (decreases n) =
    if n = 0 then () else
    let t1, t2 = y in
    let bindtk1, bindtk2 = x in
    Paco.unfold_gfp (eutt_functor e rel1) (t1, t2);
    eutt_functor_elim e rel1 (eutt' rel1) t1 t2 (aux n x) (fun k ->
      match itree_destruct t1, itree_destruct t2 with
      | Tau t, Tau t' ->
        assert(itree_destruct (bind t1 k1) == Tau (bind t k1));
        assert(itree_destruct (bind t2 k2) == Tau (bind t' k2));
        lemma (bind t k1, bind t' k2) (t, t') (n-1);
        assert(aux (n-1) (bind t k1, bind t' k2));
        eutt_functor_intro e rel2 (aux (n-1)) (bind t1 k1) (bind t2 k2) 0
      | _, _ -> begin
        match burn k t1, burn k t2 with
        | Ret r1, Ret r2 ->
          congruence_law_3_lemma0 rel1 rel2 t1 t2 k1 k2 r1 r2 k;
          Paco.gfp_iff_gfp' (eutt_functor e rel2) (bind t1 k1, bind t2 k2)
        | Vis x1 ex1 cont1, Vis x2 ex2 cont2 ->
          let rec burn_vis_lemma1 t x ex cont n :
            Lemma
              (requires burn n t == Vis #e #a x ex cont)
              (ensures burn n (bind t k1) == Vis #e #b x ex (from_fun (fun x -> bind (to_fun cont x) k1)))
              (decreases n) =
            match itree_destruct t with
            | Tau t' ->
              assert(itree_destruct (bind t k1) == Tau (bind t' k1));
              burn_vis_lemma1 t' x ex cont (n-1)
            | _ ->
              itree_repr_equality 
                (burn n (bind t k1)) 
                (Vis x ex (from_fun (fun x -> bind (to_fun cont x) k1)))
          in 
          burn_vis_lemma1 t1 x1 ex1 cont1 k;
          

          let rec burn_vis_lemma2 t x ex cont n :
            Lemma
              (requires burn n t == Vis #e #c x ex cont)
              (ensures burn n (bind t k2) == Vis #e #d x ex (from_fun (fun x -> bind (to_fun cont x) k2)))
              (decreases n) =
            match itree_destruct t with
            | Tau t' ->
              assert(itree_destruct (bind t k2) == Tau (bind t' k2));
              burn_vis_lemma2 t' x ex cont (n-1)
            | _ ->
              itree_repr_equality 
                (burn n (bind t k2)) 
                (Vis x ex (from_fun (fun x -> bind (to_fun cont x) k2)))
          in 
          burn_vis_lemma2 t2 x2 ex2 cont2 k;

          let lemma' x :
            Lemma (aux (n-1) (bind (to_fun cont1 x) k1, bind (to_fun cont2 x) k2)) =
            lemma (bind (to_fun cont1 x) k1, bind (to_fun cont2 x) k2) (to_fun cont1 x, to_fun cont2 x) (n-1)
          in
          Classical.forall_intro lemma';

          eutt_functor_intro e rel2 (aux (n-1)) (bind t1 k1) (bind t2 k2) k
      end
    )
  in

  Paco.coinduction_approx_rel (eutt_functor e rel2) pred (bind t1 k1, bind t2 k2) (t1, t2) lemma
