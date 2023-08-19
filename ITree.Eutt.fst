module ITree.Eutt

open ITree.Basics
open OnDomain
open Equiv
module T = FStar.Tactics


unfold let eutt_functor_at_depth_without_tau_tau (e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) (n:nat) :
  Paco.functor (itree e a & itree e b) = fun aux (t, t') ->
  match burn n t, burn n t' with
  | Ret r1, Ret r2 -> rel r1 r2
  | Vis x1 ex1 cont1, Vis x2 ex2 cont2 ->
    x1 == x2 /\ ex1 == ex2 /\ (forall x. 
      aux (to_fun cont1 x, to_fun cont2 x)
    )
  | _, _ -> False


// definition of equivalence up to tau
// we can define this function with an inductive (like in the paper)
// but it is difficult to proofs with it. I put the pattern matching
// in the right sens so that the arguments of aux are independent of the depth of burn
let eutt_functor_at_depth (e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) (n:nat) :
  Paco.functor (itree e a & itree e b) =
  fun aux (t, t') ->
  match itree_destruct t, itree_destruct t' with
  | Tau t, Tau t' ->
    aux (t, t')
  | _, _ -> 
    eutt_functor_at_depth_without_tau_tau e rel n aux (t, t')

[@@"opaque_to_smt"]
let eutt_functor (e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) :
  Paco.functor (itree e a & itree e b) = fun aux x ->
    exists n. eutt_functor_at_depth e rel n aux x

let eutt_functor_intro (e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop)
  (aux:itree e a & itree e b -> prop) (t:itree e a) (t':itree e b) (n:nat) :
  Lemma
    (requires eutt_functor_at_depth e rel n aux (t, t'))
    (ensures eutt_functor e rel aux (t, t'))
  = reveal_opaque (`%eutt_functor) (eutt_functor e rel)

// I use continuation passing style to reasone about depth, because
// it's easier that add an existential to a complicated context
let eutt_functor_elim 
(e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop)
  (aux:itree e a & itree e b -> prop) 
  (t:itree e a) (t':itree e b)
  (out: prop)
  (lemma: (n:nat) ->
    Lemma
      (requires eutt_functor_at_depth e rel n aux (t, t'))
      (ensures out)
  ) : Lemma
    (requires eutt_functor e rel aux (t, t'))
    (ensures out) =
  reveal_opaque (`%eutt_functor) (eutt_functor e rel);
  Classical.forall_intro (
    Classical.move_requires lemma)

let eutt_functor_monotone (e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) : 
  Lemma
    (Paco.monotone (eutt_functor e rel))
    [SMTPat (Paco.monotone (eutt_functor e rel))]
  = Paco.monotone_intro (eutt_functor e rel) (fun p q x ->
    reveal_opaque (`%eutt_functor) (eutt_functor e rel)
  )

let rec burn_composition (#e:Type -> Type) (#r:Type) (n m:nat) (t:itree e r) :
  Lemma
    (requires m >= n)
    (ensures burn m t == burn (m - n) (itree_construct (burn n t)))
    (decreases m)
  = if n = 0 then () else
  match itree_destruct t with
  | Tau t ->
    burn_composition (n-1) (m-1) t
  | _ -> ()

let rec burn_not_tau (#e:Type -> Type) (#r:Type) (n m:nat) (t:itree e r) :
  Lemma
    (requires ~(Tau? (burn n t)) /\ ~(Tau? (burn m t)))
    (ensures burn n t == burn m t)
    (decreases (if n >= m then m else n)) =
  if n = 0 || m = 0 then () else
  match itree_destruct t with
  | Tau t ->
    burn_not_tau (n-1) (m-1) t
  | _ -> ()

let eutt_functor_depth_indep (e:Type -> Type) (#a #b:Type) (rel: a -> b -> prop)
  (aux0 aux1:itree e a & itree e b -> prop) (t:itree e a) (t':itree e b) (n0 n1:nat) :
  Lemma
    (requires
      eutt_functor_at_depth e rel n0 aux0 (t, t') /\
      eutt_functor_at_depth e rel n1 aux1 (t, t')
    )
    (ensures
      eutt_functor_at_depth e rel n1 aux0 (t, t')
    )
  = match itree_destruct t, itree_destruct t' with
  | Tau t, Tau t' -> ()
  | _, _ -> 
    burn_not_tau n0 n1 t;
    burn_not_tau n0 n1 t'

#push-options "--fuel 2 --ifuel 1"
let eutt_functor_aux_commute_with_lb (e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) :
  Lemma
    (Paco.commute_with_lb (eutt_functor e rel))
    [SMTPat (Paco.commute_with_lb (eutt_functor e rel))] =
  Paco.commute_with_lb_intro (eutt_functor e rel) (fun p (t, t') ->
    eutt_functor_elim e rel (p 0) t t' 
      (eutt_functor e rel (Paco.lower_bound p) (t, t'))
      (fun n ->
        let lemma (d:nat) :
          Lemma (eutt_functor_at_depth e rel n (p d) (t, t'))
          = eutt_functor_elim e rel (p d) t t'
            (eutt_functor_at_depth e rel n (p d) (t, t'))
            (fun n' -> 
              eutt_functor_depth_indep e rel (p d) (p 0) t t' n' n
            )
        in
        Classical.forall_intro lemma;

        //itree_eutt_with_functor_intro e rel (Paco.lower_bound p) t t' n
        assert(eutt_functor_at_depth e rel n (p 0) (t, t'));
        assert(forall d. eutt_functor_at_depth e rel n (p d) (t, t'));

        match itree_destruct t, itree_destruct t' with
        | Tau t1, Tau t2 ->
          eutt_functor_intro e rel (Paco.lower_bound p) t t' n
        | _, _ -> begin
          match burn n t, burn n t' with
          | Ret r1, Ret r2 -> assert(rel r1 r2);
            eutt_functor_intro e rel (Paco.lower_bound p) t t' n
          | Vis x1 ex1 cont1, Vis x2 ex2 cont2 ->
            eutt_functor_intro e rel (Paco.lower_bound p) t t' n
        end
      )
  )
#pop-options

let eutt' (#e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) : itree e a & itree e b -> prop =
  Paco.gfp (eutt_functor e rel)

let eutt (#e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) (t:itree e a) (t':itree e b) : prop =
  eutt' rel (t, t')


let eutt_refl (#e:Type -> Type) (#r:Type) 
  (rel:r -> r -> prop) (x:itree e r) : Lemma
    (requires reflexivity rel)
    (ensures eutt rel x x)
  = let pred (x:itree e r & itree e r) : prop =
    x._1 == x._2
  in
  Paco.coinduction_pred (eutt_functor e rel) pred (x, x) (fun (t, t') -> 
    eutt_functor_intro e rel pred t t' 0
  )

let inverse_binrel (#a #b:Type) (rel:a -> b -> prop) : b -> a -> prop = fun x y -> rel y x

#push-options "--fuel 1 --ifuel 1"
let eutt_symm (#e:Type -> Type) (#r #s:Type)
  (rel:r -> s -> prop) (x:itree e s) (y:itree e r) :
  Lemma
    (requires eutt rel y x)
    (ensures eutt (inverse_binrel rel) x y) =

  let pred (t, t') = eutt rel t' t in

  Paco.coinduction_pred (eutt_functor e (inverse_binrel rel)) pred (x, y) (fun (t, t') ->
    assert(pred (t, t'));
    Paco.unfold_gfp (eutt_functor e rel) (t', t);
    eutt_functor_elim e rel
      (eutt' rel) t' t (eutt_functor e (inverse_binrel rel) pred (t, t'))
      (fun n ->
        //itree_eutt_with_functor_intro e rel pred t t' m n
        match itree_destruct t, itree_destruct t' with
        | Tau cont, Tau cont' ->
          eutt_functor_intro e (inverse_binrel rel) pred t t' n
        | _, _ -> begin
          match burn n t, burn n t' with
          | Ret _, Ret _ ->
            eutt_functor_intro e (inverse_binrel rel) pred t t' n
          | Vis _ _ _, Vis _ _ _ ->
            eutt_functor_intro e (inverse_binrel rel) pred t t' n
        end
      )
  )
#pop-options

let compose_binrel (#a #b #c:Type) (r1:a -> b -> prop) (r2:b -> c -> prop) (x:a) (z:c) : prop =
  exists (y:b). r1 x y /\ r2 y z

let max (x y:nat) : nat = if x >= y then x else y

let eutt_trans_lemma0 (#e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) (t1:itree e a) (t2:itree e b) (n m:nat) 
  (aux:itree e a & itree e b -> prop) :
  Lemma
    (requires
      eutt_functor_at_depth e rel n aux (t1, t2) /\ m >= n
    ) (ensures 
      eutt_functor_at_depth e rel m aux (t1, t2)
    ) = match itree_destruct t1, itree_destruct t2 with
  | Tau t1, Tau t2 -> ()
  | _, _ -> burn_composition n m t1;
    burn_composition n m t2;
    eutt_functor_intro e rel aux t1 t2 m

let rec eutt_trans_lemma1 (#e:Type -> Type) (#a #b:Type) 
  (rel:a -> b -> prop) (t1:itree e a) (t2:itree e b) (n:nat) (out:prop) 
  (cont: (m:nat) -> Lemma
    (requires m >= n /\ eutt_functor_at_depth_without_tau_tau e rel m (eutt' rel) (t1, t2))
    (ensures out)
  )
  : Lemma
    (requires
      eutt rel t1 t2 
      /\ (~(Tau? (burn n t1)) \/ ~(Tau? (burn n t2)))
    ) (ensures out) (decreases n) =
    reveal_opaque (`%eutt_functor) (eutt_functor e rel);
    Paco.unfold_gfp (eutt_functor e rel) (t1, t2);
    match itree_destruct t1, itree_destruct t2 with
    | Tau t1, Tau t2 ->
      eutt_trans_lemma1 rel t1 t2 (n-1) out (fun m -> cont (m+1))
    | _, _ -> begin
      match burn n t1, burn n t2 with
      | Tau t1, Tau t2 -> assert(False)
      | Tau _, _ ->
        eliminate exists m. eutt_functor_at_depth e rel m (fun (t, t') -> eutt rel t t') (t1, t2)
        returns out
        with _. begin
          reveal_opaque (`%eutt_functor) (eutt_functor e rel);
          burn_composition m (max n m) t1;
          cont (max n m)
        end
      | _, Tau _ ->
        eliminate exists m. eutt_functor_at_depth e rel m (fun (t, t') -> eutt rel t t') (t1, t2)
        returns out
        with _. begin
          reveal_opaque (`%eutt_functor) (eutt_functor e rel);
          burn_composition m (max n m) t2;
          cont (max n m)
        end
      | _, _ -> 
        eliminate exists m. eutt_functor_at_depth e rel m (fun (t, t') -> eutt rel t t') (t1, t2)
        returns out
        with _ . begin
          reveal_opaque (`%eutt_functor) (eutt_functor e rel);
          burn_not_tau n m t1;
          burn_not_tau n m t2;
          cont n
        end
    end

let eutt_trans_lemma2 (#e:Type -> Type) (#a #b #c:Type) (rel1: a -> b -> prop) (rel2:b -> c -> prop)
  (t1:itree e a) (t2:itree e b) (t3:itree e c) (n m:nat) :
  Lemma
    (requires 
      ~(Tau? (itree_destruct t1) /\ Tau? (itree_destruct t3)) /\
      eutt_functor_at_depth_without_tau_tau e rel1 n (eutt' rel1) (t1, t2) /\
      eutt_functor_at_depth_without_tau_tau e rel2 m (eutt' rel2) (t2, t3)
    )
    (ensures
      eutt_functor e (compose_binrel rel1 rel2) (fun (t1, t3) -> exists t2. eutt rel1 t1 t2 /\ eutt rel2 t2 t3) (t1, t3)
    ) =
  let rel3 = compose_binrel rel1 rel2 in
  let p (t1, t3) : prop = exists t2. eutt #e rel1 t1 t2 /\ eutt #e rel2 t2 t3 in
  burn_composition n (max n m) t1;
  burn_composition n (max n m) t2;
  burn_composition m (max n m) t2;
  burn_composition m (max n m) t3;
  match burn (max n m) t1, burn (max n m) t2, burn (max n m) t3 with
  | Ret r1, Ret r2, Ret r3 ->
    assert(rel3 r1 r3);
    eutt_functor_intro e rel3 p t1 t3 (max n m)
  | Vis x1 ex1 cont1, Vis x2 ex2 cont2, Vis x3 ex3 cont3 ->
    eutt_functor_intro e rel3 p t1 t3 (max n m)


let rec eutt_trans_lemma3 (#e:Type -> Type) (#a #b #c: Type) (rel1:a -> b -> prop) (rel2:b -> c -> prop)
  (t1:itree e a) (t2:itree e b) (t3:itree e c) (n1 n2:nat) :
  Lemma
    (requires
      eutt_functor_at_depth e rel1 n1 (eutt' rel1) (t1, t2) /\
      eutt_functor_at_depth e rel2 n2 (eutt' rel2) (t2, t3)
    ) (ensures 
      eutt_functor e (compose_binrel rel1 rel2) (fun (t1, t3) -> exists t2. eutt rel1 t1 t2 /\ eutt rel2 t2 t3) (t1, t3)
    ) (decreases n1 + n2)
  = 
  let rel3 = compose_binrel rel1 rel2 in
  let p (t1, t3) : prop = exists t2. eutt #e rel1 t1 t2 /\ eutt #e rel2 t2 t3 in 
  Classical.move_requires_3 burn_not_tau n1 n2 t2;
  match itree_destruct t1, itree_destruct t2, itree_destruct t3 with
  | Tau _, Tau _, Tau _ -> eutt_functor_intro e rel3 p t1 t3 0
  | Tau t1', _, Tau t3' ->
    burn_composition 1 n1 t1;
    burn_composition 1 n2 t3;
    eutt_trans_lemma3 rel1 rel2 t1' t2 t3' (n1-1) (n2-1);
    eutt_functor_intro e rel1 (eutt' rel1) t1' t2 (n1-1);
    eutt_functor_intro e rel2 (eutt' rel2) t2 t3' (n2-1);
    Paco.fold_gfp (eutt_functor e rel1) (t1', t2);
    Paco.fold_gfp (eutt_functor e rel2) (t2, t3');
    eutt_functor_intro e rel3 p t1 t3 0
  | _, _, _ ->
    burn_composition n1 (max n1 n2) t2;
    burn_composition n2 (max n1 n2) t2;
    assert(~(Tau? (burn (max n1 n2) t2)));
    eutt_functor_intro e rel1 (eutt' rel1) t1 t2 n1;
    eutt_functor_intro e rel2 (eutt' rel2) t2 t3 n2;
    Paco.fold_gfp (eutt_functor e rel1) (t1, t2);
    Paco.fold_gfp (eutt_functor e rel2) (t2, t3);
    eutt_trans_lemma1 rel1 t1 t2 (max n1 n2) (eutt_functor e rel3 p (t1, t3)) (fun n ->
          eutt_trans_lemma1 rel2 t2 t3 (max n1 n2) (eutt_functor e rel3 p (t1, t3)) (fun m ->
            assert(~(Tau? (itree_destruct t1) /\ Tau? (itree_destruct t3)));
            eutt_trans_lemma2 rel1 rel2 t1 t2 t3 n m
          )
        )


let eutt_trans (#e:Type -> Type) (#a #b #c:Type) (rel1:a -> b -> prop) (rel2:b -> c -> prop)
  (t1:itree e a) (t2:itree e b) (t3:itree e c) :
  Lemma
    (requires eutt rel1 t1 t2 /\ eutt rel2 t2 t3)
    (ensures eutt (compose_binrel rel1 rel2) t1 t3)
  = 
  let rel3 = compose_binrel rel1 rel2 in
  let eutt1 (t, t') = eutt #e rel1 t t' in
  let eutt2 (t, t') = eutt #e rel2 t t' in
  let eutt3 (t, t') = eutt #e rel3 t t' in
  

  let pred (x:itree e a & itree e c) (y:itree e b) : prop =
    eutt rel1 x._1 y /\ eutt rel2 y x._2
  in

  Paco.coinduction_rel #_ #(fun _ -> itree e b) 
    (eutt_functor e rel3) pred (t1, t3) t2 (fun (t1, t3) t2 ->
    let p (t1, t3) : prop = exists t2. pred (t1, t3) t2 in
    assert(pred (t1, t3) t2);
    Paco.unfold_gfp (eutt_functor e rel1) (t1, t2);
    Paco.unfold_gfp (eutt_functor e rel2) (t2, t3);
    assert(eutt_functor e rel1 eutt1 (t1, t2));
    assert(eutt_functor e rel2 eutt2 (t2, t3));

    let lemma (n1 n2:nat) : Lemma
      (requires
        eutt_functor_at_depth e rel1 n1 eutt1 (t1, t2) /\
        eutt_functor_at_depth e rel2 n2 eutt2 (t2, t3)
      ) (ensures eutt_functor e rel3 p (t1, t3)) =
      eutt_trans_lemma3 rel1 rel2 t1 t2 t3 n1 n2
    in

    Classical.forall_intro_2 (Classical.move_requires_2 lemma);
    reveal_opaque (`%eutt_functor) (eutt_functor e rel1);
    reveal_opaque (`%eutt_functor) (eutt_functor e rel2);
      
    assert (eutt_functor e rel3 p (t1, t3))
    
  )

let eutt_monotone (#e:Type -> Type) (#r #s:Type) (rel rel':r -> s -> prop) (t:itree e r) (t':itree e s)
  : Lemma
    (requires eutt rel t t' /\ (forall x y. rel x y ==> rel' x y))
    (ensures eutt rel' t t') =
  let lemma (x:itree e r & itree e s) :
    Lemma
      (requires eutt' rel x)
      (ensures eutt_functor e rel' (eutt' rel) x) =
    let t, t' = x in
    Paco.unfold_gfp (eutt_functor e rel) x;
    eutt_functor_elim e rel (eutt' rel) t t'
      (eutt_functor e rel' (eutt' rel) x) (fun n ->
      eutt_functor_intro e rel' (eutt' rel) t t' n
    )
  in

  Paco.coinduction_pred (eutt_functor e rel') (eutt' rel) (t, t') lemma
