module ITree.Interp

open ITree.Basics
open ITree.Equiv
open ITree.Eutt
open ITree.MonadLaws
open ITree.StructuralLaws
open ITree.CongruenceLaws
open ITree.KTree
open ITree.Iteration
open OnDomain
module Classical = FStar.Classical
module Tac = FStar.Tactics


class monad_iter (m:Type -> Type) = {
  mpure: ((#a:Type) -> a -> m a);
  mbind: ((#a:Type) -> (#b:Type) -> m a -> (a -> m b) -> m b);
  miter: ((#a:Type) -> (#b:Type) -> (a -> m (sum a b)) -> a -> m b);
}

instance itree_monad_iter (#e:Type -> Type) : monad_iter (itree e) = {
  mpure = ret e;
  mbind = bind;
  miter = iter;
}

let general_interp_body_vis (#e #m:Type -> Type) {|_: monad_iter m|}
  (#r #s:Type) (k:ktree e s r) : s -> m (sum (itree e r) r) =
  fun a -> mpure (Left (k a))

let general_interp_body (#e #m:Type -> Type) {|_: monad_iter m|}
  (#r:Type) (handler: ((#a:Type) -> e a -> m a)) (t:itree e r) : m (sum (itree e r) r) =
  match itree_destruct t with
  | Ret r -> mpure (Right r)
  | Tau t -> mpure (Left t)
  | Vis _ e k ->
    mbind (handler e) (general_interp_body_vis (to_fun k))

let general_interp (#e #m:Type -> Type) {|_: monad_iter m|}
  (#r:Type) (handler: ((#a:Type) -> e a -> m a)) (t:itree e r) : m r =
  miter (general_interp_body handler) t

let interp_body_vis_cont (#e #f:Type -> Type) (#r #s:Type) (k:ktree e s r) : ktree f s (sum (itree e r) r) =
  // fun a -> ret _ (Left (k a))
  general_interp_body_vis #e #(itree f) #itree_monad_iter #r k

let interp_body (#e #f:Type -> Type) (#r:Type) (handler: ((#a:Type) -> e a -> itree f a)) (t:itree e r) :
  itree f (sum (itree e r) r) =
  (*match itree_destruct t with
  | Ret r -> ret _ (Right r)
  | Tau t -> ret _ (Left t)
  | Vis _ e k ->
    bind (handler e) (interp_body_vis_cont (to_fun k))*)
  general_interp_body #e #(itree f) #itree_monad_iter handler t

let interp (#e #f:Type -> Type) (#r:Type) (handler: ((#a:Type) -> e a -> itree f a)) (t:itree e r) : itree f r =
  //iter (interp_body handler) t
  general_interp #e #(itree f) #itree_monad_iter handler t

let interp_lemma (#e #f:Type -> Type) (#r:Type) (handler: ((#a:Type) -> e a -> itree f a)) (t:itree e r) :
  Lemma (interp handler t == iter (interp_body handler) t) =
  //iter_unfold (general_interp_body handler) t;
  assert(iter #f #(itree e r) #r == miter #(itree f));
  assert(forall x. general_interp_body #e #(itree f) #itree_monad_iter #r handler x == interp_body handler x);
  //iter_unfold (interp_body handler) t;
  Classical.forall_intro (iter_unfold (general_interp_body #e #(itree f) #itree_monad_iter #r handler));

  assert(forall x. general_interp handler x ==
    bind (general_interp_body #e #(itree f) #itree_monad_iter #r handler x) 
    (iter_continuation (general_interp_body handler))
  );

  Classical.forall_intro (fun x ->
  Classical.move_requires_3 bind_extensionality 
    (interp_body #e #f #r handler x)
    (iter_continuation (general_interp_body handler))
    (ktree_case (ktree_tau (general_interp handler)) (ktree_id _))
  );

  assert(forall x. interp handler x ==
    bind (interp_body #e #f #r handler x) 
    (ktree_case (ktree_tau (general_interp handler)) (ktree_id _))
  );

  iter_universal_prop (interp_body handler) (general_interp handler) t

let interp_ret (#e #f:Type -> Type) (#r:Type) (handler: ((#a:Type) -> e a -> itree f a)) (x:r) :
  Lemma (interp handler (ret e x) == ret f x) =
  interp_lemma handler (ret e x);
  iter_unfold (interp_body handler) (ret e x);
  monad_law2 (iter_continuation (interp_body #e #f #r handler)) (Right x)

let interp_tau (#e #f:Type -> Type) (#r:Type) (handler: ((#a:Type) -> e a -> itree f a)) (t:itree e r) :
  Lemma (interp handler (tau t) == tau (interp handler t)) =
  interp_lemma handler (tau t);
  interp_lemma handler t;
  iter_unfold (interp_body handler) t;
  iter_unfold (interp_body handler) (tau t);
  monad_law2 (iter_continuation (interp_body #e #f #r handler)) (Left t)

let rec decrease_depth_eq_approx (#e:Type -> Type) (#r:Type) (t t':itree e r) (n:nat) :
  Lemma 
    (requires Paco.gfp_approx (itree_eq_functor e r) (n+1) (t, t'))
    (ensures Paco.gfp_approx (itree_eq_functor e r) n (t, t'))
    (decreases n) =
  if n = 0 then () else
  match itree_destruct t, itree_destruct t' with
  | Ret _, Ret _ -> ()
  | Tau t, Tau t' ->
    decrease_depth_eq_approx t t' (n-1)
  | Vis _ x cont, Vis _ x' cont' ->
    let lemma x :
      Lemma (Paco.gfp_approx (itree_eq_functor e r) (n-1) (to_fun cont x, to_fun cont' x)) =
      decrease_depth_eq_approx (to_fun cont x) (to_fun cont' x) (n-1)
    in
    Classical.forall_intro lemma;
    ()

let rec bind_approx (#e:Type -> Type) (#r #s:Type) (t:itree e r) (k k':ktree e r s) (n:nat) :
  Lemma
    (requires forall x. Paco.gfp_approx (itree_eq_functor e s) n (k x, k' x))
    (ensures Paco.gfp_approx (itree_eq_functor e s) n (bind t k, bind t k')) 
    (decreases n) =
  if n = 0 then () else
  match itree_destruct t with
  | Ret r -> 
    monad_law2 k r;
    monad_law2 k' r
  | Tau t ->
    structural_law2 t k;
    structural_law2 t k';
    let lemma x :
      Lemma (Paco.gfp_approx (itree_eq_functor e s) (n-1) (k x, k' x)) =
      decrease_depth_eq_approx (k x) (k' x) (n-1)
    in

    Classical.forall_intro lemma;
    bind_approx t k k' (n-1)
  | Vis _ x cont ->
    structural_law3 x (to_fun cont) k;
    structural_law3 x (to_fun cont) k';
    let lemma1 x :
      Lemma (Paco.gfp_approx (itree_eq_functor e s) (n-1) (k x, k' x)) =
      decrease_depth_eq_approx (k x) (k' x) (n-1)
    in

    Classical.forall_intro lemma1;
    let lemma2 x :
      Lemma (Paco.gfp_approx (itree_eq_functor e s) (n-1) (bind (to_fun cont x) k, bind (to_fun cont x) k')) =
      bind_approx (to_fun cont x) k k' (n-1)
    in
    Classical.forall_intro lemma2
 

let interp_bind (#e #f:Type -> Type) (#r #s:Type) (handler: ((#a:Type) -> e a -> itree f a))
  (t:itree e r) (k:ktree e r s) : Lemma (
    interp handler (bind t k) ==
    bind (interp handler t) (fun x -> interp handler (k x))
  ) =
  let cont = fun x -> interp handler (k x) in
  let rel (x:itree f s & itree f s) (body: itree e r) : prop =
    x._1 == interp handler (bind body k) /\
    x._2 == bind (interp handler body) cont
  in

  let rec lemma (x:itree f s & itree f s) (body:itree e r) (n:nat) :
    Lemma 
      (requires rel x body)
      (ensures Paco.gfp_approx (itree_eq_functor f s) n x) 
      (decreases n) =
    if n = 0 then () else
    match itree_destruct body with
    | Ret r ->
      monad_law2 k r;
      interp_ret handler r;
      monad_law2 cont r;
      itree_eq_refl x._1;
      Paco.gfp_iff_gfp' (itree_eq_functor f s) x
    | Tau t ->
      structural_law2 t k;
      let Tau t1 = itree_destruct (bind body k) in
      interp_tau handler t1;
      let Tau t2 = itree_destruct x._1 in
      interp_tau handler t;
      let Tau t3 = itree_destruct (interp handler body) in
      structural_law2 t3 cont;
      let Tau t4 = itree_destruct x._2 in
      lemma (t2, t4) t (n-1)
    | Vis _ ev k' ->
      structural_law3 ev (to_fun k') k;
      let new_k = from_fun (fun x -> bind (to_fun k' x) k) in
      assert(itree_destruct (bind body k) == Vis _ ev new_k);
      iter_unfold (interp_body handler) (bind body k);
      interp_lemma handler (bind body k);
      assert(x._1 == bind
        (bind (handler ev) (interp_body_vis_cont (to_fun new_k)))
        (iter_continuation (interp_body handler))
      );
      monad_law3 (handler ev) 
        (interp_body_vis_cont (to_fun new_k))
        (iter_continuation (interp_body handler));
      let aux0 x :
        Lemma (
          bind 
            (interp_body_vis_cont (to_fun new_k) x) 
            (iter_continuation (interp_body handler)) == 
          tau (interp handler (bind (to_fun k' x) k))
        ) =
        interp_lemma handler (bind (to_fun k' x) k);
        monad_law2 
          (iter_continuation (interp_body handler))
          (Left (to_fun new_k x))
      in
      Classical.forall_intro aux0;
      bind_extensionality
        (handler ev)
        (fun x -> bind
          (interp_body_vis_cont (to_fun new_k) x)
          (iter_continuation (interp_body handler)))
        (fun x -> tau (interp handler (bind (to_fun k' x) k)));
      assert(x._1 == bind (handler ev) (fun x -> tau (interp handler (bind (to_fun k' x) k))));

      iter_unfold (interp_body handler) body;
      interp_lemma handler (bind body k);
      interp_lemma handler body;
      assert(x._2 ==
        bind (bind (interp_body handler body) (iter_continuation (interp_body handler))) cont
      );
      assert(interp_body handler body == bind (handler ev) (interp_body_vis_cont (to_fun k')));
      monad_law3 (handler ev) 
        (interp_body_vis_cont (to_fun k'))
        (iter_continuation (interp_body handler));

      let aux1 x :
        Lemma (
          bind 
            (interp_body_vis_cont (to_fun k') x)
            (iter_continuation (interp_body handler)) ==
          tau (interp handler (to_fun k' x))
        ) = 
        interp_lemma handler (to_fun k' x);
        monad_law2
          (iter_continuation (interp_body handler))
          (Left (to_fun k' x))
      in
      Classical.forall_intro aux1;
      bind_extensionality
        (handler ev)
        (fun x -> bind
          (interp_body_vis_cont (to_fun k') x)
          (iter_continuation (interp_body handler))
        )
        (fun x -> tau (interp handler (to_fun k' x)));

      assert(x._2 == 
        bind 
          (bind (handler ev) (fun t -> tau (interp handler (to_fun k' t))))
          cont
      );
      monad_law3 (handler ev) (fun t -> tau (interp handler (to_fun k' t))) cont;
      assert(
        x._2 == bind (handler ev) (fun t -> bind (tau (interp handler (to_fun k' t))) cont)
      );
      let aux2 t :
        Lemma (Paco.gfp_approx (itree_eq_functor f s) n (
          tau (interp handler (bind (to_fun k' t) k)),
          bind (tau (interp handler (to_fun k' t))) cont
        )) =
        structural_law2 (interp handler (to_fun k' t)) cont;
        lemma (
            interp handler (bind (to_fun k' t) k), 
            bind (interp handler (to_fun k' t)) cont
          ) (to_fun k' t) (n-1)
      in
      Classical.forall_intro aux2;
      bind_approx (handler ev) 
        (fun t -> tau (interp handler (bind (to_fun k' t) k))) 
        (fun t -> bind (tau (interp handler (to_fun k' t))) cont) n
  in

  Paco.coinduction_approx_rel (itree_eq_functor f s) rel
    (interp handler (bind t k), bind (interp handler t) cont)
    t lemma;
  itree_eq_thm (interp handler (bind t k)) (bind (interp handler t) cont)


let interp_iter (#e #f:Type -> Type) (#a #b:Type)
  (handler: ((#a:Type) -> e a -> itree f a)) (g: ktree e a (sum a b)) (x:a) : 
  Lemma (interp handler (iter g x) == iter (fun x -> interp handler (g x)) x) =
  let _ = iter_universal_prop #e #a #b in

  let lemma x :
    Lemma (interp handler (iter g x) == bind (interp handler (g x))
      (ktree_case (ktree_tau (fun x -> interp handler (iter g x))) (ktree_id f))
    ) =
    interp_lemma handler (iter g x);
    iter_unfold g x;
    interp_bind handler (g x) (ktree_case (ktree_tau (iter g)) (ktree_id e));
    assert(interp handler (iter g x) == 
      bind (interp handler (g x)) (fun x -> interp handler (ktree_case (ktree_tau (iter g)) (ktree_id e) x)));
    let aux x :
      Lemma (interp handler (ktree_case (ktree_tau (iter g)) (ktree_id e) x) ==
        ktree_case (ktree_tau (fun x -> interp handler (iter g x))) (ktree_id f) x
      ) = 
      match x with
      | Right r ->
        interp_ret handler r
      | Left l ->
        interp_tau handler (iter g l)
    in
    Classical.forall_intro aux;
    bind_extensionality
      (interp handler (g x))
      (fun x -> interp handler (ktree_case (ktree_tau (iter g)) (ktree_id e) x))
      (ktree_case (ktree_tau (fun x -> interp handler (iter g x))) (ktree_id f))
  in
  Classical.forall_intro lemma;
  iter_universal_prop (fun x -> interp handler (g x)) (fun x -> interp handler (iter g x)) x
