module ITree.Iteration.Codiagonal

open ITree.Iteration

open ITree.Basics
open ITree.Eutt
open ITree.Equiv
open ITree.MonadLaws
open ITree.StructuralLaws
open ITree.CongruenceLaws
open Paco
open ITree.KTree


let iter_codiagonal_lemma0 (#e:Type -> Type) (#a #b:Type)
  (f:ktree e a (sum a (sum a b))) (x:a) :
  Lemma 
    (requires
      iter (iter f) x ==
      bind 
        (iter f x) 
        (ktree_case (ktree_tau (iter (iter f))) (ktree_id e))
    )
    (ensures
      iter (iter f) x ==
      bind
        (bind (f x) (ktree_case (ktree_tau (iter f)) (ktree_id e)))
        (ktree_case (ktree_tau (iter (iter f))) (ktree_id e))
    ) =
  iter_unfold f x

let iter_codiagonal_lemma1 (#e:Type -> Type) (#a #b:Type)
  (f:ktree e a (sum a (sum a b))) (x:a) :
  Lemma 
    (requires
      iter (iter f) x ==
        bind
          (bind (f x) (ktree_case (ktree_tau (iter f)) (ktree_id e)))
          (ktree_case (ktree_tau (iter (iter f))) (ktree_id e))
    )
    (ensures
      iter (iter f) x ==
        bind (f x)
          (ktree_cat 
            (ktree_case (ktree_tau (iter f)) (ktree_id e))
            (ktree_case (ktree_tau (iter (iter f))) (ktree_id e))
          )
    ) =
  monad_law3 (f x) 
    (ktree_case (ktree_tau (iter f)) (ktree_id e))
    (ktree_case (ktree_tau (iter (iter f))) (ktree_id e));
  bind_extensionality (f x)
    (ktree_cat
      (ktree_case (ktree_tau (iter f)) (ktree_id e))
      (ktree_case (ktree_tau (iter (iter f))) (ktree_id e))
    )
    (fun x -> bind
      (ktree_case (ktree_tau (iter f)) (ktree_id e) x)
      (ktree_case (ktree_tau (iter (iter f))) (ktree_id e))
    )

(*
let iter_codiagonal_lemma1 (#e:Type -> Type) (#a #b:Type)
  (f:ktree e a (sum a (sum a b))) (x:a) :
  Lemma
    (
      iter (iter f) x ==
      bind (bind (f x) (ktree_case (ktree_inl e) (ktree_id e)))
        (ktree_case (ktree_tau (iter (iter f))) (ktree_id e))
    ) =
  (* iter_unfold (iter f) x;
  assert(iter (iter f) x == bind (iter f x) (ktree_case (ktree_tau (iter (iter f))) (ktree_id e))); *)
  let aux0 (_:unit) :
    Lemma (iter (iter f) x == bind (iter f x) (ktree_case (ktree_tau (iter (iter f))) (ktree_id e))) =
    iter_unfold (iter f) x
  in aux0 ();

  let aux1 (_:unit) :
    Lemma (iter (iter f) x ==
      bind (bind (f x) (ktree_case (ktree_tau (iter f)) (ktree_id e)))
        (ktree_case (ktree_tau (iter (iter f))) (ktree_id e))) =
      //iter f x == bind (f x) (ktree_case (ktree_tau (iter f)) (ktree_id e))) =

    iter_unfold f x
    //monad_law3 (f x) 
    //  (ktree_case (ktree_tau (iter f)) (ktree_id e))
    //  (ktree_case (ktree_tau (iter (iter f))) (ktree_id e));
  in aux1 ();


  //iter_unfold f x;
  
  
  //assert(iter (iter f) x ==
  //  bind (bind (f x) (ktree_case (ktree_tau (iter f)) (ktree_id e)))
  //    (ktree_case (ktree_tau (iter (iter f))) (ktree_id e))
  //);
  
  admit()
*)
