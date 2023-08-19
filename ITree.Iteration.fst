module ITree.Iteration

open ITree.Basics
open ITree.Eutt
open ITree.Equiv
open ITree.MonadLaws
open ITree.StructuralLaws
open ITree.CongruenceLaws
open Paco
open ITree.KTree
module T = FStar.Tactics

// the definition of iter in the paper is a cofixed point of the form
// let iter body x = 
//   bind (body x) (fun x -> itree_construct (match x with
//     | Left x  -> Tau (iter body x)
//     | Right y -> Ret y
//   ))
// it's not possible to encode it directly as corec arguments, so I
// "unfold" the bind operator
let iter_automaton (#e:Type -> Type) (#a #b:Type) (body:ktree e a (sum a b)) 
  (state:itree e (sum a b)) :
  itree_repr e b (itree e (sum a b)) =
  match itree_destruct state with
  | Vis x ex cont -> Vis x ex cont
  | Ret (Left l)  -> Tau (body l)
  | Ret (Right r) -> Ret r
  | Tau t -> Tau t

[@@"opaque_to_smt"]
let iter (#e:Type -> Type) (#a #b:Type) (body:ktree e a (sum a b)) : ktree e a b =
  fun x -> itree_corec (iter_automaton body) (body x)


let iter_continuation (#e:Type -> Type) (#a #b:Type) (body:ktree e a (sum a b)) : ktree e (sum a b) b =
  ktree_case (ktree_tau (iter body)) (ktree_id e)


open OnDomain
let iter_unfold_lemma (#e:Type -> Type) (#a #b:Type) (body:ktree e a (sum a b)) (state:itree e (sum a b)) :
  Lemma (itree_corec (iter_automaton body) state == bind state (iter_continuation body)) =
  reveal_opaque (`%iter) (iter #e #a #b);
  reveal_opaque (`%bind) (bind #e #(sum a b) #b);
  let iter_with state = itree_corec (iter_automaton body) state in
  let bind_with state = bind state (iter_continuation body) in

  let pred (x:itree e b & itree e b) (state:itree e (sum a b)) : prop =
    x._1 == iter_with state /\
    x._2 == bind_with state
  in

  let rec lemma (x:itree e b & itree e b) (state:itree e (sum a b)) (n:nat) :
    Lemma
      (requires pred x state)
      (ensures Paco.gfp_approx (itree_eq_functor e b) n x) 
      (decreases n) =
    if n = 0 then () else
    match itree_destruct state with
    | Vis x ex cont ->
      let Vis x1 ex1 cont1 = itree_destruct (iter_with state) in
      let Vis x2 ex2 cont2 = itree_destruct (bind_with state) in
      let aux x :
        Lemma (Paco.gfp_approx (itree_eq_functor e b) (n-1) (to_fun cont1 x, to_fun cont2 x)) =
        lemma (to_fun cont1 x, to_fun cont2 x) (to_fun cont x) (n-1)
      in Classical.forall_intro aux
    | Ret (Left  l) ->
      monad_law2 (iter_continuation body) (Left l); 
      itree_eq_refl x._1;
      Paco.gfp_iff_gfp' (itree_eq_functor e b) x
    | Ret (Right r) ->
      monad_law2 (iter_continuation body) (Right r);
      itree_eq_refl x._1;
      Paco.gfp_iff_gfp' (itree_eq_functor e b) x
    | Tau st ->
      lemma (iter_with st, bind_with st) st (n-1)
  in

  Paco.coinduction_approx_rel (itree_eq_functor e b) pred 
    (itree_corec (iter_automaton body) state, bind state (iter_continuation body)) state lemma;
  itree_eq_thm (itree_corec (iter_automaton body) state) (bind state (iter_continuation body))


let iter_unfold (#e:Type -> Type) (#a #b:Type) (body:ktree e a (sum a b)) (x:a) :
  Lemma (iter body x == bind (body x) (iter_continuation body)) =
  reveal_opaque (`%iter) (iter #e #a #b);
  iter_unfold_lemma body (body x)

let iter_fixed_point (#e:Type -> Type) (#a #b:Type) (body:ktree e a (sum a b)) :
  Lemma (keq (iter body) (ktree_cat body (ktree_case (iter body) (ktree_id e)))) =
  reveal_opaque (`%iter) (iter #e #a #b);
  let lemma1 (x:sum a b) :
    Lemma (eutt (fun x y -> x == y) (iter_continuation body x) (ktree_case (iter body) (ktree_id e) x)) =
    match x with
    | Left  l -> 
      eutt_refl (fun x y -> x == y) (iter body l);
      eutt_tau_l (fun x y -> x == y) (iter body l) (iter body l)
    | Right r -> eutt_refl (fun x y -> x == y) (iter_continuation body x)
  in

  Classical.forall_intro lemma1;

  let lemma2 (x:a) :
    Lemma (eutt (fun x y -> x == y) (iter body x) (bind (body x) (ktree_case (iter body) (ktree_id e)))) =
    iter_unfold body x;
    eutt_refl (fun x y -> x == y) (body x);
    congruence_law_3 (fun x y -> x == y) (fun x y -> x == y) (body x) (body x) 
      (iter_continuation body) (ktree_case (iter body) (ktree_id e))
  in

  Classical.forall_intro lemma2

let ktree_bimap (#e:Type -> Type) (#a #b #c #d:Type) (f:ktree e a c) (g:ktree e b d) :
  ktree e (sum a b) (sum c d) =
  ktree_case (ktree_cat f (ktree_inl e)) (ktree_cat g (ktree_inr e))

let iter_parameter_lemma0 (#e:Type -> Type) (#a #b #c:Type) (f:ktree e a (sum a b)) (g:ktree e b c) (r:b) :
  Lemma
    (
      bind (itree_corec (iter_automaton f) (ret e (Right r))) g ==
      itree_corec (iter_automaton (ktree_cat f (ktree_bimap (ktree_id e) g)))
        (bind (ret e (Right r)) (ktree_bimap (ktree_id e) g))
    ) =
  reveal_opaque (`%iter) (iter #e #a #b);
  reveal_opaque (`%iter) (iter #e #a #c);
  reveal_opaque (`%iter) (iter #e #b #c);
  let body = ret e (Right r) in
  let x = bind (itree_corec (iter_automaton f) (ret e (Right r))) g in
  let y = itree_corec (iter_automaton (ktree_cat f (ktree_bimap (ktree_id e) g)))
    (bind (ret e (Right r)) (ktree_bimap (ktree_id e) g))
  in
  
  monad_law2 g r;
  monad_law2 (ktree_bimap (ktree_id e) g) (Right #a #b r);
  assert(bind body (ktree_bimap (ktree_id e) g) == bind (g r) (ktree_inr e));
  iter_unfold_lemma (ktree_cat f (ktree_bimap (ktree_id e ) g)) (bind (g r) (ktree_inr e));
  let cont = iter_continuation (ktree_cat f (ktree_bimap (ktree_id e) g)) in
  assert(y == bind (bind (g r) (ktree_inr e)) cont);
  monad_law3 (g r) (ktree_inr e) cont;
  assert(y == bind (g r) (fun x -> 
    bind (ktree_inr e x) cont
  ));
  let aux x :
    Lemma (bind (ktree_inr e x) cont == ret e x) =
    assert(ktree_inr e x == ret e (Right #a #c x));
    monad_law2 cont (Right #a #c x)
  in
  Classical.forall_intro aux;
  bind_extensionality (g r) (fun x -> bind (ktree_inr e x) cont) (ret e);
  assert(y == bind (g r) (ret e));
  monad_law1 (g r);
  assert(itree_destruct (itree_corec (iter_automaton f) body) == Ret r);
  assert(itree_corec (iter_automaton f) body == ret e r);
  assert(bind (itree_corec (iter_automaton f) body) g == g r);
  assert(x == y)

#push-options "--query_stats --split_queries"
let iter_parameter (#e:Type -> Type) (#a #b #c:Type) (f:ktree e a (sum a b)) (g:ktree e b c) :
  Lemma
    (keq (ktree_cat (iter f) g) (iter (ktree_cat f (ktree_bimap (ktree_id e) g)))) =
  reveal_opaque (`%iter) (iter #e #a #b);
  reveal_opaque (`%iter) (iter #e #a #c);
  //reveal_opaque (`%bind) (bind #e #(sum a b) #b);
  //reveal_opaque (`%bind) (bind #e #(sum a c) #c);
  reveal_opaque (`%bind) (bind #e #b #c);
  reveal_opaque (`%bind) (bind #e #(sum a b) #(sum a c));
  //reveal_opaque (`%bind) (bind #e #a #c);
  
  
  let pointwise (x:a) :
    Lemma (eutt (fun x y -> x == y) (bind (iter f x) g) (iter (ktree_cat f (ktree_bimap (ktree_id e) g)) x)) =

    let pred (x:itree e c & itree e c) (body:itree e (sum a b)) : prop =
      x._1 == bind (itree_corec (iter_automaton f) body) g /\
      x._2 == itree_corec (iter_automaton (ktree_cat f (ktree_bimap (ktree_id e) g))) 
        (bind body (ktree_bimap (ktree_id e) g))
    in

    let rec lemma (x:itree e c & itree e c) (body:itree e (sum a b)) (n:nat) :
      Lemma
        (requires pred x body)
        (ensures Paco.gfp_approx (itree_eq_functor e c) n x)
        (decreases n) =
      if n = 0 then () else
      match itree_destruct body with
      | Tau t ->
        let Tau a = itree_destruct x._1 in
        let Tau b = itree_destruct x._2 in
        lemma (a, b) t (n-1)
      | Vis a ea cont ->
        let Vis a1 ea1 cont1 = itree_destruct x._1 in
        let Vis a2 ea2 cont2 = itree_destruct x._2 in
        let aux x :
          Lemma (Paco.gfp_approx (itree_eq_functor e c) (n-1) (to_fun cont1 x, to_fun cont2 x)) =
          lemma (to_fun cont1 x, to_fun cont2 x) (to_fun cont x) (n-1)
        in Classical.forall_intro aux
      | Ret (Left t) ->
        monad_law2 (ktree_id e) t;
        monad_law2 (ktree_inl e #a #c) t;
        monad_law2 (ktree_bimap (ktree_id e) g) (Left #a #b t);
        assert(ktree_bimap (ktree_id e) g (Left t) == ret e (Left t));
        assert(bind body (ktree_bimap (ktree_id e) g) == ret e (Left t));
        let Tau a = itree_destruct x._1 in
        let Tau b = itree_destruct x._2 in
        lemma (a, b) (f t) (n-1)
      | Ret (Right r) ->
        iter_parameter_lemma0 f g r;
        assert(x._1 == x._2);
        itree_eq_refl x._1;
        Paco.gfp_iff_gfp' (itree_eq_functor e c) x
    in

    Paco.coinduction_approx_rel (itree_eq_functor e c) pred
      (bind (iter f x) g, iter (ktree_cat f (ktree_bimap (ktree_id e) g)) x)
      (f x)
      lemma;

    itree_eq_thm (bind (iter f x) g) (iter (ktree_cat f (ktree_bimap (ktree_id e) g)) x);

    eutt_refl (fun x y -> x == y) (bind (iter f x) g)
  in

  Classical.forall_intro pointwise
#pop-options

let burn_spin_lemma (#e:Type -> Type) (#r:Type) (t:itree e r) :
  Lemma (ensures (exists n. ~(Tau? (burn n t))) \/ t == spin e r) =
  let aux (_:unit) :
    Lemma 
      (requires forall n. Tau? (burn n t))
      (ensures t == spin e r) =
    let pred (x, y) : prop = (forall n. Tau? (burn n x)) /\ y == spin e r in

    let rec lemma pair (n:nat) :
      Lemma
        (requires pred pair)
        (ensures Paco.gfp_approx (itree_eq_functor e r) n pair)
        (decreases n) =
      if n = 0 then () else
      match itree_destruct pair._1 with
      | Tau t' -> 
        assert(forall n. burn n t' == burn (n+1) pair._1);
        assert(forall n. ~(Tau? (burn n t')) ==> ~(Tau? (burn (n+1) pair._1)));
        lemma (t', spin e r) (n-1)
    in
    Paco.coinduction_approx_pred (itree_eq_functor e r) pred (t, spin e r) lemma;
    itree_eq_thm t (spin e r)
  in
  Classical.move_requires aux ()


let iter_universal_prop (#e:Type -> Type) (#a #b:Type) (f:ktree e a (sum a b)) (g:ktree e a b) (x:a) :
  Lemma
    (requires forall x. g x == bind (f x) (ktree_case (ktree_tau g) (ktree_id e)))
    (ensures g x == iter f x) =
  reveal_opaque (`%iter) (iter #e #a #b);
  reveal_opaque (`%bind) (bind #e #(sum a b) #b);
    
  let pred (x:itree e b & itree e b) (body:itree e (sum a b)) : prop =
    x._1 == bind body (ktree_case (ktree_tau g) (ktree_id e)) /\
    x._2 == bind body (ktree_case (ktree_tau (iter f)) (ktree_id e))
  in

  let rec lemma (x:itree e b & itree e b) (body:itree e (sum a b)) (n:nat) :
    Lemma
      (requires pred x body)
      (ensures Paco.gfp_approx (itree_eq_functor e b) n x)
      (decreases n) =
    if n = 0 then () else
    let t1, t2 = x in
    match itree_destruct body with
    | Tau body ->
      let Tau t1 = itree_destruct t1 in
      let Tau t2 = itree_destruct t2 in
      lemma (t1, t2) body (n-1)
    | Vis x ex cont ->
      let Vis _ _ cont1 = itree_destruct t1 in
      let Vis _ _ cont2 = itree_destruct t2 in
      let aux x :
        Lemma (Paco.gfp_approx (itree_eq_functor e b) (n-1) (to_fun cont1 x, to_fun cont2 x)) =
        lemma (to_fun cont1 x, to_fun cont2 x) (to_fun cont x) (n-1)
      in Classical.forall_intro aux
    | Ret (Right r) ->
      monad_law2 (ktree_case (ktree_tau g) (ktree_id e)) (Right r);
      monad_law2 (ktree_case (ktree_tau (iter f)) (ktree_id e)) (Right r);
      assert(t1 == t2);
      itree_eq_refl t1;
      Paco.gfp_iff_gfp' (itree_eq_functor e b) (t1, t2)
    | Ret (Left l) ->
      monad_law2 (ktree_case (ktree_tau g) (ktree_id e)) (Left l);
      monad_law2 (ktree_case (ktree_tau (iter f)) (ktree_id e)) (Left l);
      assert(t1 == tau (g l));
      assert(t2 == tau (iter f l));
      iter_unfold f l;
      if n = 1 then () else lemma (g l, iter f l) (f l) (n-1)
  in

  let t1 = bind (f x) (ktree_case (ktree_tau g) (ktree_id e)) in
  let t2 = bind (f x) (ktree_case (ktree_tau (iter f)) (ktree_id e)) in

  iter_unfold f x;
  Paco.coinduction_approx_rel (itree_eq_functor e b) pred
    (t1, t2) (f x) lemma;
  itree_eq_thm t1 t2

let iter_composition_lemma0 (#e:Type -> Type) (#a #b #c:Type) (f:ktree e a (sum b c)) (g:ktree e b (sum a c)) (x:a)
  : Lemma
    (
      ktree_cat f (iter_continuation (ktree_cat g (ktree_case (ktree_tau f) (ktree_inr e)))) x ==
      ktree_cat (ktree_cat f (ktree_case (ktree_tau g) (ktree_inr e)))
      (ktree_case
        (ktree_tau (ktree_cat f (iter_continuation (ktree_cat g (ktree_case (ktree_tau f) (ktree_inr e))))))
        (ktree_id e)
      ) x
    ) =
  let f' = ktree_tau f in
  let g' = ktree_tau g in
  let f1 = ktree_cat f (ktree_case g' (ktree_inr e)) in
  let f2 = ktree_cat g (ktree_case f' (ktree_inr e)) in
  let f1' = ktree_cat f' (ktree_case g' (ktree_inr e)) in
  let f2' = ktree_cat g' (ktree_case f' (ktree_inr e)) in
  Classical.forall_intro (fun x -> structural_law2 (f x) (ktree_case g' (ktree_inr e)));
  Classical.forall_intro (fun x -> structural_law2 (g x) (ktree_case f' (ktree_inr e)));
  assert(forall x. iter_continuation f2 x == 
    ktree_case (ktree_tau (iter f2)) (ktree_id e) x
  );

  Classical.forall_intro (iter_unfold f2);
  Classical.forall_intro (fun x -> structural_law2 (f2 x) (iter_continuation f2));
  assert(forall x. iter_continuation f2 x == 
    ktree_case (ktree_cat f2' (iter_continuation f2)) (ktree_id e) x
  );
  bind_extensionality (f x)
    (iter_continuation f2)
    (ktree_case (ktree_cat f2' (iter_continuation f2)) (ktree_id e));

  assert(
    ktree_cat f (ktree_case (ktree_cat f2' (iter_continuation f2)) (ktree_id e)) x ==
    ktree_cat f (iter_continuation f2) x
  );
  
  // f2' = ktree_cat g' (ktree_case f' (ktree_inr e))
  Classical.forall_intro (fun x -> 
    monad_law3 (g' x) (ktree_case f' (ktree_inr e)) (iter_continuation f2)
  );
  Classical.forall_intro (fun x ->
    Classical.move_requires_3 bind_extensionality (g' x)
      (fun x -> bind (ktree_case f' (ktree_inr e) x) (iter_continuation f2))
      (ktree_cat (ktree_case f' (ktree_inr e)) (iter_continuation f2))
  );
  bind_extensionality (f x)
    (ktree_case (ktree_cat f2' (iter_continuation f2)) (ktree_id e))
    (ktree_case (ktree_cat g' (ktree_cat (ktree_case f' (ktree_inr e)) (iter_continuation f2))) (ktree_id e));
  monad_law3 (f x) (ktree_case g' (ktree_inr e)) (ktree_case (ktree_cat f' (iter_continuation f2)) (ktree_id e));
  bind_extensionality (f x)
    (fun x -> bind (ktree_case g' (ktree_inr e) x) (ktree_case (ktree_cat f' (iter_continuation f2)) (ktree_id e)))
    (ktree_cat (ktree_case g' (ktree_inr e)) (ktree_case (ktree_cat f' (iter_continuation f2)) (ktree_id e)));

  let t1_internal = ktree_case (ktree_cat f' (iter_continuation f2)) (ktree_id e) in
  let t2_internal = ktree_cat (ktree_case f' (ktree_inr e)) (iter_continuation f2) in
  let t1 = ktree_cat (ktree_case g' (ktree_inr e)) t1_internal in
  let t2 = ktree_case (ktree_cat g' t2_internal) (ktree_id e) in

  let lemma0 x :
    Lemma (t1_internal x == t2_internal x) =
    match x with
    | Left l ->
      ()
    | Right r ->
      monad_law2 (iter_continuation f2) (Right r)
  in

  let lemma1 x :
    Lemma (
      t1 x == t2 x
    ) =
    match x with
    | Left l ->
      Classical.forall_intro lemma0;
      bind_extensionality (g' l) t1_internal t2_internal
    | Right r ->
      monad_law2 (ktree_case (ktree_cat f' (iter_continuation f2)) (ktree_id e)) (Right r)
  in
  Classical.forall_intro lemma1;

  bind_extensionality (f x)
    (ktree_cat (ktree_case g' (ktree_inr e)) (ktree_case (ktree_cat f' (iter_continuation f2)) (ktree_id e)))
    (ktree_case (ktree_cat g' (ktree_cat (ktree_case f' (ktree_inr e)) (iter_continuation f2))) (ktree_id e));

  Classical.forall_intro (fun x -> structural_law2 (f x) (iter_continuation f2));
  assert(ktree_cat f (iter_continuation f2) x ==
    bind (f1 x) (ktree_case (ktree_cat f' (iter_continuation f2)) (ktree_id e))
  );
  
  bind_extensionality (f1 x)
    (ktree_case (ktree_cat f' (iter_continuation f2)) (ktree_id e))
    (ktree_case (ktree_tau (ktree_cat f (iter_continuation f2))) (ktree_id e))
  


let iter_composition_lemma1 (#e:Type -> Type) (#a #b #c:Type) (f:ktree e a (sum b c)) (g:ktree e b (sum a c)) :
  Lemma
    (
      iter (ktree_cat f (ktree_case (ktree_tau g) (ktree_inr e))) `keq`
      ktree_cat f (iter_continuation (ktree_cat g (ktree_case (ktree_tau f) (ktree_inr e))))
    ) =
  let f' = ktree_tau f in
  let g' = ktree_tau g in
  let f1 = ktree_cat f (ktree_case g' (ktree_inr e)) in
  let f2 = ktree_cat g (ktree_case f' (ktree_inr e)) in
  let f1' = ktree_cat f' (ktree_case g' (ktree_inr e)) in
  let f2' = ktree_cat g' (ktree_case f' (ktree_inr e)) in
  Classical.forall_intro (fun x -> structural_law2 (f x) (ktree_case g' (ktree_inr e)));
  Classical.forall_intro (fun x -> structural_law2 (g x) (ktree_case f' (ktree_inr e)));
  
  let pointwise (x:a) :
    Lemma (
      eutt (fun x y -> x == y)
        (iter f1 x)
        (ktree_cat f (iter_continuation f2) x)
    ) =
    Classical.forall_intro (iter_composition_lemma0 f g);
    iter_universal_prop f1 (ktree_cat f (iter_continuation f2)) x;
    eutt_refl (fun x y -> x == y) (iter f1 x)
  in
  Classical.forall_intro pointwise

let keq_elim (#e:Type -> Type) (#a #b:Type) (f g:ktree e a b) (x:a) :
  Lemma
    (requires f `keq` g)
    (ensures eutt (fun x y -> x == y) (f x) (g x)) = ()


let rec burn_spin_eval (e:Type -> Type) (r:Type) (n:nat) :
  Lemma (ensures burn n (spin e r) == (itree_destruct (spin e r))) (decreases n) =
  if n = 0 then () else
  burn_spin_eval e r (n-1)

let rec gfp_decreasing (#a:Type) (f:Paco.monotone_functor a{Paco.commute_with_lb f}) (n:nat) (x:a) :
  Lemma (requires Paco.gfp_approx f (n+1) x)
    (ensures Paco.gfp_approx f n x) (decreases n) =
  if n = 0 then () else begin
    Classical.forall_intro (Classical.move_requires (gfp_decreasing f (n-1)));
    Paco.monotone_elim f (Paco.gfp_approx f n) (Paco.gfp_approx f (n-1)) x
  end

let rec add_tau_left_approx (#e:Type -> Type) (#a:Type) (t t':itree e a) (n:nat) :
  Lemma
    (requires Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) n (t, t'))
    (ensures Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) n (tau t, t')) 
    (decreases n) =
  if n = 0 then () else
  let out_prop = Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) n (tau t, t') in
  let functor = Paco.gfp_approx (eutt_functor e (fun (x y:a) -> x == y)) (n-1) in
  match itree_destruct t, itree_destruct t' with
  | Tau t, Tau t' ->
    eutt_functor_elim e (fun x y -> x == y) functor
      (tau t) (tau t') out_prop (fun _ ->
      add_tau_left_approx t t' (n-1);
      eutt_functor_intro e (fun x y -> x == y)
        functor (tau (tau t)) (tau t') 0
    )
  | _, Tau t' ->
    eutt_functor_elim e (fun x y -> x == y)
      functor t (tau t') out_prop (fun k ->
      eutt_functor_intro e (fun x y -> x == y)
        functor t t' (k-1);
      gfp_decreasing (eutt_functor e (fun x y -> x == y)) (n-1) (t, t');
      eutt_functor_intro e (fun x y -> x == y)
        functor (tau t) (tau t') 0
    )
  | _, _ ->
    eutt_functor_elim e (fun x y -> x == y) functor t t'
      (Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) n (tau t, t')) (fun k ->
        eutt_functor_intro e (fun x y -> x == y) functor (tau t) t' (k+1)
      )

let rec add_tau_right_approx (#e:Type -> Type) (#a:Type) (t t':itree e a) (n:nat) :
  Lemma
    (requires Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) n (t, t'))
    (ensures Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) n (t, tau t')) 
    (decreases n) =
  if n = 0 then () else
  let out_prop = Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) n (t, tau t') in
  let functor = Paco.gfp_approx (eutt_functor e (fun (x y:a) -> x == y)) (n-1) in
  match itree_destruct t, itree_destruct t' with
  | Tau t, Tau t' ->
    eutt_functor_elim e (fun x y -> x == y) functor
      (tau t) (tau t') out_prop (fun _ ->
      add_tau_right_approx t t' (n-1);
      eutt_functor_intro e (fun x y -> x == y)
        functor (tau t) (tau (tau t')) 0
    )
  | Tau t, _ ->
    eutt_functor_elim e (fun x y -> x == y)
      functor (tau t) t' out_prop (fun k ->
      eutt_functor_intro e (fun x y -> x == y)
        functor t t' (k-1);
      gfp_decreasing (eutt_functor e (fun x y -> x == y)) (n-1) (t, t');
      eutt_functor_intro e (fun x y -> x == y)
        functor (tau t) (tau t') 0
    )
  | _, _ ->
    eutt_functor_elim e (fun x y -> x == y) functor t t'
      (Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) n (t, tau t')) (fun k ->
        eutt_functor_intro e (fun x y -> x == y) functor t (tau t') (k+1)
      )


let rec iter_congr_lemma (#e:Type -> Type) (#a #b:Type) (f g: ktree e a (sum a b))
  (body1 body2: itree e (sum a b)) (k n:nat) :
  Lemma
    (requires
      f `keq` g /\
      eutt_functor_at_depth e (fun x y -> x == y) k (eutt' (fun x y -> x == y)) (body1, body2)
    )
    (ensures
      Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) n 
        (bind body1 (iter_continuation f), bind body2 (iter_continuation g))
    )
    (decreases %[n; k]) =
  reveal_opaque (`%bind) (bind #e #(sum a b) #b);
  let out1 = bind body1 (iter_continuation f) in
  let out2 = bind body2 (iter_continuation g) in

  let out_prop = Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) n (out1, out2)
  in
  
  if n = 0 then () else
  match itree_destruct body1, itree_destruct body2 with
  | Tau t1, Tau t2 ->
    Paco.unfold_gfp (eutt_functor e (fun x y -> x == y)) (t1, t2);
    eutt_functor_elim e (fun x y -> x == y) (eutt' (fun x y -> x == y))
      t1 t2 out_prop (fun k -> 
        iter_congr_lemma f g t1 t2 k (n-1);
        eutt_functor_intro e (fun x y -> x == y) 
          (Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) (n-1)) 
          out1 out2 0
      )
  | Tau t1, _ ->
    iter_congr_lemma f g t1 body2 (k-1) n;
    structural_law2 t1 (iter_continuation f);
    add_tau_left_approx (bind t1 (iter_continuation f)) out2 n
  | _, Tau t2 ->
    iter_congr_lemma f g body1 t2 (k-1) n;
    structural_law2 t2 (iter_continuation g);
    add_tau_right_approx out1 (bind t2 (iter_continuation g)) n
  | Ret (Left l), Ret (Left _) ->
    monad_law2 (iter_continuation f) (Left l);
    monad_law2 (iter_continuation g) (Left l);
    iter_unfold f l;
    iter_unfold g l;
    keq_elim f g l;
    Paco.unfold_gfp (eutt_functor e (fun x y -> x == y)) (f l, g l);
    eutt_functor_elim e (fun x y -> x == y) (eutt' (fun x y -> x == y)) (f l) (g l) out_prop (fun k ->
      iter_congr_lemma f g (f l) (g l) k (n-1);
      eutt_functor_intro e (fun x y -> x == y) 
        (Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) (n-1)) 
        out1 out2 0
    )

  | Ret (Right r), Ret (Right _) ->
    monad_law2 (iter_continuation f) (Right r);
    monad_law2 (iter_continuation g) (Right r);
    assert(out1 == out2);
    eutt_refl (fun x y -> x == y) out1;
    Paco.gfp_iff_gfp' (eutt_functor e (fun x y -> x == y)) (out1, out2)
  | Vis x1 ex1 cont1, Vis _ _ cont2 ->
    let Vis _ _ ocont1 = itree_destruct out1 in
    let Vis _ _ ocont2 = itree_destruct out2 in
    let aux x :
      Lemma (Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) (n-1) (to_fun ocont1 x, to_fun ocont2 x)) =
      Paco.unfold_gfp (eutt_functor e (fun x y -> x == y)) (to_fun cont1 x, to_fun cont2 x);

      eutt_functor_elim e (fun x y -> x == y) (eutt' (fun x y -> x == y))
        (to_fun cont1 x) (to_fun cont2 x)
        (Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) (n-1) (to_fun ocont1 x, to_fun ocont2 x))
        (fun k -> iter_congr_lemma f g (to_fun cont1 x) (to_fun cont2 x) k (n-1))
    in Classical.forall_intro aux;
    eutt_functor_intro e (fun x y -> x == y)
      (Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) (n-1))
      out1 out2 0


let iter_congr (#e:Type -> Type) (#a #b:Type) (f g:ktree e a (sum a b)) :
  Lemma
    (requires f `keq` g)
    (ensures iter f `keq` iter g) =
  let pointwise (x:a) :
    Lemma
      (eutt (fun x y -> x == y) (bind (f x) (iter_continuation f)) (bind (g x) (iter_continuation g))) =

    let pred (x:itree e b & itree e b) (body: itree e (sum a b) & itree e (sum a b)) : prop =
      x._1 == bind body._1 (iter_continuation f) /\
      x._2 == bind body._2 (iter_continuation g) /\
      eutt' (fun x y -> x == y) body
    in

    let rec lemma (x:itree e b & itree e b) (body: itree e (sum a b) & itree e (sum a b)) (n:nat) :
      Lemma
        (requires pred x body)
        (ensures Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) n x) (decreases n) =
      if n = 0 then () else let t, t' = x in
      Paco.unfold_gfp (eutt_functor e (fun x y -> x == y)) body;
      eutt_functor_elim e (fun  x y -> x == y) (eutt' (fun x y -> x == y)) body._1 body._2
        (Paco.gfp_approx (eutt_functor e (fun x y -> x == y)) n x)
        (fun k ->
          iter_congr_lemma f g body._1 body._2 k n
        )
    in

    keq_elim f g x;
    Paco.coinduction_approx_rel (eutt_functor e (fun x y -> x == y))
      pred (bind (f x) (iter_continuation f), bind (g x) (iter_continuation g)) (f x, g x) lemma

  in Classical.forall_intro pointwise;
  Classical.forall_intro (iter_unfold f);
  Classical.forall_intro (iter_unfold g);
  keq_refl (iter g); keq_refl (iter f);

  keq_trans (iter f) (ktree_cat f (iter_continuation f)) (ktree_cat g (iter_continuation g));
  keq_trans (iter f) (ktree_cat g (iter_continuation g)) (iter g)

let iter_composition_lemma2 (#e:Type -> Type) (#a #b #c:Type) (f:ktree e a (sum b c)) (g g':ktree e b (sum a c)) h :
  Lemma 
  (requires g `keq` g')
  (ensures
    iter (ktree_cat f (ktree_case g h)) `keq` 
    iter (ktree_cat f (ktree_case g' h))
  ) =
  keq_inl_case g h;
  keq_trans
    (ktree_cat (ktree_inl e) (ktree_case g h))
    g g';

  keq_inr_case g h;

  keutt_from_keq (fun x y -> x == y) (ktree_cat (ktree_inl e) (ktree_case g h)) g';
  keutt_from_keq (fun x y -> x == y) (ktree_cat (ktree_inr e) (ktree_case g h)) h;
  keutt_case_congr (fun x y -> x == y) (ktree_case g h) g' h;

  assert(keutt (fun x y -> x == y) (ktree_case g h) (ktree_case g' h));
  assert(ktree_case g h `keq` ktree_case g' h) by (T.assumption ());
  

  keq_refl f;
  keq_congr f f (ktree_case g h) (ktree_case g' h);
  iter_congr 
    (ktree_cat f (ktree_case g h))
    (ktree_cat f (ktree_case g' h))

let iter_composition (#e:Type -> Type) (#a #b #c:Type) (f:ktree e a (sum b c)) (g:ktree e b (sum a c)) :
  Lemma (
    iter (ktree_cat f (ktree_case g (ktree_inr e))) `keq`
    ktree_cat f (ktree_case (iter (ktree_cat g (ktree_case f (ktree_inr e)))) (ktree_id e))
  ) =
  let f' = ktree_tau f in
  let g' = ktree_tau g in
  iter_composition_lemma1 f g;
  assert(
    iter (ktree_cat f (ktree_case g' (ktree_inr e))) `keq`
    ktree_cat f (ktree_case (ktree_tau (iter (ktree_cat g (ktree_case f' (ktree_inr e))))) (ktree_id e))
  );

  keq_tau g;
  keq_tau f;
  iter_composition_lemma2 f g g' (ktree_inr e);

  iter_composition_lemma2 g f' f (ktree_inr e);

  let f1 = iter (ktree_cat g (ktree_case f' (ktree_inr e))) in
  let f2 = iter (ktree_cat g (ktree_case f (ktree_inr e))) in
  let f1' = ktree_tau f1 in
  
  keq_tau f1;
  keq_trans f1' f1 f2;

  keq_inl_case f1' (ktree_id e);
  keq_inr_case f1' (ktree_id e);

  keq_trans (ktree_cat (ktree_inl e) (ktree_case f1' (ktree_id e))) f1' f2;
  keutt_case_congr (fun x y -> x == y) (ktree_case f1' (ktree_id e)) f2 (ktree_id e);
  
  keq_refl f;
  keq_congr f f (ktree_case f1' (ktree_id e)) (ktree_case f2 (ktree_id e));
  
  keq_trans 
    (iter (ktree_cat f (ktree_case g (ktree_inr e))))
    (iter (ktree_cat f (ktree_case g' (ktree_inr e))))
    (ktree_cat f (ktree_case (ktree_tau (iter (ktree_cat g (ktree_case f' (ktree_inr e))))) (ktree_id e)));

  keq_trans 
    (iter (ktree_cat f (ktree_case g (ktree_inr e))))
    (ktree_cat f (ktree_case (ktree_tau (iter (ktree_cat g (ktree_case f' (ktree_inr e))))) (ktree_id e)))
    (ktree_cat f (ktree_case (iter (ktree_cat g (ktree_case f (ktree_inr e)))) (ktree_id e)))


