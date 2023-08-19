module ITree.MonadLaws

open ITree.Basics
open ITree.Equiv
open OnDomain


let bind_right_thm (#e:Type -> Type) (#s #r:Type) (t:itree e s) (k:r -> itree e s) : 
  Lemma (itree_corec (bind_automaton k) (Right t) == t) 
  (* [SMTPat (itree_corec (bind_automaton k) (Right t))] *)
  = let p (x:itree e s & itree e s) : prop =
    x._2 == itree_corec (bind_automaton k) (Right x._1)
  in
  Paco.coinduction_pred (itree_eq_functor e s) p
    (t, itree_corec (bind_automaton k) (Right t)) (fun x -> ());
  itree_eq_thm t (itree_corec (bind_automaton k) (Right t))


let monad_law1 (#e:Type->Type) (#r:Type) (t:itree e r) :
  Lemma
    (t == (bind t (ret e)))
    (*[SMTPat (bind t (ret e))]*)
  = reveal_opaque (`%bind) (bind #e #r #r);
  let p (x:itree e r & itree e r) : prop =
    x._2 == bind x._1 (ret e)
  in
  Paco.coinduction_pred (itree_eq_functor e r) p (t, bind t (ret e)) (fun x -> ());
  itree_eq_thm t (bind t (ret e))

let monad_law2 (#e:Type->Type) (#r #s:Type) (k:r -> itree e s) (v:r) :
  Lemma
    (k v == (bind (ret e v) k))
    (*[SMTPat (bind (ret e v) k)]*)
  = reveal_opaque (`%bind) (bind #e #r #s);
  assert(
    itree_destruct (bind (ret e v) k) ==
    itree_destruct (itree_corec (bind_automaton k) (Right (k v)))
  );
  Classical.forall_intro (fun t -> bind_right_thm t k);
  itree_bisim (fun x y -> itree_destruct x == itree_destruct y)
    (bind (ret e v) k) (k v)

let bind_extensionality (#e:Type -> Type) (#r #s:Type)
  (t:itree e r) (k k':r -> itree e s) :
  Lemma
    (requires forall x. k x == k' x)
    (ensures bind t k == bind t k') =
  reveal_opaque (`%bind) (bind #e #r #s);
  let rec approx 
    (x:itree e s & itree e s) (t:itree e r) (n:nat) :
    Lemma
      (requires x._1 == bind t k /\ x._2 == bind t k' /\ (forall x. k x == k' x))
      (ensures Paco.gfp_approx (itree_eq_functor e s) n x)
      (decreases n) =
    if n = 0 then () else
    let it, it' = x in
    match itree_destruct t, itree_destruct it, itree_destruct it' with
    | Tau t, Tau it, Tau it' ->
      approx (it, it') t (n-1)
    | Vis x ex cont, Vis x' ex' cont', Vis x'' ex'' cont'' ->
      let lemma x :
        Lemma (Paco.gfp_approx (itree_eq_functor e s) (n-1) (to_fun cont' x, to_fun cont'' x))
        = approx (to_fun cont' x, to_fun cont'' x) (to_fun cont x) (n-1)
      in Classical.forall_intro lemma
    | Ret v, _, _ ->
      monad_law2 k v;
      monad_law2 k' v;
      assert(k v == k' v);
      itree_eq_refl (bind t k);
      Paco.gfp_iff_gfp' (itree_eq_functor e s) (bind t k, bind t k')
  in
  Paco.coinduction_approx_rel (itree_eq_functor e s)
    (fun (it, it') t -> it == bind t k /\ it' == bind t k')
    (bind t k, bind t k') t approx;
  itree_eq_thm (bind t k) (bind t k')


#push-options "--z3rlimit 50"
let monad_law3 (#e:Type -> Type) (#a #b #c:Type) (s:itree e a) (t:a -> itree e b) (u:b -> itree e c) :
  Lemma (bind (bind s t) u == bind s (fun x -> bind (t x) u))
  = let r
    (x:itree e c & itree e c) 
    (s:itree e a) : prop =
    x._1 == bind (bind s t) u /\
    x._2 == bind s (fun x -> bind (t x) u)
  in
  reveal_opaque (`%bind) (bind #e #a #b);
  reveal_opaque (`%bind) (bind #e #b #c);
  reveal_opaque (`%bind) (bind #e #a #c);

  let rec lemma 
    (x:itree e c & itree e c) 
    (s:itree e a) (n:nat) :
    Lemma
      (requires
        x._1 == bind (bind s t) u /\
        x._2 == bind s (fun x -> bind (t x) u)
      ) (ensures Paco.gfp_approx (itree_eq_functor e c) n x)
      (decreases n)
    = if n = 0 then () else let it, it' = x in
    match itree_destruct s with
    | Tau s -> begin
      let Tau it = itree_destruct it in
      let Tau it' = itree_destruct it' in
      lemma (it, it') s (n-1)
    end
    | Vis x ex cont_s ->
      let Vis _ _ cont_it = itree_destruct it in
      let Vis _ _ cont_it' = itree_destruct it' in
      let aux x :
        Lemma
          (Paco.gfp_approx (itree_eq_functor e c) (n-1) (to_fun cont_it x, to_fun cont_it' x)) =
        lemma (to_fun cont_it x, to_fun cont_it' x) (to_fun cont_s x) (n-1)
      in Classical.forall_intro aux
    | Ret r ->
      monad_law2 (fun x -> bind (t x) u) r;
      monad_law2 t r;
      itree_eq_refl (bind (t r) u);
      Classical.forall_intro (Paco.gfp_iff_gfp' (itree_eq_functor e c))
  in

  assert(r (bind (bind s t) u, bind s (fun x -> bind (t x) u)) s);

  Paco.coinduction_approx_rel (itree_eq_functor e c) r (bind (bind s t) u, bind s (fun x -> bind (t x) u)) s
    lemma;
  itree_eq_thm (bind (bind s t) u) (bind s (fun x -> bind (t x) u))
#pop-options
