(* 
definition of Interactive Tree using coinductive datatypes (no index) 
and paco-like propositions, and some properties about itree
*)


module ITree

module Classical = FStar.Classical
open Equiv

module T = FStar.Tactics
open OnDomain


open PFunctor
open PFUtils

module Paco = CoindProofApprox

let comp (#a #b #c:Type) (f:b -> c) (g:a -> b) : a -> c = fun x -> f (g x)

unopteq type itree_repr (e:Type -> Type) (r:Type) (aux:Type) =
| Vis : (x:Type) -> e x -> (onDomain x aux) -> itree_repr e r aux
| Tau of aux
| Ret of r

let itree_repr_equality (#e:Type -> Type) (#r:Type) (#t:Type)
  (r1 r2:itree_repr e r t) : Lemma
    (requires (match r1, r2 with
    | Vis x1 ex1 cont1, Vis x2 ex2 cont2 -> 
      x1 == x2 /\ ex1 == ex2 /\ deq cont1 cont2
    | Tau cont1, Tau cont2 -> cont1 == cont2
    | Ret r1, Ret r2 -> r1 == r2
    | _, _ -> False))
    (ensures r1 == r2)
  = ()


let itree_map (e:Type -> Type) (r:Type) (#a #b:Type)
  (f:a -> b) (it_f:itree_repr e r a) : itree_repr e r b =
  match it_f with
  | Vis x ex cont -> Vis x ex (from_fun (
    comp f (to_fun cont)
  ))
  | Tau cont -> Tau (f cont)
  | Ret r -> Ret r

let itree_functor (e:Type -> Type) (r:Type) : functor = {
  f = itree_repr e r;
  fmap = itree_map e r
}

unopteq type itree_command (e:Type -> Type) (r:Type) =
| VisC : (x:Type) -> e x -> itree_command e r
| RetC of r
| TauC

let itree_response (#e:Type -> Type) (#r:Type) (c:itree_command e r) =
  match c with
  | VisC x ex -> x
  | RetC res -> empty
  | TauC -> unit

let itree_pfunctor (e:Type -> Type) (r:Type) : pfunctor =
  {
    command = itree_command e r;
    response = itree_response;
  }

let itree_hom (e:Type -> Type) (r:Type) (#aux:Type) :
  pf_apply (itree_pfunctor e r) aux -> itree_repr e r aux = fun pa ->
  match pa.node with
  | VisC x ex ->
    Vis x ex pa.children
  | RetC r -> Ret r
  | TauC -> Tau (to_fun pa.children ())

let itree_inv (e:Type -> Type) (r:Type) (#aux:Type) :
  itree_repr e r aux -> pf_apply (itree_pfunctor e r) aux = fun f ->
  match f with
  | Vis x ex cont ->
    {node=VisC x ex; children=cont}
  | Ret r ->
    {node=RetC r; children=from_fun (fun e -> match e with)}
  | Tau cont ->
    {node=TauC; children=from_fun (fun _ -> cont)}

let itree_iso (e:Type -> Type) (r:Type) : interface_iso (itree_functor e r) = {
  pf = itree_pfunctor e r;
  hom = (fun #t pa -> 
    let res: (itree_functor e r).f t = itree_hom e r pa in res);
  inv = itree_inv e r;
  inv_hom = (fun #t -> assert(forall x. deq x.children (itree_inv e r #t (itree_hom e r x)).children));
  hom_inv = (fun #t -> ());
  hom_map = (fun #a #b g p -> 
    itree_repr_equality (itree_hom e r (map _ g p)) (itree_map e r g (itree_hom e r p)))

}

let itree (e:Type -> Type) (r:Type) = m_iso_type (itree_iso e r)

let itree_destruct (#e:Type -> Type) (#r:Type) (m:itree e r) :
  itree_repr e r (itree e r) = m_iso_destruct m

let itree_construct (#e:Type -> Type) (#r:Type) (m:itree_repr e r (itree e r)) :
  itree e r = let m: (itree_functor e r).f (itree e r) = m in
  m_iso_construct m

let itree_cons_dest (#e:Type -> Type) (#r:Type) (m:itree e r) :
  Lemma
    (itree_construct (itree_destruct m) == m)
    [SMTPat (itree_construct (itree_destruct m))]
  = ()

let itree_dest_cons (#e:Type -> Type) (#r:Type) (m:itree_repr e r (itree e r)) :
  Lemma
    (itree_destruct (itree_construct m) == m)
    [SMTPat (itree_destruct (itree_construct m))]
  = ()

let itree_equiv_aux' (e:Type -> Type) (a b:Type) (rel:a -> b -> prop) :
  (itree e a & itree e b -> prop) -> itree e a & itree e b -> prop =
  fun aux (t, t') -> match itree_destruct t, itree_destruct t' with
  | Vis x1 ex1 cont1, Vis x2 ex2 cont2 ->
    x1 == x2 /\ ex1 == ex2 /\ (
      forall arg. aux (to_fun cont1 arg, to_fun cont2 arg)
    )
  | Ret r1, Ret r2 -> rel r1 r2
  | Tau t, Tau t' -> aux (t, t')
  | _, _ -> False

let itree_equiv_aux_monotone (e:Type -> Type) (a b:Type) (rel:a -> b -> prop) :
  Lemma (Paco.monotone (itree_equiv_aux' e a b rel))
  = Paco.prove_monotone (itree_equiv_aux' e a b rel) (
    fun r1 r2 (t, t') -> ()
  )

let itree_equiv_aux_scott_continuous (e:Type -> Type) (a b:Type) (rel:a -> b -> prop) :
  Lemma (Paco.scott_continuous (itree_equiv_aux' e a b rel)) =
  Paco.prove_scott_continuous (itree_equiv_aux' e a b rel) (
    fun p x -> assert(itree_equiv_aux' e a b rel (p 0) x)
  )

let itree_equiv_aux (e:Type -> Type) (a b:Type) (rel:a -> b -> prop) :
  Paco.monotone_fun (itree e a & itree e b) =
  itree_equiv_aux_scott_continuous e a b rel;
  itree_equiv_aux_monotone e a b rel;
  itree_equiv_aux' e a b rel

let itree_eq_aux (e:Type -> Type) (r:Type) =
  itree_equiv_aux e r r (fun x y -> x == y)

// strong bisimulation relation
let itree_equiv (#e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) (t:itree e a) (t':itree e b) =
  Paco.gfp (itree_equiv_aux e a b rel) (t, t')

let itree_eq (#e:Type -> Type) (#r:Type) (t t':itree e r) =
  Paco.gfp (itree_eq_aux e r) (t, t')

let itree_eq_refl (#e:Type -> Type) (#r:Type) (t:itree e r) :
  Lemma (ensures itree_eq t t) [SMTPat (itree_eq t t)] =
  let rec approx (x:itree e r & itree e r) (n:nat) :
    Lemma
      (requires x._1 == x._2)
      (ensures Paco.gfp_approx (itree_eq_aux e r) n x)
      (decreases n) =
    if n = 0 then () else
      match itree_destruct x._1 with
      | Ret _ -> ()
      | Tau t -> approx (t, t) (n-1)
      | Vis x ex cont ->
        let lemma x :
          Lemma (Paco.gfp_approx (itree_eq_aux e r) (n-1) (to_fun cont x, to_fun cont x))
          = approx (to_fun cont x, to_fun cont x) (n-1) in
        Classical.forall_intro lemma
  in
  Paco.prove_using_pred (itree_eq_aux e r)
    (fun (t, t') -> t == t') (t, t) approx


let itree_bisim (#e:Type -> Type) (#r:Type) (rel:itree e r -> itree e r -> prop) (t t':itree e r) :
  Lemma
    (requires rel t t' /\ (
      forall t t'. rel t t' ==> itree_eq_aux e r (fun (t, t') -> rel t t') (t, t')
    ))
    (ensures t == t')
  = m_iso_bisim rel t t'

// proof of strong bisimulation theorem
let itree_eq_thm (#e:Type -> Type) (#r:Type) (t t':itree e r) :
  Lemma (requires itree_eq t t') (ensures t == t') =
  Classical.forall_intro (
    Classical.move_requires_2 Paco.unfold_gfp (itree_eq_aux e r));
  m_bisim itree_eq t t'

let itree_corec (#e:Type -> Type) (#r:Type) (#state:Type)
  (f:state -> itree_repr e r state) (x:state) : itree e r =
  m_iso_corec (itree_iso e r) f x

let itree_dest_corec (#e:Type -> Type) (#r:Type) (#state:Type)
  (f:state -> itree_repr e r state) (x:state) :
  Lemma
    (ensures itree_destruct (itree_corec f x) == itree_map e r (itree_corec f) (f x))
    [SMTPat (itree_destruct (itree_corec f x))]
  = m_iso_dest_corec #_ #(itree_iso e r) f x;
  assert(itree_destruct (itree_corec f x) == itree_map e r (itree_corec f) (f x)) by
    T.assumption ()

// definition of equivalence up to tau
let itree_eutt_aux' (e:Type -> Type) (a b:Type) (rel:a -> b -> prop) :
  (itree e a & itree e b -> prop) -> itree e a & itree e b -> prop =
  fun aux (t, t') -> match itree_destruct t, itree_destruct t' with
  | Ret r1, Ret r2 ->
    rel r1 r2
  | Vis x1 ex1 cont1, Vis x2 ex2 cont2 ->
    x1 == x2 /\ ex1 == ex2 /\ (
      forall arg. aux (to_fun cont1 arg, to_fun cont2 arg)
    )
  | Tau t, Tau t' ->
    aux (t, t')
  | Tau t, _ ->
    aux (t, t')
  | _, Tau t' ->
    aux (t, t')
  | _, _ -> False

let itree_eutt_aux_monotone (e:Type -> Type) (a b:Type) (rel:a -> b -> prop) :
  Lemma (ensures Paco.monotone (itree_eutt_aux' e a b rel)) = 
  Paco.prove_monotone (itree_eutt_aux' e a b rel) (fun r1 r2 x -> ())

let itree_eutt_aux_scott_continuous (e:Type -> Type) (a b:Type) (rel:a -> b -> prop) :
  Lemma (ensures Paco.scott_continuous (itree_eutt_aux' e a b rel)) =
  Paco.prove_scott_continuous (itree_eutt_aux' e a b rel)
    (fun p x -> assert(itree_eutt_aux' e a b rel (p 0) x))

let itree_eutt_with_aux (e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) :
  Paco.monotone_fun (itree e a & itree e b) =
  itree_eutt_aux_scott_continuous e a b rel;
  itree_eutt_aux_monotone e a b rel;
  itree_eutt_aux' e a b rel

let itree_eutt_with (#e:Type -> Type) (#a #b:Type) (rel:a -> b -> prop) (t:itree e a) (t':itree e b) : prop =
  Paco.gfp (itree_eutt_with_aux e rel) (t, t')

let itree_eutt_aux (e:Type -> Type) (r:Type) =
  itree_eutt_with_aux e (fun x y -> x == y)

let itree_eutt (#e:Type -> Type) (#r:Type) (t t':itree e r) : prop =
  Paco.gfp (itree_eutt_aux e r) (t, t')

let ret (e:Type -> Type) (#r:Type) (x:r) : itree e r = 
  itree_construct #e (Ret x)

let tau (#e:Type -> Type) (#r:Type) (cont:itree e r) : itree e r =
  itree_construct (Tau cont)

let vis (#e:Type -> Type) (#r #a:Type) (x:e a) (cont:a -> itree e r) : itree e r =
  itree_construct (Vis a x (from_fun cont))

let spin (e:Type -> Type) (r:Type) : itree e r =
  itree_corec (fun _ -> Tau ()) ()

// definition of trigger
let trigger (#e:Type -> Type) (#a:Type) (ea:e a) : itree e a =
  itree_construct (Vis a ea (from_fun (ret e))) 

let bind_add_right #e #r #s (t:itree e s) : 
  itree_repr e s (sum (itree e r) (itree e s)) =
  itree_map e s Right (itree_destruct t)

let bind_automaton (#e:Type -> Type) (#r #s:Type) (k:r -> itree e s)
  (state:sum (itree e r) (itree e s)) : itree_repr e s (sum (itree e r) (itree e s)) =
  match state with
  | Right out -> bind_add_right out
  | Left t -> begin
    match itree_destruct t with
    | Ret r -> bind_add_right (k r)
    | Tau cont -> Tau (Left cont)
    | Vis x ex cont ->
      Vis x ex (from_fun (comp Left (to_fun cont)))
      //Vis x ex (from_fun (fun x -> Left (to_fun cont x)))
  end

// definition of bind operator
let bind (#e:Type -> Type) (#r #s:Type) (t:itree e r) (k:r -> itree e s) : itree e s =
  itree_corec (bind_automaton k) (Left t)

let bind_right_thm (#e:Type -> Type) (#s #r:Type) (t:itree e s) (k:r -> itree e s) : 
  Lemma (itree_corec (bind_automaton k) (Right t) == t) 
  [SMTPat (itree_corec (bind_automaton k) (Right t))]
  =
  let rec approx (x:itree e s & itree e s) (n:nat) :
    Lemma
      (requires x._2 == itree_corec (bind_automaton k) (Right x._1))
      (ensures Paco.gfp_approx (itree_eq_aux e s) n x) 
      (decreases n) =
    let t, t' = x in
    
    if n = 0 then () else 
    match itree_destruct t, itree_destruct t' with
    | Ret r, Ret r' -> ()
    | Tau t, Tau t' -> approx (t, t') (n-1)
    | Vis x ex cont, Vis x' ex' cont' ->
      let lemma x : 
        Lemma (Paco.gfp_approx (itree_eq_aux e s) (n-1) (to_fun cont x, to_fun cont' x)) =
        approx (to_fun cont x, to_fun cont' x) (n-1)
      in
      Classical.forall_intro lemma
  in
  Paco.prove_using_pred (itree_eq_aux e s)
    (fun (t, t') -> t' == itree_corec (bind_automaton k) (Right t))
    (t, itree_corec (bind_automaton k) (Right t)) approx;
  itree_eq_thm t (itree_corec (bind_automaton k) (Right t))


let monad_low_1 (#e:Type->Type) (#r:Type) (t:itree e r) :
  Lemma
    (t == (bind t (ret e)))
    [SMTPat (bind t (ret e))]
  = let rec construct_approx (x:itree e r & itree e r) (n:nat) :
    Lemma (requires x._2 == bind x._1 (ret e))
      (ensures Paco.gfp_approx (itree_eq_aux e r) n x)
      (decreases n)
    = if n = 0 then () else begin
      let (t, t') = x in
      match itree_destruct t, itree_destruct t' with
      | Ret r, Ret r' -> assert(r == r')
      | Tau c, Tau c' -> construct_approx (c, c') (n-1)
      | Vis a ea cont, Vis a' ea' cont' ->
        assert(forall x. to_fun cont' x == bind (to_fun cont x) (ret e));
        let lemma x : 
          Lemma (Paco.gfp_approx (itree_eq_aux e r) (n-1) (to_fun cont x, to_fun cont' x)) =
          construct_approx (to_fun cont x, to_fun cont' x) (n-1)
        in
        Classical.forall_intro lemma
    end
  in
  
  Paco.prove_using_pred (itree_eq_aux e r)
    (fun (t, t') -> 
      t' == bind t (ret e)
    ) (t, bind t (ret e))
    construct_approx;
  itree_eq_thm t (bind t (ret e))

let monad_low_2 (#e:Type->Type) (#r #s:Type) (k:r -> itree e s) (v:r) :
  Lemma
    (k v == (bind (ret e v) k))
    [SMTPat (bind (ret e v) k)]
  = assert(
    itree_destruct (bind (ret e v) k) ==
    itree_destruct (itree_corec (bind_automaton k) (Right (k v)))
  );
  itree_bisim (fun x y -> itree_destruct x == itree_destruct y)
    (bind (ret e v) k) (k v)

let bind_extensionality (#e:Type -> Type) (#r #s:Type)
  (t:itree e r) (k k':r -> itree e s) :
  Lemma
    (requires forall x. k x == k' x)
    (ensures bind t k == bind t k') =
  let rec approx 
    (x:itree e s & itree e s) (t:itree e r) (n:nat) :
    Lemma
      (requires x._1 == bind t k /\ x._2 == bind t k' /\ (forall x. k x == k' x))
      (ensures Paco.gfp_approx (itree_eq_aux e s) n x)
      (decreases n) =
    if n = 0 then () else
    let it, it' = x in
    match itree_destruct t, itree_destruct it, itree_destruct it' with
    | Tau t, Tau it, Tau it' ->
      approx (it, it') t (n-1)
    | Vis x ex cont, Vis x' ex' cont', Vis x'' ex'' cont'' ->
      let lemma x :
        Lemma (Paco.gfp_approx (itree_eq_aux e s) (n-1) (to_fun cont' x, to_fun cont'' x))
        = approx (to_fun cont' x, to_fun cont'' x) (to_fun cont x) (n-1)
      in Classical.forall_intro lemma
    | Ret v, _, _ ->
      monad_low_2 k v;
      monad_low_2 k' v;
      itree_eq_refl (bind t k)
  in
  Paco.prove_using_rel (itree_eq_aux e s)
    (fun (it, it') t -> it == bind t k /\ it' == bind t k')
    (bind t k, bind t k') t approx;
  itree_eq_thm (bind t k) (bind t k')


#push-options "--z3rlimit 50"
let monad_low_3 (#e:Type -> Type) (#a #b #c:Type) (s:itree e a) (t:a -> itree e b) (u:b -> itree e c) :
  Lemma (bind (bind s t) u == bind s (fun x -> bind (t x) u))
  = let r
    (x:itree e c & itree e c) 
    (s:itree e a) : prop =
    x._1 == bind (bind s t) u /\
    x._2 == bind s (fun x -> bind (t x) u)
  in

  let rec lemma 
    (x:itree e c & itree e c) 
    (s:itree e a) (n:nat) :
    Lemma
      (requires
        x._1 == bind (bind s t) u /\
        x._2 == bind s (fun x -> bind (t x) u)
      ) (ensures Paco.gfp_approx (itree_eq_aux e c) n x)
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
          (Paco.gfp_approx (itree_eq_aux e c) (n-1) (to_fun cont_it x, to_fun cont_it' x)) =
        lemma (to_fun cont_it x, to_fun cont_it' x) (to_fun cont_s x) (n-1)
      in Classical.forall_intro aux
    | Ret r ->
      monad_low_2 (fun x -> bind (t x) u) r;
      monad_low_2 t r;
      itree_eq_refl (bind (t r) u)
  in

  assert(r (bind (bind s t) u, bind s (fun x -> bind (t x) u)) s);

  Paco.prove_using_rel (itree_eq_aux e c) r (bind (bind s t) u, bind s (fun x -> bind (t x) u)) s
    lemma;
  itree_eq_thm (bind (bind s t) u) (bind s (fun x -> bind (t x) u))
#pop-options

let itree_eutt_with_refl (#e:Type -> Type) (#r:Type) 
  (rel:r -> r -> prop) (x:itree e r) : Lemma
    (requires reflexivity rel)
    (ensures itree_eutt_with rel x x)
  = let pred (x:itree e r & itree e r) : prop =
    x._1 == x._2
  in

  let rec lemma (x:itree e r & itree e r) (n:nat) :
    Lemma
      (requires pred x)
      (ensures Paco.gfp_approx (itree_eutt_with_aux e rel) n x)
      (decreases n) =
    if n = 0 then () else
    let t, _ = x in
    match itree_destruct t with
    | Ret r -> ()
    | Tau t -> lemma (t, t) (n-1)
    | Vis x ex cont ->
      let aux x :
        Lemma (Paco.gfp_approx (itree_eutt_with_aux e rel) (n-1) (to_fun cont x, to_fun cont x))
        = lemma (to_fun cont x, to_fun cont x) (n-1)
      in Classical.forall_intro aux
  in
  Paco.prove_using_pred (itree_eutt_with_aux e rel) pred (x, x) lemma

let itree_eutt_with_symm (#e:Type -> Type) (#r:Type)
  (rel:r -> r -> prop) (x y:itree e r) :
  Lemma
    (requires itree_eutt_with rel y x /\ symmetry rel)
    (ensures itree_eutt_with rel x y) =
  let pred (x:itree e r & itree e r) : prop =
    itree_eutt_with rel x._2 x._1
  in

  let rec lemma (x:itree e r & itree e r) (n:nat) :
    Lemma
      (requires pred x)
      (ensures Paco.gfp_approx (itree_eutt_with_aux e rel) n x) 
      (decreases n) =
    if n = 0 then () else let t, t' = x in
    Paco.unfold_gfp (itree_eutt_with_aux e rel) (t', t);
    match itree_destruct t, itree_destruct t' with
    | Vis x ex cont, Vis x' ex' cont' ->
      let aux x :
        Lemma (Paco.gfp_approx (itree_eutt_with_aux e rel) (n-1) (to_fun cont x, to_fun cont' x))
        = lemma (to_fun cont x, to_fun cont' x) (n-1)
      in Classical.forall_intro aux
    | Ret r1, Ret r2 -> ()
    | Tau t, Tau t' -> lemma (t, t') (n-1)
    | Tau t, _ ->
      lemma (t, t') (n-1)
    | _, Tau t' ->
      lemma (t, t') (n-1)
  in

  Paco.prove_using_pred (itree_eutt_with_aux e rel) pred (x, y) lemma

let itree_eutt_with_trans (#e:Type -> Type) (#r:Type) (rel:r -> r -> prop)
  (a b c:itree e r) :
  Lemma
    (requires itree_eutt_with rel a b /\ itree_eutt_with rel b c /\ transitivity rel)
    (ensures itree_eutt_with rel a c)
  = let pred (x:itree e r & itree e r) (y:itree e r) : prop =
    itree_eutt_with rel x._1 y /\ itree_eutt_with rel y x._2
  in

  let rec lemma (x:itree e r & itree e r) (y:itree e r) (n:nat) :
    Lemma
      (requires pred x y)
      (ensures Paco.gfp_approx (itree_eutt_with_aux e rel) n x)
      (decreases n)
    = if n = 0 then () else let x, z = x in
    Paco.unfold_gfp (itree_eutt_with_aux e rel) (x, y);
    Paco.unfold_gfp (itree_eutt_with_aux e rel) (y, z);
    match itree_destruct x, itree_destruct y, itree_destruct z with
    | Ret r1, Ret r2, Ret r3 -> ()
    | Tau x, Tau y, Tau z ->
      lemma (x, z) y (n-1)
    | Tau x, _, Tau z ->
      lemma (x, z) y (n-1)
    | _, _, _ -> admit()
  in
  Paco.prove_using_rel (itree_eutt_with_aux e rel) pred (a, c) b lemma

let itree_eutt_refl (#e:Type -> Type) (#r:Type) (t:itree e r) :
  Lemma (itree_eutt t t) = itree_eutt_with_refl (fun x y -> x  == y) t

let itree_eutt_symm (#e:Type -> Type) (#r:Type) (t t':itree e r) :
  Lemma (requires itree_eutt t' t) (ensures itree_eutt t t')
  = itree_eutt_with_symm (fun x y -> x == y) t t'

let structural_low_1 (#e:Type -> Type) (#r:Type) (t:itree e r) :
  Lemma (itree_eutt t (tau t)) =
  let rel (x:itree e r & itree e r) : prop =
    x._2 == tau x._1
  in

  let rec lemma (x:itree e r & itree e r) (n:nat) :
    Lemma
      (requires x._2 == tau x._1)
      (ensures Paco.gfp_approx (itree_eutt_aux e r) n x)
      (decreases n)
    = if n = 0 then () else
    let t, _ = x in
    match itree_destruct t with
    | Tau t -> lemma (t, tau t) (n-1)
    | _ -> 
      itree_eutt_refl t;
      assert(Paco.gfp_approx (itree_eutt_aux e r) (n-1) (t, t))
  in

  Paco.prove_using_pred (itree_eutt_aux e r) rel (t, tau t) lemma

let structural_low_2 (#e:Type -> Type) (#r #s:Type) (t:itree e r) (k:r -> itree e s) :
  Lemma (bind (tau t) k == tau (bind t k)) =
  
  assert(itree_destruct (bind (tau t) k) == Tau (bind t k));
  itree_bisim (fun t t' ->
    itree_destruct t == itree_destruct t'
  ) (bind (tau t) k) (tau (bind t k))


let structural_low_3 (#e:Type -> Type) (#a #r #s:Type) (x: e a) (k1:a -> itree e r) (k2:r -> itree e s) :
  Lemma (bind (vis x k1) k2 == vis x (fun x -> bind (k1 x) k2)) =
  itree_repr_equality 
    (itree_destruct (bind (vis x k1) k2))
    (itree_destruct (vis x (fun x -> bind (k1 x) k2)));

  itree_bisim (fun t t' ->
    itree_destruct t == itree_destruct t'
  ) (bind (vis x k1) k2) (vis x (fun x -> bind (k1 x) k2))

let congruence_low_1 (#e:Type -> Type) (#r:Type) (t1 t2:itree e r) :
  Lemma
    (requires t1 == t2)
    (ensures tau t1 == tau t2)
  = ()

let congruence_low_2 (#e:Type -> Type) (#r #a:Type) (ea:e a) (k1 k2:a -> itree e r) :
  Lemma
    (requires forall x. itree_eutt (k1 x) (k2 x))
    (ensures itree_eutt (vis ea k1) (vis ea k2))
  = Paco.fold_gfp (itree_eutt_aux e r) (vis ea k1, vis ea k2)

let congruence_low_3 (#e:Type -> Type) (#r #s:Type) (t1 t2:itree e r) (k1 k2:r -> itree e s) :
  Lemma
    (requires itree_eutt t1 t2 /\ (forall x. itree_eutt (k1 x) (k2 x)))
    (ensures itree_eutt (bind t1 k1) (bind t2 k2)) =
  let rel (x:itree e s & itree e s) (y:itree e r & itree e r) : prop =
    x._1 == bind y._1 k1 /\ x._2 == bind y._2 k2 /\ itree_eutt y._1 y._2 in

  let rec lemma (x:itree e s & itree e s) (y:itree e r & itree e r) (n:nat) :
    Lemma
      (requires rel x y)
      (ensures Paco.gfp_approx (itree_eutt_aux e s) n x)
      (decreases n) =
    if n = 0 then () else
    let o1, o2 = x in
    let t1, t2 = y in
    Paco.unfold_gfp (itree_eutt_aux e r) (t1, t2);
    match itree_destruct t1, itree_destruct t2 with
    | Ret r1, Ret r2 -> 
      monad_low_2 k1 r1;
      monad_low_2 k2 r2;
      admit()
    | Vis x1 ex1 cont1, Vis x2 ex2 cont2 ->
      let Vis _ _ cont1' = itree_destruct o1 in
      let Vis _ _ cont2' = itree_destruct o2 in
      let aux x :
        Lemma (Paco.gfp_approx (itree_eutt_aux e s) (n-1) (to_fun cont1' x, to_fun cont2' x)) =
        lemma (to_fun cont1' x, to_fun cont2' x) (to_fun cont1 x, to_fun cont2 x) (n-1)
      in Classical.forall_intro aux
    | Tau t1, Tau t2 ->
      let Tau o1 = itree_destruct o1 in
      let Tau o2 = itree_destruct o2 in
      lemma (o1, o2) (t1, t2) (n-1)
    | Tau t1, Vis _ _ _ -> 
      structural_low_2 t1 k1;
      let Tau o1 = itree_destruct o1 in
      lemma (o1, o2) (t1, t2) (n-1)
      | Tau t1, Ret r2 ->
        monad_low_2 k2 r2;
        structural_low_2 t1 k2;
        structural_low_1 t1;
        // o1 = tau (bind t1 k1) `itree_eutt` bind t1 k1
        // o2 = k2 r2
        // t1 `itee_eutt` ret r2
        let Tau o1 = itree_destruct o1 in
        admit()
    | _, Tau t2 -> admit()
    | _, _ -> admit()
  in

  Paco.prove_using_rel (itree_eutt_aux e s) rel (bind t1 k1, bind t2 k2) (t1, t2) lemma
