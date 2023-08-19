module PFunctor.Corec

module Classical = FStar.Classical
open OnDomain
open PFunctor
open PFUtils

unopteq type goal (p:pfunctor) (args:Type) : Type =
  | Done of m_type p
  | Call of args
  | Step : (n:p.command) -> (p.response n -> goal p args) -> goal p args

let pgoal p args = g:goal p args{~(Call? g)}

let cofix_aux (#p:pfunctor) (#args:Type) (f:args -> pgoal p args) : 
  goal p args -> pf_apply p (goal p args) = fun g ->
  match g with
  | Done m -> map p Done (m_destruct m)
  | Step n c -> {node=n; children=from_fun c}
  | Call a -> begin
    match f a with
    | Done m -> map p Done (m_destruct m)
    | Step n c -> {node=n; children=from_fun c}
  end

let cofix (#p:pfunctor) (#args:Type) (f:args -> pgoal p args) (x0:args) :
  m_type p = m_corec (cofix_aux f) (f x0)

// equality functor over m_type p
let eq_functor (p:pfunctor) : Paco.functor (m_type p & m_type p) = fun aux (x, y) ->
  m_node x == m_node y /\ (forall arg.
    aux (to_fun (m_children x) arg, to_fun (m_children y) arg)
  )

let eq_functor_monotone (p:pfunctor) : 
  Lemma (Paco.monotone (eq_functor p))
  [SMTPat (Paco.monotone (eq_functor p))] =
  Paco.monotone_intro (eq_functor p) (fun _ _ _ -> ())

let eq_m_type (#p:pfunctor) (x y:m_type p) : prop =
  Paco.gfp (eq_functor p) (x, y)

let rec goal_map (#p:pfunctor) (#a #b:Type) (f:a -> b) (g:goal p a) : Tot (goal p b) (decreases g) =
  match g with
  | Done m -> Done m
  | Call x -> Call (f x)
  | Step n c ->
    Step n (fun x -> goal_map f (c x))

let rec goal_eval (#p:pfunctor) (g:goal p (m_type p)) : Tot (m_type p) (decreases g) =
  match g with
  | Done m -> m
  | Call m -> m
  | Step n cont ->
    let s = {node=n; children=from_fun (fun x -> goal_eval (cont x))} in
    m_construct s

let pf_apply_equal (#p:pfunctor) (#a:Type) (x y:pf_apply p a) : prop =
  x.node == y.node /\ deq x.children y.children

let pf_apply_lemma1 (#p: pfunctor) (#a: Type) (x y: pf_apply p a) (h1:pf_apply_equal x y) :
  Lemma (x == y) =
  assert(deq x.children y.children);
  ()

let pf_apply_thm (#p:pfunctor) (#a:Type) (x y:pf_apply p a) :
  Lemma (pf_apply_equal x y <==> x == y) =
  Classical.impl_intro #(pf_apply_equal x y) (pf_apply_lemma1 x y)

let eq_refl (#p:pfunctor) (m:m_type p) : 
  Lemma (eq_m_type m m) =
  let pred (x:m_type p & m_type p) : prop = x._1 == x._2 in
  Paco.coinduction_pred (eq_functor p) pred (m, m) (fun (m, m') -> ())

let cofix_unfold (#args:Type) (#p:pfunctor) (f:args -> pgoal p args) (x0:args) :
  Lemma (cofix f x0 == goal_eval (goal_map (cofix f) (f x0))) =
  let rel (pair: m_type p & m_type p) (x:goal p args) : prop =
    pair._1 == m_corec (cofix_aux f) x  /\
    pair._2 == goal_eval (goal_map (cofix f) x)
  in

  Paco.commute_with_lb_intro (eq_functor p) (fun q x -> assert(eq_functor p (q 0) x));
  eq_functor_monotone p;

  let lemma (pair:m_type p & m_type p) (g:goal p args) :
    Lemma (requires rel pair g)
      (ensures Paco.union_monotone (eq_functor p) (fun x -> exists y. rel x y) (Paco.gfp (eq_functor p)) pair) =
    let (m, m') = pair in
    match g with
    | Done m -> ()
    | Step n c -> ()
    | Call x -> begin
      pf_apply_thm (m_destruct m) (m_destruct m');
      m_bisim (fun m m' -> m_destruct m == m_destruct m') m m';
      eq_refl m
    end
  in
  
  Paco.strong_coinduction_rel _ (eq_functor p) rel
    (cofix f x0, goal_eval (goal_map (cofix f) (f x0))) (f x0) lemma;
    
    m_bisim (fun m m' -> eq_m_type m m') (cofix f x0) (goal_eval (goal_map (cofix f) (f x0)))
