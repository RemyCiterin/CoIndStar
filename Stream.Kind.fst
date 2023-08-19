module Stream.Kind

open Stream.Core
module Classical = FStar.Classical
module T = FStar.Tactics
module L = FStar.List.Tot
module Paco = Paco
  

let tac_nbe (_:unit) : T.Tac unit =
  T.norm [primops; iota; delta; zeta; nbe]

let paco_fun (a:Type) = (a -> prop) -> a -> prop

// definition of pointwise property
let pointwise_aux (#a:Type) (p:a -> prop) : Paco.functor (stream a) =
  fun aux s -> p (head s) /\ aux (tail s)

let pointwise_monotone (#a:Type) (p:a -> prop) :
  Lemma (Paco.monotone (pointwise_aux p)) 
  [SMTPat (Paco.monotone (pointwise_aux p))] =
  ()

let pointwise_aux_commute_with_lb (#a:Type) (p:a -> prop) :
  Lemma (Paco.commute_with_lb (pointwise_aux p)) 
  [SMTPat (Paco.commute_with_lb (pointwise_aux p))] =
  Paco.commute_with_lb_intro (pointwise_aux p) (fun pn x ->
    assert(pointwise_aux p (pn 0) x)
  )

let pointwise (#a:Type) (p:a -> prop) (s:stream a) =
  Paco.gfp (pointwise_aux p) s

// proof that the existance of invariant implie the safety
let to_generator (#a #b #state:Type) (f:b -> state -> a & state) :
  (state & stream b) -> a & (state & stream b) =
  fun (x, s) -> 
    let v, x = f (head s) x in
    (v, (x, tail s))

let rec pointwise_from_inv_aux (#a #b #state:Type)
  (p:a -> prop) (f:b -> state -> a & state) (inv:state -> prop)
  (s:stream a) (y:state & stream b) (n:nat) :
  Lemma
    (requires s == stream_corec (to_generator f) y /\
      inv y._1 /\
      (forall i x. inv x ==> p (f i x)._1) /\
      (forall i x. inv x ==> inv (f i x)._2)
    )
    (ensures Paco.gfp_approx (pointwise_aux p) n s)
    (decreases n)
  = if n = 0 then () else begin
    let x, i = y in
    pointwise_from_inv_aux p f inv (tail s) ((f (head i) x)._2, tail i) (n-1)
  end

let pointwise_from_inv (#a #b #state:Type)
  (p:a -> prop) (f:b -> state -> a & state) (inv:state -> prop)
  (x0:state) (i:stream b) :
  Lemma
    (requires inv x0 /\
      (forall i x. inv x ==> p (f i x)._1) /\
      (forall i x. inv x ==> inv (f i x)._2)
    )
    (ensures pointwise p (stream_corec (to_generator f) (x0, i)))
  = Paco.coinduction_approx_rel (pointwise_aux p)
    (fun s (y:state & stream b) -> s == stream_corec (to_generator f) y /\
      inv y._1 /\
      (forall i x. inv x ==> p (f i x)._1) /\
      (forall i x. inv x ==> inv (f i x)._2)
    ) (stream_corec (to_generator f) (x0, i)) (x0, i) (pointwise_from_inv_aux p f inv)


// proof of invariant using k-induction for k = 1
let step_case (#a #b #state:Type) (p:a -> prop) (f:b -> state -> a & state) (_:state) : prop =
  forall (i1 i2:b) (x:state). p (f i1 x)._1 ==> p (f i2 (f i1 x)._2)._1

let base_case (#a #b #state:Type) (p:a -> prop) (f:b -> state -> a & state) (x0:state) : prop =
  forall (i:b). p (f i x0)._1

let ind1_sound (#a #b #state:Type) (p:a -> prop) (f:b -> state -> a & state) (x0:state) :
  Lemma
    (requires step_case p f x0 /\ base_case p f x0)
    (ensures (let ind (x:state) = forall i. p (f i x)._1 in
      ind x0 /\ 
      (forall i x. ind x ==> p (f i x)._1) /\
      (forall i x. ind x ==> ind (f i x)._2)
    )) 
  = ()

// proof of invariant using k-induction for k : nat
noeq type transition_system (a b state:Type) = {
  safe: a -> prop;
  trans:b -> state -> a & state;
  x0:state
}

let invariant (#a #b #state:Type) (ts:transition_system a b state) (inv:state -> prop) =
  inv ts.x0 /\ (forall i x. inv x ==> inv (ts.trans i x)._2) /\ (forall i x. inv x ==> ts.safe (ts.trans i x)._1)

let rec step_case_1ind (#a #b #state:Type) (ts:transition_system a b state) (input:list b) (x:state) :
  Tot prop (decreases input) =
  match input with
  | [i] -> ts.safe (ts.trans i x)._1
  | i :: is ->
    ~(L.memP i is) /\ ts.safe (ts.trans i x)._1 ==> 
    step_case_1ind ts is (ts.trans i x)._2 
  | _ -> True


let rec base_case_1ind (#a #b #state:Type) (ts:transition_system a b state) (input:list b) (x:state) :
  Tot prop (decreases input) =
  match input with
  | [i] -> ts.safe (ts.trans i x)._1
  | i :: is ->
    ts.safe (ts.trans i x)._1 ==>
    base_case_1ind ts is (ts.trans i x)._2
  | _ -> True

let check_base_case_sound (#a #b #state:Type) (ts:transition_system a b state) :
  Lemma (requires 
    (forall i. base_case_1ind ts [i] ts.x0) /\ 
    (forall i i' x. base_case_1ind ts [i; i'] x)
  )
  (ensures
    invariant ts (fun x -> forall i. base_case_1ind ts [i] x)
  ) =
  let inv x = forall i. base_case_1ind ts [i] x in
  assert_norm(inv ts.x0);
  assert(forall i i' x. base_case_1ind ts [i; i'] x);
  Classical.forall_intro_3 (fun i i' x -> normalize_term_spec (base_case_1ind ts [i; i'] x));
  assert(forall i i' x. base_case_1ind ts [i; i'] x <==> normalize_term (base_case_1ind ts [i; i'] x));
  assert(forall i i' x. normalize_term (base_case_1ind ts [i; i'] x));
  assert_norm(base_case ts.safe ts.trans ts.x0);
  assert_norm(step_case ts.safe ts.trans ts.x0)
