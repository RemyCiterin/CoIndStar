module PFunctor

module Classical = FStar.Classical
open FStar.Tactics.Typeclasses
//open FStar.FunctionalExtensionality
open FStar.Tactics.Derived
open FStar.Tactics.Builtins
open OnDomain

module ODD = OnDomainDep

// a pfunctpr represent a type of command (the possible nodes)
// and a response, the source type of each node
//noeq type pfunctor = { command: Type; response: command -> Type }

//unopteq type pf_apply (p: pfunctor) (a: Type) : Type =
//  { node: p.command; children: onDomain (p.response node) a }

//let comp (#a #b #c: Type) (f:b -> c) (g: a -> b) : onDomain a c = from_fun (fun (x:a) -> f (g x))

let comp_lemma1 (#a #b #c: Type) (f: b -> c) (g: a -> b) :
  Lemma (forall x. to_fun (comp f g) x == f (g x)) =
  application_lemma (fun x -> f (g x))


//let map (p: pfunctor) (#a #b: Type) (g: a -> b) (pa: pf_apply p a) : pf_apply p b =
//  { node = pa.node; children = comp g (to_fun pa.children)}

let pf_apply_equal (#p:pfunctor) (#a:Type) (x y:pf_apply p a) : prop =
  x.node == y.node /\ deq x.children y.children

let pf_apply_lemma1 (#p: pfunctor) (#a: Type) (x y: pf_apply p a) (h1:pf_apply_equal x y) :
  Lemma (x == y) =
  assert(deq x.children y.children);
  ()

let pf_apply_thm (#p:pfunctor) (#a:Type) (x y:pf_apply p a) :
  Lemma (pf_apply_equal x y <==> x == y) =
  Classical.impl_intro #(pf_apply_equal x y) (pf_apply_lemma1 x y)

noeq type m_approx (p: pfunctor) : nat -> Type =
  | MContinue : m_approx p 0
  | MIntro : (#n: nat) -> pf_apply p (m_approx p n) -> m_approx p (n+1)

let m_approx_equal (#p:pfunctor) (#n:nat) (x y: m_approx p n) : prop =
  let aux (#n: nat) (x y: m_approx p (n+1)) : prop =
    match x with
    | MIntro px -> match y with | MIntro py -> pf_apply_equal px py
  in

  if n = 0 then true else aux #(n-1) x y

let m_approx_thm (#p:pfunctor) (#n:nat) (x y: m_approx p n) :
  Lemma (m_approx_equal x y <==> x == y) =
  if n = 0 then () else match x with
  | MIntro px -> match y with
  | MIntro py -> begin
    pf_apply_thm px py
  end

noeq type agree (p:pfunctor) : (n: nat) -> m_approx p n -> m_approx p (n+1) -> Type =
  | AContinue : (x: m_approx p 0) -> (y: m_approx p 1) -> agree p 0 x y
  | AIntro :
    (#n: nat) -> (a: p.command) ->
    (x: onDomain (p.response a) (m_approx p n)) ->
    (y: onDomain (p.response a) (m_approx p (n+1))) ->
    ((i: p.response a) -> squash(agree p n (to_fun x i) (to_fun y i))) ->
    agree p (n+1) (MIntro {node = a; children =  x}) (MIntro {node = a; children = y})

let agree_0_lemma (p:pfunctor) :
  Lemma (forall (x:m_approx p 0). forall (y: m_approx p 1). agree p 0 x y)
  [SMTPat (agree p 0)]
  = introduce forall x y. agree p 0 x y
  with FStar.Squash.return_squash (AContinue #p x y)


noeq type m_type' (p:pfunctor) = {
  approx: ODD.onDomainDep nat (m_approx p);
  agrees :
    ODD.onDomainDep nat (fun n ->
      squash(agree p n (ODD.to_fun approx n) (ODD.to_fun approx (n+1)))
    )
}

let m_type = m_type'

let m_approx_node (#p:pfunctor) (#n: nat) (m: m_approx p (n+1)) : p.command =
  match m with
  | MIntro content -> content.node

let m_approx_children (#p:pfunctor) (#n: nat) (m:m_approx p (n+1)) : onDomain (p.response (m_approx_node m)) (m_approx p n) =
  match m with
  | MIntro content -> content.children

let m_approx_pf_apply (#p:pfunctor) (#n: nat) (m: m_approx p (n+1)) : pf_apply p (m_approx p n) =
  match m with
  | MIntro content -> content


let rec truncate (#p: pfunctor) (#n: nat) (m:m_approx p (n+1)) : m_approx p n =
  if n = 0 then MContinue else match m with
    | MIntro content -> begin
      MIntro (map p (truncate #p #(n-1)) content)
    end


let rec truncate_thm (#p:pfunctor) (#n:nat)
  (m:m_approx p n) (m': m_approx p (n+1)) :// (h:agree p n m m') :
  Lemma
    (requires agree p n m m')
    (ensures m == truncate m') =
  FStar.Squash.bind_squash #(agree p n m m') #(m == truncate m') () (fun h ->
  match h with
  | AContinue _ _ -> ()
  | AIntro a x y h -> begin
    assert_norm(truncate m' == normalize_term (truncate m'));

    let aux (i:p.response a) : Lemma (to_fun x i == to_fun (comp truncate (to_fun y)) i) =
      h i; truncate_thm (to_fun x i) (to_fun y i)
    in

    Classical.forall_intro aux;
    deq_lemma x (comp truncate (to_fun y))
  end
  )

let m_type_node (#p:pfunctor) (m: m_type p) : p.command =
  m_approx_node #p #0 (ODD.to_fun m.approx 1)

let m_type_node_lemma (#p:pfunctor) (m: m_type p) :
  Lemma
    (ensures forall (n:pos). m_type_node m == m_approx_node #p #(n-1) (ODD.to_fun m.approx n))
    [SMTPat (m_type_node #p m)]
  = introduce forall (n:pos). m_type_node m == m_approx_node #p #(n-1) (ODD.to_fun m.approx n)
  with
    let rec aux (n:pos) :
      Lemma (m_type_node m == m_approx_node #p #(n-1) (ODD.to_fun m.approx n)) =
      if n = 1 then () else
        FStar.Squash.bind_squash
          #_ #(m_type_node m == m_approx_node #p #(n-1) (ODD.to_fun m.approx n))
          (ODD.to_fun m.agrees (n-1)) (
            fun h ->
            match h with
            | AIntro a x y h -> aux (n-1)
          )
    in
    aux n


let m_type_children_approx (#p: pfunctor) (n:nat) (m:m_type p)
  (arg:p.response (m_approx_node (ODD.to_fun m.approx (n+1)))) : m_approx p n =
  to_fun (m_approx_children (ODD.to_fun m.approx (n+1))) arg

let m_destruct_approx (#p:pfunctor) (m:m_type p)
  (arg: p.response (m_type_node m)) (n:nat) : m_approx p n =
  if n = 0 then MContinue else begin
    to_fun (m_approx_children (ODD.to_fun m.approx (n+1))) arg
  end

let m_destruct_approx_agree_lemma (#p:pfunctor) (m:m_type p)
  (arg: p.response (m_type_node m)) (n:nat) :
  squash(agree p n (m_destruct_approx m arg n) (m_destruct_approx m arg (n+1)))
  = if n = 0 then
    FStar.Squash.return_squash (AContinue #p (m_destruct_approx m arg n) (m_destruct_approx m arg (n+1)))
  else FStar.Squash.bind_squash
    #_ #(agree p n (m_destruct_approx m arg n) (m_destruct_approx m arg (n+1)))
    (ODD.to_fun m.agrees (n+1)) (fun h -> match h with
      | AIntro a x y h -> h arg
    )

let m_destruct (#p:pfunctor) (m:m_type p) : pf_apply p (m_type p) =
  {
    node = m_type_node m;
    children = from_fun (fun arg -> {
      approx = ODD.from_fun (m_destruct_approx m arg);
      agrees = ODD.from_fun (m_destruct_approx_agree_lemma m arg)
    })
  }

let rec m_approx_corec (#p:pfunctor) (#a:Type) (n:nat) (f:a -> pf_apply p a) (x:a) : m_approx p n =
  if n = 0 then MContinue else begin
    MIntro {
      node = (f x).node;
      children = from_fun (fun arg ->
        m_approx_corec (n-1) f (to_fun (f x).children arg)
      )
    }
  end

let rec m_approx_corec_agree_thm (#p:pfunctor) (#a:Type) (n:nat) (f: a -> pf_apply p a) (z:a)
  : squash(agree p n (m_approx_corec n f z) (m_approx_corec (n+1) f z)) =
  if n = 0 then
    FStar.Squash.return_squash (AContinue #p (m_approx_corec n f z) (m_approx_corec (n+1) f z))
  else begin
    let x = m_approx_corec n f z in
    let y = m_approx_corec (n+1) f z in

    let x = m_approx_children #p #(n-1) x in
    let y = m_approx_children y in

    let hyp = fun arg -> m_approx_corec_agree_thm (n-1) f (to_fun (f z).children arg) in

    FStar.Squash.return_squash (
      AIntro #p (f z).node x y hyp
    )
  end

let m_corec (#p:pfunctor) (#a:Type) (f:a -> pf_apply p a) (x:a) : m_type p =
  {
    approx = ODD.from_fun (fun n -> m_approx_corec n f x);
    agrees = ODD.from_fun (fun n -> m_approx_corec_agree_thm n f x)
  }

let m_type_eq_approx (#p:pfunctor) (m m': m_type p) :
  Lemma (requires ODD.deq m.approx m'.approx)
  (ensures m == m') [SMTPat (ODD.deq m.approx m'.approx)] =
  ODD.deq_lemma m.approx m'.approx;
  assert(ODD.deq m.agrees m'.agrees)

let m_type_dest_corec_lemma1 (#a:Type) (#p:pfunctor) (f:a -> pf_apply p a) (x:a) (n:nat) (arg: p.response (f x).node) :
  Lemma (m_destruct_approx (m_corec f x) arg n == ODD.to_fun (m_corec f (to_fun (f x).children arg)).approx n) = ()

let m_type_dest_corec_lemma2 (#a:Type) (#p:pfunctor) (f:a -> pf_apply p a) (x:a) (n:nat) (arg: p.response (f x).node) :
  Lemma (ODD.to_fun (m_corec f (to_fun (f x).children arg)).approx n == ODD.to_fun (to_fun (map p (m_corec f) (f x)).children arg).approx n)
  = ()

let m_dest_corec (#a:Type) (#p:pfunctor) (f: a -> pf_apply p a) (x:a) :
  Lemma (ensures m_destruct (m_corec f x) == map p (m_corec f) (f x)) =
  assert(forall arg. ODD.deq (ODD.from_fun (m_destruct_approx (m_corec f x) arg)) (m_corec f (to_fun (f x).children arg)).approx);
  Classical.forall_intro_2 (m_type_dest_corec_lemma1 f x);
  Classical.forall_intro_2 (m_type_dest_corec_lemma2 f x);
  comp_lemma1 (m_corec f) (to_fun (f x).children);
  assert(forall arg. forall n.
    ODD.to_fun (to_fun (m_destruct (m_corec f x)).children arg).approx n ==
    ODD.to_fun (to_fun (map p (m_corec f) (f x)).children arg).approx n
  );

  let aux1 = (m_destruct (m_corec f x)).children in
  let aux2 = (map p (m_corec f) (f x)).children in

  assert(forall arg. ODD.deq (to_fun aux1 arg).approx (to_fun aux2 arg).approx);
  assert(forall arg. ODD.deq (to_fun aux1 arg).agrees (to_fun aux2 arg).agrees);
  assert(forall arg. to_fun aux1 arg == to_fun aux2 arg);
  assert(deq aux1 aux2);
  assert(aux1 == aux2)

let rec m_bisim_lemma1 (#p:pfunctor) (r:m_type p -> m_type p -> prop) (m m':m_type p) (n:nat) :
  Lemma
    (requires r m m' /\ (forall x y. r x y ==> (
      (m_destruct x).node == (m_destruct y).node
      /\ (forall arg. r (to_fun (m_destruct x).children arg) (to_fun (m_destruct y).children arg))
    )))
    (ensures ODD.to_fun m.approx n == ODD.to_fun m'.approx n)
    (decreases n)
  = if n = 0 then () else match ODD.to_fun m.approx n with
  | MIntro p1 -> match ODD.to_fun m'.approx n with
  | MIntro p2 -> begin
    assert(p1.node == p2.node);
    let dm = m_destruct m in
    let dm' = m_destruct m' in

    assert(forall arg. to_fun p1.children arg == ODD.to_fun (to_fun dm.children arg).approx (n-1));
    assert(forall arg. to_fun p2.children arg == ODD.to_fun (to_fun dm'.children arg).approx (n-1));

    let aux (arg: p.response p1.node) :
      Lemma (to_fun p1.children arg == to_fun p2.children arg)
      = m_bisim_lemma1 r (to_fun dm.children arg) (to_fun dm'.children arg) (n-1)
    in

    Classical.forall_intro aux;
    assert(deq p1.children p2.children)
  end


let m_bisim (#p:pfunctor) (r:m_type p -> m_type p -> prop) (m m':m_type p) :
  Lemma (requires r m m' /\ (forall x y. r x y ==> (
    (m_destruct x).node == (m_destruct y).node
    /\ (forall arg. r (to_fun (m_destruct x).children arg) (to_fun (m_destruct y).children arg))
  )))
  (ensures m == m')
  =
  Classical.forall_intro (Classical.move_requires (m_bisim_lemma1 r m m'));
  assert(ODD.deq m.approx m'.approx)


