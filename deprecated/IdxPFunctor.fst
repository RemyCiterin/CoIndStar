module IdxPFunctor

module Classical = FStar.Classical
open FStar.FunctionalExtensionality
open FStar.Tactics.Derived
open FStar.Tactics.Builtins
module ODD = OnDomainDep

// already define in IdxPFunctor.fsti
(*
noeq type idx_pf (output:Type) : Type =
  {
    command: output -> Type;
    response: (o:output) -> command o -> Type;
    next: (o:output) -> (c:command o) -> response o c -> output
  }


let idx_apply_ch_out (#output:Type) (p:idx_pf output) (o:output)
  (ty:[@@@strictly_positive]output -> Type) (node: p.command o) (r:p.response o node) : Type
  = ty (p.next o node r)

unopteq type idx_apply (#output:Type) (p:idx_pf output) (o:output)
  (ty:[@@@strictly_positive]output->Type) : Type =
  {
    node: p.command o;
    children: restricted_t (p.response o node) (idx_apply_ch_out p o ty node)
  }

let idx_apply_equals (#output:Type) (#p:idx_pf output) (#o:output)
  (#ty:output -> Type) (i i':idx_apply p o ty) :
  Lemma
    (requires i.node == i'.node /\ i.children == i'.children)
    (ensures i == i')
  = match i with
  | Mkidx_apply n c -> match i' with
  | Mkidx_apply n' c' ->
    assert(n == n');
    assert(c == c');
    assert(i == i')

let map (#output:Type) (#a #b:output -> Type) (#p:idx_pf output) (#o:output)
  (f:(x:output) -> a x -> b x) (ia:idx_apply p o a) : idx_apply p o b =
  {
    node = ia.node;
    children = on_dom _ (fun x -> f _ (ia.children x))
  }
*)

unfold let flip (#a #b #c:Type) (f:a -> b -> c) (x:b) (y:a) : c = f y x

// definition of approximation of size n of nu (fun f -> idx_apply p f o)
noeq type m_approx (#output:Type) (p:idx_pf output) (o:output) : nat -> Type =
| MContinue : m_approx p o 0
| MIntro : (#n:nat) ->
  idx_apply p o (flip (m_approx p) n) ->
  m_approx p o (n+1)

let m_approx_node (#output:Type) (#p:idx_pf output) (#o:output) (n:nat)
  (m:m_approx p o (n+1)) : p.command o =
  match m with
  | MIntro content -> content.node

let m_approx_children (#output:Type) (#p:idx_pf output) (#o:output) (#n:nat) (m:m_approx p o (n+1)) :
  restricted_t 
    (p.response o (m_approx_node n m)) 
    (idx_apply_ch_out p o (flip (m_approx p) n) (m_approx_node n m)) =
  match m with
  | MIntro content -> on_domain (p.response o (m_approx_node n m)) content.children

let rec m_agree (#output:Type) (p:idx_pf output) (o:output) (n:nat)
  (m:m_approx p o n) (m':m_approx p o (n+1)) : Tot(prop) (decreases n) =
  if n = 0 then True else
    m_approx_node (n-1) m == m_approx_node n m' /\ (
      forall arg. m_agree _ _ (n-1) (m_approx_children m arg) (m_approx_children m' arg)
    )

#push-options "--print_universes"

noeq type m_type' (#output:Type) (p:idx_pf output) (o:output) =
  {
    approx: restricted_t nat (m_approx p o);
    agrees: squash(forall n. m_agree p o n (approx n) (approx (n+1)))
  }

let m_type #output p = on_dom _ (m_type' #output p)

let from_m_type' #output #p #o (m:m_type' #output p o) : m_type #output p o = m


//let m_type (#output:Type) (p:idx_pf u#a u#b u#b output) : (output -> Type u#b) 
//  = fun o -> m_type' #output p o // on_dom _ (fun o -> m_type' p o)

let m_type_eq_lemma1 (#output:Type) (#p:idx_pf output) (#o:output) (m m':m_type p o) :
  Lemma
    (requires feq m.approx m'.approx)
    (ensures m == m')
    = ()

let m_type_node (#output:Type) (#p:idx_pf output) (#o:output) (m:m_type p o) : p.command o =
  m_approx_node 0 (m.approx 1)

let m_type_approx_same_node (#output:Type) (#p:idx_pf output) (#o:output) (m:m_type p o) :
  Lemma
    (forall n. m_approx_node n (m.approx (n+1)) == m_type_node m)
  [SMTPat (m_type_node m)]
  =
  let rec aux (n:nat) :
    Lemma (m_approx_node n (m.approx (n+1)) == m_type_node m) =
    if n = 0 then () else begin
      m.agrees;
      aux (n-1)
    end
  in

  Classical.forall_intro aux

let m_destruct_approx (#output:Type) (#p:idx_pf output) (#o:output) (m:m_type p o)
  (arg: p.response o (m_type_node m)) (n:nat) : m_approx p (p.next o (m_type_node m) arg) n =
  if n = 0 then MContinue else m_approx_children (m.approx (n+1)) arg

let m_destruct_agrees (#output:Type) (#p:idx_pf output) (#o:output) (m:m_type p o)
  (arg: p.response o (m_type_node m)) (n:nat) :
  Lemma(m_agree _ _ n (m_destruct_approx m arg n) (m_destruct_approx m arg (n+1))) =
  if n = 0 then () else m.agrees

let m_destruct (#output:Type) (#p:idx_pf output) (#o:output) (m:m_type p o) :
  idx_apply p o (m_type p) =
  {
    node = m_type_node m;
    children = on_dom _ (fun arg -> from_m_type' {
      approx = on_dom _ (m_destruct_approx m arg);
      agrees = Classical.forall_intro (m_destruct_agrees m arg)
    })
  }

let rec m_corec_approx (#output:Type) (#p:idx_pf output) (#o:output)
  (#state: output -> Type) (f:(o:output) -> state o -> idx_apply p o state) (x:state o)
  (n:nat) : Tot (m_approx p o n) (decreases n) =
  if n = 0 then MContinue else
  MIntro #_ #_ #_ #(n-1) {
    node = (f o x).node;
    children = on_dom _ (fun arg ->
      m_corec_approx f ((f o x).children arg) (n-1)
    )
  }

let rec m_corec_agree (#output:Type) (#p:idx_pf output) (#o:output)
  (#state:output -> Type) (f:(o:output) -> state o -> idx_apply p o state) (x:state o) (n:nat) :
  Lemma
    (ensures m_agree _ _ n (m_corec_approx f x n) (m_corec_approx f x (n+1)))
    (decreases n)
  =
  if n = 0 then () else begin
    let m = m_corec_approx f x n in
    let m' = m_corec_approx f x (n+1) in
    assert(m_approx_node (n-1) m == m_approx_node n m');

    let aux arg :
      Lemma
        (m_agree _ _ (n-1) 
          (m_corec_approx f ((f o x).children arg) (n-1))
          (m_corec_approx f ((f o x).children arg) n))
      = m_corec_agree f ((f o x).children arg) (n-1)
    in
    Classical.forall_intro aux
  end

let m_corec (#output:Type) (#p:idx_pf output) (#o:output)
  (#state:output -> Type) (f:(o:output) -> state o -> idx_apply p o state) (x:state o) : m_type p o =
  {
    approx = on_dom _ (m_corec_approx f x);
    agrees = Classical.forall_intro (m_corec_agree f x)
  }

#push-options "--z3rlimit 50"
let m_destruct_corec_thm (#output:Type) (#p:idx_pf output) (#o:output)
  (#state:output -> Type) (f:(o:output) -> state o -> idx_apply p o state) (x:state o) :
  Lemma
    (ensures m_destruct (m_corec f x) == map (fun o -> m_corec #output #p #o f) (f o x)) =
  assert(
    forall arg. feq (m_destruct_approx (m_corec f x) arg) (m_corec f ((f o x).children arg)).approx
  );

  let aux1 = (m_destruct (m_corec f x)).children in
  let aux2 = (map (fun o -> m_corec #output #p #o f) (f o x)).children in
  assert(feq aux1 aux2)
#pop-options

//#push-options "--query_stats --ifuel 10 --fuel 10 --z3rlimit 50"

let m_approx_thm (#output:Type) (#p:idx_pf output) (#o:output) (n:nat) (m m':m_approx p o (n+1)) :
  Lemma (requires m_approx_node n m == m_approx_node n m' /\
    m_approx_children m == m_approx_children m'
  ) (ensures m == m') = match m with
  | MIntro i  -> match m' with
  | MIntro i' ->
    assert(i.children == i'.children);
    assert(i.node == i'.node);
    idx_apply_equals i i';
    assert(i == i')
    

let rec m_bisim_lemma1 (#output:Type) (#p:idx_pf output) (#o:output)
  (r: (o:output) -> m_type p o -> m_type p o -> prop) (m m':m_type p o) (n:nat) :
  Lemma (requires
    r o m m' /\ (forall o x y. r o x y ==> (
      (m_destruct x).node == (m_destruct y).node /\ (forall arg.
        r _ ((m_destruct x).children arg) ((m_destruct y).children arg)
    )))
  ) (
    ensures m.approx n == m'.approx n
  ) (decreases n) =
  if n = 0 then () else begin

    let node = m_approx_node (n-1) (m.approx n) in
    let node' = m_approx_node (n-1) (m'.approx n) in 
    
    let c = m_approx_children (m.approx n) in
    let c' = m_approx_children (m'.approx n) in
    
    m_approx_thm (n-1) (m.approx n) (MIntro{node=node; children=c});
    m_approx_thm (n-1) (m'.approx n) (MIntro{node=node'; children=c'});
    
    assert(node == node');
    let dm = m_destruct m in
    let dm' = m_destruct m' in

    assert(forall arg. c arg == m_destruct_approx m arg (n-1)) by (
      unfold_def (`m_destruct_approx); smt ()
    );
    assert(forall arg. c' arg == m_destruct_approx m' arg (n-1)) by (
      unfold_def (`m_destruct_approx); smt ()
    );

    let aux arg :
      Lemma (c arg == c' arg)
      = m_bisim_lemma1 r (dm.children arg) (dm'.children arg) (n-1)
    in

    Classical.forall_intro aux;
    extensionality _ _ c c';
    assert(feq c c');
    assert(c == c');
    
    ()
  end

let m_bisim_thm (#output:Type) (#p:idx_pf output) (#o:output) (r:(o:output) -> m_type p o -> m_type p o -> prop)
  (m m':m_type p o) : Lemma
    (requires r o m m' /\ (forall o x y. r o x y ==> (
      (m_destruct x).node == (m_destruct y).node /\ (forall arg.
        r _ ((m_destruct x).children arg) ((m_destruct y).children arg)
    ))))
    (ensures m == m')
  =
  Classical.forall_intro (Classical.move_requires (m_bisim_lemma1 r m m'));
  assert(feq m.approx m'.approx)

