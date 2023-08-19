(*
this module define a construction of indexed container and M-types using 
non-indexed M-types and Paco-like construction
*)

module PFToIdx

open PFunctor
module Classical = FStar.Classical

module T = FStar.Tactics

open OnDomain
module ODD = OnDomainDep

open PFUtils



// transform an indexed polynomial functor into a polynomial functor

let to_pfunctor (#output:Type) (ipf:idx_pfunctor output) : pfunctor =
  {
    command = (o:output & ipf.idx_command o);
    response = (fun (|o, c|) ->
      ipf.idx_response o c
    )
  }

let well_formed_aux (#output:Type) (ipf:idx_pfunctor output) :
  Paco.functor (output & m_type (to_pfunctor ipf)) =
  fun aux (o, m) ->
    (m_node m)._1 == o /\ (forall arg.
      aux (
        ipf.next o (m_node m)._2 arg, 
        to_fun (m_children m) arg
      )
    )

let well_formed_monotone (#output:Type) (ipf:idx_pfunctor output) :
  Lemma (Paco.monotone (well_formed_aux ipf))
  [SMTPat (Paco.monotone (well_formed_aux ipf))]
  = ()


let well_wormed_aux_commute_with_lb (#output:Type) (ipf:idx_pfunctor output) :
  Lemma (Paco.commute_with_lb (well_formed_aux ipf)) 
  [SMTPat (Paco.commute_with_lb (well_formed_aux ipf))] =
  Paco.commute_with_lb_intro (well_formed_aux ipf) (
    fun p x -> assert(well_formed_aux ipf (p 0) x)
  )

let well_formed (#output:Type) (ipf:idx_pfunctor output) 
  (o:output) (m:m_type (to_pfunctor ipf)) =
  Paco.gfp (well_formed_aux ipf) (o, m)


let midx_type (#output:Type) (ipf:idx_pfunctor output) (o:output) : Type =
  m:m_type (to_pfunctor ipf){well_formed ipf o m}
  
let midx_destruct (#output:Type) (#ipf:idx_pfunctor output) (#o:output)
  (m:midx_type ipf o) : idx_apply ipf o (midx_type ipf) =
  Paco.unfold_gfp (well_formed_aux ipf) (o, m);
  let node = (m_node m)._2 in
  {
    idx_node = node;
    idx_children = ODD.from_fun #_ #(idx_apply_children_ty ipf o (midx_type ipf) node) (
      fun arg -> 
        let m' = to_fun (m_children m) arg in
        assert(well_formed ipf (ipf.next o node arg) m');
        m'
    )
  }

let midx_bisim (#output:Type) (#ipf: idx_pfunctor output)
  (r:(o:output) -> midx_type ipf o -> midx_type ipf o -> prop)
  (#o:output) (m m':midx_type ipf o) :
  Lemma
    (requires r o m m' /\ (forall o m m'. r o m m' ==> (
      (midx_destruct m).idx_node == (midx_destruct m').idx_node /\ (forall arg.
        r (ipf.next o (midx_destruct m).idx_node arg)
          (ODD.to_fun (midx_destruct m).idx_children arg)
          (ODD.to_fun (midx_destruct m').idx_children arg)
      )
    )))
    (ensures m == m')
  = Classical.forall_intro (
    Classical.move_requires (Paco.unfold_gfp (well_formed_aux ipf)));
  m_bisim (
    fun x y -> 
      let ox: output = (m_destruct #(to_pfunctor ipf) x).node._1 in
      let oy: output = (m_destruct #(to_pfunctor ipf) y).node._1 in
      well_formed ipf ox x /\ well_formed ipf ox y /\ r ox x y
  ) m m'


let midx_corec_automaton (#output:Type) (#ipf:idx_pfunctor output) (#state:output -> Type)
  (f:(o:output) -> state o -> idx_apply ipf o state) :
  (o:output & state o) -> pf_apply (to_pfunctor ipf) (o:output & state o) =
  fun (|o, x|) ->
    let pa = f o x in
    {
      node = (|o, pa.idx_node|); children = from_fun
        #(ipf.idx_response o pa.idx_node)
        #(o:output & state o)
        (fun arg -> 
          (|ipf.next o pa.idx_node arg, ODD.to_fun pa.idx_children arg|)
        )
    }

let midx_corec' (#output:Type) (#ipf:idx_pfunctor output) (#state:output -> Type)
  (f:(o:output) -> state o -> idx_apply ipf o state) (o:output) (x:state o) :
  m_type (to_pfunctor ipf) =
  m_corec #(to_pfunctor ipf) #(o:output & state o) 
    (midx_corec_automaton f) (|o, x|)

let rec midx_corec_well_formed_aux (#output:Type) (#ipf:idx_pfunctor output) (#state:output -> Type)
  (f:(o:output) -> state o -> idx_apply ipf o state)
  (x:output & m_type (to_pfunctor ipf)) (s:state x._1) (n:nat) :
  Lemma 
    (requires x._2 == midx_corec' f x._1 s)
    (ensures Paco.gfp_approx (well_formed_aux ipf) n x)
    (decreases n) =
  if n = 0 then () else begin
    let pa = m_destruct x._2 in
    let aux arg :
      Lemma (
        Paco.gfp_approx (well_formed_aux ipf) (n-1) 
        (ipf.next x._1 pa.node._2 arg, to_fun pa.children arg)
      ) = 
      midx_corec_well_formed_aux f
        (ipf.next x._1 pa.node._2 arg, to_fun pa.children arg) 
        (ODD.to_fun (f x._1 s).idx_children arg) (n-1)
    in
    
    Classical.forall_intro aux
  end

let midx_corec (#output:Type) (#ipf:idx_pfunctor output) (#state:output -> Type)
  (f:(o:output) -> state o -> idx_apply ipf o state) (#o:output) (x:state o) :
  midx_type ipf o =
  Paco.coinduction_approx_rel (well_formed_aux ipf) (
      fun x s -> x._2 == midx_corec' f x._1 s
    ) (o, midx_corec' f o x) x
    (midx_corec_well_formed_aux f);
  midx_corec' f o x

let midx_dest_corec (#output:Type) (#ipf:idx_pfunctor output) (#state:output -> Type)
  (f:(o:output) -> state o -> idx_apply ipf o state) (o:output) (x:state o) :
  Lemma (midx_destruct (midx_corec f x) == idx_map (fun o -> midx_corec f #o) (f o x))
  [SMTPat (midx_destruct (midx_corec f x))]
  =
  let t1 = m_destruct (midx_corec f x) in
  let t2 = map (to_pfunctor ipf) (m_corec (midx_corec_automaton f))
    (midx_corec_automaton f (|o, x|)) 
  in

  let t3 = midx_destruct (midx_corec f x) in
  let t4 = idx_map (fun o -> midx_corec f #o) (f o x) in

  assert(forall arg. to_fun t1.children arg == ODD.to_fun t3.idx_children arg);
  let ch4 arg : m_type (to_pfunctor ipf) = ODD.to_fun t4.idx_children arg in
  assert(forall arg. to_fun t2.children arg == ch4 arg);
  assert(ODD.deq t3.idx_children t4.idx_children);

  assert(midx_destruct (midx_corec f x) == idx_map (fun o -> midx_corec f #o) (f o x))

let midx_construct (#output:Type) (#ipf:idx_pfunctor output) (#o:output)
  (pa:idx_apply ipf o (midx_type ipf)) : midx_type ipf o =
  let res: m_type (to_pfunctor ipf) = m_construct #(to_pfunctor ipf) {
    node=(|o, pa.idx_node|);
    children=from_fun
      #(ipf.idx_response o pa.idx_node)
      #(m_type (to_pfunctor ipf))
    (fun (arg:ipf.idx_response o pa.idx_node) ->
      ODD.to_fun pa.idx_children arg
    )
  }
  in
  Paco.fold_gfp (well_formed_aux ipf) (o, res);
  res


let midx_dest_cons (#output:Type) (#ipf:idx_pfunctor output) (#o:output)
  (ia:idx_apply ipf o (midx_type ipf)) : Lemma
    (ensures midx_destruct (midx_construct ia) == ia)
    [SMTPat (midx_destruct (midx_construct ia))]
  = let ia' = midx_destruct (midx_construct ia) in
  assert(ODD.deq ia.idx_children ia'.idx_children);
  match ia, ia' with
  | Mkidx_apply n c, Mkidx_apply n' c' ->
    assert(c == c')

let midx_cons_dest (#output:Type) (#ipf:idx_pfunctor output) (#o:output)
  (m:midx_type ipf o) : Lemma
    (ensures midx_construct (midx_destruct m) == m)
    [SMTPat (midx_construct (midx_destruct m))] =
  let m' = midx_construct (midx_destruct m) in
  assert(midx_destruct m == midx_destruct m');
  midx_bisim (fun o x y ->
    midx_destruct x == midx_destruct y
  ) m m'
