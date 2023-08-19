(*
this interface define indexed polynomial functor (of indexed container) and 
indexed coinductive datatype using non-indexed coinductive datatype and 
a well formed property on it
*)

module PFToIdx

open OnDomainDep
module ODD = OnDomainDep

// definition of indexed polynomial functor
unopteq type idx_pfunctor (output:Type) = 
  {
    idx_command : output -> Type;
    idx_response: (o:output) -> idx_command o -> Type;
    next: (o:output) -> (c:idx_command o) -> idx_response o c -> output
  }

let idx_apply_children_ty (#output:Type) (ipf:idx_pfunctor output) (o:output)
  (ty:output -> Type) (node:ipf.idx_command o) (r:ipf.idx_response o node) =
  ty (ipf.next o node r)

// each polynomial functor define an indexed functor
unopteq type idx_apply (#output:Type) (ipf:idx_pfunctor output) (o:output) (ty:output -> Type) =
  {
    idx_node: ipf.idx_command o;
    idx_children: onDomainDep
      (ipf.idx_response o idx_node)
      (idx_apply_children_ty ipf o ty idx_node)
  }

let idx_map (#output:Type) (#a #b:output -> Type) (#p:idx_pfunctor output) (#o:output)
  (f:(o:output) -> a o -> b o) (ia:idx_apply p o a) : idx_apply p o b =
  {
    idx_node = ia.idx_node;
    idx_children = from_fun
      #(p.idx_response o ia.idx_node)
      #(idx_apply_children_ty p o b ia.idx_node)
      (fun x -> f _ (to_fun ia.idx_children x))
  }

// definition of indexed coinductive datatype
val midx_type (#output:Type) (ipf:idx_pfunctor output) (o:output) : Type


val midx_destruct (#output:Type) (#ipf:idx_pfunctor output) (#o:output)
  (m:midx_type ipf o) : idx_apply ipf o (midx_type ipf)
// same an non-indexed: this version of bisimulation is
// complicated to use but useful to define simpler bisimulation theorem 
val midx_bisim (#output:Type) (#ipf: idx_pfunctor output)
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


val midx_corec (#output:Type) (#ipf:idx_pfunctor output) (#state:output -> Type)
  (f:(o:output) -> state o -> idx_apply ipf o state) (#o:output) (x:state o) :
  midx_type ipf o


val midx_dest_corec (#output:Type) (#ipf:idx_pfunctor output) (#state:output -> Type)
  (f:(o:output) -> state o -> idx_apply ipf o state) (o:output) (x:state o) :
  Lemma (midx_destruct (midx_corec f x) == idx_map (fun o -> midx_corec f #o) (f o x))
  [SMTPat (midx_destruct (midx_corec f x))]

val midx_construct (#output:Type) (#ipf:idx_pfunctor output) (#o:output)
  (pa:idx_apply ipf o (midx_type ipf)) : midx_type ipf o


val midx_dest_cons (#output:Type) (#ipf:idx_pfunctor output) (#o:output)
  (ia:idx_apply ipf o (midx_type ipf)) : Lemma
    (ensures midx_destruct (midx_construct ia) == ia)
    [SMTPat (midx_destruct (midx_construct ia))]


val midx_cons_dest (#output:Type) (#ipf:idx_pfunctor output) (#o:output)
  (m:midx_type ipf o) : Lemma
    (ensures midx_construct (midx_destruct m) == m)
    [SMTPat (midx_construct (midx_destruct m))]
