module ITree.Basics


module Classical = FStar.Classical
open Equiv

module T = FStar.Tactics
open OnDomain


open PFunctor
open PFUtils

module Paco = Paco

#push-options "--print_universes"

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

type empty_u : Type u#a = 
type unit_u : Type u#a = | Unit

let itree_response (#e:Type u#a -> Type u#b) (#r:Type u#c) (c:itree_command e r) =
  match c with
  | VisC x ex -> x
  | RetC res -> empty_u
  | TauC -> unit_u

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
  | TauC -> Tau (to_fun pa.children Unit)

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


let rec burn (#e:Type -> Type) (#r:Type) (n:nat) (t:itree e r) :
  Tot (itree_repr e r (itree e r)) (decreases n) =
  if n = 0 then itree_destruct t else
  match itree_destruct t with
  | Tau t -> burn (n-1) t
  | _ -> itree_destruct t


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
  end

// definition of bind operator
[@@"opaque_to_smt"]
let bind (#e:Type -> Type) (#r #s:Type) (t:itree e r) (k:r -> itree e s) : itree e s =
  itree_corec (bind_automaton k) (Left t)
