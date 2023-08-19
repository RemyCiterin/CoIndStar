module Imp

open ITree.Basics
open ITree.Equiv
open ITree.Eutt
open ITree.MonadLaws
open ITree.StructuralLaws
open ITree.CongruenceLaws
open ITree.Interp
open ITree.KTree
open ITree.Iteration
open OnDomain
module M = FStar.Map

assume val itree_codiagonal (#e:Type -> Type) (#a #b:Type)
  (f: ktree e a (sum a (sum a b))) :
  Lemma (
    iter (iter f) `keq` iter (ktree_cat f (ktree_case (ktree_inl e) (ktree_id e)))
  )


let var = string

let value = int

type expr =
  | Var of var
  | Lit of value
  | Plus : expr -> expr -> expr
  | Minus : expr -> expr -> expr
  | Times : expr -> expr -> expr

type stmt =
  | Assign : var -> expr -> stmt
  | Seq : stmt -> stmt -> stmt
  | If : expr -> stmt -> stmt -> stmt
  | While : expr -> stmt -> stmt
  | Skip

type imp_event : Type -> Type =
| GetVar : (x:var) -> imp_event value
| SetVar : (x:var) -> (v:value) -> imp_event unit

let addr = string

let reg = int

type operand =
| Oimm of value
| Oref of reg

type instr =
| Imov : reg -> operand -> instr
| Iadd : reg -> reg -> operand -> instr
| Isub : reg -> reg -> operand -> instr
| Imul : reg -> reg -> operand -> instr
| Ieq  : reg -> reg -> operand -> instr
| Ile  : reg -> reg -> operand -> instr
| Iand : reg -> reg -> operand -> instr
| Inot : reg -> operand -> instr
| Iload : reg -> addr -> instr
| Istore: addr -> operand -> instr

type branch (label: Type) : Type =
| Bjmp of label
| Bbrz : reg -> label -> label -> branch label
| Bhalt

type block (label: Type) : Type =
| Bbi: instr -> block label -> block label
| Bbb: branch label -> block label

let fin x = y:nat{y < x}

noeq type asm (a b:nat) = {
  internal: nat;
  code: fin (internal+a) -> block (fin (internal+b))
}

type asm_event : Type -> Type =
| GetReg : reg -> asm_event value
| SetReg : reg -> value -> asm_event unit
| Load : addr -> asm_event value
| Store: addr -> value -> asm_event unit
| Exit: asm_event empty

noeq type empty_event : Type -> Type =

(*
idea: define denotational semantic of imp and asm:
from asm a b to itree asm_event unit
from imp to itree imp_event unit

and interpretation
from itree asm_event alpha to memory -> registers -> itree empty_event (memory * registers * alpha)
from itree imp_event alpha to variables -> itree empty_event (variables * alpha)

show that interpretations are eutt with a certain relation
*)

let imp_itree = itree imp_event
let asm_itree = itree asm_event
let empty_itree = itree empty_event

// denotational semantic of imp programs
let rec denote_expr (e:expr) : imp_itree value =
  match e with
  | Var v ->
    trigger (GetVar v)
  | Lit x ->
    ret imp_event x
  | Times e1 e2 ->
    bind (denote_expr e1) (
      fun x1 -> bind (denote_expr e2) (
          fun x2 -> ret imp_event (op_Multiply x1 x2)
        )
    )
  | Plus e1 e2 ->
    bind (denote_expr e1) (
      fun x1 -> bind (denote_expr e2) (
          fun x2 -> ret imp_event (op_Multiply x1 x2)
        )
    )
  | Minus e1 e2 ->
    bind (denote_expr e1) (
      fun x1 -> bind (denote_expr e2) (
          fun x2 -> ret imp_event (op_Multiply x1 x2)
        )
    )

let rec denote_stmt (s:stmt) : imp_itree unit =
  match s with
  | Assign x e ->
    bind (denote_expr e) (fun v -> trigger (SetVar x v))
  | Seq s1 s2 ->
    bind (denote_stmt s1) (fun _ -> denote_stmt s2)
  | Skip -> ret _ ()
  | If e s1 s2 ->
    bind (denote_expr e)
    (fun x -> if x <> 0 then denote_stmt s1 else denote_stmt s2)
  | While e s ->
    iter (ktree_cat (fun _ -> denote_expr e) (fun x ->
      if x <> 0 then bind (denote_stmt s) (fun _ -> ret _ (Left ())) else ret _ (Right ())
    )) ()


let variables = M.t string int


// TODO: rewrite this function with interp (...) t
let interp_imp (#r:Type) (t: imp_itree r) (f:variables)
  : empty_itree r =
  iter #empty_event #(imp_itree r & variables) #r (
    fun (t, f) -> match itree_destruct t with
      | Tau t -> ret _ (Left (t, f))
      | Ret r -> ret _ (Right r)
      | Vis _ (GetVar x) k ->
        let v = M.sel f x in
        ret _ (Left (to_fun k v, f))
      | Vis _ (SetVar x v) k ->
        let f = M.upd f x v in
        ret _ (Left (to_fun k (), f))
  ) (t, f)
