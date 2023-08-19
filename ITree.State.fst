module ITree.State

open ITree.Basics
open ITree.Equiv
open ITree.Eutt
open ITree.MonadLaws
open ITree.StructuralLaws
open ITree.CongruenceLaws
open ITree.KTree
open ITree.Iteration
open ITree.Interp
open OnDomain
module Classical = FStar.Classical
module Tac = FStar.Tactics


// definition of state monad transformer
let state_t (state:Type0) (m:Type -> Type) (r:Type) = 
  state -> m (state & r)

let state_pure (state:Type0) (m:Type -> Type) {|_:monad_iter m|} (#r:Type) (x:r) : state_t state m r =
  fun s -> mpure (s, x)

let state_bind_right_term (state:Type0) (m:Type -> Type) (r s:Type)
  (g:r -> state_t state m s) : (state & r) -> m (state & s) =
  fun (s, x) -> g x s

let state_bind (state:Type0) (m:Type -> Type) {|_:monad_iter m|} (#r #s:Type) 
  (f:state_t state m r) (g:r -> state_t state m s) : state_t state m s =
  fun s0 -> mbind (f s0) (state_bind_right_term state m r s g)

let state_iter_body_right_term (state:Type0) (m:Type -> Type) {|_:monad_iter m|} (#r #s:Type)
  : (state & (sum r s)) -> m (sum (state & r) (state & s)) = fun (s, y) ->
  match y with
  | Left l -> mpure (Left (s, l))
  | Right r -> mpure (Right (s, r))

let state_iter_body (state:Type0) (m:Type -> Type) {|inst:monad_iter m|} (#r #s:Type)
  (f:r -> state_t state m (sum r s)) : (state & r) -> m (sum (state & r) (state & s)) =
  fun (s0, x) -> mbind (f x s0) (state_iter_body_right_term state m #inst #r #s)

let state_iter (state:Type0) (m:Type -> Type) {|_:monad_iter m|} (#r #s:Type)
  (f:r -> state_t state m (sum r s)) (x:r) : state_t state m s =
  fun s0 -> miter (state_iter_body state m f) (s0, x)

instance state_monad_iter (#state:Type0) (#m:Type -> Type) {|_:monad_iter m|} :
  monad_iter (state_t state m) = {
  mpure = state_pure state m;
  mbind = state_bind state m;
  miter = state_iter state m;
}

let state_interp_lemma (#state:Type0) (#e #f:Type -> Type) (#r:Type)
  (handler: ((#a:Type) -> e a -> state_t state (itree f) a)) (t:itree e r) :
  Lemma (
    general_interp handler t ==
    state_iter state _ (general_interp_body handler) t
  ) = ()

let state_interp_ret (#state:Type0) (#e #f:Type -> Type) (#r:Type) 
  (handler: ((#a:Type) -> e a -> state_t state (itree f) a)) (x:r) (s:state) :
  Lemma (
    let i: state_t state (itree f) r = general_interp handler (ret e x)
    in i s == ret f (s, x)) = 
  let i: state_t state (itree f) r = general_interp handler (ret e x) in
  let iter_body = state_iter_body state (itree f) (
    general_interp_body #e #(state_t state (itree f)) #state_monad_iter #r handler) in
  iter_unfold iter_body (s, ret e x);
  assert(i s == bind (iter_body (s, ret e x)) (iter_continuation iter_body));
  assert(iter_body (s, ret e x) == bind (ret f (s, Right x)) (state_iter_body_right_term state (itree f)));
  monad_law2 (state_iter_body_right_term state (itree f)) (s, Right #(itree e r) x);
  assert(iter_body (s, ret e x) == ret f (Right (s, x)));
  monad_law2 (iter_continuation iter_body) (Right (s, x))

(*
let state_interp_vis (#state:Type0) (#e #f:Type -> Type) (#r:Type)
  (handler: ((#a:Type) -> e a -> state_t state (itree f) a)) (s:state)
  (#ev:Type) (x:e ev) (cont: ev -> itree e r) :
  Lemma (
    let i: state_t state (itree f) r = general_interp handler (vis x cont) in
    i s == mbind (handler x) (fun t -> ktree_tau (general_interp handler (cont t))) s
  ) = admit()
*)
