module Stream.Paco

open FStar.PropositionalExtensionality
open FStar.FunctionalExtensionality
module Classical = FStar.Classical
open Stream.Core
module Paco = Paco

module T = FStar.Tactics

let stream_eq_aux (a:Type0) :
  Paco.functor (stream a * stream a) =
  fun aux -> fun (s1, s2) ->
    head s1 == head s2 /\ aux (tail s1, tail s2)

let stream_eq_aux_m (a:Type) :
  Lemma (Paco.monotone (stream_eq_aux a))
  [SMTPat (Paco.monotone (stream_eq_aux a))]
  
  = ()


let stream_eq_aux_commute_with_lb (a:Type) :
  Lemma (Paco.commute_with_lb (stream_eq_aux a)) 
  [SMTPat (Paco.commute_with_lb (stream_eq_aux a))] =
  Paco.commute_with_lb_intro (stream_eq_aux a) 
    (fun p pair -> assert(stream_eq_aux a (p 0) pair))


let stream_bellow_aux' : Paco.functor (stream int & stream int) =
  fun aux (s1, s2) ->
    head s1 <= head s2 /\ (head s1 < head s2 ==> aux (tail s1, tail s2))

let stream_bellow_monotone (_:unit) :
  Lemma (Paco.monotone stream_bellow_aux')
  = ()

let stream_bellow_commute_with_lb (_:unit) :
  Lemma (Paco.commute_with_lb stream_bellow_aux') =
  Paco.commute_with_lb_intro stream_bellow_aux' 
    (fun p pair -> assert(stream_bellow_aux' (p 0) pair))

let stream_bellow_aux : f:Paco.monotone_functor (stream int & stream int){Paco.commute_with_lb f} =
  stream_bellow_monotone ();
  stream_bellow_commute_with_lb ();
  stream_bellow_aux'

let stream_mul (s1 s2:stream int) : stream int =
  stream_corec
    (fun (s1, s2) -> (op_Multiply (head s1) (head s2), (tail s1, tail s2))) (s1, s2)

let stream_add (s1 s2:stream int) : stream int =
  stream_corec
    (fun (s1, s2) -> (head s1 + head s2, (tail s1, tail s2))) (s1, s2)

let rec stream_bellow_thm_aux (p:stream int & stream int) (n:nat) :
  Lemma 
    (requires p._2 == stream_mul p._1 p._1)
    (ensures Paco.gfp_approx stream_bellow_aux n p)
    (decreases n)
  = if n = 0 then () else begin
    let s1, s2 = p in
    assert(head s1 <= head s2);
    if head s1 = head s2 then () else stream_bellow_thm_aux (tail s1, tail s2) (n - 1)
  end

let stream_bellow (s1 s2:stream int) =
  Paco.gfp stream_bellow_aux (s1, s2)

let stream_bellow_thm (s:stream int) :
  Lemma (stream_bellow s (stream_mul s s)) =
  Paco.coinduction_approx_pred stream_bellow_aux (fun (s1, s2) -> s2 == stream_mul s1 s1) (s, stream_mul s s)
    stream_bellow_thm_aux

#push-options "--z3rlimit 50"
let rec stream_assoc_add_aux (x:stream int & stream int)
  (y:stream int & stream int & stream int) (n:nat) :
  Lemma
    (requires 
      x._1 == stream_add (stream_add y._1 y._2) y._3 /\
      x._2 == stream_add y._1 (stream_add y._2 y._3)
    )
    (ensures Paco.gfp_approx (stream_eq_aux int) n x)
    (decreases n) =
  if n = 0 then () else begin
    let sl, sr = x in let s1, s2, s3 = y in
    stream_assoc_add_aux (tail sl, tail sr) (tail s1, tail s2, tail s3) (n-1)
  end
#pop-options

let stream_eq (#a:Type) (s1 s2:stream a) =
  Paco.gfp (stream_eq_aux a) (s1, s2)


let stream_assoc_add (s1 s2 s3:stream int) :
  Lemma (stream_eq (stream_add (stream_add s1 s2) s3) (stream_add s1 (stream_add s2 s3)))
  = let r : (stream int & stream int) -> stream int & stream int & stream int -> prop = 
  fun (sl, sr) (s1, s2, s3) ->
    sl == stream_add (stream_add s1 s2) s3 /\
    sr == stream_add s1 (stream_add s2 s3)
  in

  Paco.coinduction_approx_rel (stream_eq_aux int) r
    (stream_add (stream_add s1 s2) s3, stream_add s1 (stream_add s2 s3))
    (s1, s2, s3) stream_assoc_add_aux

