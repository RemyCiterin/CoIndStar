module Stream.Core

module Classical = FStar.Classical
open OnDomain
open PFunctor
open PFUtils

open FStar.Tactics

// definition of a stream

let stream_pf (a:Type0) : pfunctor  =
  {
    command = a;
    response = (fun _ -> unit);
  }

let stream_apply (a out:Type) = a * out

let stream (a:Type) = m_type (stream_pf a)

let head (#a:Type) (s:stream a) : a =
  (m_destruct s).node

let tail (#a:Type) (s:stream a) : stream a =
  to_fun (m_destruct s).children ()

let stream_eq_thm (#a:Type) (s s':stream a) :
  Lemma
    (requires head s == head s' /\ tail s == tail s')
    (ensures s == s')
  [SMTPat (s == s')]
  = assert(deq (m_destruct s).children (m_destruct s').children);
  m_bisim (fun s s' -> m_destruct s == m_destruct s') s s'

let pf_apply_from_pair (#a #out:Type) (pair:a * out) : pf_apply (stream_pf a) out =
  {node = pair._1; children = from_fun (fun _ -> pair._2)}

let stream_corec (#a #state:Type) (f:state -> a * state) (s0:state) : stream a =
  m_corec (fun st -> pf_apply_from_pair (f st)) s0

let stream_head_corec_thm (#a #state:Type) (f:state -> a * state) (s0:state) :
  Lemma (head (stream_corec f s0) == (f s0)._1) [SMTPat (head (stream_corec f s0))] =
  m_dest_corec (fun st -> pf_apply_from_pair (f st)) s0

let stream_tail_corec_thm (#a #state: Type) (f:state -> a * state) (s0:state) :
  Lemma (tail (stream_corec f s0) == stream_corec f (f s0)._2) [SMTPat (tail (stream_corec f s0))] =
  m_dest_corec (fun st -> pf_apply_from_pair (f st)) s0

let stream_bisim_thm (#a: Type) (r:stream a -> stream a -> prop) (s s':stream a) :
  Lemma (requires r s s' /\ (forall s s'.{:pattern r s s'} r s s' ==> (
    head s == head s' /\ r (tail s) (tail s')
  )))
  (ensures s == s')
  =
  m_bisim (fun s s' -> r s s') s s'

let stream_cons (#a:Type) (hd:a) (tl:stream a) : stream a =
  // let f : m_type (stream_pf a) = fun _ -> tl in
  m_construct {node=hd; children = from_fun (fun _ -> tl)}

let stream_cons_head (#a:Type) (hd:a) (tl:stream a) :
  Lemma (ensures head (stream_cons hd tl) == hd)
  [SMTPat (head (stream_cons hd tl))] =
  m_dest_cons {node=hd; children= from_fun (fun _ -> tl)}

let stream_cons_tail (#a:Type) (hd:a) (tl:stream a) :
  Lemma (ensures tail (stream_cons hd tl) == tl)
  [SMTPat (tail (stream_cons hd tl))] =
  m_dest_cons {node=hd; children = from_fun (fun _ -> tl)}

let stream_head_tail_cons (#a:Type) (s:stream a) :
  Lemma (stream_cons (head s) (tail s) == s)
  [SMTPat (stream_cons (head s) (tail s))] =
  let s' = stream_cons (head s) (tail s) in
  assert(tail s' == tail s);
  assert(head s' == head s);
  stream_eq_thm s s'
