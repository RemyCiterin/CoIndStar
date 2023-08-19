module Stream.IdxProof

open IdxPFunctor
open Stream.Core
open FStar.FunctionalExtensionality
open Utils


let stream_mul (s1 s2:stream int) : stream int =
  stream_corec (fun (s1, s2) -> (op_Multiply (head s1) (head s2), (tail s1, tail s2))) (s1, s2)

let stream_add (s1 s2:stream int) : stream int =
  stream_corec (fun (s1, s2) -> (head s1 + head s2, (tail s1, tail s2))) (s1, s2)



let stream_bellow_pf : idx_pf (stream int & stream int) =
  {
    command = (fun (s1, s2) -> squash(head s1 <= head s2));
    response = (fun (s1, s2) _ -> if head s1 = head s2 then unit else empty);
    next = (fun (s1, s2) _ _ -> (tail s1, tail s2))
  }

let stream_bellow (s1 s2:stream int) : Type =
  m_type stream_bellow_pf (s1, s2)

let stream_mul_bellow_thm (s:stream int) : stream_bellow s (stream_mul s s) =
  m_corec #_ #_ #_
    #(fun (s1, s2) -> squash (s2 == stream_mul s1 s1))
    (fun (s1, s2) _ ->
      let f (_:(if head s1 = head s2 then unit else empty)) :
        squash(tail s2 == stream_mul (tail s1) (tail s1)) = () in
      {node = (); children = on_dom _ f}
    ) ()

let stream_assoc_equals (s1 s2 s3:stream int) :
  m_equals
    (stream_add (stream_add s1 s2) s3)
    (stream_add s1 (stream_add s2 s3)) =
  let state (sl sr:stream int) =
    s:(stream int & stream int & stream int) {
      sr == stream_add s._1 (stream_add s._2 s._3) /\
      sl == stream_add (stream_add s._1 s._2) s._3
    }
  in

  m_corec #_ #_ #_
    #(fun (|_, (sl, sr)|) -> state sl sr)
    (fun (|_, (sl, sr)|) (s1, s2, s3) ->
      let f (_:unit) : (state (tail sl) (tail sr)) =
        (tail #int s1, tail #int s2, tail #int s3) in
      {node = (); children = on_dom _ f}
    )
    (s1, s2, s3)

