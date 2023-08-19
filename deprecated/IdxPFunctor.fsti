module IdxPFunctor

open FStar.FunctionalExtensionality

noeq type idx_pf (output:Type) : Type = {
  command: output -> Type;
  response: (o:output) -> command o -> Type;
  next: (o:output) -> (c:command o) -> response o c -> output;
}

let idx_apply_ch_out (#output:Type) (p:idx_pf output) (o:output)
  (ty:output -> Type) (node:p.command o) (r:p.response o node) : Type
  = ty (p.next o node r)

unopteq type idx_apply (#output:Type) (p:idx_pf output) (o:output) (ty:output -> Type) : Type = 
  {
    node: p.command o;
    children: restricted_t (p.response o node) (idx_apply_ch_out p o ty node);
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

let map (#output:Type) (#a #b:output->Type) (#p:idx_pf output) (#o:output)
  (f:(o:output) -> a o -> b o) (ia:idx_apply p o a) : idx_apply p o b =
  {
    node = ia.node;
    children = on_dom _ (fun x -> f _ (ia.children x))
  }
// 3 2 1 2
// 2 1 1 3
val m_type (#output:Type) (p:idx_pf u#a u#b u#b output) :  (output ^-> Type u#b)


val m_destruct (#output:Type) (#p:idx_pf output) (#o:output) :
  m_type p o -> idx_apply p o (m_type p)


val m_corec (#output:Type) (#p:idx_pf output) (#o:output)
  (#state:output -> Type) (f: (o:output) -> state o -> idx_apply p o state) (x:state o)
  : m_type p o

val m_destruct_corec_thm (#output:Type) (#p:idx_pf output) (#o:output)
  (#state:output -> Type) (f:(o:output) -> state o -> idx_apply p o state) (x:state o) :
  Lemma
    (ensures m_destruct (m_corec f x) == map (fun o -> m_corec #output #p #o f) (f o x))
  [SMTPat (m_destruct (m_corec f x))]

val m_bisim_thm (#output:Type) (#p:idx_pf output) (#o:output) (r:(o:output) -> m_type p o -> m_type p o -> prop)
  (m m':m_type p o) :
  Lemma (requires r o m m' /\ (forall o x y. r o x y ==> (
    (m_destruct x).node == (m_destruct y).node /\ (forall arg.
      r _ ((m_destruct x).children arg) ((m_destruct y).children arg)
  ))))
  (ensures m == m')
