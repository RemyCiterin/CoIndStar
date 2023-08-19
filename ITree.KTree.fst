module ITree.KTree

open ITree.Basics
open ITree.Equiv
open ITree.Eutt
open ITree.MonadLaws
open ITree.StructuralLaws
open ITree.CongruenceLaws
open Equiv
open Paco

// definition of continuation tree following the description of the interaction tree paper
let ktree (e:Type -> Type) (a b:Type) : Type = a -> itree e b

let keutt (#e:Type -> Type) (#a #b #c:Type) (rel:b -> c -> prop) 
  : ktree e a b -> ktree e a c -> prop =
  fun k1 k2 -> forall x. eutt rel (k1 x) (k2 x)

let keq (#e:Type -> Type) (#a #b:Type) : ktree e a b -> ktree e a b -> prop =
  fun k1 k2 -> keutt (fun x y -> x == y) k1 k2

let keutt_monotone (#e:Type -> Type) (#a #b #c:Type) (rel1 rel2:b -> c -> prop) (k1:ktree e a b) (k2:ktree e a c) :
  Lemma (requires keutt rel1 k1 k2 /\ (forall x y. rel1 x y ==> rel2 x y)) (ensures keutt rel2 k1 k2) =
  Classical.forall_intro (
    fun x -> Classical.move_requires_2 (eutt_monotone rel1 rel2) (k1 x) (k2 x))

let ktree_cat (#e:Type -> Type) (#a #b #c:Type) :
  ktree e a b -> ktree e b c -> ktree e a c =
  fun h k x -> bind (h x) k

let (>>>) = ktree_cat

let ktree_id : (e:(Type -> Type)) -> (#a:Type) -> ktree e a a = ret

let ktree_tau (#e:Type -> Type) (#a #b:Type) (f:ktree e a b) : ktree e a b =
  fun x -> tau (f x)

let ktree_case (#e:Type -> Type) (#a #b #c:Type) : ktree e a c -> ktree e b c -> ktree e (sum a b) c =
  fun h k x -> match x with
  | Left  l -> h l
  | Right r -> k r

let ktree_inl (e:Type -> Type) (#a #b:Type) : ktree e a (sum a b) =
  fun x -> ret e (Left x)

let ktree_inr (e:Type -> Type) (#a #b:Type) : ktree e b (sum a b) =
  fun x -> ret e (Right x)

let ktree_pure (e:Type -> Type) (#a #b:Type) (f:a -> b) : ktree e a b =
  fun x -> ret e (f x)

// set of relation between ktree
let keq_id_cat (#e:Type -> Type) (#a #b:Type) (k:ktree e a b) :
  Lemma (keq (ktree_cat (ktree_id e) k) k) =
  let lemma (x:a) :
    Lemma (eutt (fun x y -> x == y) (ktree_cat (ktree_id e) k x) (k x)) =
    assert(ktree_cat (ktree_id e) k x == bind (ret e x) k);
    monad_law2 k x;
    eutt_refl (fun x y -> x == y) (k x)
  in

  Classical.forall_intro lemma

let keq_cat_id (#e:Type -> Type) (#a #b:Type) (k:ktree e a b) :
  Lemma (keq (ktree_cat k (ktree_id e)) k) =
  let lemma (x:a) :
    Lemma (eutt (fun x y -> x == y) (ktree_cat k (ktree_id e) x) (k x)) =
    monad_law1 (k x);
    eutt_refl (fun x y -> x == y) (k x)
  in

  Classical.forall_intro lemma

let keq_cat_cat (#e:Type -> Type) (#a #b #c #d:Type) (i:ktree e a b) (j:ktree e b c) (k:ktree e c d) :
  Lemma (keq (ktree_cat i (ktree_cat j k)) (ktree_cat (ktree_cat i j) k)) =
  let lemma (x:a) :
    Lemma (eutt (fun x y -> x == y) (ktree_cat i (ktree_cat j k) x) (ktree_cat (ktree_cat i j) k x)) =
    assert(ktree_cat i (ktree_cat j k) x == bind (i x) (ktree_cat j k));
    assert(ktree_cat (ktree_cat i j) k x == bind (bind (i x) j) k);
    bind_extensionality (i x) (ktree_cat j k) (fun x -> bind (j x) k);
    monad_law3 (i x) j k;
    eutt_refl (fun x y -> x == y) (bind (bind (i x) j) k)
  in

  Classical.forall_intro lemma

let keq_pure_pure (#e:Type -> Type) (#a #b #c:Type) (f:a -> b) (g:b -> c) :
  Lemma (keq (ktree_cat (ktree_pure e f) (ktree_pure e g)) (ktree_pure e #a #c (fun x -> g (f x)))) =
  let lemma (x:a) :
    Lemma (eutt (fun x y -> x == y) (ktree_cat (ktree_pure e f) (ktree_pure e g) x) (ktree_pure e (fun x -> g (f x)) x))
    = assert(ktree_cat (ktree_pure e f) (ktree_pure e g) x == bind (ret e (f x)) (ktree_pure e g));
    assert(ktree_pure e (fun x -> g (f x)) x == ret e (g (f x)));
    monad_law2 (ktree_pure e g) (f x);
    eutt_refl (fun x y -> x == y) (ret e (g (f x)))
  in

  Classical.forall_intro lemma

let keq_inl_case (#e:Type -> Type) (#a #b #c:Type) (h:ktree e a c) (k:ktree e b c) :
  Lemma (keq (ktree_cat (ktree_inl e) (ktree_case h k)) h) =
  let lemma (x:a) :
    Lemma (eutt (fun x y -> x == y) (ktree_cat (ktree_inl e) (ktree_case h k) x) (h x)) =
    assert(ktree_cat (ktree_inl e) (ktree_case h k) x == bind (ret e (Left x)) (ktree_case h k));
    monad_law2 (ktree_case h k) (Left x);
    eutt_refl (fun x y -> x == y) (h x)
  in

  Classical.forall_intro lemma

let keq_inr_case (#e:Type -> Type) (#a #b #c:Type) (h:ktree e a c) (k:ktree e b c) :
  Lemma (keq (ktree_cat (ktree_inr e) (ktree_case h k)) k) =
  let lemma (x:b) :
    Lemma (eutt (fun x y -> x == y) (ktree_cat (ktree_inr e) (ktree_case h k) x) (k x)) =
    assert(ktree_cat (ktree_inr e) (ktree_case h k) x == bind (ret e (Right x)) (ktree_case h k));
    monad_law2 (ktree_case h k) (Right x);
    eutt_refl (fun x y -> x == y) (k x)
  in

  Classical.forall_intro lemma


let keutt_case_congr (#e:Type -> Type) (#a #b #c #d:Type) (rel:c -> d -> prop) 
  (f:ktree e (sum a b) c) (h:ktree e a d) (k:ktree e b d) :
  Lemma 
    (requires keutt rel (ktree_cat (ktree_inl e) f) h /\ keutt rel (ktree_cat (ktree_inr e) f) k)
    (ensures keutt rel f (ktree_case h k)) =
  let lemma (x:sum a b) :
    Lemma (eutt rel (f x) (ktree_case h k x)) =
    match x with
    | Left  l ->
      assert(eutt rel (bind (ret e (Left l)) f) (h l));
      monad_law2 f (Left l);
      eutt_refl (fun x y -> x == y) (f (Left l));
      eutt_trans (fun x y -> x == y) rel (f (Left l)) (bind (ret e (Left l)) f) (h l);
      eutt_monotone (compose_binrel (fun x y -> x == y) rel) rel (f (Left l)) (h l)
    | Right r ->
      monad_law2 f (Right r);
      eutt_refl (fun x y -> x == y) (f (Right r));
      eutt_trans (fun x y -> x == y) rel (f (Right r)) (bind (ret e (Right r)) f) (k r);
      eutt_monotone (compose_binrel (fun x y -> x == y) rel) rel (f (Right r)) (k r)
  in
  Classical.forall_intro lemma

let keutt_left_cat (#e:Type -> Type) (#a #b #c:Type) (rel:b -> c -> prop) (f:ktree e a b) (g:ktree e a c) 
  (lemma: (h:ktree e a a) -> 
    Lemma (ensures keutt rel (ktree_cat h f) (ktree_cat h g))
  ) : Lemma (ensures keutt rel f g) =
  let aux (x:a) :
    Lemma (eutt rel (f x) (g x)) =
    lemma (fun x -> ret e x);
    monad_law2 f x;
    monad_law2 g x
  in
  Classical.forall_intro aux

let keutt_refl (#e:Type -> Type) (#a #b:Type) (rel:b -> b -> prop) (k:ktree e a b) :
  Lemma (requires reflexivity rel) (ensures keutt rel k k) =
  let lemma (x:a) : 
    Lemma (eutt rel (k x) (k x)) =
    eutt_refl rel (k x)
  in
  Classical.forall_intro lemma

let keq_refl (#e:Type -> Type) (#a #b:Type) (t:ktree e a b) :
  Lemma (keq t t) =
  keutt_refl (fun x y -> x == y) t

let keutt_from_keq (#e:Type -> Type) (#a #b:Type) (rel:b -> b -> prop) (t t':ktree e a b) :
  Lemma (requires keq t t' /\ reflexivity rel)
    (ensures keutt rel t t') =
  keutt_monotone (fun x y -> x == y) rel t t'
    

let keutt_symm (#e:Type -> Type) (#a #b #c:Type) (rel:c -> b -> prop) (k:ktree e a b) (k':ktree e a c) :
  Lemma (requires keutt rel k' k) (ensures keutt (inverse_binrel rel) k k') =
  let lemma (x:a) :
    Lemma (eutt (inverse_binrel rel) (k x) (k' x)) =
    eutt_symm rel (k x) (k' x)
  in
  Classical.forall_intro lemma

let keq_symm (#e:Type -> Type) (#a #b:Type) (k k':ktree e a b) :
  Lemma (requires keq k' k) (ensures keq k k') =
  keutt_symm (fun x y -> x == y) k k';
  keutt_monotone (inverse_binrel (fun x y -> x == y)) (fun x y -> x == y) k k'

let keutt_trans (#e:Type -> Type) (#a #b #c #d:Type)
  (rel1: b -> c -> prop) (rel2: c -> d -> prop)
  (h:ktree e a b) (k:ktree e a c) (l:ktree e a d) :
  Lemma (requires keutt rel1 h k /\ keutt rel2 k l) (ensures keutt (compose_binrel rel1 rel2) h l) =
  let lemma (x:a) :
    Lemma (eutt (compose_binrel rel1 rel2) (h x) (l x)) =
    eutt_trans rel1 rel2 (h x) (k x) (l x)
  in
  Classical.forall_intro lemma

let keq_trans (#e:Type -> Type) (#a #b:Type) (h k l:ktree e a b) :
  Lemma (requires keq h k /\ keq k l) (ensures keq h l) =
  keutt_trans (fun x y -> x == y) (fun x y -> x == y) h k l;
  keutt_monotone (compose_binrel (fun x y -> x == y) (fun x y -> x == y)) (fun x y -> x == y) h l


let keq_congr (#e:Type -> Type) (#a #b #c:Type) (h h':ktree e a b) (k k':ktree e b c) :
  Lemma (requires keq h h' /\ keq k k') (ensures keq (ktree_cat h k) (ktree_cat h' k')) =
  let lemma (x:a) :
    Lemma (eutt (fun x y -> x == y) (ktree_cat h k x) (ktree_cat h' k' x)) =
    congruence_law_3 (fun x y -> x == y) (fun x y -> x == y) (h x) (h' x) k k'
  in
  Classical.forall_intro lemma

let keq_tau (#e:Type -> Type) (#a #b:Type) (t:ktree e a b) :
  Lemma (keq t (ktree_tau t) /\ keq (ktree_tau t) t) =
  let lemma (x:a) :
    Lemma (eutt (fun x y -> x == y) (t x) (ktree_tau t x)) =
    structural_law1 (fun x y -> x == y) (t x)
  in
  Classical.forall_intro lemma;
  keq_symm (ktree_tau t) t

let keutt_add_tau (#e:Type -> Type) (#a #b #c:Type) (rel:b -> c -> prop) (t:ktree e a b) (t':ktree e a c) :
  Lemma
    (requires keutt rel t t')
    (ensures 
      (keutt rel (ktree_tau t) t') /\
      (keutt rel t (ktree_tau t'))
    ) =
  keq_tau t';
  keq_tau t;

  keutt_trans (fun x y -> x == y) rel (ktree_tau t) t t';
  keutt_monotone (compose_binrel (fun x y -> x == y) rel) rel (ktree_tau t) t';

  keutt_trans rel (fun x y -> x == y) t t' (ktree_tau t');
  keutt_monotone (compose_binrel rel (fun x y -> x == y)) rel t (ktree_tau t')

let keutt_remove_tau_left (#e:Type -> Type) (#a #b #c:Type) (rel:b -> c -> prop) (t:ktree e a b) (t':ktree e a c) :
  Lemma
    (requires keutt rel (ktree_tau t) t')
    (ensures keutt rel t t') =
  keq_tau t;
  keutt_trans (fun x y -> x == y) rel t (ktree_tau t) t';
  keutt_monotone (compose_binrel (fun x y -> x == y) rel) rel t t'

let keutt_remove_tau_right (#e:Type -> Type) (#a #b #c:Type) (rel:b -> c -> prop) (t:ktree e a b) (t':ktree e a c) :
  Lemma
    (requires keutt rel t (ktree_tau t'))
    (ensures keutt rel t t') =
  keq_tau t';
  keutt_trans rel (fun x y -> x == y) t (ktree_tau t') t';
  keutt_monotone (compose_binrel rel (fun x y -> x == y)) rel t t'
  
