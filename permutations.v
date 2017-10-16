Require Import Vector.
Require Import Strings.String.
Require Import Strings.Ascii.
Require Import Coq.Setoids.Setoid.
Require Import Program.
Require Import alphabet.
Require Import utils.
Require Import Omega.


Inductive NoDupVec {A : Type} : forall {n : nat}, Vec A n -> Prop :=
| NoDupVec_nil : NoDupVec (nil A)
| NoDupVec_cons : forall x m (v : Vec A m), ~ In x v -> NoDupVec v -> NoDupVec (cons _ x m v).


Definition summary := Vec nat 26.


Definition empty_summary : summary :=
  Vector.const 0 26.


Definition increment_summary (a : Alpha) (s : summary) : summary :=
  let v := S (nth s a) in replace s a v.


Fixpoint summarize_vec {n : nat} (v : Vec Alpha n) : summary :=
  match v with
  | nil _ => empty_summary
  | cons _ a n' t => increment_summary a (summarize_vec t)
  end.


Theorem summarize_nil :
  summarize_vec (nil _) = empty_summary.
Proof.
  reflexivity.
Qed.


Theorem nth_cons :
  forall {A n k e x} (v : Vec A n),
    nth v k = e ->
    nth (cons A x n v) (Fin.FS k) = e.
Proof.
  auto.
Qed.


Theorem nth_cons' :
  forall {A n k x} (v : Vec A n),
    nth (cons A x n v) (Fin.FS k) = nth v k.
Proof.
  auto.
Qed.


Theorem replace_replaces :
  forall {A n k e} (v : Vec A n),
    nth (replace v k e) k = e.
Proof.
  intros A n k e v. induction v.
  - inversion k.
  - dependent destruction k.
    + reflexivity.
    + simpl. auto.
Qed.


Theorem nth_replace :
  forall {A n j k e} (v : Vec A n),
    j <> k ->
    nth (replace v j e) k = nth v k.
Proof.
  intros A n j k. induction v.
  - inversion j.
  - dependent destruction k.
    + dependent destruction j.
      * contradiction.
      * reflexivity.
    + dependent destruction j.
      * reflexivity.
      * intros. simpl. apply IHv.
        unfold not in *. intros Hjk.
        apply H. rewrite Hjk. reflexivity.
Qed.


Theorem increment_summary_increments :
  forall {k j} (s : summary),
    nth s k = j ->
    nth (increment_summary k s) k = S j.
Proof.
  intros k j s H.
  unfold increment_summary.
  rewrite replace_replaces.
  auto.
Qed.


Theorem increment_summary_increments' :
  forall {k} (s : summary),
    nth (increment_summary k s) k = S (nth s k).
Proof.
  intros k s.
  erewrite increment_summary_increments; reflexivity.
Qed.


Theorem summarize_empty :
  forall k,
    nth empty_summary k = 0.
Proof.
  intros k.
  unfold empty_summary.
  apply const_nth.
Qed.


Theorem increment_summary_greater :
  forall {x k j} (s : summary),
    nth s k = j ->
    nth (increment_summary x s) k >= j.
Proof.
  intros x k j s.
  unfold increment_summary.
  intros Hnth.
  destruct (Fin.eq_dec x k).
  - rewrite e. rewrite replace_replaces.
    subst. auto.
  - rewrite nth_replace. rewrite Hnth.
    + auto.
    + assumption.
Qed.


Theorem increment_summary_greater_greater :
  forall {x k j} (s : summary),
    nth s k >= j ->
    nth (increment_summary x s) k >= j.
Proof.
  intros x k j s.
  unfold increment_summary.
  intros Hnth.
  destruct (Fin.eq_dec x k).
  - rewrite e. rewrite replace_replaces.
    subst. auto.
  - rewrite nth_replace; auto.
Qed.


Theorem increment_summary_neq :
  forall {x k} (s : summary),
    x <> k ->
    nth (increment_summary x s) k = nth s k.
Proof.
  intros x k s H.
  unfold increment_summary.
  apply nth_replace.
  assumption.
Qed.


Theorem summarize_cons :
  forall {k n j} x (v : Vec Alpha n),
    nth (summarize_vec v) k = j ->
    nth (summarize_vec (cons _ x n v)) k >= j.
Proof.
  intros k n j x v H.
  simpl. apply increment_summary_greater.
  assumption.
Qed.


Theorem in_summarize :
  forall {k n} (v : Vec Alpha n),
    nth (summarize_vec v) k > 0 ->
    In k v.
Proof.
  intros k n v H.
  generalize dependent k.
  induction v.
  - intros k H.
    pose proof summarize_nil. rewrite H0 in H.
    pose proof summarize_empty. rewrite H1 in H. inversion H.
  - simpl. intros k H.
    destruct (Fin.eq_dec h k); subst; constructor.
    rewrite increment_summary_neq in H; auto.
Qed.


Theorem summarize_in :
  forall {k n} (v : Vec Alpha n),
    In k v ->
    nth (summarize_vec v) k > 0.
Proof.
  intros k n v H.
  generalize dependent k.
  induction v.
  - intros k H. inversion H.
  - simpl. intros k H.
    destruct (Fin.eq_dec h k); subst.
    + rewrite increment_summary_increments'. apply Gt.gt_Sn_O.
    + invert_existT H; try contradiction.
      apply IHv in H2.
      inversion H2; apply increment_summary_greater_greater; auto.
Qed.


Theorem summarize_alphabet :
  summarize_vec alphabet = Vector.const 1 26.
Proof.
  reflexivity.
Qed.


Theorem all_in_alphabet :
   forall (a : Alpha),
    In a alphabet.
Proof.
  intros a.
  apply in_summarize.
  rewrite summarize_alphabet.
  rewrite const_nth. auto.
Qed.


Theorem vec_0_is_nil :
  forall {A} (v : Vec A 0),
    v = nil A.
Proof.
  intros A v. unfold Vec in *.
  refine (match v with
          | nil _ => _
          | cons _ x _ v => _
          end).
  reflexivity.
  apply idProp.
Qed.


Theorem Forall_nth :
  forall {A n} (P : A -> Prop) (v : Vec A n),
    Forall P v <->
    forall k, P (nth v k).
Proof.
  intros A n P v.
  split; intros H.
  - intros k. induction H.
    + inversion k.
    + dependent induction k; simpl; auto.
  - induction v; constructor.
    + apply (H Fin.F1).
    + apply IHv. intros k.
      pose proof (H (Fin.FS k)) as Hnth.
      rewrite nth_cons' in Hnth.
      apply Hnth.
Qed.


Theorem no_dup_summary :
  forall h (s : summary),
    Forall (fun n : nat => n < 2) (increment_summary h s) ->
    Forall (fun n : nat => n < 2) s.
Proof.
  intros h s H. unfold summary in *. unfold Vec in *.
  unfold Alpha in *. unfold Fin in *.
  rewrite Forall_nth in H.
  rewrite Forall_nth.
  intros k.
  pose proof (H k) as Hk.
  destruct (Fin.eq_dec h k).
  - subst.
    rewrite increment_summary_increments' in Hk.
    apply PeanoNat.Nat.lt_succ_l in Hk. auto.
  - pose proof(increment_summary_neq s n) as Hnth.
    rewrite <- Hnth. auto.
Qed.


Theorem no_dup_summary_nth :
  forall {n h} (v : Vec Alpha n),
    Forall (fun n : nat => n < 2) (increment_summary h (summarize_vec v)) ->
    nth (summarize_vec (cons _ h _ v)) h < 2.
Proof.
  intros n h v H.
  simpl.
  rewrite Forall_nth in H.
  apply H.
Qed.


Theorem no_dup_summarize :
  forall {n} (v : Vec Alpha n),
    Forall (fun n => n < 2) (summarize_vec v) ->
    NoDupVec v.
Proof.
  intros n v H.
  induction v; simpl in *; constructor.
  - unfold not. intros Hin.
    apply summarize_in in Hin.

    pose proof H as Hnth.
    apply no_dup_summary_nth in Hnth.
    simpl in Hnth.
    rewrite increment_summary_increments' in Hnth.
    apply Lt.lt_S_n in Hnth. 
    apply NPeano.Nat.lt_1_r in Hnth.
    rewrite Hnth in Hin.
    inversion Hin.
  - apply IHv. eauto using no_dup_summary.
Qed.


Theorem no_dup_alphabet' :
  NoDupVec alphabet.
Proof.
  apply no_dup_summarize.
  apply Forall_nth.
  intros k.

  rewrite summarize_alphabet.
  rewrite const_nth.

  auto.
Qed.


Fixpoint in_vector {A : Type} {n : nat} (decA : forall x y : A, {x = y} + {x <> y}) (a : A) (v : Vec A n) : bool :=
  match v with
  | nil _ => false
  | cons _ x n t =>
    if decA a x
    then true
    else in_vector decA a t
  end.


Theorem In_in_vector :
  forall {n : nat} {A : Type} (decA : forall x y : A, {x = y} + {x <> y}) (a : A) (v : Vec A n),
    In a v -> in_vector decA a v = true.
Proof.
  intros n A decA a v H.
  induction H; simpl; destruct decA; try reflexivity; auto.
Qed.


Theorem in_vector_In :
  forall {n : nat} {A : Type} (decA : forall x y : A, {x = y} + {x <> y}) (a : A) (v : Vec A n),
    in_vector decA a v = true -> In a v.
Proof.
  intros n A decA a v H.
  induction v.
  - simpl in H. inversion H.
  - simpl in *. destruct (decA a h) eqn:HdecA.
    + destruct HdecA. subst. apply In_cons_hd.
    + apply In_cons_tl. auto.
Qed.


Inductive IsPermutation {A} : forall {n}, Vec A n -> Vec A n -> Prop :=
| permNil : IsPermutation (nil _) (nil _)
| permSkip : forall {x m} (v1 : Vec A m) (v2 : Vec A m),
    IsPermutation v1 v2 -> IsPermutation (cons _ x m v1) (cons _ x m v2)
| permSwap : forall {x y m} (v : Vec A m),
    IsPermutation (cons _ x (S m) (cons _ y _ v))
                  (cons _ y (S m) (cons _ x _ v))
| permTrans : forall {m} (v1 : Vec A m) (v2 : Vec A m) (v3 : Vec A m),
    IsPermutation v1 v2 -> IsPermutation v2 v3 -> IsPermutation v1 v3
.


Lemma incremented_summary_not_empty :
  forall h (s : summary),
    increment_summary h s <> empty_summary.
Proof.
  unfold not.
  intros h s H.
  pose proof eq_nth_iff nat 26.
  rewrite <- H0 in H.
  pose proof (H h h). rewrite increment_summary_increments' in H1. unfold empty_summary in H1.
  rewrite const_nth in H1.
  assert (h=h) by reflexivity.
  apply H1 in H2.
  inversion H2.
Qed.


Lemma summarize_empty_is_nil :
  forall {n} (v : Vec Alpha n),
    summarize_vec v = empty_summary ->
    n = 0.
Proof.
  intros n v H. induction v; trivial.
  simpl in *.
  pose proof (incremented_summary_not_empty h (summarize_vec v)).
  contradiction.
Qed.


Lemma increment_same :
  forall h s1 s2,
    increment_summary h s1 = increment_summary h s2 ->
    s1 = s2.
Proof.
  intros h s1 s2 H.

  apply eq_nth_iff.
  intros x' x Hpp. subst.

  pose proof H as Hnth.
  apply (f_equal (fun s => nth s x)) in Hnth.

  destruct (Fin.eq_dec h x).
  - subst.
    repeat rewrite increment_summary_increments' in Hnth.
    inversion Hnth.
    reflexivity.
  - repeat (rewrite increment_summary_neq in Hnth; try assumption).
Qed.


Fixpoint summary_total {n} (s : Vec nat n) : nat :=
  match s with
  | nil _ => 0
  | cons _ h _ s' => h + summary_total s'
  end.


Fixpoint cons_rep {A n} (a : A) (k : nat) (v : Vec A n) : Vec A (k + n) :=
  match k with
  | 0 => v
  | S k' => cons _ a (k' + n) (cons_rep a k' v)
  end.


Fixpoint summary_to_vector_helper {n} (a : Alpha) (s : Vec nat n) : Vec Alpha (summary_total s) :=
  match s as s' return (Vec Alpha (summary_total s')) with
  | nil _ => nil _
  | cons _ h _ t => cons_rep a h (summary_to_vector_helper (step_fin a) t)
  end.


Definition summary_to_vector {n} (s : Vec nat n) : Vec Alpha (summary_total s) := summary_to_vector_helper Fin.F1 s.


Lemma summary_total_replace :
  forall {n h} (v : Vec nat n),
    summary_total (replace v h (S (nth v h))) = S (summary_total v).
Proof.
  intros n h v.
  induction v as [| x n' v].
  - inversion h.
  - refine (match h as h' in Fin.t n
                  return forall pf : n = S n',
                         eq_rect n Fin h' (S n') pf = h ->
                         summary_total (replace (VectorDef.cons nat x n' v) h (S (nth (VectorDef.cons nat x n' v) h))) = S (summary_total (VectorDef.cons nat x n' v)) with
            | Fin.F1 => _
            | Fin.FS h' => _
            end eq_refl eq_refl); intros pf H; inversion pf; subst; repeat rewrite <- Eqdep_dec.eq_rect_eq_dec by apply eq_nat_dec; simpl.
    + reflexivity.
    + rewrite IHv. rewrite plus_n_Sm.
      reflexivity.
Qed.


Lemma increment_summary_total :
  forall {h} (s : summary),
    summary_total (increment_summary h s) = S (summary_total s).
Proof.
  intros h s.
  apply summary_total_replace.
Qed.


Lemma summarize_same_length :
  forall {n} (v : Vec Alpha n),
    summary_total (summarize_vec v) = n.
Proof.
  intros n v.
  induction v.
  - reflexivity.
  - simpl. rewrite increment_summary_total. rewrite IHv.
    reflexivity.
Qed.


Definition summarize_and_back {n} (v : Vec Alpha n) : Vec Alpha n.
  pose proof summary_to_vector (summarize_vec v).
  rewrite summarize_same_length in H.
  apply H.
Defined.


Lemma summarize_and_back_nil :
  summarize_and_back (nil _) = nil _.
Proof.
  unfold summarize_and_back. simpl.
  unfold eq_rec.
  rewrite <- Eqdep_dec.eq_rect_eq_dec by apply eq_nat_dec.
  reflexivity.
Qed.


(*
I have:

H: summary_total (increment_summary h empty_summary) = 1


Goal:

eq_rect (summary_total (increment_summary h empty_summary)) (fun n : nat => Vec Alpha n)
    (summary_to_vector (increment_summary h empty_summary)) 1
    (summarize_same_length (cons (Fin 26) h 0 (nil (Fin 26))))

Why can't I rewrite using H in the goal?

eq_rect : forall {A : Type} (x : A) (P : A -> Type) (f : P x) (y : A) (e : x = y)

In this case.... eq_rect x P f y e

x = (summary_total (increment_summary h empty_summary))
P = (fun n : nat => Vec Alpha n)
f = (summary_to_vector (increment_summary h empty_summary))
y = 1
e = (summarize_same_length (cons (Fin 26) h 0 (nil (Fin 26))))

summarize_same_length : forall {n : nat} (v : Vec (Fin.t 26) n), summary_total (summarize_vec v) = n
 *)

Lemma summarize_and_back_one :
  forall h,
    summarize_and_back (cons _ h _ (nil _)) = cons _ h _ (nil _).
Proof.
  intros h.
  unfold Alpha in *.
  dependent destruction h. compute. reflexivity.
  
  unfold summarize_and_back. simpl.
  pose proof @increment_summary_total h empty_summary.
  rewrite EqdepFacts.eq_sig_snd.
  
  unfold summarize_same_length.
  unfold eq_rect. simpl.
  
Qed.

Print summarize_and_back_one.

Lemma bleh :
  forall h n v,
    IsPermutation (cons Alpha h n (summarize_and_back v)) (summarize_and_back (VectorDef.cons Alpha h n v)).
Proof.
  intros h n v.
  induction v.
  - rewrite summarize_and_back_nil.
    unfold summarize_and_back. simpl.

Qed.


Lemma summary_is_perm :
  forall {n} (v : Vec Alpha n),
    IsPermutation v (summarize_and_back v).
Proof.
  intros n v.
  induction v.
  - unfold summarize_and_back. simpl. rewrite <- eq_rec_eq. constructor.
  - econstructor.
    + constructor. apply IHv.
    + 
                    
Qed.


(*
Lemma permutation_extract :
  forall {n} h (v : Vec Alpha (S n)),
    In h v ->
    exists v', IsPermutation (cons _ h n v') v.
Proof.
  dependent destruction v.
  intros H.
  destruct (Fin.eq_dec h h0).
  - subst.
    

Qed.
*)

(*
  by induction on v1...

  If v1 is nil, then v2 must also be nil, since the have the same length. Thus
  the condition holds, since IsPermutation nil nil is true.

  Then we assume it works for some v1, and we want to show that it works for some
  (h :: v1).

  Thus we have summarize_vec (h :: v1) = summarize_vec v2, and
  forall v2, summarize_vec v1 = summarize_vec v2 -> IsPermutation v1 v2

  We want to show that:

  IsPermutation (h :: v1) v2.

  If we destruct v2, then we can have

  IsPermutation (h :: v1) (h :: v2') which is just

  IsPermutation v1 v2', so we can apply the induction hypothesis, and
  then see that if we incremented h for the summary of v1 and v2 you
  would get the same thing.

  However, when you have x <> h...

  IsPermutation (h :: v1) (x :: v2')

  is much more difficult to show, since there isn't a constructor for
  IsPermutation which immediately applies.

  We want to show that h is in v2 (which is clear because v2's summary
  equals h::v1's summary, which means h is in v2). And then knowing that we want to say that...

  IsPermutation (h :: v2') v2

  for some v2'
*)
Theorem summarize_permutation :
  forall {n} (v1 v2 : Vec Alpha n),
    summarize_vec v1 = summarize_vec v2 ->
    IsPermutation v1 v2.
Proof.
  intros n v1 v2 H.
  econstructor.
  induction v1.
  - simpl in H. pose proof vec_0_is_nil v2. subst.
    constructor.
  - simpl in H. dependent destruction v2. simpl in *.
    induction (Fin.eq_dec h0 h).
    + subst. constructor. apply IHv1.
      apply (increment_same h). assumption.
    + subst.

Qed.


Definition wf_permutation (perm : Vec Alpha 26) : Prop :=
  IsPermutation perm alphabet.


Theorem Forall_hd :
  forall {A n h} (f : A -> Prop) (v : Vec A n),
    Forall f (cons _ h n v) ->
    f h.
Proof.
  intros A n h f v H.
  inversion H. assumption.
Qed.


Theorem In_not_in_tl :
  forall {A n x h} (v : Vec A n),
    In x (cons _ h n v) ->
    not (In x v) ->
    x = h.
Proof.
  intros A n x h v Hin Hnin.
  invert_existT Hin.
  - reflexivity.
  - contradiction.
Qed.


Theorem Forall_In :
  forall {A n} (f : A -> Prop) (v : Vec A n),
    Forall f v ->
    (forall x, In x v -> f x).
Proof.  
  intros A n f v Hall x Hin.
  induction Hall.
  - inversion Hin.
  - invert_existT Hin; auto.
Qed.


Theorem In_Forall :
  forall {A n} (f : A -> Prop) (v : Vec A n),
    (forall x, In x v -> f x) ->
    Forall f v.
Proof.
  intros A n f v.
  induction v.
  - intros x. constructor.
  - intros H. constructor.
    + apply H. constructor.
    + apply IHv. intros x Hin.
      apply H. constructor.
      assumption.
Qed.


Theorem Forall_tl :
  forall {A n x} (f : A -> Prop) (v : Vec A n),
    Forall f (cons A x n v) ->
    Forall f v.
Proof.
  intros A n x f v H.
  apply In_Forall.
  pose proof Forall_In f (cons A x n v).
  intros x0 H1.
  apply H0.
  assumption.
  constructor.
  assumption.
Qed.


Theorem forall_perm :
  forall {A n} (f : A -> Prop) (v1 v2 : Vec A n),
    Forall f v1 ->
    IsPermutation v1 v2 ->
    Forall f v2.
Proof.
  intros A n f v1 v2 Hall Hperm.
  induction Hperm.
  - constructor.
  - constructor.
    + inversion Hall; assumption.
    + apply IHHperm. apply Forall_tl in Hall. assumption.
  - constructor.
    + apply Forall_tl in Hall. inversion Hall; assumption.
    + constructor.
      * inversion Hall; assumption.
      * repeat apply Forall_tl in Hall. assumption.
  - auto.
Qed.    


Theorem in_cons_swap :
  forall {A n x y1 y2} (v : Vec A n),
    In x (cons A y1 (S n) (cons A y2 n v)) ->
    In x (cons A y2 (S n) (cons A y1 n v)).
Proof.
  intros A n x y1 y2 v H.
  invert_existT H.
  - repeat constructor.
  - invert_existT H2; repeat constructor; auto.
Qed.


Theorem not_in_swap :
  forall {A n x y} (v : Vec A n),
    NoDupVec (cons A y n v) ->
    ~ In x (cons A y n v) ->
    ~ In y (cons A x n v).
Proof.
  unfold not.
  intros A n x y v Hdup Hxy Hyx.
  invert_existT Hyx.
  - contradiction.
  - invert_existT Hdup. contradiction.
Qed.

v
Theorem in_perm :
  forall {A n x} (v1 v2 : Vec A n),
    In x v1 ->
    IsPermutation v1 v2 ->
    In x v2.
Proof.
  intros A n x v1 v2 Hin Hperm.
  induction Hperm.
  - assumption.
  - invert_existT Hin; constructor; auto.
  - invert_existT Hin.
    + repeat constructor.
    + apply in_cons_swap. assumption.
  - auto.
Qed.


Theorem not_in_perm :
  forall {A n x} (v1 v2 : Vec A n),
    ~ In x v1 ->
    IsPermutation v1 v2 ->
    ~ In x v2.
Proof.
  unfold not.
  intros A n x v1 v2 Hnin Hperm Hin.
  induction Hperm; auto.
  - invert_existT Hin.
    + apply Hnin. constructor.
    + apply IHHperm; auto.
      intros. apply Hnin.
      constructor. apply H.
  - invert_existT Hin; apply Hnin; apply in_cons_swap; auto.
Qed.


Theorem NoDupVec_weaken :
  forall {A n x} (v : Vec A n),
    NoDupVec (cons A x n v) ->
    NoDupVec v.
Proof.
  intros A n x v H; invert_existT H; assumption.
Qed.


Theorem no_dup_perm :
  forall {A n} (v1 v2 : Vec A n),
    NoDupVec v1 ->
    IsPermutation v1 v2 ->
    NoDupVec v2.
Proof.
  intros A n v1 v2 Hdup Hperm.
  induction Hperm.
  - constructor.
  - invert_existT Hdup.
    constructor; pose proof not_in_perm v1 v2 H2; auto.
  - invert_existT Hdup.
    constructor.
    + apply not_in_swap; assumption.
    + apply NoDupVec_weaken in H3.
      constructor.
      * unfold not in *. intros. apply H2.
        constructor. assumption.
      * assumption.
  - auto.
Qed.
