Require Import Vector.
Require Import Strings.String.
Require Import Strings.Ascii.
Require Import Coq.Setoids.Setoid.
Require Import Program.
Require Import alphabet.
Require Import utils.


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


Definition wf_permutation (perm : Vec Alpha 26) : Prop :=
  IsPermutation perm alphabet.


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
