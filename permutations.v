Require Import Vector.
Require Import Strings.String.
Require Import Strings.Ascii.
Require Import Program.
Require Import alphabet.

(*
Theorem all_in_alphabet :
   forall (a : Alpha),
    VectorDef.In a alphabet.
Proof.
  intros a.
  unfold Alpha in *.
  repeat (dependent destruction a; try apply VectorDef.In_cons_hd; apply VectorDef.In_cons_tl).
Qed.
*)


Inductive NoDupVec {A : Type} : forall {n : nat}, Vec A n -> Prop :=
| NoDupVec_nil : NoDupVec (nil A)
| NoDupVec_cons : forall x m (v : Vec A m), ~ In x v -> NoDupVec v -> NoDupVec (cons _ x m v)
.


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


(*
Definition wf_permutation (perm : Vec Alpha 26) : Prop :=
  VectorDef.Forall (fun a => VectorDef.In a perm) alphabet.
*)

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


Theorem no_dup_alphabet :
  NoDupVec alphabet.
Proof.
  repeat (apply NoDupVec_cons; try (unfold not; intros H; apply (In_in_vector Fin.eq_dec) in H; simpl in H; inversion H)).
  apply NoDupVec_nil.
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
  inversion Hin.
  - reflexivity.
  - apply inj_pair2 in H2. subst.
    contradiction.
Qed.


Theorem Forall_In :
  forall {A n} (f : A -> Prop) (v : Vec A n),
    Forall f v ->
    (forall x, In x v -> f x).
Proof.  
  intros A n f v Hall x Hin.
  induction Hall.
  - inversion Hin.
  - inversion Hin.
    + assumption.
    + subst. apply inj_pair2 in H3. subst. auto.
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


Theorem in_swap :
  forall {A n x y1 y2} (v : Vec A n),
    In x (cons A y1 (S n) (cons A y2 n v)) ->
    In x (cons A y2 (S n) (cons A y1 n v)).
Proof.
  intros A n x y1 y2 v H.
  inversion H.
  - repeat constructor.
  - subst. apply inj_pair2 in H3. subst.
    inversion H2.
    + constructor.
    + subst. apply inj_pair2 in H4. subst.
      repeat constructor.
      assumption.
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
  - inversion Hin.
    + apply In_cons_hd.
    + subst. apply inj_pair2 in H2. subst. constructor. auto.
  - inversion Hin.
    + repeat constructor.
    + subst. apply inj_pair2 in H2. subst.
      apply in_swap.
      assumption.
  - auto.
Qed.



(*
Theorem no_dup_perm :
  forall {A n} (v1 v2 : Vec A n),
    NoDupVec v1 ->
    IsPermutation v1 v2 ->
    NoDupVec v2.
Proof.
  intros A n v1 v2 Hdup Hperm.
  induction Hperm.
  - assumption.
  - apply NoDupVec_cons. unfold not.
    intros H.

Qed.


Theorem wf_permutation_alphabet :
  forall perm,
    Forall (fun a => In a perm) alphabet ->
    wf_permutation perm.
Proof.
  intros perm H. unfold wf_permutation.
  inversion H.
  
Qed.

Theorem wf_permutation_alphabet :
  forall perm,
    wf_permutation perm ->
    Forall (fun a => In a perm) alphabet.
Proof.
  unfold wf_permutation.
  intros perm H.
  inversion H.
  
Qed.
*)