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
| NoDupVec_nil : NoDupVec (VectorDef.nil A)
| NoDupVec_cons : forall x m (v : Vec A m), ~ VectorDef.In x v -> NoDupVec v -> NoDupVec (VectorDef.cons _ x m v)
.


Fixpoint in_vector {A : Type} {n : nat} (decA : forall x y : A, {x = y} + {x <> y}) (a : A) (v : Vec A n) : bool :=
  match v with
  | VectorDef.nil _ => false
  | VectorDef.cons _ x n t =>
    if decA a x
    then true
    else in_vector decA a t
  end.


Theorem In_in_vector :
  forall {n : nat} {A : Type} (decA : forall x y : A, {x = y} + {x <> y}) (a : A) (v : Vec A n),
    VectorDef.In a v -> in_vector decA a v = true.
Proof.
  intros n A decA a v H.
  induction H; simpl; destruct decA; try reflexivity; auto.
Qed.


Theorem in_vector_In :
  forall {n : nat} {A : Type} (decA : forall x y : A, {x = y} + {x <> y}) (a : A) (v : Vec A n),
    in_vector decA a v = true -> VectorDef.In a v.
Proof.
  intros n A decA a v H.
  induction v.
  - simpl in H. inversion H.
  - simpl in *. destruct (decA a h) eqn:HdecA.
    + destruct HdecA. subst. apply VectorDef.In_cons_hd.
    + apply VectorDef.In_cons_tl. auto.
Qed.


(*
Definition wf_permutation (perm : Vec Alpha 26) : Prop :=
  VectorDef.Forall (fun a => VectorDef.In a perm) alphabet.
*)

Inductive IsPermutation {A} : forall {n}, Vec A n -> Vec A n -> Prop :=
| permNil : IsPermutation (VectorDef.nil _) (VectorDef.nil _)
| permSkip : forall {x m} (v1 : Vec A m) (v2 : Vec A m),
    IsPermutation v1 v2 -> IsPermutation (VectorDef.cons _ x m v1) (VectorDef.cons _ x m v2)
| permSwap : forall {x y m} (v : Vec A m),
    IsPermutation (VectorDef.cons _ x (S m) (VectorDef.cons _ y _ v))
                  (VectorDef.cons _ y (S m) (VectorDef.cons _ x _ v))
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
    v = VectorDef.nil A.
Proof.
  intros A v. unfold Vec in *.
  refine (match v with
          | VectorDef.nil _ => _
          | VectorDef.cons _ x _ v => _
          end).
  reflexivity.
  apply idProp.
Qed.


(*
Theorem in_perm :
  forall {A n x} (v1 v2 : Vec A n),
    VectorDef.In x v1 ->
    IsPermutation v1 v2 ->
    VectorDef.In x v2.
Proof.
  intros A n x v1 v2 Hin Hperm.
  generalize dependent x.
  generalize dependent v1.
  generalize dependent v2.
  induction n.
  - intros v2 v1 Hperm x Hin.
    pose proof vec_0_is_nil v1.
    rewrite H in Hin. inversion Hin.
  - intros v2 v1 Hperm x Hin.
    
Qed.

  
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
    VectorDef.Forall (fun a => VectorDef.In a perm) alphabet ->
    wf_permutation perm.
Proof.
  intros perm H. unfold wf_permutation.
  inversion H.
  
Qed.

Theorem wf_permutation_alphabet :
  forall perm,
    wf_permutation perm ->
    VectorDef.Forall (fun a => VectorDef.In a perm) alphabet.
Proof.
  unfold wf_permutation.
  intros perm H.
  inversion H.
  
Qed.
*)