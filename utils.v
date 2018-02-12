Require Import Program.
Require Import Vector.
Require Import alphabet.


Ltac invert_existT H := subst; inversion H; subst;
                        repeat (match goal with
                                | H : existT _ _ _ = existT _ _ _ |- _ => try apply inj_pair2 in H
                                end; subst).


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


Ltac nilify := repeat (match goal with
                       | H : Vec _ 0 |- _ => rewrite (vec_0_is_nil H) in *
                       end; simpl in *; subst; simpl in *).
