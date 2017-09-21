Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.


Definition surjective {A B : Type} (f : A -> B) :=
  forall (b : B), exists a, f a = b.


Definition injective {A B : Type} (f : A -> B) :=
  forall (a1 a2 : A), f a1 = f a2 -> a1 = a2.


Definition left_inverse {A B : Type} (f : A -> B) :=
  exists (g : B -> A), (forall a, g (f a) = a).


(* Permutations are bijections on an alphabet *)
Definition bijective {A B : Type} (f : A -> B) :=
  injective f /\ surjective f.


Theorem injective_composition :
  forall (A B C : Type) (f : A -> B) (g : B -> C),
    injective f ->
    injective g ->
    injective (compose g f).
Proof.
  intros A B C f g Hf Hg.
  unfold injective in *. unfold compose in *.
  intros a1 a2 H.
  apply Hg in H. apply Hf in H.
  assumption.
Qed.


Theorem composition_injective :
  forall (A B C : Type) (f : A -> B) (g : B -> C),
    injective (compose g f) ->
    surjective f ->
    injective f /\ injective g.
Proof.
  intros A B C f g Hinj Hsurj.
  unfold injective in *. unfold compose in *.
  split.
  - intros a1 a2 Hf.
    apply Hinj. rewrite Hf.
    reflexivity.
  - intros b1 b2 Hg.
    unfold surjective in Hsurj.
    destruct (Hsurj b1) as [a1 Hfa1].
    destruct (Hsurj b2) as [a2 Hfa2].
    subst.
    apply Hinj in Hg. subst.
    reflexivity.
Qed.


Theorem composition_surjective :
  forall (A B C : Type) (f : A -> B) (g : B -> C),
    surjective (compose g f) ->
    surjective g.
Proof.
  intros A B C f g H.
  unfold surjective in *.
  intros b. destruct (H b) as [a Hcomp].
  exists (f a). assumption.
Qed.


Theorem injective_id :
  forall (A : Type), injective (@id A).
Proof.
  unfold injective. intros A a1 a2 H.
  compute in H.
  assumption.
Qed.


Theorem surjective_id :
  forall (A : Type), surjective (@id A).
Proof.
  unfold surjective. intros A b.
  exists b.
  reflexivity.
Qed.


Theorem composition_id :
  forall (A B : Type) (f : A -> B) (g : B -> A),
  (forall a, g (f a) = a) -> compose g f = id.
Proof.
  intros A B f g H.
  apply functional_extensionality.
  apply H.
Qed.


Theorem composition_surjective_f :
  forall (A B : Type) (f : A -> B) (g : B -> A),
  surjective (compose g f) -> injective g -> surjective f.
Proof.
  unfold surjective.
  intros A B f g H Hinj b.
  pose proof (H (g b)). destruct H0.
  exists x. unfold compose in H0.
  apply Hinj in H0.
  assumption.
Qed.


Theorem to_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (a : A),
    g (f a) = (compose g f) a.
Proof.
  reflexivity.
Qed.


Theorem left_inverse_injective :
  forall {A B : Type} (f : A -> B),
    left_inverse f ->
    injective f.
Proof.
  intros A B f [g H].
  unfold injective.
  intros a1 a2 Hfa.
  apply f_equal with (f:=g) in Hfa.
  apply composition_id in H.
  rewrite to_compose with (f:=f) in Hfa.
  rewrite to_compose with (f:=f) in Hfa.
  rewrite H in Hfa.
  compute in Hfa.
  assumption.
Qed.


Theorem left_inverse_not_equal :
  forall {A B : Type} (f : A -> B) (a b : A),
    left_inverse f ->
    a <> b ->
    f a <> f b.
Proof.
  intros A B f a b [g Hinv] Hab.
  unfold not in *.
  intros Hfab.
  apply Hab.
  apply (f_equal g) in Hfab.
  repeat rewrite Hinv in Hfab.
  assumption.
Qed.


Theorem left_inverse_injective_on_domain :
  forall {A B : Type} (f : A -> B) (g : B -> A),
    (forall a, g (f a) = a) ->
    forall a1 a2, g (f a1) = g (f a2) -> f a1 = f a2.
Proof.
  intros A B f g H a1 a2 Hgf.
  repeat rewrite H in Hgf.
  subst. reflexivity.
Qed.
