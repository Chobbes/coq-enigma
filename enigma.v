Require Import Vector.
Require Import Numbers.Natural.Peano.NPeano.
Require Import Strings.String.
Require Import Strings.Ascii.
Require Import Program.
Require Import List.
Require Import bijections.
Require Import alphabet.
Require Import permutations.
Require Import utils.


(* An enigma machine consists of some of the following:

   - A plugboard (Stecker)
   - Static wheel (ETW)
     + Order keys are connected to this varies by the enigma model.
   - Several rotating wheels
   - Reflector (UKW)

   Rightmost wheel moves first, rotated counter clockwise relative to
   the ETW.

 *)


(* A well formed wheel can't actually have a letter mapped to
itself. Wouldn't make sense in a circuit. *)

(* Probably want a better notion of a permutation.

We do need to invert these, since current is passed back through the
wheels in the opposite direction.

 *)


Definition Bimap := (Vec Alpha 26 * Vec Alpha 26)%type.


Definition in_map (bimap : Bimap) (a : Alpha) : Alpha :=
  match bimap with
    (input, output) =>  VectorDef.nth input a
 end.


Definition out_map (bimap : Bimap) (a : Alpha) : Alpha :=
  match bimap with
    (input, output) =>  VectorDef.nth output a
 end.


(* Bimap, list of notches, index *)
Record Wheel : Type :=
  mkWheel {
      wheel_map : Bimap;
      wheel_notches : list (Fin 26);
      wheel_index : Fin 26
    }.


(* Plugboard is just a permutation *)
Definition Plugboard := Bimap.


(* Reflector is just a permutation *)
Definition Reflector := Bimap.


(* A bimap is well formed if it is an invertible permutation. *)
Definition wf_bimap (bimap : Bimap) : Prop :=
  forall (a : Alpha),
    in_map bimap (out_map bimap a) = a /\ out_map bimap (in_map bimap a) = a.


(* A reflector can not map a letter to itself, and
   must be its own inverse.
 *)
Definition wf_reflector (bimap : Bimap) : Prop :=
  wf_bimap bimap /\
  (forall (a : Alpha), in_map bimap a <> a) /\
  (forall (a : Alpha), in_map bimap (in_map bimap a) = a).


Definition wf_wheel (wheel : Wheel) : Prop :=
  wf_bimap (wheel_map wheel).


Record Enigma : Type :=
  mkEnigma {
      reflector : Reflector;
      plugboard : Plugboard;

      wheels : list Wheel;

      (* Wheels which don't rotate during operation. *)
      right_static_wheels : list Wheel;
      left_static_wheels : list Wheel;

      (* Does this Enigma perform double stepping? *)
      double_stepping : bool
    }.


(* An enigma is well formed if the reflector is well formed, as are
   all the wheels, and the plugboard.
 *)
Definition wf_enigma (enigma : Enigma) : Prop :=
  wf_reflector (reflector enigma) /\
  wf_bimap (plugboard enigma) /\
  Forall wf_wheel (wheels enigma) /\
  Forall wf_wheel (right_static_wheels enigma) /\
  Forall wf_wheel (left_static_wheels enigma).


Definition through_wheels (wheels : list Wheel) (a : Alpha) : Alpha :=
  fold_left (fun a w => in_map w a) (map wheel_map wheels) a.


Definition out_wheels (wheels : list Wheel) (a : Alpha) : Alpha :=
  fold_left (fun a w => out_map w a) (rev (map wheel_map wheels)) a.


(* Run a character through the circuit in the Enigma. This is like
   pressing a key, but without advancing any rotors *)
Definition encipher (enigma : Enigma) (a : Alpha) : Alpha :=
  let all_wheels := right_static_wheels enigma ++ wheels enigma ++ left_static_wheels enigma in
  let the_reflector := reflector enigma in
  let the_plugboard := plugboard enigma in

  out_map the_plugboard (
  out_wheels all_wheels (
  in_map the_reflector (
  through_wheels all_wheels (
  in_map the_plugboard a)))).


(* in_wheels and out_wheels are bijections *)
Theorem out_through_wheels_inverse :
  forall (ws : list Wheel),
  Forall wf_wheel ws ->
  forall a, through_wheels ws (out_wheels ws a) = a.
Proof.
  intros ws H a.
  induction ws as [| w ws'].
  - reflexivity.
  - unfold through_wheels in *.
    unfold out_wheels in *. simpl in *.
    inversion H.
    unfold wf_wheel in H2. unfold wf_bimap in H2.
    pose proof (H2 (fold_left (fun (a0 : Alpha) (w0 : Bimap) => out_map w0 a0) (rev (map wheel_map ws')) a)) as [Hin Hout].
    rewrite fold_left_app. simpl.

    rewrite Hin.
    apply IHws'.
    assumption.
Qed.


Theorem rev_nil :
  forall A (l : list A),
  rev l = nil -> l = nil.
Proof.
  intros A l H.
  destruct l.
  - reflexivity.
  - simpl in H.
    pose proof (app_cons_not_nil (rev l) nil a) as Hnil.
    unfold not in Hnil.
    
    exfalso.
    apply Hnil.
    symmetry.
    assumption.
Qed.


Theorem forall_app :
forall A (l1 l2 : list A) (P : A -> Prop),
  Forall P l1 ->
  Forall P l2 ->
  Forall P (l1 ++ l2).
Proof.
  intros A l1 l2 P Hl1 Hl2.
  induction Hl1.
  - apply Hl2.
  - simpl. apply Forall_cons; assumption.
Qed.


Theorem forall_rev :
  forall A (l : list A) (P : A -> Prop),
    Forall P l ->
    Forall P (rev l).
Proof.
  intros A l P H.
  induction H.
  - apply Forall_nil.
  - simpl. apply forall_app; auto.
Qed.


Theorem through_out_wheels_inverse :
  forall (ws : list Wheel),
  Forall wf_wheel ws ->
  forall a, out_wheels ws (through_wheels ws a) = a.
Proof.
  intros ws H a.
  induction ws as [| w ws'] using rev_ind.
  - reflexivity.
  - unfold through_wheels in *.
    unfold out_wheels in *. simpl in *.

    apply forall_rev in H.
    rewrite rev_app_distr in H. simpl in H.
    inversion H.

    unfold wf_wheel in H2. unfold wf_bimap in H2.

    rewrite <- map_rev. rewrite rev_app_distr. simpl.

    rewrite map_app.
    rewrite fold_left_app.
    simpl.

    pose proof (H2 (fold_left (fun (a0 : Alpha) (w0 : Bimap) => in_map w0 a0) (map wheel_map ws') a)) as [Hin Hout].

    rewrite Hout.
    rewrite map_rev.
    apply IHws'.

    apply forall_rev in H3.
    rewrite rev_involutive in H3.
    assumption.
Qed.


Theorem through_app :
  forall (ws1 ws2 : list Wheel),
  forall a, through_wheels (ws1 ++ ws2) a = through_wheels ws2 (through_wheels ws1 a).
Proof.
  induction ws1 as [| w' ws1'].
  - reflexivity.
  - intros ws2 b.
    simpl in *.
    unfold through_wheels in *.
    simpl in *.
    rewrite IHws1'.
    reflexivity.
Qed.


Theorem through_wheels_left_inverse :
  forall (ws : list Wheel),
  Forall wf_wheel ws ->
  left_inverse (through_wheels ws).
Proof.
  unfold left_inverse.
  intros ws H.
  exists (out_wheels ws).
  apply through_out_wheels_inverse.
  assumption.
Qed.


Theorem bimap_left_inverse :
  forall (b : Bimap),
  wf_bimap b ->
  left_inverse (in_map b).
Proof.
  intros b H.
  unfold left_inverse.
  exists (out_map b). unfold wf_bimap in H. apply H.
Qed.


(* Going through the plugboard and then wheels is left invertible *)
Theorem plugboard_through_wheels_left_inverse :
  forall (ws : list Wheel) (the_plugboard : Plugboard),
  wf_bimap the_plugboard ->
  Forall wf_wheel ws ->
  forall a, out_map the_plugboard (out_wheels ws (through_wheels ws (in_map the_plugboard a))) = a.
Proof.
  intros ws the_plugboard Hpb Hws a.
  unfold wf_bimap in Hpb.

  pose proof (through_out_wheels_inverse ws) as Hwinv.
  apply Hwinv with (a:=(in_map the_plugboard a)) in Hws.
  rewrite Hws.

  apply Hpb.
Qed.


Theorem out_wheels_plugboard_left_inverse :
  forall (ws : list Wheel) (the_plugboard : Plugboard),
  wf_bimap the_plugboard ->
  Forall wf_wheel ws ->
  forall a, through_wheels ws (in_map the_plugboard (out_map the_plugboard (out_wheels ws a))) = a.
Proof.
  intros ws the_plugboard Hpb Hws a.
  unfold wf_bimap in Hpb.

  pose proof (out_through_wheels_inverse ws) as Hwinv.

  pose proof Hpb (out_wheels ws a) as [Hin _].
  rewrite Hin.

  apply Hwinv.
  assumption.
Qed.


Theorem left_inverse_disruption :
  forall {A B : Type} (f : A -> B) (g : B -> A) (k : B -> B),
  (forall a, g (f a) = a) ->
  (forall b, f (g b) = b) ->
  (forall b, k b <> b) ->
  (forall a, g (k (f a)) <> a).
Proof.
  intros A B f g k Hgf Hfg Hkb a.
  unfold not in *.
  intros Hgkf.

  apply Hkb with (b:=f a).
  pose proof (left_inverse_injective g).
  unfold injective in H.

  apply H.
  - unfold left_inverse.
    exists f. assumption.
  - rewrite Hgf.
    assumption.
Qed.


(* A letter can not be encoded as itself.

   Rough sketch of why this is true:

   Since the reflector can not encode a letter as itself, the circuit
   that the current originally came from can not be retraced, so we
   can't get back to the original letter.

   Sufficies to condense the rest of the enigma machine (everything
   but the reflector) to a bijection.

   Then since this is a bijection we can show that the well-formedness
   property of the reflector, which insists that a value coming in is
   encoded as a different value leads to a different value coming out
   of the bijection.

   You get a different value due to injectivity...

   g (f a) = a

   g is injective, so if I feed it b <> f a, then...

   g (f a) <> g (b)

 *)
Theorem no_self_encoding :
  forall (enigma : Enigma),
    wf_enigma enigma ->
    forall (a : Alpha), encipher enigma a <> a.
Proof.
  intros enigma [Hwf_ref [Hwf_plug [Hwf_wheels [Hwf_right Hwf_left]]]] a.
  unfold encipher.
  unfold wf_reflector in Hwf_ref.
  destruct Hwf_ref as [Hbimap [Hdiff Hblah]].

  set (all_wheels := right_static_wheels enigma ++ wheels enigma ++ left_static_wheels enigma) in *.
  set (ref := reflector enigma) in *.
  set (plug := plugboard enigma) in *.

  apply (left_inverse_disruption (fun a => (through_wheels all_wheels (in_map plug a)))
                                 (fun a => (out_map plug (out_wheels all_wheels a)))
                                 (in_map (reflector enigma))).

  - apply plugboard_through_wheels_left_inverse.
    + assumption.
    + repeat (apply forall_app; try assumption).
  - apply out_wheels_plugboard_left_inverse.
    + assumption.
    + repeat (apply forall_app; try assumption).
  - assumption.
Qed.

(* Enigma messages can be decoded *)
Theorem enigma_decode :
  forall (enigma : Enigma),
    wf_enigma enigma ->
    forall (a : Alpha), encipher enigma (encipher enigma a) = a.
Proof.
  intros enigma [Hwf_ref [Hwf_plug [Hwf_wheels [Hwf_right Hwf_left]]]] a.
  unfold encipher.

  set (all_wheels := right_static_wheels enigma ++ wheels enigma ++ left_static_wheels enigma) in *.
  set (ref := reflector enigma) in *.
  set (plug := plugboard enigma) in *.

  unfold wf_bimap in Hwf_plug.

  pose proof (Hwf_plug (out_wheels all_wheels (in_map ref (through_wheels all_wheels (in_map plug a))))) as [Hin Hout].

  rewrite Hin.

  rewrite out_through_wheels_inverse.
  - unfold wf_reflector in Hwf_ref. destruct Hwf_ref as [Hrefbi [Hrefne Hrefinv]].
    rewrite Hrefinv.
    rewrite through_out_wheels_inverse.
    + apply Hwf_plug.
    + repeat (apply forall_app; try assumption).
  - repeat (apply forall_app; try assumption).
Qed.


Definition step_wheel (w : Wheel) : Wheel :=
  match w with
  | mkWheel m ns i => mkWheel m ns (step_fin i)
  end.


(* Step a wheel if the previous wheel has a notch in the correct position. *)
Definition step_if_notched (prev : Wheel) (w : Wheel) : Wheel :=
  match prev with
  | mkWheel m notches i =>
    if in_dec Fin.eq_dec i notches
    then step_wheel w
    else w
  end.


(* Step a wheel if the previous wheel has a notch in the correct
   position, or the next wheel does. *)
Definition double_step_if_notched (prev : Wheel) (next : Wheel) (w : Wheel) : Wheel :=
  match prev with
  | mkWheel _ notches i =>
    if in_dec Fin.eq_dec i notches
    then step_wheel w
    else match next with
         | mkWheel _ next_notches next_i =>
           if in_dec Fin.eq_dec next_i next_notches
           then step_wheel w
           else w
         end
  end.


(* Step the notched wheels without taking double stepping into account *)
Fixpoint step_carry_wheels (prev : Wheel) (ws : list Wheel) : list Wheel :=
  match ws with
  | nil => nil
  | w :: ws' =>
    step_if_notched prev w :: step_carry_wheels w ws'
  end.


(* Step the notched wheels taking double stepping into account *)
Fixpoint double_step_carry_wheels (prev : Wheel) (ws : list Wheel) : list Wheel :=
  match ws with
  | nil => nil
  | w :: nil => step_if_notched prev w :: nil
  | w :: next :: ws' =>
    double_step_if_notched prev next w :: step_carry_wheels w ws'
  end.


(* 1) Step the first wheel always.
   2) Step all wheel's whose previous wheel has a notch at the current
      index.
   3) If double stepping, then every wheel with a notch at the current
      index must also step as well, unless it's the last wheel.
 *)
Fixpoint step_wheels (ws : list Wheel) : list Wheel :=
  match ws with
  | nil => nil
  | w :: ws' => step_wheel w :: step_carry_wheels w ws'
  end.


Fixpoint double_step_wheels (ws : list Wheel) : list Wheel :=
  match ws with
  | nil => nil
  | w :: ws' => step_wheel w :: double_step_carry_wheels w ws'
  end.


Definition step_enigma (enigma : Enigma) : Enigma :=
  match enigma with
  | mkEnigma ref plug wheels right_ws left_ws double_step =>
    if double_step
    then let new_wheels := double_step_wheels wheels in
         mkEnigma ref plug new_wheels right_ws left_ws double_step
    else let new_wheels := step_wheels wheels in
         mkEnigma ref plug new_wheels right_ws left_ws double_step
  end.


(* Press a key, causing the wheels to rotate, and a letter to light up.

   Return the letter which lights up, and the new state of the enigma machine.
*)
Definition press_key (enigma : Enigma) (a : Alpha) : (Alpha * Enigma) :=
  let enigma' := step_enigma enigma in (encipher enigma' a, enigma').


Fixpoint encipher_message (enigma : Enigma) (message : list Alpha) : (list Alpha) :=
    match message with
    | nil => nil
    | a :: message' =>
      let (o, enigma') := press_key enigma a in
      o :: encipher_message enigma' message'
    end.


Fixpoint vector_find {A} {n} (decA : forall x y : A, {x = y} + {x <> y}) (a : A) (vec : Vec A n) : option (Fin n) :=
  match vec with
  | VectorDef.nil _ => None
  | VectorDef.cons _ x m t =>
    if decA a x
    then Some (Fin.F1)
    else match vector_find decA a t with
         | None => None
         | Some f => Some (Fin.FS f)
         end
  end.


Theorem vector_find_in_list :
  forall A n (decA : forall x y : A, {x = y} + {x <> y}) (a : A) (vec : Vec A n),
    VectorDef.In a vec ->
    vector_find decA a vec <> None.
Proof.
  intros A n decA a vec H.
  unfold not in *.
  induction H.
  - simpl. destruct decA.
    + intros contra.
      inversion contra.
    + contradiction.
  - simpl. destruct decA.
    + intros contra. inversion contra.
    + destruct (vector_find decA a v) eqn:bleh.
      * intros H0. inversion H0.
      * contradiction.
Qed.


Theorem vector_find_in_list' :
  forall {A n} (decA : forall x y : A, {x = y} + {x <> y}) (a : A) (vec : Vec A n),
    VectorDef.In a vec ->
    exists k, vector_find decA a vec = Some k.
Proof.
  intros A n decA a vec Hin.
  induction Hin.
  - simpl. destruct decA.
    + exists Fin.F1. reflexivity.
    + contradiction.
  - simpl. destruct decA.
    + exists Fin.F1. reflexivity.
    + destruct IHHin. rewrite H.
      exists (Fin.FS x0). reflexivity.
Qed.


Theorem vector_find_cons :
  forall A n (decA : forall x y : A, {x = y} + {x <> y}) (a : A) (vec : Vec A n),
    vector_find decA a (Vector.cons A a n vec) = Some Fin.F1.
Proof.
  intros A n decA a vec.
  simpl. destruct decA.
  - reflexivity.
  - contradiction.
Qed.


Definition get_option {A} (a : A) (o : option A) : A :=
  match o with
  | None => a
  | Some v => v
  end.


Definition Permutation := Vec Alpha 26.


(* Want to find the position for each letter *)
Fixpoint invert_permutation (perm : Permutation) : Permutation :=
  VectorDef.map (fun a => get_option Fin.F1 ( vector_find Fin.eq_dec a perm)) alphabet.


Theorem vector_nth_cons :
  forall A n k (a x : A) (vec : Vec A n),
    VectorDef.In a vec ->
    Vector.nth vec k = a ->
    Vector.nth (Vector.cons A x n vec) (Fin.FS k) = a.
Proof.
  auto.
Qed.


Theorem not_in_not_eq :
  forall {A n} (a x : A) (vec : Vec A n),
    VectorDef.In a vec ->
    ~ VectorDef.In x vec ->
    x <> a.
Proof.
  unfold not.
  intros A n a x vec Hin Hnin Hxa.
  invert_existT Hin; contradiction.
Qed.


Theorem match_madness :
  forall n (o : option (Fin n)) k,
    (match o with
    | Some f => Some (Fin.FS f)
    | None => None
    end) = Some (Fin.FS k) ->
    o = Some k.
Proof.
  intros n o k H.
  induction o.
  - invert_existT H. reflexivity.
  - inversion H.
Qed.


Theorem vector_find_cons_neq_weaken :
  forall {A n k} (decA : forall x y : A, {x = y} + {x <> y}) (a x : A) (vec : Vec A n),
    VectorDef.In a vec ->
    a <> x ->
    vector_find decA a (Vector.cons A x n vec) = Some (Fin.FS k) ->
    vector_find decA a vec = Some k.
Proof.
  intros A n k decA a x vec Hin Hnax Hfind.
  induction Hin;
  unfold vector_find in *; destruct decA;
    try contradiction;
    try (destruct decA;
         try (invert_existT Hfind; reflexivity);
         try (apply match_madness in Hfind; apply Hfind)).
Qed.


Theorem vector_find_cons_neq :
  forall {A n} (decA : forall x y : A, {x = y} + {x <> y}) (a x : A) (vec : Vec A n),
    VectorDef.In a vec ->
    a <> x ->
    exists k, vector_find decA a (Vector.cons A x n vec) = Some (Fin.FS k).
Proof.
  intros A n decA a x vec Hin Hneq.
  induction vec.
  - inversion Hin.
  - invert_existT Hin.
    + simpl. destruct decA.
      * contradiction.
      * destruct decA.
        -- exists Fin.F1. reflexivity.
        -- contradiction.
    + simpl. destruct decA.
      * contradiction.
      * simpl in *. subst. apply IHvec in H1.
        destruct decA.
        -- contradiction.
        -- destruct decA.
           ++ subst. exists Fin.F1. reflexivity.
           ++ destruct H1. rewrite H. exists (Fin.FS x0). reflexivity.
Qed.


Theorem neq_sym :
  forall {A} (a x : A),
    a <> x -> x <> a.
Proof.
  unfold not.
  intros A a x Hax Hxa.
  auto.
Qed.


Theorem find_inverse :
  forall A n k (decA : forall x y : A, {x = y} + {x <> y}) (a : A) (vec : Vec A n),
    VectorDef.In a vec ->
    NoDupVec vec ->
    vector_find decA a vec = Some k ->
    Vector.nth vec k = a.
Proof.
  intros A n k decA a vec Hin Hdup Hfind.
  generalize dependent k.
  induction vec; intros k Hfind.
  - inversion Hin.
  - invert_existT Hin.
    + unfold Fin in k. rewrite vector_find_cons in Hfind.
      inversion Hfind.
      reflexivity.
    + invert_existT Hdup.
      pose proof not_in_not_eq a h vec H1 H3.
      apply neq_sym in H.
      pose proof vector_find_cons_neq decA a h vec H1 H.
      destruct H0. rewrite H0 in Hfind. inversion Hfind.
      apply vector_nth_cons; auto.
      apply IHvec; auto.
      pose proof vector_find_in_list' decA a vec H1.
      destruct H2.
      subst.
      apply (vector_find_cons_neq_weaken decA a h vec H1 H H0).
Qed.

Theorem tiny_alpha :
  forall (perm : Vec (Fin 1) 1),
    NoDupVec perm ->
    IsPermutation perm (Vector.cons _ Fin.F1 0 (Vector.nil _)).
Proof.
  intros perm H. simpl.
  repeat dependent destruction perm.
  repeat match goal with
  | H : NoDupVec ?v |- _ => invert_existT H
  end.
  econstructor. eauto.
  simpl in *.
  unfold not in *.
  
Qed.

Theorem invert_permutation_is_permutatino :
  forall (perm : Permutation),
    NoDupVec perm ->
    IsPermutation perm alphabet.
Proof.
  intros perm H.
  repeat match goal with
  | H : NoDupVec ?v |- _ => invert_existT H
  end.
  econstructor. econstructor.
  econstructor. econstructor.
  econstructor. econstructor.
  econstructor. econstructor.
  econstructor. econstructor.
  econstructor. econstructor.
  econstructor. econstructor.
  econstructor. econstructor.
  econstructor. econstructor.
  econstructor. econstructor.
  econstructor. econstructor.
  econstructor. econstructor.
  econstructor. econstructor.
  econstructor. constructor.
  

  simpl in *. repeat econstructor; repeat eauto.
  invert_existT H.
  invert_existT H3.
Qed.


Theorem invert_permutation_left :
  forall (perm : Permutation) (a b : Alpha),
    Vector.nth perm a = b ->
    Vector.nth (invert_permutation perm) b = a.
Proof.
  intros perm a b H.
  unfold invert_permutation.
Qed.


(* Transform a new alphabet into a well formed bimap. *)
Definition mkBimap (permutation : Permutation) : Bimap :=
  (permutation, invert_permutation permutation).


Theorem wf_bimap_wf_bimap :
  forall (perm : Permutation),
    wf_permutation perm ->
    wf_bimap (mkBimap perm).
Proof.
  intros perm H.
  unfold wf_permutation in H.
  unfold wf_bimap. unfold mkBimap.
  simpl. unfold invert_permutation. simpl.
  intros a.

  split.
  - unfold Alpha in *. simpl.

    (* Want to say that nth invert_perm a is (vector_find Fin.eq_dec a perm)

       And since vector_find Fin.eq_dec a perm is just going to find
       the occurance of 'a' in perm (which is guaranteed to be
       unique), then nth perm (where-a-is) is going to be a.
     *)
Qed.


Theorem wf_permutation_wf_bimap :
  forall (perm : Vec Alpha 26),
    wf_permutation perm ->
    wf_bimap (mkBimap perm).
Proof.
  intros perm H.
  unfold wf_permutation in H.
  unfold wf_bimap.
  intros a. split.
  unfold out_map.
  
Qed.
*)
  
(* Need identical enigma machine to decipher (note: navy one was convertible...)

   Restrict to same set of wheels and such. Same *type* of
   enigma. Then you need identical settings for ALL messages. Some may
   be decoded regardless, if short. E.g., two different settings may
   map a -> k.
*)

(* Pressing the same key multiple times should lead to different
   letters due to wheel rotation.

   Does it ever result in the same letter? It can if other wheels
   turn.
   
 *)

(* Enigma M4 and M3 / 1 equivalence *)