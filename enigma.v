Require Coq.Vectors.VectorDef.
Require Coq.Vectors.Fin.
Require Import List.

Definition Vec := VectorDef.t.
Definition Fin := Fin.t.

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
Definition Alpha := Fin 26.


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


(* A reflector can not map a letter to itself *)
Definition wf_reflector (bimap : Bimap) : Prop :=
  wf_bimap bimap /\
  forall (a : Alpha), in_map bimap a <> a.


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


(* An enigma is well formed if the reflector is well formed, as are all the wheels, and the plugboard. *)
Definition wf_enigma (enigma : Enigma) : Prop :=
  wf_reflector (reflector enigma) /\
  wf_bimap (plugboard enigma) /\
  Forall wf_wheel (wheels enigma) /\
  Forall wf_wheel (right_static_wheels enigma) /\
  Forall wf_wheel (left_static_wheels enigma).


Definition through_wheels (wheels : list Wheel) (a : Alpha) : Alpha :=
  fold_right (fun w => in_map w) a (map wheel_map wheels).


Definition out_wheels (wheels : list Wheel) (a : Alpha) : Alpha :=
  fold_right (fun w => out_map w) a (rev (map wheel_map wheels)).


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

(* A letter can not be encoded as itself *)

(* Enigma messages can be decoded *)

(* Encryption is the same as decryption. E.g., A -> B means B -> A as
well. Same as above more or less. *)

(* Pressing the same key multiple times should lead to different
   letters due to wheel rotation.
 *)

(* Enigma M4 and M3 / 1 equivalence *)