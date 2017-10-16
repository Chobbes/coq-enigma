Require Import Vector.
Require Import Numbers.Natural.Peano.NPeano.
Require Import Strings.String.
Require Import Strings.Ascii.
Require Import List.


Definition Vec := VectorDef.t.
Definition Fin := Fin.t.
Definition Alpha := Fin 26.


Definition alpha_to_ascii (a : Alpha) : ascii :=
  match Fin.to_nat a with
  | exist _ a pf => ascii_of_nat ((nat_of_ascii "A") + a)
  end.


Definition ascii_to_alpha (a : ascii) : Alpha :=
  match Compare_dec.lt_dec (nat_of_ascii a - nat_of_ascii "A") 26 with
  | left pf_lt => Fin.of_nat_lt pf_lt
  | right pf_ge => Fin.F1
  end.


Fixpoint string_to_alpha (str : string) : list Alpha :=
  match str with
  | EmptyString => nil
  | String a str' => ascii_to_alpha a :: string_to_alpha str'
  end.


Definition alpha_to_string (alphas : list Alpha) : string :=
  fold_left (fun str a => String (alpha_to_ascii a) str) (rev alphas) EmptyString.


Fixpoint string_to_vec (str : string) : Vec Alpha (String.length str) :=
  match str as str' return Vec Alpha (String.length str') with
  | EmptyString => VectorDef.nil Alpha
  | String a str' => VectorDef.cons Alpha (ascii_to_alpha a) (String.length str') (string_to_vec str')
  end.


Definition alphabet : Vec Alpha 26 :=
  string_to_vec "ABCDEFGHIJKLMNOPQRSTUVWXYZ".


Example alpha_to_string_inverse_test :
  alpha_to_string (string_to_alpha "HELLOWORLD") = "HELLOWORLD"%string.
Proof. reflexivity. Qed.


Definition step_fin {n : nat} (f : Fin (S n)) : Fin (S n) :=
  match (Fin.to_nat f) with
  | exist _ i pf =>
    match Compare_dec.lt_dec (S i) (S n) return Fin (S n) with
    | left pf_lt => Fin.of_nat_lt pf_lt
    | right pf_nlt => Fin.F1
    end
  end.
