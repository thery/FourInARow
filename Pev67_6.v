From Stdlib Require Import ZArith Ascii List String PrimInt63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_boot.
From HB Require Import structures.

From Stdlib Require Import Lia.
Require Import ssr_int.
Require Import Pbasic.
Require Import Pmoves.
Require Import Phash.
Require Import Palphabeta.
Require Import FourInARow.
Require Import FourInARow67.
Require Import Eval67.

(******************************************************************************)
(*                                                                            *)
(*                                                                            *)
(*    Third position                                                          *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)


Import PrimInt63Notations.
Import Uint63Axioms.
Import Uint63.
Open Scope uint63_scope.

Definition ev6 := (
                 "______"
              ++ "______"
              ++ "______"
              ++ "______"
              ++ "______"
              ++ "______"
              ++ "_X___O")%string.

Definition ew6 :=  (get_position 6 7 ev6).1.
Definition eb6 :=  (get_position 6 7 ev6).2.

Lemma eval_ev6E : top_eval67 ew6 eb6 = win.
Proof.
native_cast_no_check (refl_equal win).
Time Qed.

Lemma eval_ev6 : eval 6 7 ew6 eb6 = WIN.
Proof.
suff : valid_eval 6 7 ew6 eb6 win.
  by rewrite /valid_eval; case/or3P: (@evalOr 6 7 isT isT ew6 eb6) => /eqP->.
rewrite -eval_ev6E.
by apply: topeval67_correct.
Qed.

