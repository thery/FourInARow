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
(*    Second position                                                         *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)


Import PrimInt63Notations.
Import Uint63Axioms.
Import Uint63.
Open Scope uint63_scope.


Definition ev2 := (
                 "______"
              ++ "______"
              ++ "______"
              ++ "______"
              ++ "______"
              ++ "_O____"
              ++ "_X____")%string.

Definition ew2 :=  (get_position 6 7 ev2).1.
Definition eb2 :=  (get_position 6 7 ev2).2.

Lemma eval_ev2E : top_eval67 ew2 eb2 = win.
Proof.
native_cast_no_check (refl_equal win).
(*
Time Qed.
*)
Admitted.

Lemma eval_ev2 : eval 6 7 ew2 eb2 = WIN.
Proof.
suff : valid_eval 6 7 ew2 eb2 win.
  by rewrite /valid_eval; case/or3P: (@evalOr 6 7 isT isT ew2 eb2) => /eqP->.
rewrite -eval_ev2E.
by apply: topeval67_correct.
Qed.
