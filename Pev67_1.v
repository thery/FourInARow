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
(*    First position                                                          *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)


Import PrimInt63Notations.
Import Uint63Axioms.
Import Uint63.
Open Scope uint63_scope.

Definition ev1 := (
                 "______"
              ++ "______"
              ++ "______"
              ++ "______"
              ++ "______"
              ++ "______"
              ++ "OX____")%string.


Definition ew1 :=  (get_position 6 7 ev1).1.
Definition eb1 :=  (get_position 6 7 ev1).2.

Lemma eval_ev1E : top_eval67 ew1 eb1 = win.
Proof.
native_cast_no_check (refl_equal win).
Time Qed.

Lemma eval_ev1 : eval 6 7 ew1 eb1 = WIN.
Proof.
suff : valid_eval 6 7 ew1 eb1 win.
  by rewrite /valid_eval; case/or3P: (@evalOr 6 7 isT isT ew1 eb1) => /eqP->.
rewrite -eval_ev1E.
by apply: topeval67_correct.
Qed.

