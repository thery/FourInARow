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
(*    Fifth position                                                          *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)


Import PrimInt63Notations.
Import Uint63Axioms.
Import Uint63.
Open Scope uint63_scope.

Definition ev3 := (
                 "______"
              ++ "______"
              ++ "______"
              ++ "______"
              ++ "______"
              ++ "______"
              ++ "_X__O_")%string.

Definition ew5 :=  (get_position 6 7 ev3).1.
Definition eb5 :=  (get_position 6 7 ev3).2.

Lemma eval_ev5E : top_eval67 ew5 eb5 = win.
Proof.
native_cast_no_check (refl_equal win).
(*
Time Qed.
*)
Admitted.

Lemma eval_ev5 : eval 6 7 ew5 eb5 = WIN.
Proof.
suff : valid_eval 6 7 ew5 eb5 win.
  by rewrite /valid_eval; case/or3P: (@evalOr 6 7 isT isT ew5 eb5) => /eqP->.
rewrite -eval_ev5E.
by apply: topeval67_correct.
Qed.

