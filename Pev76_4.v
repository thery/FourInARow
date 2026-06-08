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
Require Import FourInARow76.
Require Import Eval76.

(******************************************************************************)
(*                                                                            *)
(*                                                                            *)
(*    Forth position                                                          *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)


Import PrimInt63Notations.
Import Uint63Axioms.
Import Uint63.
Open Scope uint63_scope.

Definition ev4 := (
                 "_______"
              ++ "_______"
              ++ "_______"
              ++ "_______"
              ++ "___O___"
              ++ "___X___")%string.

Definition ew4 :=  (get_position 7 6 ev4).1.
Definition eb4 :=  (get_position 7 6 ev4).2.

Lemma eval_ev4E : top_eval76 ew4 eb4 = win.
Proof.
native_cast_no_check (refl_equal win).
Time Qed.
(*
Admitted.
*)

Lemma eval_ev4 : eval 7 6 ew4 eb4 = WIN.
Proof.
suff : valid_eval 7 6 ew4 eb4 win.
  by rewrite /valid_eval; case/or3P: (@evalOr 7 6 isT isT ew4 eb4) => /eqP->.
rewrite -eval_ev4E.
by apply: topeval76_correct.
Qed.
