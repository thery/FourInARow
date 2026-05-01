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
                 "_______"
              ++ "_______"
              ++ "_______"
              ++ "_______"
              ++ "_______"
              ++ "O__X___")%string.


Definition ew1 :=  (get_position ev1).1.
Definition eb1 :=  (get_position ev1).2.

Lemma eval_ev1E : top_eval ew1 eb1 = win.
Proof.
native_cast_no_check (refl_equal win). 
Time Qed.

Lemma eval_ev1 : eval ew1 eb1 = WIN.
Proof.
suff : valid_eval ew1 eb1 win.
  by rewrite /valid_eval; case/or3P: (evalOr ew1 eb1) => /eqP->.
rewrite -eval_ev1E.
by apply: topeval_correct.
Qed.

