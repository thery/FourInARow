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
(*    Third position                                                          *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)


Import PrimInt63Notations.
Import Uint63Axioms.
Import Uint63.
Open Scope uint63_scope.

Definition ev3 := (
                 "_______"
              ++ "_______"
              ++ "_______"
              ++ "_______"
              ++ "_______"
              ++ "__OX___")%string.

Definition ew3 :=  (get_position ev3).1.
Definition eb3 :=  (get_position ev3).2.

Lemma eval_ev3E : top_eval ew3 eb3 = win.
Proof.
(* vm_cast_no_check (refl_equal win). *)
Admitted.

Lemma eval_ev3 : eval ew3 eb3 = WIN.
Proof.
suff : valid_eval ew3 eb3 win.
  by rewrite /valid_eval; case/or3P: (evalOr ew3 eb3) => /eqP->.
rewrite -eval_ev3E.
by apply: topeval_correct.
Qed.

