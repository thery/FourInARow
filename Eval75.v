
(******************************************************************************)
(*        A program that performs a perfect play for 4 in a row               *)
(*        This is directly inspired by a program by John Tromp                *)
(******************************************************************************)


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
Require Import FourInARow75.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition htop_eval75 w b ht :=
  let: PRes sc _ _ := 
    alpha_beta (1 + nheight * nwidth) 0 w b loss win zero ht in sc.

Lemma htop_eval75_equiv w b ht : 
  htop_eval 7 5 w b ht  = htop_eval75 w b ht.
Proof. by []. Qed.

Lemma htopeval75_correct w b ht : 
 valid_posb 7 5 w b -> valid_htable 7 5 ht -> valid_eval 7 5 w b (htop_eval75 w b ht).
Proof.
move=> Hv Ht.
rewrite -htop_eval75_equiv.
apply: htopeval_correct; [done|done|done|done| |done|done].
rewrite -to_nat_lsl_one; last by [].
by apply: nltbP.
Qed.

Definition top_eval75 w b := htop_eval75 w b (make_hash tt) .

Lemma topeval75_correct w b : valid_posb 7 5 w b -> valid_eval 7 5 w b (top_eval75 w b).
Proof.
move=> Hv.
rewrite -[top_eval75 _ _]htop_eval75_equiv.
apply: topeval_correct; [done|done|done|done| |done].
rewrite -to_nat_lsl_one; last by [].
by apply: nltbP.
Qed.
