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
Require Import Eval74.
Require Import Eval65.
Require Import Eval56.
Require Import Eval47.
Require Import Eval75.
Require Import Eval66.
Require Import Eval57.
Require Import Pmain76.
Require Import Pmain67.

(******************************************************************************)
(*                                                                            *)
(*                                                                            *)
(*    Table                                                                   *)
(*               Width                                                        *)
(*          4      5      6      7                                            *)
(*      ┌─────────────────────────────┐                                       *)
(*   4  │ Draw   Draw   Loss   Draw   │                                       *)
(*      ├─────────────────────────────┤                                       *)
(*   5  │ Draw   Draw   Draw   Draw   │                                       *)
(*      ├─────────────────────────────┤                                       *)
(*   6  │ Draw   Draw   Loss   Win    │                                       *)
(*      ├─────────────────────────────┤                                       *)
(*   7  │ Draw   Draw   Win           │                                       *)
(*      └─────────────────────────────┘                                       *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)


Import PrimInt63Notations.
Import Uint63Axioms.
Import Uint63.
Open Scope uint63_scope.

(******************************************************************************)
(*                                                                            *)
(*       4 x 4 is draw                                                        *)
(*                                                                            *)
(******************************************************************************)

Lemma eval_ev4x4E : top_eval 4 4 0 0 = draw.
Proof.
native_cast_no_check (refl_equal draw). 
(*
Time Qed.
*)
Admitted.

Lemma eval_ev4x4 : eval 4 4 0 0 = DRAW.
Proof.
suff : valid_eval 4 4 0 0 draw.
  by rewrite /valid_eval; case/or3P: (@evalOr 4 4 isT isT 0 0) => /eqP->.
rewrite -eval_ev4x4E.
by apply: topeval_correct.
Qed.

(******************************************************************************)
(*                                                                            *)
(*       5 x 4 is draw                                                        *)
(*                                                                            *)
(******************************************************************************)
Lemma eval_ev5x4E : top_eval 5 4 0 0 = draw.
Proof.
native_cast_no_check (refl_equal draw).
(*
Time Qed.
*)
Admitted. 

Lemma eval_ev5x4 : eval 5 4 0 0 = DRAW.
Proof.
suff : valid_eval 5 4 0 0 draw.
  by rewrite /valid_eval; case/or3P: (@evalOr 5 4 isT isT 0 0) => /eqP->.
rewrite -eval_ev5x4E.
by apply: topeval_correct.
Qed.

(******************************************************************************)
(*                                                                            *)
(*       4 x 5 is draw                                                        *)
(*                                                                            *)
(******************************************************************************)
Lemma eval_ev4x5E : top_eval 4 5 0 0 = draw.
Proof.
native_cast_no_check (refl_equal draw).
(*
Time Qed.
*)
Admitted.

Lemma eval_ev4x5 : eval 4 5 0 0 = DRAW.
Proof.
suff : valid_eval 4 5 0 0 draw.
  by rewrite /valid_eval; case/or3P: (@evalOr 4 5 isT isT 0 0) => /eqP->.
rewrite -eval_ev4x5E.
by apply: topeval_correct.
Qed.

(******************************************************************************)
(*                                                                            *)
(*       6 x 4 is loss                                                        *)
(*                                                                            *)
(******************************************************************************)
Lemma eval_ev6x4E : top_eval 6 4 0 0 = loss.
Proof.
native_cast_no_check (refl_equal loss).
(*
Time Qed.
*)
Admitted.

Lemma eval_ev6x4 : eval 6 4 0 0 = LOSS.
Proof.
suff : valid_eval 6 4 0 0 loss.
  by rewrite /valid_eval; case/or3P: (@evalOr 6 4 isT isT 0 0) => /eqP->.
rewrite -eval_ev6x4E.
by apply: topeval_correct.
Qed.

(******************************************************************************)
(*                                                                            *)
(*       5 x 5 is draw                                                        *)
(*                                                                            *)
(******************************************************************************)
Lemma eval_ev5x5E : top_eval 5 5 0 0 = draw.
Proof.
native_cast_no_check (refl_equal draw).
(*
Time Qed.
*)
Admitted.

Lemma eval_ev5x5 : eval 5 5 0 0 = DRAW.
Proof.
suff : valid_eval 5 5 0 0 draw.
  by rewrite /valid_eval; case/or3P: (@evalOr 5 5 isT isT 0 0) => /eqP->.
rewrite -eval_ev5x5E.
by apply: topeval_correct.
Qed.

(******************************************************************************)
(*                                                                            *)
(*       4 x 6 is draw                                                        *)
(*                                                                            *)
(******************************************************************************)
Lemma eval_ev4x6E : top_eval 4 6 0 0 = draw.
Proof.
native_cast_no_check (refl_equal draw).
(*
Time Qed.
*)
Admitted.

Lemma eval_ev4x6 : eval 4 6 0 0 = DRAW.
Proof.
suff : valid_eval 4 6 0 0 draw.
  by rewrite /valid_eval; case/or3P: (@evalOr 4 6 isT isT 0 0) => /eqP->.
rewrite -eval_ev4x6E.
by apply: topeval_correct.
Qed.

(******************************************************************************)
(*                                                                            *)
(*       7 x 4 is draw                                                        *)
(*                                                                            *)
(******************************************************************************)
Lemma eval_ev7x4E : top_eval 7 4 0 0 = draw.
Proof.
rewrite [LHS]htop_eval74_equiv. 
native_cast_no_check (refl_equal draw).
(*
Time Qed.
*)
Admitted. 

Lemma eval_ev7x4 : eval 7 4 0 0 = DRAW.
Proof.
suff : valid_eval 7 4 0 0 draw.
  by rewrite /valid_eval; case/or3P: (@evalOr 7 4 isT isT 0 0) => /eqP->.
rewrite -eval_ev7x4E.
by apply: topeval_correct.
Qed.


(******************************************************************************)
(*                                                                            *)
(*       6 x 5 is draw                                                        *)
(*                                                                            *)
(******************************************************************************)
Lemma eval_ev6x5E : top_eval 6 5 0 0 = draw.
Proof.
rewrite [LHS]htop_eval65_equiv. 
native_cast_no_check (refl_equal draw).
(*
Time Qed.
*)
Admitted.

Lemma eval_ev6x5 : eval 6 5 0 0 = DRAW.
Proof.
suff : valid_eval 6 5 0 0 draw.
  by rewrite /valid_eval; case/or3P: (@evalOr 6 5 isT isT 0 0) => /eqP->.
rewrite -eval_ev6x5E.
by apply: topeval_correct.
Qed.

(******************************************************************************)
(*                                                                            *)
(*       5 x 6 is draw                                                        *)
(*                                                                            *)
(******************************************************************************)
Lemma eval_ev5x6E : top_eval 5 6 0 0 = draw.
Proof.
rewrite [LHS]htop_eval56_equiv. 
native_cast_no_check (refl_equal draw).
(*
Time Qed.
*)
Admitted.

Lemma eval_ev5x6 : eval 5 6 0 0 = DRAW.
Proof.
suff : valid_eval 5 6 0 0 draw.
  by rewrite /valid_eval; case/or3P: (@evalOr 5 6 isT isT 0 0) => /eqP->.
rewrite -eval_ev5x6E.
by apply: topeval_correct.
Qed.

(******************************************************************************)
(*                                                                            *)
(*       4 x 7 is draw                                                        *)
(*                                                                            *)
(******************************************************************************)
Lemma eval_ev4x7E : top_eval 4 7 0 0 = draw.
Proof.
rewrite [LHS]htop_eval47_equiv. 
native_cast_no_check (refl_equal draw). 
(*
Time Qed.
*)
Admitted.

Lemma eval_ev4x7 : eval 4 7 0 0 = DRAW.
Proof.
suff : valid_eval 4 7 0 0 draw.
  by rewrite /valid_eval; case/or3P: (@evalOr 4 7 isT isT 0 0) => /eqP->.
rewrite -eval_ev4x7E.
by apply: topeval_correct.
Qed.

(******************************************************************************)
(*                                                                            *)
(*       7 x 5 is draw                                                        *)
(*                                                                            *)
(******************************************************************************)

Lemma eval_ev7x5E : top_eval 7 5 0 0 = draw.
Proof.
rewrite [LHS]htop_eval75_equiv. 
native_cast_no_check (refl_equal draw).
(*
Time Qed.
*)
Admitted.

Lemma eval_ev7x5 : eval 7 5 0 0 = DRAW.
Proof.
suff : valid_eval 7 5 0 0 draw.
  by rewrite /valid_eval; case/or3P: (@evalOr 7 5 isT isT 0 0) => /eqP->.
rewrite -eval_ev7x5E.
by apply: topeval_correct.
Qed.

(******************************************************************************)
(*                                                                            *)
(*       6 x 6 is loss                                                        *)
(*                                                                            *)
(******************************************************************************)

Lemma eval_ev6x6E : top_eval 6 6 0 0 = loss.
Proof.
rewrite [LHS]htop_eval66_equiv. 
native_cast_no_check (refl_equal loss).
(*
Time Qed.
*)
Admitted.

Lemma eval_ev6x6 : eval 6 6 0 0 = LOSS.
Proof.
suff : valid_eval 6 6 0 0 loss.
  by rewrite /valid_eval; case/or3P: (@evalOr 6 6 isT isT 0 0) => /eqP->.
rewrite -eval_ev6x6E.
by apply: topeval_correct.
Qed.


(******************************************************************************)
(*                                                                            *)
(*       5 x 7 is draw                                                        *)
(*                                                                            *)
(******************************************************************************)

Lemma eval_ev5x7E : top_eval 5 7 0 0 = draw.
Proof.
rewrite [LHS]htop_eval57_equiv. 
native_cast_no_check (refl_equal draw).
(*
Time Qed.
*)
Admitted.

Lemma eval_ev5x7 : eval 5 7 0 0 = DRAW.
Proof.
suff : valid_eval 5 7 0 0 draw.
  by rewrite /valid_eval; case/or3P: (@evalOr 5 7 isT isT 0 0) => /eqP->.
rewrite -eval_ev5x7E.
by apply: topeval_correct.
Qed.

(******************************************************************************)
(*                                                                            *)
(*       7 x 6 is won                                                         *)
(*                                                                            *)
(******************************************************************************)

Lemma eval_ev7x6 : eval 7 6 0 0 = WIN.
Proof. by apply: main76. Qed.

(******************************************************************************)
(*                                                                            *)
(*       6 x 7 is won                                                         *)
(*                                                                            *)
(******************************************************************************)

Lemma eval_ev6x7 : eval 6 7 0 0 = WIN.
Proof. by apply: main67. Qed.

(**
Finished transaction in 1.531 secs (0.879u,0.513s) (successful)
Finished transaction in 4.442 secs (3.778u,0.522s) (successful)
Finished transaction in 2.411 secs (1.746u,0.522s) (successful)
Finished transaction in 70.08 secs (69.54u,0.169s) (successful)
Finished transaction in 43.287 secs (42.915u,0.025s) (successful)
Finished transaction in 12.268 secs (12.1u,0.004s) (successful)
Finished transaction in 25.793 secs (25.405u,0.138s) (successful)
Finished transaction in 24.323 secs (24.05u,0.027s) (successful)
Finished transaction in 12.78 secs (12.61u,0.003s) (successful)
Finished transaction in 1.695 secs (1.593u,0.s) (successful)
Finished transaction in 279.908 secs (278.633u,0.032s) (successful)
Finished transaction in 625.088 secs (621.327u,0.056s) (successful)
Finished transaction in 117.299 secs (116.248u,0.302s) (successful)
**)