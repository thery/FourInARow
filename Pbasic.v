From Stdlib Require Import ZArith Ascii List String PrimInt63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_boot.
From HB Require Import structures.

From Stdlib Require Import Lia.

Import PrimInt63Notations.
Import Uint63Axioms.
Import Uint63.
Require Import ssr_int.
Require Import FourInARow.
Open Scope uint63_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(*                                                                            *)
(*    Basic definitions and properties for the proof of the main program      *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

Lemma nhorizontalLwB : nhorizontal < nwB.
Proof.
rewrite -[nhorizontal]/(to_nat horizontal).
by apply: to_nat_bounded.
Qed.

Lemma nwidthLwB : nwidth < nwB.
Proof.
rewrite -[nwidth]/(to_nat width).
by apply: to_nat_bounded.
Qed.

Lemma whLd : nwidth * nhorizontal < ndigits.
Proof. by []. Qed.

Lemma whLw : nwidth * nhorizontal < nwB.
Proof. by apply: ltn_trans whLd ndigitsLwB. Qed.

Lemma whE : to_nat (width * horizontal) = (nwidth * nhorizontal)%N.
Proof. by rewrite to_nat_mul // whLw. Qed.

Lemma ihLwh i: i < nwidth -> i * nhorizontal < nwidth * nhorizontal.
Proof. by move=> iLw; rewrite ltn_mul2r iLw. Qed.

Lemma ihLd i : i < nwidth -> i * nhorizontal < ndigits.
Proof. by move=> /ihLwh/ltn_trans ->. Qed.

Lemma ihLw i : i < nwidth -> i * nhorizontal < nwB.
Proof. by move=> /ihLd/ltn_trans/(_ ndigitsLwB). Qed.

Lemma ihE i : 
  i < nwidth -> to_nat (of_nat i * horizontal) = (i * nhorizontal)%N.
Proof.
move=> iLw; have iLwb : i < nwB by apply: ltn_trans nwidthLwB.
by rewrite  to_nat_mul of_natK // ihLw.
Qed.

Lemma ihjLwh i j :
  i < nwidth -> j < nhorizontal -> i * nhorizontal  + j < nwidth * nhorizontal.
Proof.
move=> iLw jLh.
apply: leq_trans (_ : i * nhorizontal + nhorizontal <= _).
  by rewrite ltn_add2l.
by rewrite addnC -mulSn leq_mul2r iLw.
Qed.

Lemma ihjLd i j : 
  i < nwidth  -> j < nhorizontal -> i * nhorizontal + j < ndigits.
Proof. by move=> ? ?; apply: ltn_trans (ihjLwh _ _) _. Qed.

Lemma ihjLw i j : 
  i < nwidth  -> j < nhorizontal -> i * nhorizontal + j < nwB.
Proof. by move=> ? ?; apply: ltn_trans (ihjLd _ _) ndigitsLwB. Qed.

Lemma ihjE i j : 
  i < nwidth  -> j < nhorizontal -> 
  to_nat (of_nat i * horizontal + of_nat j) = (i * nhorizontal + j)%N.
Proof.
move=> iLw jLh.
have jLw : j < nwB by apply: ltn_trans nwidthLwB.
by rewrite to_nat_add ihE // of_natK // ihjLw.
Qed.

Lemma ihj_inv i1 i2 j1 j2 : 
  i1 < nwidth -> i2 < nwidth -> j1 < nhorizontal -> j2 < nhorizontal ->
  (i1 * nhorizontal + j1 = i2 * nhorizontal + j2 -> i1 = i2)%N.
Proof.
move=> i1Lw i2Lw j1Lh j2Lh i1j1E.
case: (ltngtP i1 i2) => // [i1Li2|j1Lj2].
  suff : i1 * nhorizontal + j1 < i2 * nhorizontal + j2.
    by rewrite i1j1E ltnn.
  apply: leq_trans (_ : i1.+1 * nhorizontal <= _).
    by rewrite mulSn addnC ltn_add2r.
  apply: leq_trans (leq_addr _ _).
  by rewrite leq_mul2r.
suff : i2 * nhorizontal + j2 < i1 * nhorizontal + j1.
  by rewrite i1j1E ltnn.
apply: leq_trans (_ : i2.+1 * nhorizontal <= _).
  by rewrite mulSn addnC ltn_add2r.
apply: leq_trans (leq_addr _ _).
by rewrite leq_mul2r.
Qed.
  
Lemma all_set_spec i : bit all_set i = (i <? number_of_cells).
Proof. by apply: bit_decr. Qed.

Lemma first_column_spec i : bit first_column i = (i <? height).
Proof. by apply: bit_decr. Qed.

Lemma full_first_column_spec i : bit full_first_column i = (i <? horizontal).
Proof. by apply: bit_decr. Qed.

Lemma bottom_spec i : 
  bit bottom i = ((i mod horizontal =? 0) && (i <? width * horizontal)).
Proof.
have ncE : to_nat (lsl one number_of_cells) = 2 ^ (nwidth * nhorizontal).
  by rewrite to_nat_lsl_one;[congr (_ ^ _)|].
rewrite bitE to_nat_div to_nat_sub ?ncE; last 2 first.
- by rewrite (@leq_exp2l 2 0).
- by rewrite nwB_pow ltn_exp2l.
rewrite subn1 to_nat_decr; last by [].
rewrite to_nat_lsl_one; last by [].
rewrite mulnC expnM xm1_sum mulKn; last by rewrite -ltnS prednK ?expn_gt0.
under eq_bigr do rewrite -expnM.
rewrite (sum_pow_incr_div_mod (fun i => nhorizontal * i)%N); last 2 first.
- by [].
- by move=> j k /andP[jLk _]; rewrite ltn_mul2l.
rewrite modn_small; last by case: (_ \in _).
rewrite modn_small ?bool1E; last by [].
apply/mapP/andP; last first.
  move=> [/neqbP imh /nltbP iLwh].
  rewrite to_nat_mod in imh.
  rewrite to_nat_mul in iLwh; last by rewrite mulnC whLw.
  exists (to_nat i %/ nhorizontal); last first.
    by rewrite [LHS](divn_eq _ nhorizontal) imh addn0 mulnC.
  by rewrite mem_iota add0n ltn_divLR.
move=> [k]; rewrite mem_iota => kLw iE; split.
  by apply/neqbP; rewrite to_nat_mod iE; apply: modnMr.
apply/nltbP; rewrite iE to_nat_mul ?whLw; last by [].
by rewrite mulnC ltn_mul2r.
Qed.

Lemma top_spec i : 
  bit top i = ((i mod horizontal =? height) && (i <? width * horizontal)).
Proof.
rewrite bit_lsl bottom_spec.
have [dLi|/negP] := nlebP.
  suff -> : i <? width * horizontal = false by rewrite orbT andbF.
  by case: nltbP => // /(leq_ltn_trans dLi).
rewrite -ltnNge => iLd.  
have [iLh|/negP] := nltbP.
  suff -> : i mod horizontal =? height = false by [].
  case: neqbP => //; rewrite to_nat_mod modn_small.
    by move/eqP; case: ltngtP iLh.
  by apply: ltn_trans iLh _.
rewrite -leqNgt => hLi.
have iLwB := to_nat_bounded i.
case: neqbP; rewrite to_nat_mod to_nat_sub //; last first.
case: neqbP=> // /eqP; rewrite to_nat_mod.
  have hLh : to_nat height < nhorizontal by [].
  rewrite -{1}(modn_small hLh) -{1}[to_nat height]add0n -{1}(subnK hLi).
  by rewrite eqn_modDr mod0n => /eqP->.
move=> ihmh_eq0.
case: neqbP; rewrite to_nat_mod; last first.
  case.
  by rewrite -(subnK hLi) -modnDml ihmh_eq0 add0n modn_small.
move=> imhEh.
case: nltbP; case: nltbP => //; last first.
  move=> iLwh; rewrite to_nat_sub // => /negP.
  by rewrite -leqNgt => /(leq_trans iLwh); rewrite ltnNge leq_subr.
move=> /negP; rewrite -leqNgt => iLwh; rewrite to_nat_sub // => ihLwh.
move: imhEh.
rewrite -(subnK iLwh) -modnDmr {2}to_nat_mul; last by apply:whLw.
rewrite modnMr addn0 modn_small; last first.
  apply: ltn_trans (_ : _ < to_nat height) _; last by [].
  by rewrite ltn_subLR // addnC  -ltn_subLR.
by move=> iwhE; rewrite -iwhE subKn ?ltnn in ihLwh.
Qed.

Lemma bit_mhash i : bit mhash i = (i <? lhash).
Proof. by apply: bit_decr. Qed.

Lemma bit_logand2_aux s dir i : 
  dir <=? digits ->
  bit (s land s >> dir land (s land s >> dir) >> (2 * dir)) i =
                   [&&
                       bit s i, bit s (i + dir),
                       bit s (i + 2 * dir) & bit s (i + 3 * dir)].
Proof.
case: nlebP => // dirP1 _.
have iP := to_nat_bounded i.
have dirP := to_nat_bounded dir.
have dir2P := to_nat_bounded (2 * dir).
have dir3P := to_nat_bounded (3 * dir).
have Fp := to_nat_bounded digits.
have F2p : (2 * to_nat digits < nwB).
  apply: ltn_trans (_ : 2 ^ 7 < _); first by [].
  by rewrite nwB_pow ltn_exp2l.
rewrite !(land_spec, bit_lsr).
have [iLd|/negP] := nltbP i digits; last first.
  by rewrite -leqNgt => dLi; rewrite bit_M //; apply/nlebP.  
case: bit => //=. 
have diLwb : to_nat dir + to_nat i < nwB.
  apply: leq_ltn_trans (_ : to_nat digits + to_nat i < _).
    by rewrite leq_add2r.
  apply: ltn_trans (_ : to_nat digits + to_nat digits < _).
    by rewrite ltn_add2l.
  apply: ltn_trans (_ : 2 ^ 7 < _); first by [].
  by rewrite nwB_pow ltn_exp2l.
have -> : i <=? dir + i.
  by apply/nlebP; rewrite to_nat_add // leq_addl.
rewrite add_comm; case: bit => //.
have tdE : to_nat (2 * dir) = (to_nat dir).*2.
  rewrite to_nat_mul mul2n //.
  apply: leq_ltn_trans (_ : ndigits.*2 < _); first by rewrite leq_double.
  apply: ltn_trans (_ : 2 ^ 7 < _); first by [].
  by rewrite nwB_pow ltn_exp2l.
have tdiE : to_nat (2 * dir + i) = ((to_nat dir).*2 + to_nat i)%N.
  rewrite to_nat_add tdE //.
  apply: leq_ltn_trans (_ : ndigits.*2 + to_nat i < _).
    by rewrite leq_add2r // leq_double.
  apply: ltn_trans (_ : ndigits.*2 + ndigits < _).
    by rewrite ltn_add2l.
  apply: ltn_trans (_ : 2 ^ 8 < _); first by [].
  by rewrite nwB_pow ltn_exp2l.
have -> : i <=? 2 * dir + i.
  by apply/nlebP; rewrite tdiE ?leq_addl.
rewrite add_comm; case: bit => //.
have -> :  i + 2 * dir ≤? dir + (i + 2 * dir).
  apply/nlebP; rewrite add_comm tdiE to_nat_add tdiE ? leq_addl //.
  rewrite addnA.
  apply: leq_ltn_trans (_ : ndigits + (to_nat dir).*2 + to_nat i < _).
    by rewrite 2!leq_add2r.
  apply: leq_ltn_trans (_ : ndigits + ndigits.*2 + to_nat i < _).
    by rewrite leq_add2r leq_add2l leq_double.
  apply: ltn_trans (_ : ndigits + ndigits.*2 + ndigits < _).
    by rewrite ltn_add2l.
  apply: ltn_trans (_ : 2 ^ 8 < _); first by [].
  by rewrite nwB_pow ltn_exp2l.
suff -> : dir + (i + 2 * dir) = i + 3 * dir by [].
have -> : 2 = 1 + 1 by []; have -> : 3 = 1 + 1 + 1 by [].
by ring.
Qed. 

Lemma bit_logand2 s dir dir2 : 
  dir <=? digits -> dir2 = 2 * dir ->
  logand2 s dir dir2 = [forall i, 
                       ~~ [&& bit s i, bit s (i + dir),
                              bit s (i + 2 * dir) & bit s (i + 3 * dir)]].
Proof.
move=> Hd Hd2.
rewrite /logand2 is_zeroP /= Hd2.
apply/forallP/forallP => /= H i.
  by have := H i; rewrite bit_logand2_aux.
by rewrite bit_logand2_aux; have := H i.
Qed.

Lemma bit_is_won s  : 
  is_won s  = [exists i,
                [exists dir,
                   [&&
                      dir \in [:: horizontal; vertical; up_left; up_right],
                      bit s i, bit s (i + dir),
                          bit s (i + 2 * dir) & bit s (i + 3 * dir)]]].
Proof.
rewrite /is_won !bit_logand2 // -!negb_exists.
case: existsP => [[i /and4P[Hb1 Hb2 Hb3 Hb4]]|Hh].
  apply/sym_equal/existsP.
  exists i; apply/existsP; exists horizontal.
  by rewrite inE eqxx Hb1 Hb2 Hb3 Hb4.
case: existsP => /= [[i /and4P[Hb1 Hb2 Hb3 Hb4]]|Hv].
  apply/sym_equal/existsP.
  exists i; apply/existsP; exists vertical.
  by rewrite !inE eqxx andTb Hb1 Hb2 Hb3 Hb4.
case: existsP => /= [[i /and4P[Hb1 Hb2 Hb3 Hb4]]|Hur].
  apply/sym_equal/existsP.
  exists i; apply/existsP; exists up_right.
  by rewrite !inE eqxx andTb Hb1 Hb2 Hb3 Hb4.
case: existsP => /= [[i /and4P[Hb1 Hb2 Hb3 Hb4]]|Hul].
  apply/sym_equal/existsP.
  exists i; apply/existsP; exists up_left.
  by rewrite !inE eqxx andTb Hb1 Hb2 Hb3 Hb4.
apply/sym_equal/idP => /existsP [i /existsP [dir /and5P[]]].
rewrite !inE; case/or4P => /eqP-> Hb1 Hb2 Hb3 Hb4.
- by case: Hh; exists i; rewrite Hb1 Hb2 Hb3 Hb4.
- by case: Hv; exists i; rewrite Hb1 Hb2 Hb3 Hb4.
- by case: Hul; exists i; rewrite Hb1 Hb2 Hb3 Hb4.
by case: Hur; exists i; rewrite Hb1 Hb2 Hb3 Hb4.
Qed.

Definition get_column (state : int) (i : int) :=
  (state >> (i * horizontal)) land full_first_column.

Lemma get_column0 i : get_column 0 i = 0.
Proof. by rewrite /get_column lsr0 land0. Qed.

Lemma bit_get_column0 s i j :  height <? j -> bit (get_column s i) j = false.
Proof.
have iB := to_Z_bounded i.
have jB := to_Z_bounded j.
case: nltbP => // hLj _.
have hEh : nhorizontal = (to_nat (height) + 1)%nat by [].
rewrite /get_column land_spec full_first_column_spec.
case: nltbP => [|]; last by rewrite andbF.
by rewrite [X in (_ < X)%nat]hEh addn1 ltnS leqNgt hLj.
Qed.

Lemma bit_get_column s i j : 
  j <=? height ->
 (to_nat i * nhorizontal + to_nat j < nwB)%nat ->
  bit (get_column s i) j = bit s ((i * horizontal) + j).
Proof.
have iB := to_Z_bounded i.
have jB := to_Z_bounded j.
case: nlebP => // jLh _ ijLw.
have hEh : nhorizontal = (to_nat (height) + 1)%nat by [].
rewrite /get_column land_spec full_first_column_spec.
case: nltbP => [_|]; last first.
  by rewrite [to_nat horizontal]hEh addn1 ltnS.
have ihE : to_nat (i * horizontal) = (to_nat i * nhorizontal)%nat.
  by rewrite to_nat_mul // (leq_ltn_trans _ ijLw) // leq_addr.
rewrite andbT bit_lsr; case: nlebP => //.
by rewrite to_nat_add ihE // leq_addl.
Qed.

Lemma bit_get_columnW s i j : 
  i <=? width -> j <=? height ->
  bit (get_column s i) j = bit s ((i * horizontal) + j).
Proof.
move=> iLw jLh.
apply: bit_get_column => //.
case: nlebP iLw jLh => //; case: nlebP => // jLh iLw _ _.
apply: leq_ltn_trans (_ : to_nat width * nhorizontal + to_nat height < _)%nat;
    last first.
  apply: leq_ltn_trans (_ : 2 ^ 6 < _)%nat; first by [].
  by rewrite nwB_pow ltn_exp2l.
apply: leq_trans (_ : to_nat width * nhorizontal + to_nat j <= _)%nat.
  by rewrite leq_add2r leq_pmul2r.
by rewrite leq_add2l.
Qed.

(** (one)^*(zero)^+ *)
Definition opzs (b : int) (i : int) :=
  [exists j : int, (j <=? b) && [forall k : int,  bit i k == (k <? j)]].

Lemma opzsE b i :
  b <? digits -> opzs b i = [exists j, (j <=? b) && (i == decr (lsl one j))].
Proof.
case: ltbP => // bLd _.
apply/existsP/existsP => [[k /andP[kLb /forallP Hb]]|[k /andP[kLb /eqP iEd]]].
  exists k; rewrite kLb.
  have kLd : k <? digits by apply/ltbP; case: lebP kLb => //; lia.
  apply/eqP/bit_ext => j.
  by rewrite bit_decr; have := eqP (Hb j).
exists k; rewrite kLb; apply/forallP => j.
have kLd : k <? digits by apply/ltbP; case: lebP kLb => //; lia.
by rewrite iEd bit_decr.
Qed.

Lemma opzs0 b : opzs b 0.
Proof.
apply/existsP; exists 0.
case: nlebP => // _; apply/forallP => k.
by rewrite bit_0; case: nltbP.
Qed.

Lemma opzsE' b i :
  b <? digits -> 
  opzs b i = (up_log2 i <=? b) && (i == decr (lsl one (up_log2 i))).
Proof.
move=> bLd; rewrite (opzsE _ bLd).
apply/existsP/andP=> [[j /andP[jLb /eqP iE]]|[/nlebP uiLb /eqP iE]]; last first.
  exists (up_log2 i); rewrite -iE eqxx andbT.
  by apply/nlebP.
rewrite /up_log2; case: eqP => [->|i_neq0]; first by split => //; apply/nlebP.
case: (neqbP j 0) => [/to_nat_inj jE|jD0]; first by rewrite iE jE in i_neq0.
have j_pos : 0 < to_nat j by case: (to_nat _) jD0.
have jB := to_nat_bounded j.
have tjE : to_nat (decr j) = (to_nat j).-1 by apply/to_nat_decr/nltbP.
have jE : log2 i = decr j.
  apply: log2E; rewrite tjE prednK //.
  have jLd : to_nat j < ndigits.
    apply: leq_trans (_ : to_nat b < ndigits)%N; last by apply/nltbP.
    by rewrite ltnS; apply/nlebP.
  rewrite iE to_nat_decr; last first.
    by apply/nltbP; rewrite to_nat_lsl_one ?expn_gt0.
  rewrite -ltnS to_nat_lsl_one // prednK ?leqnn ?andbT ?expn_gt0 //.
  by rewrite ltn_exp2l // prednK.
rewrite jE; split; last first.
  suff -> : incr (decr j) = j by apply/eqP.
  apply: to_nat_inj.
  by rewrite to_nat_incr ?tjE ?prednK.
by apply/nlebP; rewrite to_nat_incr tjE prednK //; apply/nlebP.
Qed.

Lemma opzsE'' b i :
  b <? digits -> 
  opzs b i = 
  (to_nat (up_log2 i) <= to_nat b) && (to_nat i == (2 ^ to_nat (up_log2 i)).-1).
Proof.
move => /nltbP bLd; rewrite opzsE'; last by apply/nltbP.
apply/andP/andP => [[/nlebP iLb /eqP iE] | [iLb /eqP iE]].
  have uiLd : to_nat (up_log2 i) < ndigits.
    by apply: leq_ltn_trans (_ : to_nat b < _).
  split => //.
  rewrite {1}iE to_nat_decr 1?to_nat_lsl_one //.
  by apply/nltbP; rewrite to_nat_lsl_one ?expn_gt0.
split; first by apply/nlebP.
have uiLd : to_nat (up_log2 i) < ndigits.
  by apply: leq_ltn_trans (_ : to_nat b < _).
apply/eqP/to_nat_inj; rewrite iE to_nat_decr 1?to_nat_lsl_one //.
by apply/nltbP; rewrite to_nat_lsl_one ?expn_gt0.
Qed.

Definition cell (w : int) (i : nat) (j : nat) := 
  bit w (of_nat i * horizontal + of_nat j).

Lemma cell_0 i j : cell 0 i j = false.
Proof. by rewrite /cell bit_0. Qed.

Lemma cell_get_column w i j : 
  i < nwidth -> j < nhorizontal -> 
  cell w i j = bit (get_column w (of_nat i)) (of_nat j).
Proof.
move=> iB jB.
have iB' : i < nwB by apply: leq_trans iB (ltnW nwidthLwB).
have jB' : j < nwB by apply: leq_trans jB (ltnW nhorizontalLwB).
have ihjB : i * nhorizontal + j < nwB.
  apply: ltn_trans (_ : i * nhorizontal + nhorizontal < _).
    by rewrite ltn_add2l.
  apply: leq_ltn_trans (_ : nwidth * nhorizontal + nhorizontal < _).
    by rewrite leq_add2r leq_pmul2r // ltnW.
  apply: ltn_trans (_ : 2 ^ 6 < _); first by [].
  by rewrite nwBE Z2Nat.inj_pow.
rewrite /cell /get_column land_spec full_first_column_spec.
case: nltbP => [_|[]]; last first.
  by rewrite of_natK //; apply : leq_trans jB _.
rewrite andbT bit_lsr.
case: nlebP => // [] [].
rewrite to_nat_add; first by by apply: leq_addl.  
rewrite to_nat_mul ?of_natK //.
rewrite -[to_nat _]/nhorizontal.
by apply: leq_ltn_trans ihjB; rewrite leq_addr.
Qed.

Definition hwin s := 
  [exists x : 'I_nwidth,  
  [exists y : 'I_nheight, 
     [&& x.+3 < nwidth, cell s x y, cell s x.+1 y, cell s x.+2 y & cell s x.+3 y]]].

Definition vwin s := 
  [exists x : 'I_nwidth,  
  [exists y : 'I_nheight, 
     [&& y.+3 < nheight, cell s x y, cell s x y.+1, cell s x y.+2 & cell s x y.+3]]].

Definition uwin s := 
  [exists x : 'I_nwidth,  
  [exists y : 'I_nheight, 
     [&& x.+3 < nwidth, y.+3 < nheight, cell s x y, cell s x.+1 y.+1, cell s x.+2 y.+2 & cell s x.+3 y.+3]]].

Definition dwin s := 
  [exists x : 'I_nwidth,  
  [exists y : 'I_nheight, 
     [&& x.+3 < nwidth, 2 < y, cell s x y, cell s x.+1 y.-1, cell s x.+2 y.-2 & cell s x.+3 y.-2.-1]]].

Definition cwin s := [|| hwin s, vwin s, uwin s | dwin s].

Definition wf_state (w : int) := 
  [forall i, bit w i ==> (i <? width * horizontal)] &&
  [forall i, (i <? width) ==> opzs height (get_column w i)].

Lemma wf_state0 : wf_state 0.
Proof.
apply/andP; split; apply/forallP => i; rewrite ?bit_0 //.
by rewrite get_column0 opzs0 implybT.
Qed.

Lemma wf_state_opzs w i :
  i < nwidth -> wf_state w -> opzs height (get_column w (of_nat i)).
Proof.
move=> iLw /andP[_ /forallP/(_ (of_nat i))]/implyP->//.
by apply/nltbP; rewrite of_natK // (ltn_trans _ nwidthLwB) //.
Qed.

Lemma wf_state_true_width w i : 
  wf_state w -> bit w i -> (to_nat i %/ nhorizontal < nwidth).
Proof.
move=> Hwf Hb; rewrite ltn_divLR //.
have /andP[/forallP/(_ i)/implyP/(_ Hb)] := Hwf.
by case: nltbP.
Qed.

Lemma wf_state_bit_false w i : 
  wf_state w -> nwidth * nhorizontal <= to_nat i -> ~~ bit w i.
Proof.
move=> Hwf whLi.
have /andP[/forallP/(_ i)/implyP] := Hwf.
case: bit => // /(_ isT).
by case: nltbP; rewrite to_nat_mul ?whLw // ltnNge whLi.
Qed.

Lemma bit_get_column_exclude w j k l :
  wf_state w ->
  j < nwidth ->
  k < nwidth ->
  bit (lsl (get_column w (of_nat j)) (of_nat j * horizontal)) l = true ->
  bit (lsl (get_column w (of_nat k)) (of_nat k * horizontal)) l = true -> j = k.
Proof.
move=> Hwf jLw kLw.
have lB := to_nat_bounded l.
have jB : j < nwB by apply: leq_trans jLw (ltnW nwidthLwB).
have kB : k < nwB by apply: leq_trans kLw (ltnW nwidthLwB).
rewrite !bit_lsl.
case: nlebP; first by rewrite !orbT.
rewrite !orbF => /negP; rewrite -ltnNge => lLd.
case: nltbP => // /negP; rewrite -leqNgt => jhLl.
case: nltbP => // /negP; rewrite -leqNgt => khLl.
rewrite to_nat_mul 1?of_natK // -[to_nat _]/nhorizontal in jhLl; last first.
  apply: leq_ltn_trans whLw.
  by rewrite leq_pmul2r // ltnW.
rewrite to_nat_mul 1?of_natK // -[to_nat _]/nhorizontal in khLl; last first.
  apply: leq_ltn_trans whLw.
  by rewrite leq_pmul2r // ltnW.
wlog : j k kLw jLw  jhLl khLl kB jB / (j <= k)%nat.
  move=> Hbjk Hbj Hbk.
  case: (leqP j k) => [jLk|kLj]; first by apply: Hbjk. 
  by apply/sym_equal/Hbjk => //; apply: ltnW.
rewrite leq_eqVlt => /orP[/eqP //|jLk].
rewrite bit_get_column0 //.
case: nltbP => // [] [].
rewrite to_nat_sub // ihE //.
have -> : (to_nat height).+1 = nhorizontal by [].
by rewrite leq_subRL // addnC -mulSn (leq_trans _ khLl) // leq_pmul2r.
Qed.

Lemma wf_stateE w : 
  wf_state w -> 
  w = \big[add/0]_(i < nwidth) 
  (lsl (get_column w (of_nat i)) (of_nat i * horizontal)).
Proof.
move=> Hwf.
apply: bit_ext => i.
have iB := to_nat_bounded i.
pose u := (to_nat i %/ nhorizontal).
pose v := (to_nat i %% nhorizontal).
pose f i := lsl (get_column w (of_nat i)) (of_nat i * horizontal).
rewrite (big_lor_add _ xpredT f) /f; last first.
  move=> j k l jLw kLw _ _.
  by apply: bit_get_column_exclude.
have [wLu|uLw] := (leqP nwidth u).
  have -> := (big_bit_lor xpredT f).
  rewrite big1 => [|/= j _].
    case bE : bit => //.
    suff : ~~(nwidth <= u) by move/negP.
    rewrite -ltnNge.
    by apply: wf_state_true_width Hwf _.
  have jLwb: (j < nwB)%nat by apply: ltn_trans nwidthLwB.
  rewrite bit_lsl.
  case: nlebP; rewrite (orbF, orbT) // => /negP.
  rewrite -ltnNge => iLd.
  case: nltbP => // /negP.
  rewrite -leqNgt => jhLi.
  have jhE : to_nat (of_nat j * horizontal) = (j * nhorizontal)%N.
    by apply: ihE.
  rewrite jhE // in jhLi.
  have := @bit_get_column0 w (of_nat j) (i - of_nat j * horizontal).
  case: nltbP => [_|/negP]; first by apply.
  rewrite -leqNgt to_nat_sub ?jhE // -ltnS -[(to_nat height).+1]/nhorizontal
        => ijLh _.
  suff : u < nwidth by rewrite ltnNge wLu.
  apply: leq_trans (ltn_ord j). 
  by rewrite ltn_divLR // mulSn addnC -ltn_subLR.
have uLwB : (u < nwB)%nat by apply: ltn_trans nwidthLwB.
pose uo := Ordinal uLw.
rewrite (bigD1 uo) //= /olor lor_spec.
have HP : (fun i : 'I_nwidth => i != uo) =i (fun i : 'I_nwidth => i != u :> nat).
  move=> j.
  rewrite /in_mem /=.
  apply/idP/idP; first by move=> /eqP/val_eqP.
  by move=> H; apply/eqP/val_eqP.
rewrite (eq_bigl _ _ HP) /in_mem /=.
have -> := (big_bit_lor (fun i1 : nat =>  i1 != u) f). 
rewrite big1 => [|/= j jDu].
  rewrite orbF bit_lsl.
  case: nlebP; rewrite (orbF, orbT) => Ld.
    by rewrite bit_M //; case: nlebP.
  have uhE :  to_nat (of_nat u * horizontal) = (u * nhorizontal)%nat.
    rewrite to_nat_mul 1?of_natK //.
    apply: leq_ltn_trans iB.
    by rewrite (divn_eq (to_nat i) nhorizontal) leq_addr.  
  case: nltbP; rewrite uhE.
    by rewrite ltnNge (divn_eq (to_nat i) nhorizontal) leq_addr.
  move=> /negP; rewrite -leqNgt => uhLi.
  have iuhE :  to_nat (i - of_nat u * horizontal) = v.
    rewrite to_nat_sub ?uhE //.
    by rewrite (divn_eq (to_nat i) nhorizontal) addnC addnK.
  rewrite bit_get_column //.
  - congr bit.
    apply: to_nat_inj.
    by rewrite to_nat_add uhE iuhE // -divn_eq.
  - case: nlebP => // [] [].
    rewrite iuhE -ltnS.
    by apply: ltn_pmod.
  by rewrite iuhE 1?of_natK // -divn_eq.
have jLwB : (j < nwB)%nat by apply: ltn_trans nwidthLwB.
rewrite bit_lsl.
case: nlebP; rewrite (orbT, orbF) // => /negP.
rewrite -ltnNge => iLd.
case: nltbP => // /negP.
rewrite -leqNgt => jhLi.
have jhE : to_nat (of_nat j * horizontal) = (j * nhorizontal)%nat.
  by apply: ihE.
rewrite jhE in jhLi.
have := @bit_get_column0 w (of_nat j) (i - of_nat j * horizontal).
case: nltbP => [_|/negP]; first by apply.
rewrite -leqNgt to_nat_sub ?jhE // -ltnS -[(to_nat height).+1]/nhorizontal
    => ijLh _.
case/eqP: jDu.
apply/sym_equal/divn_inv.
by rewrite jhLi mulSn addnC -ltn_subLR.
Qed.

Lemma ltn_to_nat_get_column s i : 
  (to_nat (get_column s i) < 2 ^ nhorizontal)%nat.
Proof.
rewrite to_nat_sum -[nhorizontal]/(nheight.+1).
apply: leq_ltn_trans (sum_pow2 _).
have /(big_ord_widen _ _)-> : (nheight.+1 <= ndigits)%nat by [].
have -> /= := @big_mkcond nat _  addn _ 
  (index_enum (ordinal ndigits)) 
  (fun i => i < nheight.+1)%nat (fun i => 2 ^ i)%nat .
apply: leq_sum => j _.
case: ltnP => nLj; first by case: bit; rewrite (mul0n, mul1n).
rewrite bit_get_column0 //.
case: nltbP => //.
by rewrite of_natK // (leq_trans (ltn_ord _)) // (ltnW ndigitsLwB).
Qed.

Lemma wf_state_to_natE w : 
  wf_state w -> 
  to_nat w = 
    \sum_(i < nwidth) 
      (to_nat (get_column w (of_nat i)) * 2 ^ (i * nhorizontal)).
Proof.
move=> Hw.
rewrite [in LHS](wf_stateE Hw).
pose f i := lsl (get_column w (of_nat i)) (of_nat i * horizontal).
have ->// := to_nat_add_exclude nwidth xpredT
               (fun i => lsl (get_column w (of_nat i)) (of_nat i * horizontal)).
  apply: eq_bigr => /= i _.
  have iLwB : (i < nwB)%nat by apply: ltn_trans nwidthLwB.
  rewrite to_nat_lslW to_nat_mul 1?of_natK //.
    rewrite modn_small //.
    apply: leq_trans (_ : _ < 2 ^ nhorizontal * 2 ^ (i * nhorizontal))%nat _.
      rewrite ltn_pmul2r; first by apply: ltn_to_nat_get_column.
      by rewrite expn_gt0.
    rewrite -expnD.
    apply: leq_trans (_ : _ <= 2 ^ (nwidth * nhorizontal))%nat _.
      apply: leq_pexp2l => //.
      by rewrite mulnC -mulnS mulnC leq_pmul2r.
    have -> : nwB = (2 ^ ndigits)%nat.
      apply: Nat2Z.inj.
      rewrite nwBE [LHS]Z2Nat.id; last by [].
      by rewrite Z_of_nat_exp.
    by apply: leq_pexp2l.
  apply: ltn_trans whLw.
  by rewrite ltn_pmul2r.
by move=> j k l jLw kLw _ _; apply: bit_get_column_exclude.
Qed.

Lemma wf_state_cell s x y z : 
  wf_state s -> x < nwidth -> y < nhorizontal -> 
  z < y -> cell s x y -> cell s x z.
Proof.
move=> Hwf xLw yLh zLy.
have xLwb : x < nwB by apply: ltn_trans nwidthLwB.
rewrite !cell_get_column //; last by apply: ltn_trans yLh.
have : opzs height (get_column s (of_nat x)).
  have /andP[_ /forallP/(_ (of_nat x))/implyP->//] := Hwf.
  by case: nltbP; rewrite of_natK.
rewrite opzsE // => /existsP[/= u /andP[/nlebP uLh /eqP] ->].
have uLd : u <? digits.
  by case: nltbP => // [] []; apply: leq_ltn_trans (isT : nheight < ndigits).
rewrite !bit_decr //.
have yLwB : y < nwB by apply: ltn_trans nhorizontalLwB.
have zLwB : z < nwB by apply: ltn_trans yLwB.
(do 2 case: nltbP); rewrite of_natK // of_natK // => nzLu yLu; case: nzLu.
by apply: ltn_trans yLu.
Qed.

Lemma to_nat_all_set : to_nat all_set = (2 ^ (nwidth * nhorizontal)).-1.
Proof.
rewrite to_nat_decr; last by [].
rewrite to_nat_lsl_one; last by [].
by congr (_ ^ _).-1.
Qed.

Lemma bottomE : to_nat bottom = \sum_(i < nwidth) 2 ^ (i * nhorizontal).
Proof.
rewrite to_nat_div to_nat_all_set.
rewrite to_nat_decr; last by [].
rewrite to_nat_lsl_one; last by [].
suff -> : (2 ^ (nwidth * nhorizontal)).-1 =
       ((2 ^ to_nat horizontal).-1 * \sum_(i < nwidth)  2 ^ (i * nhorizontal))%N.
  by rewrite mulKn.
have -> : (2 ^ (nwidth * nhorizontal)).-1 = 
          (((2 ^ nhorizontal) ^ nwidth) - 1 ^ nwidth)%N.
  by rewrite mulnC expnM exp1n subn1.
rewrite subn_exp subn1.
congr ((_ ^ _).-1 * _)%N.
rewrite [RHS](sum_rev _ (fun i => 2 ^ (i * nhorizontal))%N).
apply: eq_bigr => i _.
by rewrite exp1n muln1 -expnM mulnC.
Qed.

Lemma wf_state_button w : 
  wf_state w -> 
  to_nat (bottom + w) = 
    \sum_(i < nwidth) 
    (2 ^ (to_nat (up_log2 (get_column w (of_nat i))))) * 2 ^ (i * nhorizontal).
Proof.
move=> Hw.
suff Hf : (to_nat bottom + to_nat w)%N = 
          \sum_(i < nwidth)  
        2 ^ to_nat (up_log2 (get_column w (of_nat i))) * 2 ^ (i * nhorizontal).
  rewrite to_nat_add // Hf.
  apply: leq_trans ( _ : 2 ^ (nwidth * nhorizontal) <= _); last first.
    by rewrite nwB_pow leq_exp2l.
  pose f i := 2 ^ to_nat (up_log2 (get_column w (of_nat i))).
  apply: (sum_exp_bound _ _ f) => i iLn; rewrite /f.
  have : opzs height (get_column w (of_nat i)).
    case/andP: Hw => _ /forallP/(_ (of_nat i))/implyP-> //.
    by apply/nltbP; rewrite of_natK // (ltn_trans _ nwidthLwB).
  rewrite opzsE'' // => /andP[Hle _].
  apply: leq_ltn_trans (_ : 2 ^ to_nat height < _); first by rewrite leq_exp2l.
  by rewrite ltn_exp2l.
rewrite bottomE wf_state_to_natE // -big_split /=.
apply: eq_bigr => i _.
rewrite -mulSn; congr (_ * _)%N.
have : opzs height (get_column w (of_nat i)).
  case/andP: Hw => _ /forallP/(_ (of_nat i))/implyP-> //.
  by apply/nltbP; rewrite of_natK // (ltn_trans _ nwidthLwB).
by rewrite opzsE'' // => /andP[_ /eqP->]; rewrite prednK // expn_gt0.
Qed.

Lemma cell_lor s1 s2 i j : cell (s1 lor s2) i j =  cell s1 i j || cell s2 i j.
Proof. by rewrite [LHS]lor_spec. Qed.

Lemma cell_height s i : i < nwidth -> wf_state s -> ~~ cell s i nheight.
Proof.
move=> iLw sWf; apply/negP.
have iLwb : i < nwB by apply: ltn_trans nwidthLwB.
rewrite cell_get_column //.
have /existsP[/= k /andP[kLh /forallP/(_ height)]/eqP->] : 
    opzs height (get_column s (of_nat i)).
  by apply: wf_state_opzs => //; apply/nltbP; rewrite of_natK.
case: nltbP => //.
by case: nlebP kLh => //; rewrite ltnNge => ->.
Qed.

Lemma cell_width s j : j < nhorizontal -> wf_state s -> ~~ cell s nwidth j.
Proof.
move=> jLh sWf; apply/negP.
have jLw : j < nwB by rewrite (leq_trans jLh) // ltnW // nhorizontalLwB.
rewrite /cell => Hcc.
have : to_nat (width * horizontal + of_nat j) %/ nhorizontal < nwidth.
  by apply: wf_state_true_width sWf _.
suff -> : to_nat (width * horizontal + of_nat j) %/ nhorizontal = nwidth.
  by [].
rewrite to_nat_add ?of_natK //.
  rewrite to_nat_mul; last by apply: whLw.
  by rewrite divnMDl // divn_small.
rewrite to_nat_mul; last by apply: whLw.
apply: leq_trans (_ : to_nat width * to_nat horizontal + nhorizontal <= _).
  by rewrite ltn_add2l.
apply: leq_trans (_ : 2 ^ 8 <= _); first by [].
by rewrite nwB_pow leq_exp2l.
Qed.

Lemma of_nat_int_add_mod i j : 
  i = of_nat (to_nat i %/ to_nat j) * j + of_nat (to_nat i %% to_nat j).
Proof.
rewrite [LHS](int_add_mod i j); congr (_ * _ + _); apply: to_nat_inj.
  rewrite of_natK; first by rewrite to_nat_div.
  by apply: leq_ltn_trans (leq_div _ _) (to_nat_bounded _).
  rewrite of_natK; first by rewrite to_nat_mod.
by apply: leq_ltn_trans (leq_mod _ _) (to_nat_bounded _).
Qed.

Lemma bit_cell s i : 
  bit s i = cell s (to_nat i %/ nhorizontal) (to_nat i %% nhorizontal).
Proof. by rewrite [in LHS](of_nat_int_add_mod i horizontal). Qed.

Lemma is_won_cwin w b : wf_state (w lor b) -> is_won w = cwin w.
Proof.
move=> Hw.
have fLwB : 4 < nwB by rewrite nwB_pow (@ltn_exp2l 2 2).
have wLwB  : nwidth < nwB by rewrite nwB_pow  (leq_trans _ (_ : 2 ^ 3 <= _)).
have hLwB  : nheight < nwB by rewrite nwB_pow  (leq_trans _ (_ : 2 ^ 3 <= _)).
have Hv k l m : k * horizontal + l + m * horizontal = (k + m) * horizontal + l.
  rewrite -add_assoc add_comm -add_assoc add_comm; congr (_ + _).
  by rewrite -mul_add_distr_r add_comm.
have Hr k l m : 
   k * horizontal + l + m * up_right =  (k + m) * horizontal + (l + m).
  have -> : up_right = horizontal + 1 by [].
  rewrite !(mul_add_distr_r, mul_add_distr_l) -!add_assoc; congr (_ + _).
  rewrite add_comm -add_assoc; congr (_ + _).
  by rewrite mul_comm mul_1_l add_comm.
have Hl k l m : 
  k * horizontal + l + m * up_left = (k + m) * horizontal + (l - m).
  have -> : up_left = horizontal - 1 by [].
  rewrite !minus_addE !(mul_add_distr_r, mul_add_distr_l) -!add_assoc; congr (_ + _).
  rewrite add_comm -!add_assoc; congr (_ + _).
  rewrite add_comm; congr (_ + _).
  by rewrite mul_comm mul_N1_l.
rewrite bit_is_won.
apply/existsP/or4P => /= [[x /existsP[/= dir /andP[]]]|].
  rewrite !inE => /or4P[]/eqP-> /and4P[Hb1 Hb2 Hb3 Hb4].
  - apply: Or41; apply/existsP=> /=.
    pose v := x / horizontal.
    have vB : (to_nat v < nwidth)%N.
      by rewrite to_nat_div (wf_state_true_width Hw) // lor_spec Hb1.
    exists (Ordinal vB) => /=.
    pose r := x mod horizontal.
    have rB : (to_nat r < nheight)%N.
      have : to_nat r < nhorizontal by rewrite to_nat_mod ltn_mod.
      rewrite leq_eqVlt => /orP[/eqP He|//].
      have He1 : to_nat r = nheight by case: He.
      have /negP[] : ~~ cell (w lor b) (to_nat v) (to_nat r).
        by rewrite He1 (cell_height _ Hw).
      by rewrite cell_lor /cell !to_natK // -int_add_mod // Hb1.
    apply/existsP; exists (Ordinal rB) => /=.
    have Fv k : k < 4 -> of_nat (to_nat v + k) = v + of_nat k.
      move=> kL4.
      have kLwB : k < nwB.
        apply: leq_trans kL4 _.
        by rewrite nwB_pow (@leq_exp2l 2 2).
      have vkLb : to_nat v + k < nwB.
        apply: ltn_trans (_ : to_nat v + 4 < _); first by rewrite ltn_add2l.
        apply: ltn_trans (_ : nwidth + 4 < _); first by rewrite ltn_add2r.
        apply: ltn_trans (_ : 2 ^8 < _); first by[].
        by rewrite nwB_pow ltn_exp2l.
      apply: to_nat_inj; rewrite of_natK //.
      by rewrite to_nat_add of_natK.
    move: vB; rewrite  leq_eqVlt => /orP[/eqP He |vB].
      have /negP[] : ~~ cell (w lor b) (to_nat v).+1 (to_nat r).
        rewrite He.
        apply: cell_width Hw => //.
        by apply: leq_trans rB _.
      rewrite cell_lor /cell; apply/orP; left.
      rewrite !to_natK // -addn1 Fv //.
      rewrite mul_add_distr_r mul_1_l -add_assoc [_ + r]add_comm add_assoc.
      by rewrite -int_add_mod.
    move: vB; rewrite  leq_eqVlt => /orP[/eqP He |vB].
      have /negP[] : ~~ cell (w lor b) (to_nat v).+2 (to_nat r).
        rewrite He.
        apply: cell_width Hw => //.
        by apply: leq_trans rB _.
      rewrite cell_lor /cell; apply/orP; left.
      rewrite !to_natK // -addn2 Fv //.
      rewrite mul_add_distr_r -add_assoc [_ + r]add_comm add_assoc.
      by rewrite -int_add_mod.
    move: vB; rewrite  leq_eqVlt => /orP[/eqP He |vB].
      have /negP[] : ~~ cell (w lor b) (to_nat v).+3 (to_nat r).
        rewrite He.
        apply: cell_width Hw => //.
        by apply: leq_trans rB _.
      rewrite cell_lor /cell; apply/orP; left.
      rewrite !to_natK // -addn3 Fv //.
      rewrite mul_add_distr_r -add_assoc [_ + r]add_comm add_assoc.
      by rewrite -int_add_mod.
    rewrite vB //=.
    rewrite /cell !to_natK.
    rewrite -addn3 Fv // -Hv -addn2 Fv // -Hv -addn1 Fv // -Hv.
    by rewrite -int_add_mod Hb1 Hb2 Hb3 Hb4.
  - apply: Or42; apply/existsP=> /=.
    pose v := x / horizontal.
    have vB : (to_nat v < nwidth)%N.
      by rewrite to_nat_div (wf_state_true_width Hw) // lor_spec Hb1.
    exists (Ordinal vB) => /=.
    pose r := x mod horizontal.
    have rB : (to_nat r < nheight)%N.
      have : to_nat r < nhorizontal by rewrite to_nat_mod ltn_mod.
      rewrite leq_eqVlt => /orP[/eqP He|//].
      have He1 : to_nat r = nheight by case: He.
      have /negP[] : ~~ cell (w lor b) (to_nat v) (to_nat r).
        by rewrite He1 (cell_height _ Hw).
      rewrite cell_lor /cell; apply/orP; left;
      by rewrite !to_natK // -int_add_mod.
    apply/existsP; exists (Ordinal rB) => /=.
    have Fr k : k < 4 -> of_nat (to_nat r + k) = r + of_nat k.
      move=> kL4.
      have kLwB : k < nwB.
        apply: leq_trans kL4 _.
        by rewrite nwB_pow (@leq_exp2l 2 2).
      have vkLb : to_nat r + k < nwB.
        apply: ltn_trans (_ : to_nat r + 4 < _); first by rewrite ltn_add2l.
        apply: ltn_trans (_ : nheight + 4 < _); first by rewrite ltn_add2r.
        apply: ltn_trans (_ : 2 ^8 < _); first by[].
        by rewrite nwB_pow ltn_exp2l.
      apply: to_nat_inj; rewrite of_natK //.
      by rewrite to_nat_add of_natK.
    move: rB; rewrite  leq_eqVlt => /orP[/eqP He |rB].
      have /negP[] : ~~ cell (w lor b) (to_nat v) (to_nat r).+1.
        by rewrite He; apply: cell_height Hw.
      rewrite cell_lor /cell; apply/orP; left.
      rewrite !to_natK //.
      by rewrite -addn1 Fr // add_assoc -int_add_mod.
    move: rB; rewrite  leq_eqVlt => /orP[/eqP He |rB].
      have /negP[] : ~~ cell (w lor b) (to_nat v) (to_nat r).+2.
        by rewrite He; apply: cell_height Hw.
      rewrite cell_lor /cell; apply/orP; left; rewrite !to_natK //.
      by rewrite -addn2 Fr // add_assoc -int_add_mod.
    move: rB; rewrite  leq_eqVlt => /orP[/eqP He |rB].
      have /negP[] : ~~ cell (w lor b) (to_nat v) (to_nat r).+3.
        by rewrite He; apply: cell_height Hw.
      rewrite cell_lor /cell; apply/orP; left; rewrite !to_natK //.
      by rewrite -addn3 Fr // add_assoc -int_add_mod.
    rewrite rB //=.
    rewrite /cell !to_natK.
    rewrite -addn3 Fr // -addn2 Fr // -addn1 Fr // !add_assoc.
    by rewrite -int_add_mod Hb1 Hb2 Hb3 Hb4.
  - apply: Or44; apply/existsP=> /=.
    pose v := x / horizontal.
    have vB : (to_nat v < nwidth)%N.
      by rewrite to_nat_div (wf_state_true_width Hw) // lor_spec Hb1.
    exists (Ordinal vB) => /=.
    pose r := x mod horizontal.
    have rB : (to_nat r < nheight)%N.
      have : to_nat r < nhorizontal by rewrite to_nat_mod ltn_mod.
      rewrite leq_eqVlt => /orP[/eqP He|//].
      have He1 : to_nat r = nheight by case: He.
      have /negP[] : ~~ cell (w lor b) (to_nat v) (to_nat r).
        by rewrite He1 (cell_height _ Hw).
      rewrite cell_lor /cell; apply/orP; left.
      by rewrite !to_natK // -int_add_mod.
    apply/existsP; exists (Ordinal rB) => /=.
    have Fv k : k < 4 -> of_nat (to_nat v + k) = v + of_nat k.
      move=> kL4.
      have kLwB : k < nwB.
        apply: leq_trans kL4 _.
        by rewrite nwB_pow (@leq_exp2l 2 2).
      have vkLb : to_nat v + k < nwB.
        apply: ltn_trans (_ : to_nat v + 4 < _); first by rewrite ltn_add2l.
        apply: ltn_trans (_ : nwidth + 4 < _); first by rewrite ltn_add2r.
        apply: ltn_trans (_ : 2 ^8 < _); first by[].
        by rewrite nwB_pow ltn_exp2l.
      apply: to_nat_inj; rewrite of_natK //.
      by rewrite to_nat_add of_natK.
    have Fr k :
        k <= to_nat r -> to_nat r < nwB -> of_nat (to_nat r - k) = r - of_nat k.
      move=> kLr rLw.
      have kLwB : k < nwB by apply: leq_ltn_trans kLr _.
      apply: to_nat_inj; rewrite of_natK //; last first.
        by apply: leq_trans rLw; rewrite ltnS leq_subr.
      by rewrite to_nat_sub // of_natK.
    have rLw : to_nat r < nwB.
      by apply: ltn_trans rB hLwB.  
    have : 0 <= to_nat r by []; rewrite  leq_eqVlt => /orP[/eqP He |r1B].
      have /negP[] : ~~ cell (w lor b) (to_nat v) nheight.
        by apply: cell_height Hw.
      rewrite cell_lor /cell; apply/orP; left; rewrite to_natK //.
      suff -> : v * horizontal = x by [].
      rewrite (int_add_mod x horizontal) -/v -/r.
      suff -> : r = 0 by rewrite add_comm add_0_l.
      by apply: to_nat_inj.
    move: vB; rewrite  leq_eqVlt => /orP[/eqP He |vB].
      have /negP[] : ~~ cell (w lor b) (to_nat v).+1 (to_nat r).-1.
        rewrite He.
        apply: cell_width Hw => //.
        rewrite prednK // ltnW //.
        by apply: leq_trans rB _.
      rewrite cell_lor /cell; apply/orP; left.
      rewrite -addn1 -subn1 Fv // Fr //=.
      by rewrite -Hl mul_1_l -int_add_mod.
    move: r1B; rewrite  leq_eqVlt => /orP[/eqP He |r1B].
      have /negP[] : ~~ cell (w lor b) (to_nat v).+1 nheight.
        by apply: cell_height Hw.
      rewrite cell_lor /cell; apply/orP; left.
      rewrite -addn1 Fv // mul_add_distr_r mul_1_l -add_assoc.
      have -> : (horizontal + of_nat nheight) = 1 + 2 * up_left by [].
      have <- : r = 1 by apply: to_nat_inj.
      by rewrite add_assoc -int_add_mod.
    move: vB; rewrite  leq_eqVlt => /orP[/eqP He |vB].
      have /negP[] : ~~ cell (w lor b) (to_nat v).+2 (to_nat r).-2.
        rewrite He.
        apply: cell_width Hw => //.
        by rewrite -subn2 (leq_ltn_trans (leq_subr _ _)) // (leq_trans rB).
      rewrite cell_lor /cell; apply/orP; left.
      rewrite -addn2 -subn2 Fv // Fr//=.
      by rewrite -Hl -int_add_mod.
    move: r1B; rewrite  leq_eqVlt => /orP[/eqP He |r1B].
      have /negP[] : ~~ cell (w lor b) (to_nat v).+2 nheight.
        by apply: cell_height Hw.
      rewrite cell_lor /cell; apply/orP; left.
      rewrite -addn2 Fv // mul_add_distr_r -add_assoc.
      have -> : (2 * horizontal + of_nat nheight) = 2 + 3 * up_left by [].
      have <- : r = 2 by apply: to_nat_inj.
      by rewrite add_assoc -int_add_mod.
    move: vB; rewrite  leq_eqVlt => /orP[/eqP He |vB].
      have /negP[] : ~~ cell (w lor b) (to_nat v).+3 (to_nat r).-1.-2.
        rewrite He.
        apply: cell_width Hw => //.
        by rewrite -subn3 (leq_ltn_trans (leq_subr _ _)) // (leq_trans rB).
      rewrite cell_lor /cell; apply/orP; left.
      rewrite  -addn3 -subn3  Fv // Fr //=.
      by rewrite -Hl -int_add_mod.
    rewrite r1B vB /=.
    rewrite /cell !to_natK.
    rewrite -addn3 -subn3 Fv // Fr // -Hl.
    rewrite -addn2 -subn2 Fv // Fr // 1?ltnW // -Hl.
    rewrite -addn1 -subn1 Fv // Fr // 2?ltnW // -Hl.
    by rewrite -int_add_mod Hb1 Hb2 Hb3 Hb4.
  apply: Or43; apply/existsP=> /=.
  pose v := x / horizontal.
  have vB : (to_nat v < nwidth)%N.
    by rewrite to_nat_div (wf_state_true_width Hw) // lor_spec Hb1.
  exists (Ordinal vB) => /=.
  pose r := x mod horizontal.
  have rB : (to_nat r < nheight)%N.
    have : to_nat r < nhorizontal by rewrite to_nat_mod ltn_mod.
    rewrite leq_eqVlt => /orP[/eqP He|//].
    have He1 : to_nat r = nheight by case: He.
    have /negP[] : ~~ cell (w lor b) (to_nat v) (to_nat r).
      by rewrite He1 (cell_height _ Hw).
    by rewrite cell_lor /cell; apply/orP; left; rewrite !to_natK // -int_add_mod.
  apply/existsP; exists (Ordinal rB) => /=.
  have Fv k : k < 4 -> of_nat (to_nat v + k) = v + of_nat k.
    move=> kL4.
    have kLwB : k < nwB.
      apply: leq_trans kL4 _.
      by rewrite nwB_pow (@leq_exp2l 2 2).
    have vkLb : to_nat v + k < nwB.
      apply: ltn_trans (_ : to_nat v + 4 < _); first by rewrite ltn_add2l.
      apply: ltn_trans (_ : nwidth + 4 < _); first by rewrite ltn_add2r.
      apply: ltn_trans (_ : 2 ^8 < _); first by[].
      by rewrite nwB_pow ltn_exp2l.
    apply: to_nat_inj; rewrite of_natK //.
    by rewrite to_nat_add of_natK.
  have Fr k : k < 4 -> of_nat (to_nat r + k) = r + of_nat k.
    move=> kL4.
    have kLwB : k < nwB.
      apply: leq_trans kL4 _.
      by rewrite nwB_pow (@leq_exp2l 2 2).
    have vkLb : to_nat r + k < nwB.
      apply: ltn_trans (_ : to_nat r + 4 < _); first by rewrite ltn_add2l.
      apply: ltn_trans (_ : nheight + 4 < _); first by rewrite ltn_add2r.
      apply: ltn_trans (_ : 2 ^8 < _); first by[].
      by rewrite nwB_pow ltn_exp2l.
    apply: to_nat_inj; rewrite of_natK //.
    by rewrite to_nat_add of_natK.
  have rLw : to_nat r < nwB.
    by apply: ltn_trans rB hLwB.
  move: vB; rewrite  leq_eqVlt => /orP[/eqP He |vB].
    have /negP[] : ~~ cell (w lor b) (to_nat v).+1 (to_nat r).+1.
      by rewrite He; apply: cell_width Hw.
    rewrite cell_lor /cell; apply/orP; left.
    rewrite -addn1 Fv // -[(to_nat r).+1]addn1 Fr //=.
    by rewrite -Hr mul_1_l -int_add_mod.
  move: rB; rewrite  leq_eqVlt => /orP[/eqP He |rB].
    have /negP[] : ~~ cell (w lor b) (to_nat v).+1 nheight.
      by apply: cell_height Hw.
    rewrite cell_lor /cell; apply/orP; left.
    rewrite -He -addn1 Fv // -[(to_nat r).+1]addn1 Fr //=.
    by rewrite -Hr mul_1_l -int_add_mod.
  move: vB; rewrite  leq_eqVlt => /orP[/eqP He |vB].
    have /negP[] : ~~ cell (w lor b) (to_nat v).+2 (to_nat r).+2.
      by rewrite He; apply: cell_width Hw.
    rewrite cell_lor /cell; apply/orP; left.
    rewrite -addn2 Fv // -[(to_nat r).+2]addn2 Fr //=.
    by rewrite -Hr -int_add_mod.
  move: rB; rewrite  leq_eqVlt => /orP[/eqP He |rB].
    have /negP[] : ~~ cell (w lor b) (to_nat v).+2 nheight.
      by apply: cell_height Hw.
    rewrite cell_lor /cell; apply/orP; left.
    rewrite -He -addn2 Fv // -[(to_nat r).+2]addn2 Fr //=.
    by rewrite -Hr -int_add_mod.
  move: vB; rewrite  leq_eqVlt => /orP[/eqP He |vB].
    have /negP[] : ~~ cell (w lor b) (to_nat v).+3 (to_nat r).+3.
      by rewrite He; apply: cell_width Hw.
    rewrite cell_lor /cell; apply/orP; left.
    rewrite -addn3 Fv // -[(to_nat r).+3]addn3 Fr //=.
    by rewrite -Hr -int_add_mod.
  move: rB; rewrite  leq_eqVlt => /orP[/eqP He |rB].
    have /negP[] : ~~ cell (w lor b) (to_nat v).+3 nheight.
      by apply: cell_height Hw.
    rewrite cell_lor /cell; apply/orP; left.
    rewrite -He -addn3 Fv // -[(to_nat r).+3]addn3 Fr //=.
    by rewrite -Hr -int_add_mod.
  rewrite rB vB /=.
  rewrite /cell !to_natK.
  rewrite -addn3 -[(to_nat r).+3]addn3 Fv // Fr // -Hr.
  rewrite -addn2 -[(to_nat r).+2]addn2 Fv // Fr // -Hr.
  rewrite -addn1 -[(to_nat r).+1]addn1 Fv // Fr // -Hr.
  by rewrite -int_add_mod Hb1 Hb2 Hb3 Hb4.
case => [] /existsP[/= x] /existsP[/= y] /and5P[].
- move=> xLw; rewrite /cell => Hb1 Hb2 Hb3 Hb4.
  exists (of_nat x * horizontal + of_nat y).
  apply/existsP; exists horizontal; rewrite !inE eqxx !andTb.
  suff F k : k < 4 -> of_nat x * horizontal + of_nat y + of_nat k * horizontal = 
    of_nat (x + k) * horizontal + of_nat y.
    by rewrite (F 1%N)// addn1 (F 2%N)// addn2 (F 3%N)// addn3 Hb1 Hb2 Hb3 Hb4.
  move=> kL4.
  have kLnwB : k < nwB by apply: leq_trans kL4 _; rewrite ltnW.
  have xkLnwB : x + k < nwB. 
    rewrite (leq_trans _ wLwB) // ltnS (leq_trans _ xLw) // -addn4 leq_add2l.
    by rewrite ltnW. 
  have xLnwB : x < nwB by apply: leq_trans xkLnwB; rewrite ltnS leq_addr.
  have -> : of_nat (x + k) = of_nat x + of_nat k.
    by apply: to_nat_inj; rewrite to_nat_add !of_natK.
  by rewrite mul_add_distr_r -!add_assoc; congr (_ + _); rewrite add_comm.
- move=> yLh; rewrite /cell => Hb1 Hb2 Hb3 Hb4.
  exists (of_nat x * horizontal + of_nat y).
  apply/existsP; exists vertical; rewrite !inE eqxx !andTb.
  suff F k : k < 4 -> of_nat x * horizontal + of_nat y + of_nat k = 
    of_nat x * horizontal + of_nat (k + y).
    by rewrite (F 1%N) // (F 2%N) // (F 3%N) // Hb1 Hb2 Hb3 Hb4.
  move=> kL4.
  rewrite -add_assoc; congr (_ + _).
  have kLnwB : k < nwB by apply: leq_trans kL4 _; rewrite ltnW.
  have ykLnwB : y + k < nwB. 
    rewrite (leq_trans _ hLwB) // ltnS (leq_trans _ yLh) // -addn4 leq_add2l.
    by rewrite ltnW. 
  have yLnwB : y < nwB by apply: leq_trans ykLnwB; rewrite ltnS leq_addr.
  by apply: to_nat_inj; rewrite to_nat_add !of_natK // addnC.
- move=> xLw yLh; rewrite /cell => Hb1 Hb2 /andP[Hb3 Hb4].
  exists (of_nat x * horizontal + of_nat y).
  apply/existsP; exists up_right; rewrite !inE eqxx !andTb.
  suff F k : k < 4 -> of_nat x * horizontal + of_nat y + of_nat k * up_right = 
    of_nat (k + x) * horizontal + of_nat (k + y).
    by rewrite (F 1%N) // (F 2%N) // (F 3%N) // Hb1 Hb2 Hb3 Hb4.
  move=> kL4.
  have kLnwB : k < nwB by apply: leq_trans kL4 _; rewrite ltnW.
  have xkLnwB : x + k < nwB. 
    rewrite (leq_trans _ wLwB) // ltnS (leq_trans _ xLw) // -addn4 leq_add2l.
    by rewrite ltnW. 
  have xLnwB : x < nwB by apply: leq_trans xkLnwB; rewrite ltnS leq_addr.
  have ykLnwB : y + k < nwB. 
    rewrite (leq_trans _ hLwB) // ltnS (leq_trans _ yLh) // -addn4 leq_add2l.
    by rewrite ltnW. 
  have yLnwB : y < nwB by apply: leq_trans ykLnwB; rewrite ltnS leq_addr.
  have -> :  of_nat (k + x) = of_nat k + of_nat x.
    by apply: to_nat_inj; rewrite to_nat_add !of_natK // addnC.
  have -> :  of_nat (k + y) = of_nat k + of_nat y.
    by apply: to_nat_inj; rewrite to_nat_add !of_natK // addnC.
  rewrite (add_comm (of_nat k)) mul_add_distr_r -!add_assoc; congr (_ + _).
  rewrite !add_assoc [RHS]add_comm; congr (_ + _).
  have -> : up_right = horizontal + 1 by [].
  by rewrite mul_add_distr_l [_ * 1]mul_comm mul_1_l.
move=> xLw yG2; rewrite /cell => Hb1 Hb2 /andP[Hb3 Hb4].
exists (of_nat x * horizontal + of_nat y).
apply/existsP; exists up_left; rewrite !inE eqxx !andTb.
suff F k : k < 4 -> of_nat x * horizontal + of_nat y + of_nat k * up_left = 
  of_nat (k + x) * horizontal + of_nat (y - k).
  rewrite (F 1%N) // subn1 (F 2%N) // subn2 (F 3%N) // subnS subn2.
  by rewrite Hb1 Hb2 Hb3 Hb4.
move=> kL4.
have kLnwB : k < nwB by apply: leq_trans kL4 _; rewrite ltnW.
have xkLnwB : x + k < nwB. 
  rewrite (leq_trans _ wLwB) // ltnS (leq_trans _ xLw) // -addn4 leq_add2l.
  by rewrite ltnW. 
have xLnwB : x < nwB by apply: leq_trans xkLnwB; rewrite ltnS leq_addr.
have yLnwB : y < nwB by rewrite (leq_trans _ hLwB) // ltnS ltnW.
have ykLnwB : y - k < nwB by apply: leq_trans yLnwB; rewrite ltnS leq_subr. 
have -> :  of_nat (k + x) = of_nat k + of_nat x.
  by apply: to_nat_inj; rewrite to_nat_add !of_natK // addnC.
rewrite [of_nat k + _]add_comm mul_add_distr_r -!add_assoc; congr (_ + _).
have -> : horizontal = up_left + 1 by [].
rewrite mul_add_distr_l [_ * 1]mul_comm mul_1_l.
rewrite add_comm -add_assoc; congr (_ + _).
have kLy : k <= y by rewrite  -ltnS (leq_trans kL4).
by apply: to_nat_inj; rewrite to_nat_add !of_natK // addnC subnK.
Qed.


Lemma in_insert_fmove m1 m2 v1 v2 l : 
  (m1, v1) \in (insert_fmove m2 v2 l) = 
  (m1 == m2) && (v1 == v2) || ((m1,v1) \in l).
Proof.
elim: l m2 v2  => [|[m3 v3] l IH] m2 v2 /=; rewrite ?inE ?xpair_eqE ?orbF //.
case: (_ ?= _); rewrite ?inE ?xpair_eqE ?orbF ?IH //.
by do 2 case: (_ && _).
Qed.

Lemma insert_fmove_uniq_fst m v l : 
  m \notin (map fst l) -> uniq (map fst l) -> uniq (map fst (insert_fmove m v l)).
Proof.
elim: l => //= [] [m1 v1] l IH.
rewrite inE negb_or => /andP[mDm1 mNIl] /andP[m1NIl Ul].
case E : (_ ?= _); rewrite /= ?inE.
- by rewrite (negPf mDm1) /= mNIl m1NIl.
- rewrite IH // andbT.
  apply/negP => /mapP[[m2 v2]].
  rewrite in_insert_fmove => /orP[/andP[/eqP m2E _]|m2I] /= m1E.
    by case/eqP: mDm1; rewrite m1E.
  by case/negP: m1NIl; apply/mapP; exists (m2, v2).
by rewrite (negPf mDm1) /= mNIl m1NIl.
Qed.

Lemma nheightLwB : nheight < nwB.
Proof.
apply: ltn_trans (_ : 2 ^ 6 < _); first by [].
by rewrite nwB_pow ltn_exp2l.
Qed.

Lemma get_columnE s x :
  x < nwidth ->
  to_nat (get_column s (of_nat x)) = \sum_(i < nhorizontal)  cell s x i * 2 ^ i.
Proof.
move=> xLw.
rewrite to_nat_sum.
have hLd : nhorizontal <= ndigits by [].
rewrite (big_ord_widen _ 
          (fun i => cell s x i * 2 ^ i)%N (isT: nhorizontal <= ndigits)).
rewrite [RHS]big_mkcond.
apply: eq_bigr => /= i _.
case: nltbP (@bit_get_column0 s (of_nat x) (of_nat i));
    (rewrite of_natK; last by apply: leq_trans (ltn_ord i) (ltnW ndigitsLwB)).
  by move=> H /(_ isT) ->; rewrite ifN // -leqNgt.
move/negP; rewrite -leqNgt -ltnS.
rewrite ltnS -[to_nat height]/nheight => iLh _.
by rewrite ifT // -cell_get_column.
Qed.


Notation size := seq.size.

Lemma columns_size : size columns = nwidth.
Proof.
have -> : columns = make_columns nwidth first_column by [].
by elim: nwidth first_column => //= ? IH c; rewrite IH.
Qed.

Lemma columns_val i : 
  i < nwidth -> nth 0 columns i = lsl first_column (of_nat i * horizontal).
Proof.
move=> iLw.
have: i * nhorizontal < nwB by apply: ltn_trans whLw; rewrite ltn_mul2r.
have -> : columns = make_columns nwidth first_column by [].
move: iLw.
elim: {-2}nwidth (leqnn nwidth) i first_column  => //= w IH HL [|i] f.
  by rewrite lsl0_r.
rewrite ltnS => iLw i1hLwb; rewrite [LHS]/= IH //; last 2 first.
- by rewrite ltnW.
- by rewrite (leq_ltn_trans _ i1hLwb) // leq_mul2r leqnSn orbT.
have iLwB : i < nwB by rewrite (ltn_trans _ nwidthLwB) // (ltn_trans iLw).
rewrite -lsl_add_distl.
  have -> : of_nat i.+1 = 1 + of_nat i.
    apply: to_nat_inj; rewrite to_nat_add !of_natK //.
      by rewrite (leq_ltn_trans _ nwidthLwB) // (ltn_trans iLw).
    by rewrite add1n (leq_ltn_trans _ nwidthLwB) // (ltn_trans _ HL).
  by rewrite mul_add_distr_r mul_1_l.
rewrite to_nat_mul; last first.
  by rewrite of_natK // (ltn_trans _ i1hLwb) // ltn_mul2r ltnS leqnn.
by rewrite addnC -mulSn of_natK.
Qed.

Lemma wf_state_up_log2_cell (s : int) (x z : nat) :
   let y := to_nat (up_log2 (get_column s (of_nat x))) in 
    wf_state s -> x < nwidth -> z < nhorizontal -> 
    cell (bottom + s) x z = (z == y).
Proof.
move=> /= Hwf xLw zLh.
rewrite /cell bitE wf_state_button //.
under eq_bigr do rewrite -expnD.
pose f i := (to_nat (up_log2 (get_column s (of_nat i))) + i * nhorizontal)%N.
rewrite (sum_pow_incr_div_mod f) // {}/f => [|j k /andP[jLk kLw]]; last first.
  have jLw : j < nwidth by apply: ltn_trans kLw.
  have := wf_state_opzs jLw Hwf.
  rewrite opzsE' //; case: nlebP => // uLh _.
  apply: leq_trans (_ : j.+1 * nhorizontal <= _).
    by rewrite mulSn ltn_add2r.
  apply: leq_trans (_ : k * nhorizontal <= _); last by apply: leq_addl.
  by rewrite leq_mul2r jLk orbT.
rewrite modn_small; last by case: (_ \in _).
rewrite to_nat_add //; last first.
  rewrite to_nat_mul; last first.
    rewrite of_natK; last by apply: ltn_trans nwidthLwB.
    by apply: leq_trans (ltnW whLw); rewrite ltn_mul2r.
  rewrite of_natK; last by apply: ltn_trans nwidthLwB.
  rewrite of_natK; last by apply: ltn_trans nhorizontalLwB.
  apply: leq_trans (_ : x.+1 * nhorizontal <= _).
    by rewrite mulSn addnC ltn_add2r.
  by apply: leq_trans (ltnW whLw); rewrite leq_mul2r.
rewrite to_nat_mul; last first.
  rewrite of_natK; last by apply: ltn_trans nwidthLwB.
  by apply: leq_trans (ltnW whLw); rewrite ltn_mul2r.
rewrite bool1E; apply/mapP/eqP => [[x1]|->]; last first.
  exists x; first by rewrite mem_iota.
  rewrite of_natK; last by apply: ltn_trans nwidthLwB.
  by rewrite addnC to_natK.
rewrite (of_natK x); last by apply: ltn_trans nwidthLwB.
rewrite (of_natK z); last by apply: ltn_trans nhorizontalLwB.
rewrite mem_iota add0n => /andP[_ x1Lw] H.
rewrite addnC in H.
have [xLx1|x1Lx|xEx1] := ltngtP x x1; last first.
- by move/eqP: H; rewrite xEx1 eqn_add2r => /eqP.
- suff : (to_nat (up_log2 (get_column s (of_nat x1))) + x1 * nhorizontal
          < z + x * to_nat horizontal)%N.
    by rewrite -H ltnn.
  apply: leq_trans (_ : x1.+1 * to_nat horizontal <= _).
    rewrite mulSn ltn_add2r.
    have := wf_state_opzs x1Lw Hwf.
    rewrite opzsE' //; case: nlebP => // uLh _.
    apply: leq_trans (_ : x * nhorizontal <= _).
      by rewrite leq_mul2r.
    by apply: leq_addl.
suff : (z + x * to_nat horizontal < 
        to_nat (up_log2 (get_column s (of_nat x1))) + x1 * nhorizontal)%N.
  by rewrite -H ltnn.
apply: leq_trans (_ : x.+1 * to_nat horizontal <= _).
  by rewrite mulSn ltn_add2r // (leq_trans jLh).
apply: leq_trans (_ : x1 * to_nat horizontal <= _).
  by rewrite leq_mul2r xLx1 orbT.
by apply: leq_addl.
Qed.


Notation "t .[ i ]" := (get t i)
  (at level 1, left associativity, format "t .[ i ]").
Notation "t .[ i <- a ]" := (set t i a)
  (at level 1, left associativity, format "t .[ i <- a ]").


Lemma fmsE wstate bstate border columns res :
fms wstate bstate border columns res =
  match columns with 
  | nil => make_moves res
  | column :: columns =>
      let move := border land column in
      if is_zero move then fms wstate bstate border columns res
      else
      if is_won (make_move move wstate) then Win
      else
      if is_won (make_move move bstate) then 
        fmt wstate border columns (Forced move)
      else
        let v := (values.[log2 move]) in
        fms wstate bstate border columns (insert_fmove move v res)
   end.
Proof.
by case: columns.
Qed.

(* Number of free cells *)
Definition ncells s := \sum_(i < nwidth) \sum_(j < nheight) (~~ cell s i j).

Definition empty_state := 0.

Lemma ncells_empty_state : ncells empty_state = (nwidth * nheight)%N.
Proof.
rewrite /ncells; under eq_bigr do under eq_bigr do rewrite /cell bit_0.
under eq_bigr do rewrite sum_nat_const /= card_ord muln1.
by rewrite sum_nat_const /= card_ord.
Qed.

Lemma leq_ncells s1 s2 : 
  (forall i j, i < nwidth -> j < nheight -> cell s1 i j -> cell s2 i j) ->
   ncells s2 <= ncells s1.
Proof.
move=> cell_le; apply: leq_sum => /= i _; apply: leq_sum => /= j _.
have := cell_le i j (ltn_ord _) (ltn_ord _).
by (do 2 case: cell) => //= /(_ isT).
Qed.

Lemma leq_ncells_lorl s1 s2 : ncells (s1 lor s2) <= ncells s1.
Proof.
by apply: leq_ncells => i j iLw jLh; rewrite cell_lor; case: cell.
Qed.

Lemma leq_ncells_lorr s1 s2 : ncells (s1 lor s2) <= ncells s2.
Proof.
by apply: leq_ncells => i j iLw jLh; rewrite cell_lor; do 2 case: cell.
Qed.

Lemma cell_land s1 s2 i j : cell (s1 land s2) i j = cell s1 i j && cell s2 i j.
Proof. by rewrite /cell land_spec. Qed.

Lemma leq_ncells_landl s1 s2 : ncells s1 <= ncells (s1 land s2).
Proof. by apply: leq_ncells => i j iLw jLh; rewrite cell_land; case: cell. Qed.

Lemma leq_ncells_landr s1 s2 : ncells s2 <= ncells (s1 land s2).
Proof. by apply: leq_ncells => i j iLw jLh; rewrite cell_land; case: cell. Qed.

Lemma ltn_ncells i j s1 s2 : 
  (forall i j, i < nwidth -> j < nheight -> cell s1 i j -> cell s2 i j) ->
   i < nwidth -> j < nheight -> ~~ cell s1 i j -> cell s2 i j ->
  ncells s2 < ncells s1.
Proof.
move=> le_cell iLw jLh nCs1ij Cs2ij.
rewrite /ncells (bigD1 (Ordinal iLw)) //= [X in _ < X](bigD1 (Ordinal iLw)) //=.
set ss1 := (X in X + _ < _); set ss2 := (X in _ < X + _).
set ss3 := (X in _ + X < _); set ss4 := (X in _ < _ + X).
apply: leq_trans (_ : ss2 + ss3 <= _).
  rewrite ltn_add2r /ss1 /ss2.
  rewrite (bigD1 (Ordinal jLh)) //= [X in _ < X](bigD1 (Ordinal jLh)) //=.
  rewrite nCs1ij Cs2ij ltnS add0n.
  apply: leq_sum => /= k _.
  have := le_cell i k iLw (ltn_ord _).
  by (do 2 case: cell) => //= /(_ isT).
rewrite leq_add2l; apply: leq_sum => /= k _; apply: leq_sum => /= l _.
have := le_cell k l (ltn_ord _) (ltn_ord _).
by (do 2 case: cell) => //= /(_ isT).
Qed.

Definition WIN := to_nat win.

Definition LOSS := to_nat loss.
Definition DRAW := to_nat draw.
Definition UNKNOWN := to_nat unknown.
Definition wcomp w := (WIN + LOSS - w)%N.

Lemma wcompWIN : wcomp WIN = LOSS.
Proof. by []. Qed.

Lemma wcompLOSS : wcomp LOSS = WIN.
Proof. by []. Qed.

Lemma wcompDRAW : wcomp DRAW = DRAW.
Proof. by []. Qed.

Definition mk_move s i j := s lor (lsl 1 (of_nat i * horizontal + of_nat j)).

Definition is_move m := 
 [exists i : 'I_nwidth, exists j: 'I_nheight, 
    m == lsl 1 (of_nat i * horizontal + of_nat j)].


Lemma cell_mk_movel s i j : 
  i < nwidth -> j < nhorizontal -> cell (mk_move s i j) i j.
Proof.
move=> iLw jLh.
have iLwB : i < nwB by apply: ltn_trans nwidthLwB.
have jLwB : j < nwB by apply: ltn_trans nhorizontalLwB.
have ihLwB : i * nhorizontal < nwB.
  by rewrite (leq_ltn_trans _ whLw) // leq_mul2r ltnW.
have ijLwB : i * nhorizontal + j < nwB.
  rewrite (leq_ltn_trans _ whLw) //.
  rewrite -(@prednK nwidth) // mulSn addnC.
  by rewrite leq_add ?(leq_trans (ltnW jLh)) // leq_mul2r.
have HE : to_nat (of_nat i * horizontal + of_nat j) = (i * nhorizontal + j)%N.
  rewrite to_nat_add //; last by rewrite to_nat_mul ?of_natK.
  by rewrite of_natK // to_nat_mul ?of_natK.
suff HL : of_nat i * horizontal + of_nat j <? digits.
  by rewrite cell_lor /cell bit_onenn ?eqxx ?orbT.
apply/nltbP/(leq_ltn_trans _ (_ : nwidth * nhorizontal < _)) => //.
rewrite HE -(@prednK nwidth) // mulSn addnC.
by rewrite leq_add ?(leq_trans (ltnW jLh)) // leq_mul2r.
Qed.

Lemma cell_mk_mover s i1 i2 j1 j2 : 
  i1 < nwidth -> j1 < nhorizontal -> i2 < nwidth -> j2 < nhorizontal ->
 ((i1 != i2) || (j1 != j2)) ->
  cell (mk_move s i1 j1) i2 j2 = cell s i2 j2.
Proof.
move=> i1Lw j1Lh i2Lw j2Lh i1Di2Oj1Dj2.       
have i1LwB : i1 < nwB by apply: ltn_trans nwidthLwB.
have j1LwB : j1 < nwB by apply: ltn_trans nhorizontalLwB.
have i1hLwB : i1 * nhorizontal < nwB.
  by rewrite (leq_ltn_trans _ whLw) // leq_mul2r ltnW.
have i1j1LwB : i1 * nhorizontal + j1 < nwB.
  rewrite (leq_ltn_trans _ whLw) //.
  rewrite -(@prednK nwidth) // mulSn addnC.
  by rewrite leq_add ?(leq_trans (ltnW j1Lh)) // leq_mul2r.
have HE1 : to_nat (of_nat i1 * horizontal + of_nat j1) = 
                  (i1 * nhorizontal + j1)%N.
  rewrite to_nat_add //; last by rewrite to_nat_mul ?of_natK.
  by rewrite of_natK // to_nat_mul ?of_natK.
have HL1 : of_nat i1 * horizontal + of_nat j1 <? digits.
  apply/nltbP/(leq_ltn_trans _ (_ : nwidth * nhorizontal < _)) => //.
  rewrite HE1 -(@prednK nwidth) // mulSn addnC.
  by rewrite leq_add ?(leq_trans (ltnW j1Lh)) // leq_mul2r.
have i2LwB : i2 < nwB by apply: ltn_trans nwidthLwB.
have j2LwB : j2 < nwB by apply: ltn_trans nhorizontalLwB.
have i2hLwB : i2 * nhorizontal < nwB.
  by rewrite (leq_ltn_trans _ whLw) // leq_mul2r ltnW.
have i2j2LwB : i2 * nhorizontal + j2 < nwB.
  rewrite (leq_ltn_trans _ whLw) //.
  rewrite -(@prednK nwidth) // mulSn addnC.
  by rewrite leq_add ?(leq_trans (ltnW j2Lh)) // leq_mul2r.
have HE2 : to_nat (of_nat i2 * horizontal + of_nat j2) =
             (i2 * nhorizontal + j2)%N.
  rewrite to_nat_add //; last by rewrite to_nat_mul ?of_natK.
  by rewrite of_natK // to_nat_mul ?of_natK.
have HL2 : of_nat i2 * horizontal + of_nat j2 <? digits.
  apply/nltbP/(leq_ltn_trans _ (_ : nwidth * nhorizontal < _)) => //.
  rewrite HE2 -(@prednK nwidth) // mulSn addnC.
  by rewrite leq_add ?(leq_trans (ltnW j2Lh)) // leq_mul2r.
rewrite /make_move cell_lor /cell bit_onenn ?eqxx ?orbT //.
suff /negPf-> : of_nat i1 * horizontal + of_nat j1 !=
                of_nat i2 * horizontal + of_nat j2 by rewrite orbF.
apply/neqbP/eqP; rewrite HE1 HE2.
case: eqP i1Di2Oj1Dj2 => [<-|i1Di2] /= j1Dj2; first by rewrite eqn_add2l.
apply/eqP=> i1j1Di2j2.
have [i1Li2|i2Li1|//] := ltngtP i1 i2.
  suff : i1 * nhorizontal + j1 < i2 * nhorizontal + j2 by rewrite i1j1Di2j2 ltnn.
  apply: leq_trans (leq_addr _ _).
  apply: leq_trans (_ : i1.+1 * nhorizontal <= _).
    by rewrite mulSn addnC ltn_add2r.
  by rewrite leq_mul2r.
suff : i2 * nhorizontal + j2 < i1 * nhorizontal + j1 by rewrite i1j1Di2j2 ltnn.
apply: leq_trans (leq_addr _ _).
apply: leq_trans (_ : i2.+1 * nhorizontal <= _).
  by rewrite mulSn addnC ltn_add2r j2Lh.
by rewrite leq_mul2r.
Qed.

Definition transpose s1 s2 := 
  [forall i : 'I_nwidth, [forall j : 'I_nhorizontal, 
     cell s1 i j == cell s2 (rev_ord i) j]].

Lemma transposeP s1 s2 :
  reflect (forall i j, i < nwidth -> j < nhorizontal -> 
              cell s1 i j = cell s2 (nwidth - i.+1) j)
           (transpose s1 s2).
Proof.
apply: (iffP forallP) => /= [H i j iLw jLh| H i].
  by have/forallP/(_ (Ordinal jLh))/eqP := H (Ordinal iLw).
by apply/forallP => j; rewrite H.
Qed.

Lemma transpose_sym s1 s2 : transpose s1 s2 = transpose s2 s1.
Proof.
by apply/transposeP/transposeP => H i j iLw jLh;
   have /val_eqP/eqP/= HrK := rev_ordK (Ordinal iLw);
   rewrite H ?HrK // (ltn_ord (rev_ord (Ordinal iLw))).
Qed. 

Lemma transpose_lor s1 s2 s3 s4 : 
  transpose s1 s2 -> transpose s3 s4 -> transpose (s1 lor s3) (s2 lor s4).
Proof.
move=> /transposeP cs1E /transposeP cs3E; apply/transposeP => i j iLw jLh.
by rewrite !cell_lor cs1E // cs3E.
Qed.

Lemma ncells_transpose s1 s2 : transpose s1 s2 -> ncells s1 = ncells s2.
Proof.
rewrite transpose_sym => /transposeP Ht; rewrite /ncells.
pose f i := \sum_(j < nheight)  ~~ cell s1 i j.
have <- := big_mkord xpredT f.
rewrite big_nat_rev /= big_mkord /= add0n.
apply: eq_bigr => i _; apply: eq_bigr => j _; rewrite Ht //.
by apply: ltn_trans (ltn_ord j) _.
Qed.

Lemma cwin_transpose s1 s2 : transpose s1 s2 -> cwin s1 = cwin s2.
Proof.
have Hhi s3 s4 : transpose s3 s4 -> hwin s3 -> hwin s4.
  move=> /transposeP Ht.
  move=> /existsP[/= i /existsP[/= j /and5P[Hc1 Hc2 Hc3 Hc4 Hc5]]].
  apply/existsP; exists (rev_ord (Ordinal Hc1)); apply/existsP; exists j => /=.
  have jLh' : j < nhorizontal by apply: ltn_trans (ltn_ord j) _.
  apply/and5P; split => //.
  - by rewrite -!subSn // ?subSS ?leq_subr // (leq_trans Hc1).
  - by rewrite -Ht.
  - rewrite subnS prednK; last by rewrite subn_gt0.
    by rewrite -Ht // (leq_trans _ Hc1).
  - rewrite 2!subnS !prednK; last 2 first.
    - by rewrite subn_gt0 (leq_trans _ Hc1).
    - by rewrite -subnS subn_gt0.
    by rewrite -Ht // (leq_trans _ Hc1) // ltnW.
  rewrite 3!subnS !prednK; last 3 first.
  - by rewrite subn_gt0 (leq_trans _ Hc1) // ltnW // ltnW.
  - by rewrite -subnS subn_gt0  (leq_trans _ Hc1).
  - by rewrite -2!subnS subn_gt0  (leq_trans _ Hc1).
  by rewrite -Ht // (leq_trans _ Hc1) // ltnW.
have Hh s3 s4 : transpose s3 s4 -> hwin s3 = hwin s4.
  by move=> Ht; apply/idP/idP; apply: Hhi => //; rewrite transpose_sym.
have Hvi s3 s4 : transpose s3 s4 -> vwin s3 -> vwin s4.
  move=> /transposeP Ht.
  move=> /existsP[/= i /existsP[/= j /and5P[Hc1 Hc2 Hc3 Hc4 Hc5]]].
  have j3Lh' : j.+3 < nhorizontal by apply: leq_trans Hc1 _.
  apply/existsP; exists (rev_ord i); apply/existsP; exists j => /=.
  apply/and5P; split; rewrite -1?Ht //.
  - by rewrite ltnW // ltnW // ltnW.
  - by rewrite ltnW // ltnW.
  by rewrite ltnW.
have Hv s3 s4 : transpose s3 s4 -> vwin s3 = vwin s4.
  by move=> Ht; apply/idP/idP; apply: Hvi => //; rewrite transpose_sym.
have Hudi s3 s4 : transpose s3 s4 -> uwin s3 -> dwin s4.
  move=> /transposeP Ht.
  move=> /existsP[/= i /existsP[/= j /and5P[Hc1 Hc2 Hc3 Hc4 /andP[Hc5 Hc6]]]].
  apply/existsP; exists (rev_ord (Ordinal Hc1)).
  apply/existsP; exists (Ordinal Hc2) => /=.
  have j3Lh' : j.+3 < nhorizontal by apply: leq_trans Hc2 _.
  apply/and5P; split => //.
  - by rewrite -!subSn // ?subSS ?leq_subr // (leq_trans Hc1).
  - by rewrite -Ht.
  - rewrite subnS prednK; last by rewrite subn_gt0.
    by rewrite -Ht // ltnW.
  - rewrite 2!subnS !prednK; last 2 first.
    - by rewrite subn_gt0 (leq_trans _ Hc1).
    - by rewrite -subnS subn_gt0.
    by rewrite -Ht // ltnW // ltnW.
  rewrite 3!subnS !prednK; last 3 first.
  - by rewrite subn_gt0 (leq_trans _ Hc1) // ltnW // ltnW.
  - by rewrite -subnS subn_gt0  (leq_trans _ Hc1).
  - by rewrite -2!subnS subn_gt0  (leq_trans _ Hc1).
  by rewrite -Ht // ltnW // ltnW // ltnW.
have Hdui s3 s4 : transpose s3 s4 -> dwin s3 -> uwin s4.
  move=> /transposeP Ht.
  move=> /existsP[/= i /existsP[/= j /and5P[Hc1 Hc2 Hc3 Hc4 /andP[Hc5 Hc6]]]].
  apply/existsP; exists (rev_ord (Ordinal Hc1)).
  have j3Lh : j.-2.-1 < nheight.
    apply: leq_trans (ltn_ord j).
    by case: (j : nat) => // [] [|[|j1]] //=; rewrite ltnS ltnW // ltnW.
  have j_gt0 : 0 < j by apply: leq_trans Hc2.
  have j1_gt0 : 0 < j.-1 by rewrite -subn1 subn_gt0 (leq_trans _ Hc2).
  have j2_gt0 : 0 < j.-2 by rewrite -subn2 subn_gt0 (leq_trans _ Hc2).
    apply/existsP; exists (Ordinal j3Lh) => /=.
  have jLh' : j < nhorizontal by apply: leq_trans (ltn_ord j).
  apply/and5P; split; [idtac|idtac|idtac|idtac|apply/andP; split] => //.
  - by rewrite -!subSn // ?subSS ?leq_subr // (leq_trans Hc1).
  - by rewrite !prednK.
  - by rewrite -Ht // (leq_trans j3Lh).
  - rewrite subnS prednK; last by rewrite subn_gt0.
    rewrite -Ht //; first by rewrite prednK.
    by apply: leq_trans Hc1.
  - rewrite 2!subnS !prednK //; last 2 first.
    - by rewrite subn_gt0 (leq_trans _ Hc1).
    - by rewrite -subnS subn_gt0.
    rewrite -Ht //; first by rewrite (leq_trans _ Hc1) // ltnW.
    by rewrite prednK // (leq_trans (ltnW jLh')).
  - rewrite subnS prednK; last by rewrite subn_gt0.
    rewrite subnS prednK; last by rewrite subn_gt0 (leq_trans _ Hc1).
    rewrite subnS prednK; last by rewrite subn_gt0 (leq_trans _ Hc1) // ltnW.
    by rewrite !prednK // -Ht.
have Hud s3 s4 : transpose s3 s4 -> uwin s3 = dwin s4.
  by move=> Ht; apply/idP/idP => [/Hudi->|/Hdui->]; rewrite // transpose_sym.
move=> Ht; rewrite /cwin (Hh _ _ Ht) (Hv _ _ Ht) (Hud _ _ Ht).
rewrite -[dwin s1](@Hud s2 s1) 1?transpose_sym //.
by case: hwin; case: vwin; case: dwin; case: uwin.
Qed.

Lemma mk_move_transpose s1 s2 i j :
   transpose s1 s2 -> i < nwidth -> j < nheight ->
   transpose (mk_move s1 i j) (mk_move s2 (nwidth - i.+1) j).
Proof.
move=> /transposeP Ht iLw jLh.
have jLh' : j < nhorizontal by apply: leq_trans jLh _.
apply/transposeP => i1 j1 i1Lw j1Lh.
have /= niLw := (ltn_ord (rev_ord (Ordinal iLw))).
have /= ni1Lw := (ltn_ord (rev_ord (Ordinal i1Lw))).
have [<-|/eqP jDj1] := (j =P j1); last first.
  by rewrite !cell_mk_mover -?Ht // jDj1 orbT.
have [<-|/eqP iDi1] := (i =P i1); last first.
  by rewrite !cell_mk_mover -?Ht ?iDi1 // eqn_sub2lE // eqSS iDi1.
by rewrite !cell_mk_movel.
Qed.


Lemma wf_state_get_border_width w b j : 
  wf_state (w lor b) -> bit (get_border w b) j -> 
      to_nat j %/ nhorizontal < nwidth.
Proof.
move=> Hwf; rewrite /get_border bitE wf_state_button // => Hf.
case: ltnP => // wLjh; move: Hf.
under eq_bigr do rewrite -expnD.
pose f i := (to_nat (up_log2 (get_column (w lor b) (of_nat i))) 
              + i * nhorizontal)%N.
rewrite (sum_pow_incr_div _ _ f) // => [|j1 k1 /andP[j1Lk1 k1Lw]]; last first.
  have j1Lw : j1 < nwidth by apply: ltn_trans k1Lw.
  have := wf_state_opzs j1Lw Hwf.
  rewrite opzsE' //; case: nlebP => // uLh _.
  apply: leq_trans (_ : j1.+1 * nhorizontal <= _).
    by rewrite mulSn ltn_add2r.
  apply: leq_trans (_ : k1 * nhorizontal <= _); last by apply: leq_addl.
  by rewrite leq_mul2r j1Lk1 orbT.
rewrite big1 //= => i _; rewrite /f.
rewrite divn_small // ltn_exp2l //.
have := wf_state_opzs (ltn_ord i) Hwf.
rewrite opzsE' //; case: nlebP => // uLh _.
apply: leq_trans (_ : to_nat j %/ nhorizontal * nhorizontal <= _); last first.
  by rewrite [X in _ <=  X](divn_eq (to_nat j) nhorizontal) leq_addr.
apply: leq_trans (_ : nwidth * nhorizontal <= _); last by rewrite leq_mul2r.
apply: leq_ltn_trans (_ :   to_nat height + i * nhorizontal < _).
  by rewrite leq_add2r.
apply: leq_trans (_ :  i.+1 * nhorizontal <= _).
  by rewrite mulSn ltn_add2r.
by rewrite leq_mul2r ltn_ord.
Qed.

Lemma get_borderC w b : get_border w b = get_border b w.
Proof. by rewrite /get_border lorC. Qed.

Lemma wf_state_up_log2_lt (s : int) (x z : nat) :
   let y := to_nat (up_log2 (get_column s (of_nat x))) in 
    wf_state s -> x < nwidth -> z < nhorizontal -> cell s x z -> z < y.
Proof.
move=> y sWf xLw zLh.
rewrite cell_get_column //.
have := wf_state_opzs xLw sWf.
rewrite opzsE' => [/andP[/nlebP uLh /eqP->]|]; last by case: nltbP.
rewrite bit_decr; last by apply/nltbP/(leq_trans uLh).
case: nltbP => //.
by rewrite -/y of_natK // (ltn_trans _ nhorizontalLwB).
Qed.

Definition fmove_eq (a b : fmove) := 
match a, b with
| Win, Win => true
| Draw, Draw => true
| Moves l1, Moves l2 => l1 == l2
| Forced i1, Forced i2 => i1 == i2 
| _, _ => false
end.

Lemma fmove_eqP : Equality.axiom fmove_eq.
Proof.
case => [||l1|i1]; case => [||l2|i2]/=; try constructor => //=.
  by apply: (iffP eqP) => [->//|[]].
by apply: (iffP eqP) => [->//|[]].
Qed.

HB.instance Definition _ := hasDecEq.Build fmove fmove_eqP.

Lemma bit_lsl_first_column_divE i k : 
  i < nwidth ->
  bit (lsl first_column (of_nat i * horizontal)) k -> 
  i = (to_nat k %/ nhorizontal).
Proof.
move=> iLw; rewrite bit_lsl first_column_spec.
have iLwB: i < nwB by apply: ltn_trans nwidthLwB.
case: (nltbP _ height); last by rewrite if_same.
case: nltbP; case: nlebP => // /negP dLk /negP kLih kihLh _.
rewrite -ltnNge ltnS in kLih; rewrite -ltnNge in dLk.
have kLwB : to_nat k < nwB by apply: ltn_trans ndigitsLwB.
move: kihLh; rewrite to_nat_sub //.
have ihE : to_nat (of_nat i * horizontal) = (i * nhorizontal)%N by apply: ihE.
rewrite ihE in kLih; rewrite ihE ltn_subLR //.
move=> kihLh; apply/sym_equal/divn_inv.
by rewrite kLih (leq_trans kihLh) // mulSn addnC leq_add2r.
Qed.

Lemma bit_lsl_first_column_mod_lt i k : 
  i < nwidth ->
  bit (lsl first_column (of_nat i * horizontal)) k -> 
  to_nat k %% nhorizontal < nheight.
Proof.
move=> iLw Hb.
have iE := bit_lsl_first_column_divE iLw Hb.
move: Hb; rewrite bit_lsl first_column_spec.
have iLwB: i < nwB by apply: ltn_trans nwidthLwB.
case: (nltbP _ height); last by rewrite if_same.
case: nltbP; case: nlebP => // /negP dLk /negP kLih kihLh _.
rewrite -ltnNge ltnS in kLih; rewrite -ltnNge in dLk.
have kLwB : to_nat k < nwB by apply: ltn_trans ndigitsLwB.
have ihE : to_nat (of_nat i * horizontal) = (i * nhorizontal)%N by apply: ihE.
rewrite to_nat_sub // ihE [X in (X - _ < _)%N](divn_eq _ nhorizontal) in kihLh.
by rewrite -iE addnC addnK in kihLh.
Qed.

Lemma get_column_lor s1 s2 i :
    get_column (s1 lor s2) i = get_column s1 i lor get_column s2 i.
Proof. by rewrite /get_column lsr_lor land_lor_distrl. Qed.


Lemma cwin_lor w1 w2 : cwin w1 -> cwin (w1 lor w2).
Proof.
rewrite /cwin; case: (boolP (hwin w1)) => 
    [/existsP[i1 /existsP[j1]/and5P[i1Lw Hc1 Hc2 Hc3 Hc4]] _|_].
  suff -> : hwin (w1 lor w2) by [].  
  apply/existsP; exists i1; apply/existsP; exists j1.
  by apply/and5P; split; rewrite // cell_lor ?(Hc1, Hc2, Hc3, Hc4).
case: (boolP (vwin w1)) => 
    [/existsP[i1 /existsP[j1]/and5P[jLh Hc1 Hc2 Hc3 Hc4]] _|_].
  suff -> : vwin (w1 lor w2) by rewrite orbT.  
  apply/existsP; exists i1; apply/existsP; exists j1.
  by apply/and5P; split; rewrite // cell_lor ?(Hc1, Hc2, Hc3, Hc4).
case: (boolP (uwin w1)) => 
    [/existsP[i1 /existsP[j1]/and5P[i1Lw j1Lw Hc1 Hc2 /andP[Hc3 Hc4]]] _|_].
  suff -> : uwin (w1 lor w2) by rewrite ?orbT.  
  apply/existsP; exists i1; apply/existsP; exists j1.
  by apply/and5P; split; rewrite // !cell_lor ?(j1Lw, Hc1, Hc2, Hc3, Hc4).
case: (boolP (dwin w1)) => 
    [/existsP[i1 /existsP[j1]/and5P[i1Lw j1_gt2 Hc1 Hc2 /andP[Hc3 Hc4]]] _|//].
suff -> : dwin (w1 lor w2) by rewrite ?orbT.  
apply/existsP; exists i1; apply/existsP; exists j1.
by apply/and5P; split; rewrite // !cell_lor ?(j1_gt2, Hc1, Hc2, Hc3, Hc4).
Qed.

Definition wf_pos w b := 
  [/\ wf_state (w lor b), w land b = 0, ~~cwin w & ~~ cwin b].

Definition nlhash := to_nat lhash.

Lemma to_nat_mhash c : to_nat (c land mhash) = to_nat c %% 2 ^ nlhash.
Proof.
rewrite land_power2 // to_nat_mod to_nat_lslW [(_ %% nwB)%N]modn_small //.
by rewrite mul1n nwB_pow ltn_exp2l.
Qed.

Definition nscoresize := to_nat scoresize.

Definition LOSSDRAW := to_nat lossdraw.
Definition DRAWWIN := to_nat drawwin.

Definition down_score s := 
  if s == unknown then LOSS
  else if s == loss then LOSS 
  else if s == lossdraw then LOSS
  else if s == draw then DRAW
  else if s == drawwin then DRAW
  else if s == win then WIN else WIN.

Definition up_score s := 
  if s == unknown then WIN
  else if s == loss then LOSS 
  else if s == lossdraw then DRAW
  else if s == draw then DRAW
  else if s == drawwin then WIN
  else if s == win then WIN else LOSS.

Lemma transpose_get_border w1 w2 b1 b2 : 
  wf_state (w1 lor b1) -> wf_state (w2 lor b2) ->
  transpose w1 w2 -> transpose b1 b2 ->
  transpose (get_border w1 b1) (get_border w2 b2).
Proof.
move=> Hwf1 Hwf2 Hw1 Hw2.
apply/transposeP => i j iLw iLh.
rewrite !wf_state_up_log2_cell //; last first.
  by rewrite ltn_subLR // addSn ltnS leq_addl.
suff -> : get_column (w1 lor b1) (of_nat i) = 
         get_column (w2 lor b2) (of_nat (nwidth - i.+1)) by [].
apply: to_nat_inj.
rewrite [LHS]get_columnE // [RHS]get_columnE //; last first.
  by rewrite ltn_subLR // addSn ltnS leq_addl.
apply: eq_bigr => /= k _; congr (_ * _)%N.
suff/transposeP : transpose (w1 lor b1) (w2 lor b2) by move=> ->.
by apply: transpose_lor.
Qed.
