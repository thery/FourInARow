From Stdlib Require Import ZArith Ascii List String PrimInt63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_boot.
From HB Require Import structures.

From Stdlib Require Import Lia.
Require Import ssr_int.
Require Import FourInARow.
Require Import Pbasic.

Import PrimInt63Notations.
Import Uint63Axioms.
Import Uint63.
Open Scope uint63_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(*                                                                            *)
(*    Moves generation                                                        *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

Definition cmove s (x : nat) (y : nat) :=
 [&& x < nwidth, y < nheight & 
   [forall z : 'I_nhorizontal, cell s x z == (z < y)]].
  
Lemma cmove_cell s x y : cmove s x y -> ~~ cell s x y.
Proof.
move/and3P => [xLw yLh /forallP Hf].
have yLho : y < nhorizontal by apply: ltn_trans yLh _.
by have /eqP-> := Hf (Ordinal yLho); rewrite ltnn.
Qed.

Lemma cmove_lt s x y z : cmove s x y -> z < y -> cell s x z.
Proof.
move/and3P => [xLw yLh /forallP Hf] zLy.
have zLho : z < nhorizontal by apply: ltn_trans zLy (ltn_trans yLh _).
by have /eqP-> := Hf (Ordinal zLho).
Qed.

Lemma cmove_ge s x y z : cmove s x y -> y <= z < nhorizontal -> ~~ cell s x z.
Proof.
move/and3P => [xLw yLh /forallP Hf] /andP[yLz zLh].
by have /eqP-> /= := Hf (Ordinal zLh); rewrite ltnNge yLz.
Qed.

Lemma in_insert_fmove m1 m2 v1 v2 l : 
  (m1, v1) \in (insert_fmove m2 v2 l) = 
  (m1 == m2) && (v1 == v2) || ((m1,v1) \in l).
Proof.
elim: l m2 v2  => [|[m3 v3] l IH] m2 v2 /=; rewrite ?inE ?xpair_eqE ?orbF //.
case: (_ ?= _); rewrite ?inE ?xpair_eqE ?orbF ?IH //.
by do 2 case: (_ && _).
Qed.

Lemma cmove0l s x : cmove s x 0 -> get_column s (of_nat x) = 0.
Proof.
move=> /and3P[xLw yLh /forallP /= Hf]; apply/to_nat_inj.
rewrite get_columnE // big1 //= => i _.
by have /eqP-> := Hf i; rewrite ltn0.
Qed.

Lemma cmoveE s x y : 
  cmove s x y -> y = to_nat (up_log2 (get_column s (of_nat x))).
Proof.
move=> Hc; have /and3P[xLw yLh /forallP Hp] := Hc.
have yLwB : y < nwB by apply: ltn_trans nheightLwB.
have yLho : y < nhorizontal by apply: ltn_trans yLh _.
rewrite -(of_natK _ yLwB); congr (to_nat _).
have [yE0|yNE0] := (y =P 0%N); first by rewrite  yE0 cmove0l // -yE0.
apply/sym_equal/up_log2E.
have -> : to_nat (get_column s (of_nat x)) = 
          \sum_(i < nhorizontal)  (i < y) * 2 ^ i.
  rewrite get_columnE //.
  by apply: eq_bigr => /= i _; rewrite (eqP (Hp i)).
rewrite of_natK //; apply/andP; split.
  have y1Lh : y.-1 < nhorizontal by apply: leq_ltn_trans (leq_pred _) _.
  rewrite (bigD1 (Ordinal y1Lh)) ?prednK ?leqnn ?mul1n ?leq_addr //=.
  by case: (y) yNE0.
suff -> : \sum_(i < nhorizontal)  (i < y) * 2 ^ i = \sum_(i < y) 2 ^ i.
  by apply: sum_pow2.
rewrite (big_ord_widen _ _ (ltnW yLho)).
by rewrite [RHS]big_mkcond /=; apply: eq_bigr => i; case: leqP; rewrite ?mul1n.
Qed.

Lemma cmoveE1 s x (y := to_nat (up_log2 (get_column s (of_nat x)))) : 
  wf_state s -> x < nwidth -> y < nheight -> cmove s x y.
Proof.
move=> sWf xLw yLh; apply/and3P; split => //; apply/forallP => /= z; apply/eqP.
have zLnwB : z < nwB by apply: ltn_trans nhorizontalLwB.
have := wf_state_opzs xLw sWf.
rewrite cell_get_column // opzsE' // => /andP[uLh /eqP ->].
case: nlebP uLh => // uLh _.
rewrite bit_decr; last first.
  by case: nltbP => // [] []; apply: leq_ltn_trans (_ : nheight < ndigits).
by case: nltbP; rewrite -/y of_natK //; case: ltngtP.
Qed.


Notation size := seq.size.


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

Definition has_move s := 
  [exists i : 'I_nwidth, exists j : 'I_nheight, cmove s i j].

Lemma ncells_has_move s : has_move s <= ncells s.
Proof.
rewrite /has_move; case: existsP => [[/= x /existsP[/= y Csxy]]|//].
by rewrite /ncells (bigD1 x) //= (bigD1 y) //= cmove_cell.
Qed.

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

Lemma ncells_cmove w b i j :
  cmove (w lor b) i j -> 
  ncells (w lor b) = (ncells (b lor mk_move w i j)).+1.
Proof.
move=> cm.
have /and3P[iLw jLh _] := (cm).
have jLh' : j < nhorizontal by apply: leq_trans jLh _.
pose i1 := Ordinal iLw; pose j1 := Ordinal jLh.
rewrite /ncells [LHS](bigD1 i1) //= [in RHS](bigD1 i1) //= -addSn.
congr (_ + _)%N; last first.
  apply: eq_bigr => k kDj; apply: eq_bigr => l _.
  have lLh' : l < nhorizontal by apply: leq_trans (ltn_ord _) _.
  by rewrite 2!cell_lor cell_mk_mover 1?orbC // orbC eq_sym kDj.
rewrite [LHS](bigD1 j1) //= [in RHS](bigD1 j1) //=.
have F1 : ~~ cell (w lor b) i j by apply: cmove_cell.
have F2 : ~~ cell b i j.
  by move: F1; rewrite cell_lor; case: (cell b _ _); case: cell.
rewrite F1 cell_lor negb_or F2 cell_mk_movel //= add1n add0n.
congr (_).+1; apply: eq_bigr => k kDj.
have kLh' : k < nhorizontal by apply: leq_trans (ltn_ord _) _.
by rewrite 2!cell_lor cell_mk_mover 1?orbC // eq_sym kDj.
Qed.

Lemma get_border_correct w b i j : 
  wf_state (w lor b) ->
  i < nwidth -> j < nheight -> cell (get_border w b) i j = cmove (w lor b) i j.
Proof.
set wb := _ lor _ => wf_wb iLw jLh.
rewrite wf_state_up_log2_cell //; last by apply: leq_trans jLh _.
move: jLh; have [-> jLh|nP jLh] /= := (j =P _).
  by apply/sym_equal/idP/cmoveE1.
by apply/sym_equal/idP => /= /cmoveE.
Qed.

Lemma get_border_w w b : wf_state (w lor b) -> get_border w b land w = 0.
Proof.
move=> Hwf; apply/is_zero_spec; rewrite is_zeroP; apply/forallP=> /= i.
rewrite land_spec negb_and.
have [/= Hb|//] := boolP (bit _ _).
have Hwidth := wf_state_get_border_width Hwf Hb.
move: Hb.
rewrite (int_add_mod i horizontal).
rewrite -(to_natK (i / horizontal)) to_nat_div.
rewrite -(to_natK (i mod horizontal)) to_nat_mod.
set x := _ %/ _ in Hwidth *; set y := _ %% _.
have yLh : y < nhorizontal by rewrite ltn_mod.
rewrite -![bit _ _]/(cell _ _ _).
have : y <= nheight by [].
case: ltngtP => [yLh'||->] _ //; last first.
  move=> _; suff : ~~ cell (w lor b) x nheight.
    by rewrite cell_lor; case: cell.
  by apply: cell_height Hwf.
rewrite get_border_correct // => /cmove_cell.
by rewrite cell_lor negb_or => /andP[].
Qed.

Lemma wf_state_cmove w b i j : 
  wf_state (w lor b) -> cmove (w lor b) i j -> 
  wf_state (b lor (mk_move w i j)).
Proof.
move=> Hwf Hc.
have iLw : i < nwidth by case/and3P: Hc.
have jLh : j < nheight by case/and3P: Hc.
have jLho : j < nhorizontal by apply: ltn_trans jLh _.
rewrite lorA  [b lor _]lorC.
apply/andP; split; apply/forallP => x.
  rewrite lor_spec.
  have /andP[/forallP/(_ x)] := Hwf.
  case : bit => // _ _.
  rewrite orFb bit_lsl.
  case: nltbP => // /negP; rewrite ?orFb -leqNgt ihjE // => ijLx.
  case: nlebP => // /negP; rewrite -ltnNge => xLd.
  have xLw : to_nat x < nwB by apply: ltn_trans ndigitsLwB.
  rewrite bit_1; case: neqbP => //.
  rewrite to_nat_sub // ihjE //.
  move => /eqP; rewrite subn_eq0 => xLij.
  apply/nltbP => //.
  rewrite to_nat_mul ?whLw //.
  by apply: leq_ltn_trans xLij (ihjLwh _ _).
apply/implyP => /nltbP xLw.
have Ho : opzs height (get_column (w lor b) x).
  by rewrite -[x]to_natK // wf_state_opzs.
rewrite get_column_lor.
have iLw': i < nwB by apply: ltn_trans nwidthLwB.
have jLw : j < nwB by apply: ltn_trans nheightLwB.
have ihLd : i * to_nat horizontal < ndigits by apply: ihLd.
have ihjLd : i * to_nat horizontal + j < ndigits by apply: ihjLd.
have ihLw : i * to_nat horizontal < nwB by apply: ihLw.
have ihjLw : i * to_nat horizontal + j < nwB by apply: ihjLw.
have xhE : to_nat (x * horizontal) = (to_nat x * nhorizontal)%N.
  by rewrite to_nat_mul // (ltn_trans _ whLw) // ltn_mul2r.
have ihE : to_nat (of_nat i * horizontal) = (i * nhorizontal)%N by apply: ihE.
have ihjE : to_nat (of_nat i * horizontal + of_nat j) = 
              (i * nhorizontal + j)%N by apply ihjE.
have [xLi|iLx|xE]:= ltngtP (to_nat x) i.
- have ihxhE : to_nat (of_nat i * horizontal + of_nat j - x * horizontal) =
              (i * nhorizontal + j - to_nat x * nhorizontal)%N.
    rewrite to_nat_sub ?ihjE ?xhE //.
    apply: leq_trans _ (leq_addr _ _).
    by rewrite leq_mul2r ltnW.
  suff -> : get_column (lsl 1 (of_nat i * horizontal + of_nat j)) x = 0.
    by rewrite lor0_r.
  rewrite /get_column lsl_lsr_le; last 2 first.
  - by rewrite mul1n nwB_pow ltn_exp2l // ihjE ihjLd.
  - apply/nlebP; rewrite ihjE xhE.
    apply: leq_trans (leq_addr _ _).
    by rewrite leq_mul2r ltnW.
  apply/bit_ext => k; rewrite land_spec full_first_column_spec bit_0.
  case: (nltbP k horizontal) => [kLh|hLk]; last by rewrite andbF.
  rewrite andbT bit_onenn //; last 2  first.
  - apply/nltbP; rewrite ihxhE.
    by apply: leq_ltn_trans (leq_subr _ _) ihjLd.
  - by apply/nltbP/(ltn_trans kLh).
  case: eqP => // kE.
  have : nhorizontal <= i * nhorizontal + j - to_nat x * nhorizontal.
    rewrite leq_subRL //; last first.
      apply: leq_trans (leq_addr _ _).
      by rewrite leq_mul2r ltnW.
    apply: leq_trans (leq_addr _ _).
    by rewrite addnC -mulSn leq_mul2r.
  by rewrite -ihxhE kE leqNgt kLh.
- suff -> : get_column (lsl 1 (of_nat i * horizontal + of_nat j)) x = 0.
    by rewrite lor0_r.
  rewrite /get_column lsl_lsr_ge; last 2 first.
  - by rewrite mul1n nwB_pow ltn_exp2l // ihjE ihjLd.
  - apply/nlebP; rewrite ihjE xhE.
    apply: leq_trans (_ : i.+1 * nhorizontal <= _).
      by rewrite mulSn addnC leq_add2r ltnW.
    by rewrite leq_mul2r.
  suff -> : 1 >> (x * horizontal - (of_nat i * horizontal + of_nat j)) = 0 by [].
  apply: to_nat_inj; rewrite to_nat_lsr divn_small //.
  rewrite -[X in X <= _]expn1 leq_exp2l // to_nat_sub ?xhE ?ihjE.
  - rewrite subn_gt0 //.
    apply: leq_trans (_ : i.+1 * nhorizontal <= _).
      by rewrite mulSn addnC ltn_add2r.
    by rewrite leq_mul2r.
  - apply: leq_trans (_ : i.+1 * nhorizontal <= _).
      by rewrite mulSn addnC leq_add2r ltnW.
    by rewrite leq_mul2r.
  by apply: ltn_trans whLw; rewrite ltn_mul2r.
have -> : get_column (lsl 1 (of_nat i * horizontal + of_nat j)) x = 
      lsl 1 (of_nat j).
  rewrite /get_column lsl_lsr_le //.
  - have -> : of_nat i * horizontal + of_nat j - x * horizontal = of_nat j.
      apply: to_nat_inj.
      by rewrite of_natK // to_nat_sub ?ihjE ?xhE ?xE ?addKn // leq_addr.
    apply: bit_ext => k.
    have [dLk|/negP kLd] := nlebP digits k.
      by rewrite !bit_M //; apply/nlebP.
    rewrite land_spec full_first_column_spec bit_onenn //.
    - by case: eqP => // <-; apply/nltbP; rewrite of_natK.
    - by apply/nltbP; rewrite of_natK // (ltn_trans jLho).
    by case: nltbP => // /negP; rewrite -leqNgt (negPf kLd).
  - by rewrite mul1n nwB_pow ltn_exp2l // ihjE.
  by apply/nlebP; rewrite ?xhE ?ihjE ?xE (leq_addr _ _).
move: Ho; rewrite opzsE' //.
set i1 := up_log2 _ => /andP[/nlebP i1Lh /eqP cE].
have jE : j = to_nat i1 by have := cmoveE Hc; rewrite -xE to_natK.
rewrite cE jE to_natK //.
rewrite -and_imp_add_or; last first.
  apply: bit_ext => k; rewrite bit_0.
  have [dLk|/negP kLd] := nlebP digits k.
    by rewrite !bit_M //; apply/nlebP.
  rewrite land_spec bit_decr; last first.
    by apply/nltbP/(leq_ltn_trans i1Lh).
  rewrite bit_onenn //.
  - case: eqP; rewrite ?andbF ?andbT // => <-.
    by apply/nltbP; rewrite ?ltnn.
  - by apply/nltbP; rewrite -jE (ltn_trans jLh).
  by apply/nltbP; rewrite ltnNge.
rewrite opzsE //.
apply/existsP; exists (i1 + 1).
have jLd : j < ndigits by apply: ltn_trans jLh _.
have j1Ld : j.+1 < ndigits by apply: (leq_trans _ (_ : nhorizontal <= _)).
have i11E : to_nat (i1 + 1) = j.+1.
  rewrite to_nat_add; first by rewrite -jE addn1.
  by rewrite addn1 -jE (leq_trans _ nhorizontalLwB).
apply/andP; split; first by apply/nlebP; rewrite i11E.
apply/eqP/to_nat_inj.
rewrite to_nat_decr; last first.
  by apply/nltbP; rewrite to_nat_lsl_one ?expn_gt0 // i11E.
have dE : to_nat (decr (lsl one i1)) = (2 ^ j).-1.
  rewrite to_nat_decr; last first.
    by apply/nltbP; rewrite to_nat_lsl_one ?expn_gt0 // -jE.
  by rewrite to_nat_lsl_one -?jE.
have jjE : ((2 ^ j).-1 + 2 ^ j)%N = (2 ^ j.+1).-1.
  by rewrite expnS mul2n -addnn -[X in _ = (X + _).-1]prednK ?expn_gt0.
rewrite to_nat_lsl_one; last by rewrite i11E.
rewrite to_nat_add dE to_nat_lsl_one ?i11E -?jE // jjE prednK ?expn_gt0 //.
by rewrite nwB_pow leq_exp2l.
Qed.

Lemma land_cmove w b i j : 
  cmove (w lor b) i j -> w land b = 0 -> b land (mk_move w i j) = 0.
Proof.
move=> Hf Hc.
apply: bit_ext => k.
have [kLd|/negP] := nltbP k digits; last first.
  by rewrite -leqNgt => dLk; rewrite !bit_M //; apply/nlebP.
have := cmove_cell Hf.
have : bit (w land b) k = false by rewrite Hc bit_0.
rewrite /cell !(bit_0, land_spec, lor_spec).
have [ijLd|/negP] := nltbP (of_nat i * horizontal + of_nat j) digits; last first.
  rewrite -leqNgt => dLij.
  rewrite !(bit_M _ (_ + _)); last by apply/nlebP.
    case: bit => //; case: bit => //=; rewrite bit_lsl ifT //.
    by apply/orP; left; apply/nltbP; apply: leq_trans _ dLij.
  by apply/nlebP.
rewrite bit_onenn; try (by apply/nltbP).
by case: (of_nat i * horizontal + of_nat j =P k) => [->|]; do 2 case: bit.
Qed.

Lemma fmt_win_rect_corect w b res i cols : 
  wf_state (w lor b) -> 
  (size cols + i = nwidth)%N ->
  (forall j, j < size cols -> 
      nth 0 cols j = lsl first_column (of_nat (j + i) * horizontal)) ->
  (fmt w (get_border w b) cols res == Win) = 
    ((res == Win) ||
     [exists i1 : 'I_nwidth, exists j1 : 'I_nheight, 
      [&& i <= i1, cmove (w lor b) i1 j1 & cwin (mk_move w i1 j1)]]).
Proof.
move=> Hwf.
elim: cols i => /= [i|c cols IH i Hsi Hf].
  rewrite add0n => -> _; case: eqP => //= _.
  apply/sym_equal/idP/negP; rewrite negb_exists.
  apply/forallP => x; rewrite negb_exists; apply/forallP => y.
  by rewrite leqNgt ltn_ord.
have iLw : i < nwidth by rewrite -Hsi addSn ltnS leq_addl.
have iLwB : i < nwB by apply: ltn_trans nwidthLwB.
have Hc : c = lsl first_column (of_nat i * horizontal).
  by apply: (Hf ord0).
have Hf'  j : j < size cols -> nth 0 cols j =
                    lsl  first_column (of_nat (j + i.+1) * horizontal).
  by move=> jLs; rewrite -addSnnS -Hf.
have Hs : (size cols + i.+1)%N = nwidth by rewrite -addSnnS.
have IH' := IH _ Hs Hf'.
case: ifP => Hif1.
  rewrite IH'; congr (_ || _).
  apply/existsP/existsP=> [] [i1 /existsP[j1 /and3P[iLi1 i1j1C i1k1Cw]]].
    by exists i1; apply/existsP; exists j1; rewrite (ltnW iLi1) i1j1C.
  have j1LwB : j1 < nwB by apply: ltn_trans nheightLwB.
  move: iLi1; case: ltngtP => // [iLi1|iEi1] _ /=.
    by exists i1; apply/existsP; exists j1; rewrite iLi1 i1j1C.
  rewrite -get_border_correct // -iEi1 in i1j1C.
  suff : cell (get_border w b land c) i j1.
    by have /is_zero_spec-> := Hif1; rewrite cell_0.
  rewrite cell_land i1j1C Hc /cell bit_lsl ifN.
    rewrite add_comm addK first_column_spec.
    by apply/nltbP; rewrite of_natK // (ltn_trans _ nheightLwB).
  have ihE : to_nat (of_nat i * horizontal) = (i * nhorizontal)%N.
    by rewrite to_nat_mul of_natK // (ltn_trans _ whLw) // ltn_mul2r iLw.
  have ihj1E : to_nat (of_nat i * horizontal + of_nat j1) = 
               (i * nhorizontal + j1)%N.
    rewrite to_nat_add ?ihE ?of_natK //.
    apply: leq_ltn_trans (_ : i.+1 * nhorizontal < _).
      by rewrite mulSn addnC leq_add2r // ltnW // (ltn_trans (ltn_ord _)).
    apply: leq_ltn_trans whLw.
    by rewrite leq_mul2r (leq_ltn_trans _ iLw) // (leq_trans (leq_subr _ _)).
  rewrite negb_or; apply/andP; (split; apply/negP) => [/nltbP|/nlebP].
    by rewrite ihj1E ihE ltnNge leq_addr.
  rewrite ihj1E leqNgt (leq_trans (_ : _ < i.+1 * nhorizontal)) //.
    by rewrite mulSn addnC ltn_add2r (leq_trans (ltn_ord _)).
  apply: leq_trans (_ : nwidth * nhorizontal <= _) => //.
  by rewrite leq_mul2r iLw.
have /negP/negP := Hif1; rewrite is_zeroNP =>/existsP[/= k kE].
have : bit c k by move: kE; rewrite land_spec; case: bit.
rewrite {1}Hc => /(bit_lsl_first_column_divE iLw) iE.
have : bit c k by move: kE; rewrite land_spec; case: bit.
rewrite {1}Hc => /(bit_lsl_first_column_mod_lt iLw) => kLh.
have cM :  cmove (w lor b) i (to_nat k %% nhorizontal).
  rewrite -get_border_correct // iE -bit_cell.
  by move: (kE); rewrite land_spec; case/andP.
have cmE : cwin (mk_move w i (to_nat k %% nhorizontal)) = 
       is_won (make_move (get_border w b land c) w).
  rewrite -(@is_won_cwin _ b) //; last first.
    by rewrite lorC; apply: wf_state_cmove.
  rewrite /mk_move iE -(of_nat_int_add_mod k horizontal) lorC.
  rewrite /make_move.
  suff <- : get_border w b land c = lsl 1 k by [].
  apply: bit_ext => k1.
  move: (kE); rewrite land_spec; case/andP => bE cE /=.
  have kLd : to_nat k < ndigits.
    by case: ltnP => // dLk; rewrite bit_M // in cE; apply/nlebP.
  have [k1Ld|/negP dLk1] := nltbP k1 digits; last first.
    by rewrite !bit_M //; apply/nlebP; rewrite leqNgt.
  rewrite bit_onenn //; try by apply/nltbP.
  rewrite land_spec.
  case: eqP => [<-|kDk1]; first by rewrite bE.
  case: (boolP (bit c k1)); last by rewrite andbF.
  move=> bck1; move: (bck1).
  rewrite Hc => /(bit_lsl_first_column_divE iLw) // iE'.
  case: (boolP (bit _ _)) => //.
  rewrite bit_cell get_border_correct //; last 2 first.
  - by rewrite -iE'.
  - by move: bck1; rewrite Hc => /(bit_lsl_first_column_mod_lt iLw).
  move=> /cmoveE k1mE.
  move: bE.
  rewrite bit_cell get_border_correct //; last by rewrite -iE.
  move=> /cmoveE kmE.
  case: kDk1.
  apply/to_nat_inj.
  rewrite (divn_eq (to_nat k) nhorizontal).
  by rewrite kmE -iE iE' -k1mE -divn_eq.
case: ifP => HE.
  rewrite eqxx; apply/sym_equal/orP; right. 
  apply/existsP; exists (Ordinal iLw).
  apply/existsP; exists (Ordinal kLh) => /=.
  by rewrite leqnn cM cmE HE.
rewrite IH'; case: eqP => //= _.
apply/existsP/existsP => [] [/= i2 /existsP[j2 /and3P[iLi2 i2j2C i2j2Cw]]]; 
  exists i2; apply/existsP; exists j2; apply/and3P; split => //.
  by apply: ltnW.
move: iLi2; case: ltngtP => // iEi2.
case/idP: HE; rewrite -cmE iEi2.
by rewrite (cmoveE cM) iEi2 -(cmoveE i2j2C).
Qed.

Lemma fmt_win_corect w b move : 
  wf_state (w lor b) -> 
  (fmt w (get_border w b) columns (Forced move) == Win) = 
     [exists i1 : 'I_nwidth, exists j1 : 'I_nheight, 
        cmove (w lor b) i1 j1 && cwin (mk_move w i1 j1)].
Proof.
move=> Hwf.
rewrite (@fmt_win_rect_corect _ _ _ 0%N) // => j jLs.
by rewrite addn0; apply: columns_val; rewrite -columns_size.
Qed.

Lemma fmt_not_win_corect w b res cols : 
  (fmt w b cols res != Win) -> fmt w b cols res == res.
Proof.
by elim: cols => //= c cols IH; case: ifP => // _; case: ifP.
Qed.

Lemma fms_win_rect_corect w b res i cols : 
  wf_state (w lor b) -> 
  (size cols + i = nwidth)%N ->
  (forall j, j < size cols -> 
      nth 0 cols j = lsl first_column (of_nat (j + i) * horizontal)) ->
  (fms w b (get_border w b) cols res == Win) = 
     [exists i1 : 'I_nwidth, exists j1 : 'I_nheight, 
      [&& i <= i1, cmove (w lor b) i1 j1 & cwin (mk_move w i1 j1)]].
Proof.
move=> Hwf.
elim: cols i res => /= [i res|c cols IH i res Hsi Hf].
  rewrite add0n => -> _.
  have -> : (make_moves res == Win) = false by case: res.
  apply/sym_equal/idP/negP; rewrite negb_exists.
  apply/forallP => x; rewrite negb_exists; apply/forallP => y.
  by rewrite leqNgt ltn_ord.
have iLw : i < nwidth by rewrite -Hsi addSn ltnS leq_addl.
have iLwB : i < nwB by apply: ltn_trans nwidthLwB.
have Hc : c = lsl first_column (of_nat i * horizontal).
  by apply: (Hf ord0).
have Hf'  j : j < size cols -> nth 0 cols j =
                    lsl  first_column (of_nat (j + i.+1) * horizontal).
  by move=> jLs; rewrite -addSnnS -Hf.
have Hs : (size cols + i.+1)%N = nwidth by rewrite -addSnnS.
set res1 := insert_fmove _ _ _.
have IH' r := IH _ r Hs Hf'.
case: ifP => Hif1.
  rewrite IH'.
  apply/existsP/existsP=> [] [i1 /existsP[j1 /and3P[iLi1 i1j1C i1j1Cw]]].
    by exists i1; apply/existsP; exists j1; rewrite (ltnW iLi1) i1j1C.
  have j1LwB : j1 < nwB by apply: ltn_trans nheightLwB.
  move: iLi1; case: ltngtP => // [iLi1|iEi1] _ /=.
    by exists i1; apply/existsP; exists j1; rewrite iLi1 i1j1C.
  rewrite -get_border_correct // -iEi1 in i1j1C.
  suff : cell (get_border w b land c) i j1.
    by have /is_zero_spec-> := Hif1; rewrite cell_0.
  rewrite cell_land i1j1C Hc /cell bit_lsl ifN.
    rewrite add_comm addK first_column_spec.
    by apply/nltbP; rewrite of_natK // (ltn_trans _ nheightLwB).
  have ihE : to_nat (of_nat i * horizontal) = (i * nhorizontal)%N.
    by rewrite to_nat_mul of_natK // (ltn_trans _ whLw) // ltn_mul2r iLw.
  have ihj1E : to_nat (of_nat i * horizontal + of_nat j1) = 
               (i * nhorizontal + j1)%N.
    rewrite to_nat_add ?ihE ?of_natK //.
    apply: leq_ltn_trans (_ : i.+1 * nhorizontal < _).
      by rewrite mulSn addnC leq_add2r // ltnW // (ltn_trans (ltn_ord _)).
    apply: leq_ltn_trans whLw.
    by rewrite leq_mul2r (leq_ltn_trans _ iLw) // (leq_trans (leq_subr _ _)).
  rewrite negb_or; apply/andP; (split; apply/negP) => [/nltbP|/nlebP].
    by rewrite ihj1E ihE ltnNge leq_addr.
  rewrite ihj1E leqNgt (leq_trans (_ : _ < i.+1 * nhorizontal)) //.
    by rewrite mulSn addnC ltn_add2r (leq_trans (ltn_ord _)).
  apply: leq_trans (_ : nwidth * nhorizontal <= _) => //.
  by rewrite leq_mul2r iLw.
have /negP/negP := Hif1; rewrite is_zeroNP =>/existsP[/= k kE].
have : bit c k by move: kE; rewrite land_spec; case: bit.
rewrite {1}Hc => /(bit_lsl_first_column_divE iLw) iE.
have : bit c k by move: kE; rewrite land_spec; case: bit.
rewrite {1}Hc => /(bit_lsl_first_column_mod_lt iLw) => kLh.
have cM :  cmove (w lor b) i (to_nat k %% nhorizontal).
  rewrite -get_border_correct // iE -bit_cell.
  by move: (kE); rewrite land_spec; case/andP.
have cmE : cwin (mk_move w i (to_nat k %% nhorizontal)) = 
       is_won (make_move (get_border w b land c) w).
  rewrite -(@is_won_cwin _ b) //; last first.
    by rewrite lorC; apply: wf_state_cmove.
  rewrite /mk_move iE -(of_nat_int_add_mod k horizontal) lorC.
  rewrite /make_move.
  suff <- : get_border w b land c = lsl 1 k by [].
  apply: bit_ext => k1.
  move: (kE); rewrite land_spec; case/andP => bE cE /=.
  have kLd : to_nat k < ndigits.
    by case: ltnP => // dLk; rewrite bit_M // in cE; apply/nlebP.
  have [k1Ld|/negP dLk1] := nltbP k1 digits; last first.
    by rewrite !bit_M //; apply/nlebP; rewrite leqNgt.
  rewrite bit_onenn //; try by apply/nltbP.
  rewrite land_spec.
  case: eqP => [<-|kDk1]; first by rewrite bE.
  case: (boolP (bit c k1)); last by rewrite andbF.
  move=> bck1; move: (bck1).
  rewrite Hc => /(bit_lsl_first_column_divE iLw) // iE'.
  case: (boolP (bit _ _)) => //.
  rewrite bit_cell get_border_correct //; last 2 first.
  - by rewrite -iE'.
  - by move: bck1; rewrite Hc => /(bit_lsl_first_column_mod_lt iLw).
  move=> /cmoveE k1mE.
  move: bE.
  rewrite bit_cell get_border_correct //; last by rewrite -iE.
  move=> /cmoveE kmE.
  case: kDk1.
  apply/to_nat_inj.
  rewrite (divn_eq (to_nat k) nhorizontal).
  by rewrite kmE -iE iE' -k1mE -divn_eq.
case: ifP => HE.
  rewrite eqxx; apply/sym_equal/idP.
  apply/existsP; exists (Ordinal iLw).
  apply/existsP; exists (Ordinal kLh) => /=.
  by rewrite leqnn cM cmE HE.
case: ifP => HE1.
  rewrite (@fmt_win_rect_corect _ _ _ i.+1) // orFb.
  apply/existsP/existsP => [] [/= i2 /existsP[j2 /and3P[iLi2 i2j2C i2j2Cw]]]; 
    exists i2; apply/existsP; exists j2; apply/and3P; split => //.
    by apply: ltnW.
  move: iLi2; case: ltngtP => // iEi2.
  case/idP: HE; rewrite -cmE iEi2.
  by rewrite (cmoveE cM) iEi2 -(cmoveE i2j2C).
rewrite IH'.
apply/existsP/existsP => [] [/= i2 /existsP[j2 /and3P[iLi2 i2j2C i2j2Cw]]]; 
  exists i2; apply/existsP; exists j2; apply/and3P; split => //.
  by apply: ltnW.
move: iLi2; case: ltngtP => // iEi2.
case/idP: HE; rewrite -cmE iEi2.
by rewrite (cmoveE cM) iEi2 -(cmoveE i2j2C).
Qed.

Lemma fms_win_corect w b : 
  wf_state (w lor b) -> 
  (fms w b (get_border w b) columns [::] == Win) = 
     [exists i1 : 'I_nwidth, exists j1 : 'I_nheight, 
      cmove (w lor b) i1 j1 && cwin (mk_move w i1 j1)].
Proof.
move=> Hwf.
rewrite (@fms_win_rect_corect _ _ _ 0%N) // => j jLs.
by rewrite addn0; apply: columns_val; rewrite -columns_size.
Qed.

Lemma size_insert_move m v l : size (insert_fmove m v l) = (size l).+1.
Proof.
elim: l m v => //= [] [m1 v1] l IH m2 v2.
by case: (_ ?= _); rewrite /= ?IH.
Qed.

Lemma fms_cons_not_draw_rect_corect w b res cols : 
  (0 < size res)%N -> fms w b (get_border w b) cols res != Draw. 
Proof.
elim: cols res => /= [[]//|c cols IH res Hc].
case: ifP => _; first by apply: IH.
case: ifP => _ //.
case: ifP => _; last first.
  by apply: IH; rewrite size_insert_move; move: Hc; case: size.
elim: {IH}cols => //= a l IH.
by do 2 (case: ifP => _ //).
Qed.

Lemma fms_draw_rect_corect i w b res cols : 
  wf_state (w lor b) -> 
  (size cols + i = nwidth)%N ->
  (forall j, j < size cols -> 
      nth 0 cols j = lsl first_column (of_nat (j + i) * horizontal)) ->
  (fms w b (get_border w b) cols res == Draw) = 
    (res == [::]) &&
     [forall i1 : 'I_nwidth, forall j1 : 'I_nheight, 
      (i <= i1) ==> ~~ cmove (w lor b) i1 j1].
Proof.
move=> Hwf.
elim: cols i res => /= [i res|c cols IH i res Hsi Hf].
  rewrite add0n => -> _.
  case: res; rewrite /= ?eqxx //; apply/sym_equal/forallP => x.
  by apply/forallP => y; rewrite leqNgt ltn_ord.
have iLw : i < nwidth by rewrite -Hsi addSn ltnS leq_addl.
have iLwB : i < nwB by apply: ltn_trans nwidthLwB.
have Hc : c = lsl first_column (of_nat i * horizontal).
  by apply: (Hf ord0).
have Hf'  j : j < size cols -> nth 0 cols j =
                    lsl  first_column (of_nat (j + i.+1) * horizontal).
  by move=> jLs; rewrite -addSnnS -Hf.
have Hs : (size cols + i.+1)%N = nwidth by rewrite -addSnnS.
set res1 := insert_fmove _ _ _.
have IH' r := IH _ r Hs Hf'.
case: ifP => Hif1.
  rewrite IH'.
  case: eqP => //= _.
  apply/forallP/forallP => /= Hcm i1; apply/forallP => /= j1; 
      apply/implyP => iLi1; last first.
    have /forallP/(_ j1)/implyP->// := Hcm i1.
    by apply: ltnW.
  case: ltngtP iLi1 => // [iLi1 _|iEi1 _].
    by have /forallP/(_ j1)/implyP/(_ iLi1) := Hcm i1.
  have j1Lw : j1 < nwB by apply: ltn_trans _ nheightLwB.
  apply/negP => i1j1C.
  rewrite -get_border_correct // -iEi1 in i1j1C.
  suff : cell (get_border w b land c) i j1.
    by have /is_zero_spec-> := Hif1; rewrite cell_0.
  rewrite cell_land i1j1C Hc /cell bit_lsl ifN.
    rewrite add_comm addK first_column_spec.
    by apply/nltbP; rewrite of_natK.
  have ihE : to_nat (of_nat i * horizontal) = (i * nhorizontal)%N.
    by rewrite to_nat_mul of_natK // (ltn_trans _ whLw) // ltn_mul2r iLw.
  have ihj1E : to_nat (of_nat i * horizontal + of_nat j1) = 
              (i * nhorizontal + j1)%N.
    rewrite to_nat_add ?ihE ?of_natK //.
    apply: leq_ltn_trans (_ : i.+1 * nhorizontal < _).
      by rewrite mulSn addnC leq_add2r // ltnW // (ltn_trans (ltn_ord _)).
    apply: leq_ltn_trans whLw.
    by rewrite leq_mul2r (leq_ltn_trans _ iLw) // (leq_trans (leq_subr _ _)).
  rewrite negb_or; apply/andP; (split; apply/negP) => [/nltbP|/nlebP].
    by rewrite ihj1E ihE ltnNge leq_addr.
  rewrite ihj1E leqNgt (leq_trans (_ : _ < i.+1 * nhorizontal)) //.
    by rewrite mulSn addnC ltn_add2r (leq_trans (ltn_ord _)).
  apply: leq_trans (_ : nwidth * nhorizontal <= _) => //.
  by rewrite leq_mul2r iLw.
have /negP/negP := Hif1; rewrite is_zeroNP =>/existsP[/= k kE].
have : bit c k by move: kE; rewrite land_spec; case: bit.
rewrite {1}Hc => /(bit_lsl_first_column_divE iLw) iE.
have : bit c k by move: kE; rewrite land_spec; case: bit.
rewrite {1}Hc => /(bit_lsl_first_column_mod_lt iLw) => kLh.
have cM :  cmove (w lor b) i (to_nat k %% nhorizontal).
  rewrite -get_border_correct // iE -bit_cell.
  by move: (kE); rewrite land_spec; case/andP.
set x := _ && _; have -> :  x = false.
  apply/negP/negP; rewrite negb_and; apply/orP; right.
  rewrite negb_forall; apply/existsP; exists (Ordinal iLw).
  rewrite negb_forall; apply/existsP; exists (Ordinal kLh).
  by rewrite /= cM leqnn.
case: ifP => //= _.
case: ifP => //= _.
  elim: (cols) => //= c1 cls IH1.
  by do 2 (case: ifP => // _).
rewrite IH'.
apply/negP/negP; rewrite negb_and; apply/orP; left.
rewrite /res1; elim: (res) => //= [] [m v] cls IH1.
by case: (_ ?= _).
Qed.

Lemma fms_draw_corect w b : 
  wf_state (w lor b) -> 
  (fms w b (get_border w b) columns [::] == Draw) = ~~ has_move (w lor b).
Proof.
move=> Hwf.
rewrite (@fms_draw_rect_corect 0) //; last first.
  by move=> j jLc; rewrite addn0 columns_val.
rewrite andTb negb_exists.
apply/forallP/forallP => /= H i; first by rewrite negb_exists H.
by have := H i; rewrite negb_exists.
Qed. 

Lemma fmt_forced_rect_corect i w b res k cols : 
  wf_state (w lor b) -> 
  (size cols + i = nwidth)%N ->
  (forall j, j < size cols -> 
      nth 0 cols j = lsl first_column (of_nat (j + i) * horizontal)) ->
  (fmt w (get_border w b) cols res == Forced k) = 
    ((res == Forced k) &&
     [forall i1 : 'I_nwidth, forall j1 : 'I_nheight, 
      [==> i <= i1, cmove (w lor b) i1 j1 => ~~ cwin (mk_move w i1 j1)]]).
Proof.
move=> Hwf.
elim: cols i => /= [i|c cols IH i Hsi Hf].
  rewrite add0n => -> _; case: eqP => //= _.
  apply/sym_equal/idP/forallP => /= i1.
  by apply/forallP =>j1; rewrite leqNgt ltn_ord.
have iLw : i < nwidth by rewrite -Hsi addSn ltnS leq_addl.
have iLwB : i < nwB by apply: ltn_trans nwidthLwB.
have Hc : c = lsl first_column (of_nat i * horizontal).
  by apply: (Hf ord0).
have Hf'  j : j < size cols -> nth 0 cols j =
                    lsl  first_column (of_nat (j + i.+1) * horizontal).
  by move=> jLs; rewrite -addSnnS -Hf.
have Hs : (size cols + i.+1)%N = nwidth by rewrite -addSnnS.
have IH' := IH _ Hs Hf'.
case: ifP => Hif1.
  rewrite IH'; congr (_ && _).
  apply/forallP/forallP => /= H i1; apply/forallP => /= j1; apply/implyP => H1;
      apply/implyP=> H2; last first.
    by have /forallP/(_ j1) := H i1; rewrite ltnW // H2.
  have j1Lw : j1 < nwB by apply: ltn_trans nheightLwB.    
  move: H1; case: ltngtP => // [H1|iEi1] _ /=.
    by have /forallP/(_ j1) := H i1; rewrite H2 H1.
  rewrite -get_border_correct // -iEi1 in H2.
  suff : cell (get_border w b land c) i j1.
    by have /is_zero_spec-> := Hif1; rewrite cell_0.
  rewrite cell_land H2 Hc /cell bit_lsl ifN.
    rewrite add_comm addK first_column_spec.
    by apply/nltbP; rewrite of_natK // (ltn_trans _ nheightLwB).
  have ihE : to_nat (of_nat i * horizontal) = (i * nhorizontal)%N.
    by rewrite to_nat_mul of_natK // (ltn_trans _ whLw) // ltn_mul2r iLw.
  have ihj1E : to_nat (of_nat i * horizontal + of_nat j1) = 
               (i * nhorizontal + j1)%N.
    rewrite to_nat_add ?ihE ?of_natK //.
    apply: leq_ltn_trans (_ : i.+1 * nhorizontal < _).
      by rewrite mulSn addnC leq_add2r // ltnW // (ltn_trans (ltn_ord _)).
    apply: leq_ltn_trans whLw.
    by rewrite leq_mul2r (leq_ltn_trans _ iLw) // (leq_trans (leq_subr _ _)).
  rewrite negb_or; apply/andP; (split; apply/negP) => [/nltbP|/nlebP].
    by rewrite ihj1E ihE ltnNge leq_addr.
  rewrite ihj1E leqNgt (leq_trans (_ : _ < i.+1 * nhorizontal)) //.
    by rewrite mulSn addnC ltn_add2r (leq_trans (ltn_ord _)).
  apply: leq_trans (_ : nwidth * nhorizontal <= _) => //.
  by rewrite leq_mul2r iLw.
have /negP/negP := Hif1; rewrite is_zeroNP =>/existsP[/= k1 k1E].
have : bit c k1 by move: k1E; rewrite land_spec; case: bit.
rewrite {1}Hc => /(bit_lsl_first_column_divE iLw) iE.
have : bit c k1 by move: k1E; rewrite land_spec; case: bit.
rewrite {1}Hc => /(bit_lsl_first_column_mod_lt iLw) => kLh.
have cM :  cmove (w lor b) i (to_nat k1 %% nhorizontal).
  rewrite -get_border_correct // iE -bit_cell.
  by move: (k1E); rewrite land_spec; case/andP.
have cmE : cwin (mk_move w i (to_nat k1 %% nhorizontal)) = 
       is_won (make_move (get_border w b land c) w).
  rewrite -(@is_won_cwin _ b) //; last first.
    by rewrite lorC; apply: wf_state_cmove.
  rewrite /mk_move iE -(of_nat_int_add_mod k1 horizontal) lorC.
  rewrite /make_move.
  suff <- : get_border w b land c = lsl 1 k1 by [].
  apply: bit_ext => k2.
  move: (k1E); rewrite land_spec; case/andP => bE cE /=.
  have k1Ld : to_nat k1 < ndigits.
    by case: ltnP => // dLk; rewrite bit_M // in cE; apply/nlebP.
  have [k2Ld|/negP dLk2] := nltbP k2 digits; last first.
    by rewrite !bit_M //; apply/nlebP; rewrite leqNgt.
  rewrite bit_onenn //; try by apply/nltbP.
  rewrite land_spec.
  case: eqP => [<-|k1Dk2]; first by rewrite bE.
  case: (boolP (bit c k2)); last by rewrite andbF.
  move=> bck2; move: (bck2).
  rewrite Hc => /(bit_lsl_first_column_divE iLw) // iE'.
  case: (boolP (bit _ _)) => //.
  rewrite bit_cell get_border_correct //; last 2 first.
  - by rewrite -iE'.
  - by move: bck2; rewrite Hc => /(bit_lsl_first_column_mod_lt iLw).
  move=> /cmoveE k2mE.
  move: bE.
  rewrite bit_cell get_border_correct //; last by rewrite -iE.
  move=> /cmoveE kmE.
  case: k1Dk2.
  apply/to_nat_inj.
  rewrite (divn_eq (to_nat k1) nhorizontal).
  by rewrite kmE -iE iE' -k2mE -divn_eq.
case: ifP => HE.
  apply/sym_equal/negP/negP.
  rewrite negb_and; apply/orP; right.
  rewrite negb_forall; apply/existsP; exists (Ordinal iLw).
  rewrite negb_forall; apply/existsP; exists (Ordinal kLh) => /=.
  by rewrite cmE HE leqnn cM.
rewrite IH'; case: eqP => //= _.
apply/forallP/forallP => /= Hcm i1; apply/forallP => /= j1;
    apply/implyP => iLi1; apply/implyP => i1j1C; last first.
  by have /forallP/(_ j1) := Hcm i1; rewrite ltnW //= i1j1C.
move: iLi1; case: ltngtP => // [iLi1|iEi1] _.
  by have /forallP/(_ j1) := Hcm i1; rewrite iLi1 //= i1j1C.
by rewrite (cmoveE i1j1C) -iEi1 -(cmoveE cM) cmE HE.
Qed.

Lemma fms_forced_rect_corect i w b res k cols : 
  wf_state (w lor b) -> 
  (size cols + i = nwidth)%N ->
  (forall j, j < size cols -> 
      nth 0 cols j = lsl first_column (of_nat (j + i) * horizontal)) ->
  (fms w b (get_border w b) cols res == Forced k) -> 
    (forall i1 j1 , 
      i <= i1 -> cmove (w lor b) i1 j1 ->  ~~ cwin (mk_move w i1 j1))
    /\
    (exists i1, exists j1,  
      [/\ 
         k = lsl 1 (of_nat i1 * horizontal + of_nat j1),
         cmove (w lor b) i1 j1 & cwin (mk_move b i1 j1)]).
Proof.
move=> Hwf.
elim: cols i res => /= [i res|c cols IH i res Hsi Hf].
  rewrite add0n => -> _.
  by case: res.
have iLw : i < nwidth by rewrite -Hsi addSn ltnS leq_addl.
have iLwB : i < nwB by apply: ltn_trans nwidthLwB.
have Hc : c = lsl first_column (of_nat i * horizontal).
  by apply: (Hf ord0).
have Hf'  j : j < size cols -> nth 0 cols j =
                    lsl  first_column (of_nat (j + i.+1) * horizontal).
  by move=> jLs; rewrite -addSnnS -Hf.
have Hs : (size cols + i.+1)%N = nwidth by rewrite -addSnnS.
set res1 := insert_fmove _ _ _.
have IH' r := IH _ r Hs Hf'.
case: ifP => Hif1.
  move/IH'.
  have Hcm j2 : j2 < nheight -> ~~ cmove (w lor b) i j2.
    move=> j2Lh.
    rewrite -get_border_correct //=; apply/negP=> Ci1j1.
    have j2Lw : j2 < nwB by apply: ltn_trans nheightLwB.
    suff : cell (get_border w b land c) i j2.
      by have /is_zero_spec-> := Hif1; rewrite cell_0.
    rewrite cell_land Ci1j1 Hc /cell bit_lsl ifN.
      rewrite add_comm addK first_column_spec.
      by apply/nltbP; rewrite of_natK // (ltn_trans _ nheightLwB).
    have ihE : to_nat (of_nat i * horizontal) = (i * nhorizontal)%N.
      by rewrite to_nat_mul of_natK // (ltn_trans _ whLw) // ltn_mul2r iLw.
    have ihj1E : to_nat (of_nat i * horizontal + of_nat j2) = 
                   (i * nhorizontal + j2)%N.
      rewrite to_nat_add ?ihE ?of_natK //.
      apply: leq_ltn_trans (_ : i.+1 * nhorizontal < _).
        by rewrite mulSn addnC leq_add2r // ltnW // (ltn_trans j2Lh).
      apply: leq_ltn_trans whLw.
      by rewrite leq_mul2r (leq_ltn_trans _ iLw) // (leq_trans (leq_subr _ _)).
    rewrite negb_or; apply/andP; (split; apply/negP) => [/nltbP|/nlebP].
      by rewrite ihj1E ihE ltnNge leq_addr.
    rewrite ihj1E leqNgt (leq_trans (_ : _ < i.+1 * nhorizontal)) //.
      by rewrite mulSn addnC ltn_add2r (leq_trans j2Lh).
    apply: leq_trans (_ : nwidth * nhorizontal <= _) => //.
    by rewrite leq_mul2r iLw.
  move=> [Hwin Hec]; split => [i1 j1|//].
  case: ltngtP => //= iEi2 _ H3; first by apply: Hwin.
  have j1Lh : j1 < nheight by case/and3P : H3.
  by have /negP[] := Hcm _ j1Lh; rewrite iEi2.
have /negP/negP := Hif1; rewrite is_zeroNP =>/existsP[/= k1 k1E].
have : bit c k1 by move: k1E; rewrite land_spec; case: bit.
rewrite {1}Hc => /(bit_lsl_first_column_divE iLw) iE.
have : bit c k1 by move: k1E; rewrite land_spec; case: bit.
rewrite {1}Hc => /(bit_lsl_first_column_mod_lt iLw) => kLh.
have cM :  cmove (w lor b) i (to_nat k1 %% nhorizontal).
  rewrite -get_border_correct // iE -bit_cell.
  by move: (k1E); rewrite land_spec; case/andP.
have gbcL : get_border w b land c = lsl 1 k1.
  apply: bit_ext => k2.
  move: (k1E); rewrite land_spec; case/andP => bE cE /=.
  have k1Ld : to_nat k1 < ndigits.
    by case: ltnP => // dLk1; rewrite bit_M // in cE; apply/nlebP.
  have [k2Ld|/negP dLk2] := nltbP k2 digits; last first.
    by rewrite !bit_M //; apply/nlebP; rewrite leqNgt.
  rewrite bit_onenn //; try by apply/nltbP.
  rewrite land_spec.
  case: eqP => [<-|k1Dk2]; first by rewrite bE.
  case: (boolP (bit c k2)); last by rewrite andbF.
  move=> bck2; move: (bck2).
  rewrite Hc => /(bit_lsl_first_column_divE iLw) // iE'.
  case: (boolP (bit _ _)) => //.
  rewrite bit_cell get_border_correct //; last 2 first.
  - by rewrite -iE'.
  - by move: bck2; rewrite Hc => /(bit_lsl_first_column_mod_lt iLw).
  move=> /cmoveE k2mE.
  move: bE.
  rewrite bit_cell get_border_correct //; last by rewrite -iE.
  move=> /cmoveE kmE.
  case: k1Dk2.
  apply/to_nat_inj.
  rewrite (divn_eq (to_nat k1) nhorizontal).
  by rewrite kmE -iE iE' -k2mE -divn_eq.
have cmE : cwin (mk_move w i (to_nat k1 %% nhorizontal)) = 
       is_won (make_move (get_border w b land c) w).
  rewrite -(@is_won_cwin _ b) //; last first.
    by rewrite lorC; apply: wf_state_cmove.
  rewrite /mk_move iE -(of_nat_int_add_mod k1 horizontal) lorC.
  rewrite /make_move.
  by suff <- : get_border w b land c = lsl 1 k1 by [].
have cmE1 : cwin (mk_move b i (to_nat k1 %% nhorizontal)) = 
       is_won (make_move (get_border w b land c) b).
  rewrite -(@is_won_cwin _ w) //; last first.
    by rewrite lorC; apply: wf_state_cmove; rewrite 1? lorC.
  rewrite /mk_move iE -(of_nat_int_add_mod k1 horizontal) lorC.
  rewrite /make_move.
  suff <- : get_border w b land c = lsl 1 k1 by [].
  apply: bit_ext => k2.
  move: (k1E); rewrite land_spec; case/andP => bE cE /=.
  have k1Ld : to_nat k1 < ndigits.
    by case: ltnP => // dLk1; rewrite bit_M // in cE; apply/nlebP.
  have [k2Ld|/negP dLk2] := nltbP k2 digits; last first.
    by rewrite !bit_M //; apply/nlebP; rewrite leqNgt.
  rewrite bit_onenn //; try by apply/nltbP.
  rewrite land_spec.
  case: eqP => [<-|k1Dk2]; first by rewrite bE.
  case: (boolP (bit c k2)); last by rewrite andbF.
  move=> bck2; move: (bck2).
  rewrite Hc => /(bit_lsl_first_column_divE iLw) // iE'.
  case: (boolP (bit _ _)) => //.
  rewrite bit_cell get_border_correct //; last 2 first.
  - by rewrite -iE'.
  - by move: bck2; rewrite Hc => /(bit_lsl_first_column_mod_lt iLw).
  move=> /cmoveE k2mE.
  move: bE.
  rewrite bit_cell get_border_correct //; last by rewrite -iE.
  move=> /cmoveE kmE.
  case: k1Dk2.
  apply/to_nat_inj.
  rewrite (divn_eq (to_nat k1) nhorizontal).
  by rewrite kmE -iE iE' -k2mE -divn_eq.
case: ifP => HE //.
case: ifP => HE1.
  rewrite (@fmt_forced_rect_corect i.+1) //.
  move=> /andP[/eqP[gE] /forallP /= Hm].
  split => [i1 j1|].
    case: ltngtP => // [iLi1|iEi1] _ cM1.
      have i1Lw : i1 < nwidth by case/and3P: cM1.
      have j1Lh : j1 < nheight by case/and3P: cM1.
      have /forallP/(_ (Ordinal j1Lh) ):= Hm (Ordinal i1Lw).
      by rewrite iLi1 /= => /implyP/(_ cM1).
    rewrite -iEi1 in cM1 *.
    by rewrite (cmoveE cM1) -(cmoveE cM) cmE HE.
  exists i; exists (to_nat k1 %% nhorizontal); split => //.
    rewrite iE -gE gbcL; congr lsl.
    by rewrite [LHS](of_nat_int_add_mod k1 horizontal).
  by rewrite cmE1 HE1.
move=> /IH' [Hcw Hem]; split => // i1 j1.
case: ltngtP => // [iLi1|iEi1] _; first by apply: Hcw.
move=> cM1.
by rewrite (cmoveE cM1) -iEi1 -(cmoveE cM) cmE HE.
Qed.

Lemma fms_forced_corect w b k : 
  wf_state (w lor b) -> 
  fms w b (get_border w b) columns [::] == Forced k -> 
    (forall i1 j1 , cmove (w lor b) i1 j1 ->  ~~ cwin (mk_move w i1 j1))
    /\
    (exists i1, exists j1,  
      [/\ 
         k = lsl 1 (of_nat i1 * horizontal + of_nat j1),
         cmove (w lor b) i1 j1 & cwin (mk_move b i1 j1)]).
Proof.
move=> Hwf /(@fms_forced_rect_corect 0) // /(_ Hwf) [].
- by rewrite addn0 columns_size.
- by move=> j jLc; rewrite addn0 columns_val.
by move=> Hcm ?; split => // i1 j1; apply: Hcm.
Qed.

Lemma mem_insert_fmove i1 i2 j1 j2 l : 
  (i1, j1)  \in insert_fmove i2 j2 l = 
   ((i1, j1) == (i2, j2)) || ((i1, j1) \in l).
Proof.
elim: l i1 i2 j1 j2 => //= [] [i3 j3] l IH i1 i2 j1 j2.
case: (_ ?= _); rewrite !in_cons; first by case: eqP.
  by rewrite IH; case: eqP => //; case: eqP.
by case: eqP.
Qed.

Lemma fms_subset w b bd c r l : fms w b bd c r == Moves l -> r \subset l.
Proof.
elim: c r => [|v c1 IH r] //=; first by case => //= a l1 /eqP[->].
case: ifP => // _; first by apply: IH.
case: ifP => // _.
case: ifP => // _.
  elim: (c1) => //= a c2 IH1; first by do 2 (case: ifP => // _).
move=> /IH Hi; apply: subset_trans Hi.
apply/subsetP =>  /= [] [x y]; rewrite mem_insert_fmove => ->.
by rewrite orbT.
Qed.

Lemma fms_moves_rect_corect i w b res l cols : 
  wf_state (w lor b) -> 
  uniq (map fst res) ->
  (size cols + i = nwidth)%N ->
  (forall j, j < size cols -> 
      nth 0 cols j = lsl first_column (of_nat (j + i) * horizontal)) ->
  (forall i1 j1, (i1, j1) \in res ->
      (exists i2 j2, [/\ cmove (w lor b) i2 j2, i2 < i & 
         i1 = lsl 1 (of_nat i2 * horizontal + of_nat j2)])) ->
  (fms w b (get_border w b) cols res == Moves l) -> 
  [/\ 
    (forall i1 j1 , 
      i <= i1 -> cmove (w lor b) i1 j1 ->  ~~ cwin (mk_move w i1 j1)),
    (forall i1 j1 , 
      i <= i1 -> cmove (w lor b) i1 j1 ->  ~~ cwin (mk_move b i1 j1)),
    0 < size l /\ uniq (map fst l),
   (forall i1 j1, (i1, j1) \in l -> 
      (exists i2 j2, cmove (w lor b) i2 j2 /\
         i1 = lsl 1 (of_nat i2 * horizontal + of_nat j2))) &
   (forall i1 j1, i <= i1 -> cmove (w lor b) i1 j1 ->
      (exists j2, ((lsl 1 (of_nat i1 * horizontal + of_nat j1)), j2) \in l))].
Proof.
move=> Hwf.
elim: cols i res => /= [i res Ures |c cols IH i res Ures Hsi Hf Hin].
  rewrite add0n => -> _; move: Ures.
  case: res => //= [] [m v] l1 Ur Hin /eqP[<-]; split => //=.
  - by move=> i1 j1 wLi1 /and3P[]; rewrite ltnNge wLi1.
  - by move=> i1 j1 wLi1 /and3P[]; rewrite ltnNge wLi1.
  - by move=> i1 j1 /Hin[i2 [j2 [w2j2C i2Lw i2E]]]; exists i2; exists j2.
  by move=> i1 j1 wLi1 /and3P[]; rewrite ltnNge wLi1.
have iLw : i < nwidth by rewrite -Hsi addSn ltnS leq_addl.
have iLwB : i < nwB by apply: ltn_trans nwidthLwB.
have cE : c = lsl first_column (of_nat i * horizontal).
  by apply: (Hf ord0).
have Hf'  j : j < size cols -> nth 0 cols j =
                    lsl  first_column (of_nat (j + i.+1) * horizontal).
  by move=> jLs; rewrite -addSnnS -Hf.
have Hs : (size cols + i.+1)%N = nwidth by rewrite -addSnnS.
set res1 := insert_fmove _ _ _.
have IH' (r : seq (int * int)) (K : uniq (map fst r)) := IH _ r K Hs Hf'.
have Hin' i1 j1 :
  (i1, j1)  \in res ->
   exists i2 j2 : nat, [/\ cmove (w lor b) i2 j2,  i2 < i.+1  & 
   i1 = lsl 1 (of_nat i2 * horizontal + of_nat j2)].
  case/Hin => i2 [j2 [i2j2C i2Li i1E]]; exists i2; exists j2; split => //.
  by rewrite ltnS ltnW.
case: ifP => Hif1.
  move/IH' => /(_ Ures).
  have Hcm j2 : j2 < nheight -> ~~ cmove (w lor b) i j2.
    move=> j2Lh.
    rewrite -get_border_correct //=; apply/negP=> Cij2.
    have j2Lw : j2 < nwB by apply: ltn_trans nheightLwB.
    suff : cell (get_border w b land c) i j2.
      by have /is_zero_spec-> := Hif1; rewrite cell_0.
    rewrite cell_land Cij2 cE /cell bit_lsl ifN.
      rewrite add_comm addK first_column_spec.
      by apply/nltbP; rewrite of_natK // (ltn_trans _ nheightLwB).
    have ihE : to_nat (of_nat i * horizontal) = (i * nhorizontal)%N.
      by rewrite to_nat_mul of_natK // (ltn_trans _ whLw) // ltn_mul2r iLw.
    have ihj1E : to_nat (of_nat i * horizontal + of_nat j2) = 
                   (i * nhorizontal + j2)%N.
      rewrite to_nat_add ?ihE ?of_natK //.
      apply: leq_ltn_trans (_ : i.+1 * nhorizontal < _).
        by rewrite mulSn addnC leq_add2r // ltnW // (ltn_trans j2Lh).
      apply: leq_ltn_trans whLw.
      by rewrite leq_mul2r (leq_ltn_trans _ iLw) // (leq_trans (leq_subr _ _)).
    rewrite negb_or; apply/andP; (split; apply/negP) => [/nltbP|/nlebP].
      by rewrite ihj1E ihE ltnNge leq_addr.
    rewrite ihj1E leqNgt (leq_trans (_ : _ < i.+1 * nhorizontal)) //.
      by rewrite mulSn addnC ltn_add2r (leq_trans j2Lh).
    apply: leq_trans (_ : nwidth * nhorizontal <= _) => //.
    by rewrite leq_mul2r iLw.
  move=> /(_ Hin') [Hcw1 Hcw2 [Hsize Ul] He1 He2]; split => //.
  - move=> i1 j1; case: ltngtP => // [i1Lj1|<-] _ ij1C; first by apply: Hcw1.
    have j1Lh : j1 < nheight by case/and3P : ij1C.
    by have /negP[] := (Hcm j1 j1Lh).
  - move=> i1 j1; case: ltngtP => // [i1Lj1|<-] _ ij1C; first by apply: Hcw2.
    have j1Lh : j1 < nheight by case/and3P : ij1C.
    by have /negP[] := (Hcm j1 j1Lh).
  move=> i1 j1; case: ltngtP => // [i1Lj1|<-] _ ij1C; first by apply: He2.
  have j1Lh : j1 < nheight by case/and3P : ij1C.
  by have /negP[] := (Hcm j1 j1Lh).
have /negP/negP := Hif1; rewrite is_zeroNP =>/existsP[/= k1 k1E].
have : bit c k1 by move: k1E; rewrite land_spec; case: bit.
rewrite {1}cE => /(bit_lsl_first_column_divE iLw) iE.
have : bit c k1 by move: k1E; rewrite land_spec; case: bit.
rewrite {1}cE => /(bit_lsl_first_column_mod_lt iLw) => kLh.
have cM :  cmove (w lor b) i (to_nat k1 %% nhorizontal).
  rewrite -get_border_correct // iE -bit_cell.
  by move: (k1E); rewrite land_spec; case/andP.
have gbcL : get_border w b land c = lsl 1 k1.
  apply: bit_ext => k2.
  move: (k1E); rewrite land_spec; case/andP => Hb1 Hb2 /=.
  have k1Ld : to_nat k1 < ndigits.
    by case: ltnP => // dLk1; rewrite bit_M // in Hb1; apply/nlebP.
  have [k2Ld|/negP dLk2] := nltbP k2 digits; last first.
    by rewrite !bit_M //; apply/nlebP; rewrite leqNgt.
  rewrite bit_onenn //; try by apply/nltbP.
  rewrite land_spec.
  case: eqP => [<-|k1Dk2]; first by rewrite Hb1.
  case: (boolP (bit c k2)); last by rewrite andbF.
  move=> bck2; move: (bck2).
  rewrite cE => /(bit_lsl_first_column_divE iLw) // iE'.
  case: (boolP (bit _ _)) => //.
  rewrite bit_cell get_border_correct //; last 2 first.
  - by rewrite -iE'.
  - by move: bck2; rewrite cE => /(bit_lsl_first_column_mod_lt iLw).
  move=> /cmoveE k2mE.
  move: Hb1.
  rewrite bit_cell get_border_correct //; last by rewrite -iE.
  move=> /cmoveE kmE.
  case: k1Dk2.
  apply/to_nat_inj.
  rewrite (divn_eq (to_nat k1) nhorizontal).
  by rewrite kmE -iE iE' -k2mE -divn_eq.
have cmE : cwin (mk_move w i (to_nat k1 %% nhorizontal)) = 
       is_won (make_move (get_border w b land c) w).
  rewrite -(@is_won_cwin _ b) //; last first.
    by rewrite lorC; apply: wf_state_cmove.
  rewrite /mk_move iE -(of_nat_int_add_mod k1 horizontal) lorC.
  rewrite /make_move.
  by suff <- : get_border w b land c = lsl 1 k1 by [].
have cmE1 : cwin (mk_move b i (to_nat k1 %% nhorizontal)) = 
       is_won (make_move (get_border w b land c) b).
  rewrite -(@is_won_cwin _ w) //; last first.
    by rewrite lorC; apply: wf_state_cmove; rewrite 1? lorC.
  rewrite /mk_move iE -(of_nat_int_add_mod k1 horizontal) lorC.
  rewrite /make_move.
  suff <- : get_border w b land c = lsl 1 k1 by [].
  apply: bit_ext => k2.
  move: (k1E); rewrite land_spec; case/andP => Hb1 Hb2 /=.
  have k1Ld : to_nat k1 < ndigits.
    by case: ltnP => // dLk1; rewrite bit_M // in Hb1; apply/nlebP.
  have [k2Ld|/negP dLk2] := nltbP k2 digits; last first.
    by rewrite !bit_M //; apply/nlebP; rewrite leqNgt.
  rewrite bit_onenn //; try by apply/nltbP.
  rewrite land_spec.
  case: eqP => [<-|k1Dk2]; first by rewrite Hb1.
  case: (boolP (bit c k2)); last by rewrite andbF.
  move=> bck2; move: (bck2).
  rewrite cE => /(bit_lsl_first_column_divE iLw) // iE'.
  case: (boolP (bit _ _)) => //.
  rewrite bit_cell get_border_correct //; last 2 first.
  - by rewrite -iE'.
  - by move: bck2; rewrite cE => /(bit_lsl_first_column_mod_lt iLw).
  move=> /cmoveE k2mE.
  move: Hb1.
  rewrite bit_cell get_border_correct //; last by rewrite -iE.
  move=> /cmoveE kmE.
  case: k1Dk2.
  apply/to_nat_inj.
  rewrite (divn_eq (to_nat k1) nhorizontal).
  by rewrite kmE -iE iE' -k2mE -divn_eq.
case: ifP => HE //.
case: ifP => HE1.
  suff /negPf-> : fmt w (get_border w b) cols (Forced (get_border w b land c)) 
                      != Moves l by [].
  elim: (cols) => //= a l1 IH1.
  by do 2 (case: ifP => //).
have IHi i1 j1 : 
    (i1, j1)  \in res1 -> 
    exists i2 j2 : nat, 
    [/\ cmove (w lor b) i2 j2, i2 < i.+1  & 
        i1 = lsl 1 (of_nat i2 * horizontal + of_nat j2)].
  rewrite mem_insert_fmove => /orP[|]; last by apply: Hin'.
  rewrite xpair_eqE => /andP[/eqP -> _].
  exists i; exists (to_nat k1 %% nhorizontal); split => //.
  by rewrite iE -(of_nat_int_add_mod _ horizontal).
move=> Hms.
have rSl : res1 \subset l by apply: fms_subset Hms.
have Ures1 : uniq (map fst res1).
  apply: insert_fmove_uniq_fst => //.
  apply/negP => /mapP[[i1 v1 /Hin[i2 [j2 [i2j2C i2Li i1E]]]]] wbcE.
  have /(congr1 (fun x => to_nat x))/eqP := i1E.
  rewrite -[i1]wbcE gbcL to_nat_lsl_one; last first.
    case: ltnP => // dLk1.
    by rewrite bit_M // in k1E; apply/nlebP.
  rewrite (divn_eq (to_nat k1) nhorizontal) // -iE.
  have i2Lw : i2 < nwidth by case/and3P: i2j2C.
  have j2Lh : j2 < nheight by case/and3P: i2j2C.
  have j2Lho : j2 < nhorizontal by apply: ltn_trans j2Lh _.
  rewrite [X in _ == X]to_nat_lsl_one ihjE //; last by apply: ihjLd.
  rewrite eqn_exp2l // => /eqP /ihj_inv iEi2.
  by rewrite iEi2 ?ltn_pmod // ltnn in i2Li. 
have /IH' := Hms => /(_ Ures1).
move=> /(_ IHi) [Hcw1 Hcw2 [Hsize Ul] He1 He2]; split => // i1 j1.
- case: ltngtP => // [iLi1|iEi1] _; first by apply: Hcw1.
  move=> cM1.
  by rewrite (cmoveE cM1) -iEi1 -(cmoveE cM) cmE HE.
- case: ltngtP => // [iLi1|iEi1] _; first by apply: Hcw2.
  move=> cM1.
  by rewrite (cmoveE cM1) -iEi1 -(cmoveE cM) cmE1 HE1.
case: ltngtP => // [iLi1|iEi1] _; first by apply: He2.
rewrite -iEi1 => cM1; rewrite (cmoveE cM1) -(cmoveE cM).
rewrite iE -(of_nat_int_add_mod _ horizontal) -gbcL.
exists values.[log2 (get_border w b land c)].
apply: (subsetP rSl).
by rewrite mem_insert_fmove eqxx.
Qed.

Lemma fms_moves_corect w b l : 
  wf_state (w lor b) -> 
   fms w b (get_border w b) columns [::] == Moves l -> 
  [/\ 
    (forall i1 j1, cmove (w lor b) i1 j1 ->  ~~ cwin (mk_move w i1 j1)),
    (forall i1 j1, cmove (w lor b) i1 j1 ->  ~~ cwin (mk_move b i1 j1)),
    0 < size l /\  uniq (map fst l),
   (forall i1 j1, (i1, j1) \in l -> 
      (exists i2 j2, cmove (w lor b) i2 j2 /\
         i1 = lsl 1 (of_nat i2 * horizontal + of_nat j2))) &
   (forall i1 j1, cmove (w lor b) i1 j1 ->
      (exists j2, ((lsl 1 (of_nat i1 * horizontal + of_nat j1)), j2) \in l))].
Proof.
move=> Hwf /(@fms_moves_rect_corect 0) // /(_ Hwf) [] //.
  by move=> j jLc; rewrite addn0 columns_val.
move=> Hcw1 Hcw2 [Hsize Ul] He1 He2; split => // i1 j1; first by apply: Hcw1.
  by apply: Hcw2.
by apply: He2.
Qed.

Lemma cmoveC i1 i2 j1 j2 w b : 
  cmove (w lor b) i1 j1 -> cmove (w lor b) i2 j2 -> i1 != i2 ->
  cmove ((mk_move w i1 j1) lor b) i2 j2.
Proof.
move => /and3P[i1Lw j1Lh /forallP/= ci1] /and3P[i2Lw j2Lh /forallP/= ci2] i1Di2.
have j1Lho : j1 < nhorizontal by apply: ltn_trans j1Lh _.
have j2Lho : j2 < nhorizontal by apply: ltn_trans j2Lh _.
apply/and3P; split => //; apply/forallP => /= z.
rewrite lorC lorA [b lor _]lorC cell_lor (eqP (ci2 z)).
rewrite /cell bit_onenn; last 2 first.
- by apply/nltbP; rewrite ihjE // ihjLd.
- by apply/nltbP; rewrite ihjE // ihjLd.
case: (boolP (_ == _ + _)) => [/eqP i1hj1Ei2hz|]; last by rewrite orbF.
case/eqnP : i1Di2.
apply : (ihj_inv i1Lw i2Lw j1Lho (ltn_ord z)).
by rewrite -ihjE // i1hj1Ei2hz ihjE.
Qed.

Fixpoint eval_aux (n : nat) w b := 
  let s := w lor b in 
  if cwin w then WIN else
  if has_move s then
    if n is n1.+1 then
      \max_(i < nwidth) \max_(j < nheight | cmove s i j) 
                wcomp (eval_aux n1 b (mk_move w i j))
    else UNKNOWN
  else if cwin b then LOSS else DRAW.

Definition eval w b := eval_aux (ncells (w lor b)) w b.

Lemma evalS w b : 
  eval w b = 
  let s := w lor b in 
  if cwin w then WIN else
  if has_move s then
      \max_(i < nwidth) \max_(j < nheight | cmove s i j) 
                wcomp (eval b (mk_move w i j))
  else if cwin b then LOSS else DRAW.
Proof.
rewrite /eval; have := refl_equal (ncells (w lor b)).
move: {-1}(ncells _)=> n; elim: n w b => /= [|n IH] w b nE.
  case Ew: cwin => //; case Em: has_move => //.
  by have := ncells_has_move (w lor b); rewrite nE Em.
case Ew: cwin => //; case Em: has_move => //.
apply: eq_bigr => i _; apply: eq_bigr => j ijC.
congr (wcomp (eval_aux _ _ _)).
by move: nE; rewrite (ncells_cmove ijC) => [] [].
Qed.

Lemma evalOr w b : [|| eval w b == WIN, eval w b == DRAW | eval w b == LOSS].
Proof.
move:  {-1}(ncells (w lor b)) (refl_equal (ncells (w lor b))).
move=> n; elim: n w b => /= [|n IH] w b cE; rewrite evalS.
  case: cwin => //=.
  by have := ncells_has_move (w lor b); rewrite cE; case: has_move; case: cwin.
case: cwin => //=.
case E : has_move => //; last by case: cwin.
set m := \max_(i < _) _.
suff /or3P[/eqP->|/eqP->|/eqP->] : [|| m == WIN,  m == DRAW  | m == LOSS] by [].
have /idP/existsP[/= i1/existsP[/= j1 Hj1]] := E.
rewrite /m (bigD1 i1) //= (bigD1 j1) //=.
set m1 := \max_(i < _ | _) _; set m2 := \max_(i < _ | _)  _.
set m3 := eval _ _.
have IH1 i k (P : nat -> _) : 
    let m :=  \max_(j < k | cmove (w lor b) i j && P j)
                    wcomp (eval b (mk_move w i j)) in
    [|| m == UNKNOWN,  m == WIN,  m == DRAW  | m == LOSS].
  elim:  k => /= [|k IHk]; first by rewrite big_ord0.
  rewrite big_mkcond /= big_ord_recr /=  -big_mkcond /=.
  case E1 : (cmove _ _ _) => /=; last by rewrite maxn0.
  have {E1}/idP E1 := E1.
  case: (P k) => //=.
  suff /IH/or3P[/eqP->|/eqP->|/eqP->] :
       ncells (b lor (mk_move w i k)) = n by case/or4P : IHk => /eqP->.
  by have := ncells_cmove E1; rewrite cE => [] [].
have : [|| m1 == UNKNOWN, m1 == WIN, m1 == DRAW  | m1 == LOSS].
  by rewrite /= (IH1 i1 nheight (fun n => n != \val j1)).
pose gf i := \max_(j < nheight | cmove (w lor b) i j )
                    wcomp (eval b (mk_move w i j)).
have Hgf i : [|| gf i == UNKNOWN,  gf i == WIN,  gf i == DRAW  | gf i == LOSS].
  pose f (j : 'I_nheight) := cmove (w lor b) i j && true.
  rewrite /gf (eq_bigl f) => [|j]; first by apply: (IH1 i nheight xpredT).
  by rewrite /f andbT.
have IH2 k (P : nat -> _) : 
    let m :=  \max_(i < k | P i) gf i in
    [|| m == UNKNOWN,  m == WIN,  m == DRAW  | m == LOSS].
  elim: k => /= [|k IHk]; first by rewrite big_ord0.
  rewrite big_mkcond /= big_ord_recr /=  -big_mkcond /=.
  by case: (P k); case/or4P : IHk => /eqP->//; 
     case/or4P : (Hgf k) => /eqP ->.
have : [|| m2 == UNKNOWN, m2 == WIN, m2 == DRAW  | m2 == LOSS].
  by apply: (IH2 nwidth (fun n => n != i1)).
have : [|| m3 == WIN, m3 == DRAW  | m3 == LOSS].
  apply: IH.
  by have := ncells_cmove Hj1; rewrite cE => [] [].
by case/or3P => /eqP-> /or4P[]/eqP->/or4P[]/eqP->.
Qed.

Lemma eval_winP w b : 
  reflect 
  (cwin w \/ exists i j, cmove (w lor b) i j /\ eval b (mk_move w i j) = LOSS)
  (eval w b == WIN).
Proof.
pose f (i : 'I_nwidth) (j : 'I_nheight) := wcomp (eval b (mk_move w i j)).
pose g  (i : 'I_nwidth)  := \max_(j < nheight | cmove (w lor b) i j) f i j.
apply: (iffP eqP) => [|[Hc|[i [j [Cij Eij]]]]]; last 2 first.
- by rewrite evalS Hc.
- rewrite evalS; case E : cwin => //=.
  have iLw : i < nwidth by case/and3P: Cij.
  have jLh : j < nheight by case/and3P: Cij.
  have E1 : has_move (w lor b).
    by apply/existsP; exists (Ordinal iLw); apply/existsP; exists (Ordinal jLh).
  rewrite E1.
  have := evalOr w b; rewrite evalS /= E E1.
  set ss := \max_(_ < _) _ => Hss.
  suff : WIN <= ss by case/or3P : Hss => /eqP->.
  rewrite -[WIN]/(wcomp LOSS) -Eij.
  apply: leq_trans (leq_bigmax (Ordinal iLw)).
  by apply (@leq_bigmax_cond _ _ (f (Ordinal iLw)) (Ordinal jLh)).
rewrite evalS; case E : cwin => /=; first by left.
case E1 : has_move; last by case: cwin.
case: (eq_bigmax g) => /= [|i -> Mi]; first by rewrite card_ord.
case: (@eq_bigmax_cond _ (fun j : 'I_nheight => cmove (w lor b) i j) (f i)).
  case E2 : #|(fun j : 'I_nheight => cmove (w lor b) i j)| => //.
  move: Mi; rewrite /g big1 => //= j Cij.
  by rewrite (cardD1 j)/in_mem /= Cij in E2.
move => /= j; rewrite /in_mem /= => Cij maxE; right.
exists i; exists j; split => //.
rewrite -[LOSS]/(wcomp WIN) -Mi /g maxE /f.
by case/or3P : (evalOr  b (mk_move w i j)) => /eqP->.
Qed.

Lemma eval_lossP w b : 
  reflect 
  (~~ cwin w /\ 
    (cwin b \/ 
      has_move (w lor b) /\  
      forall i j, cmove (w lor b) i j -> eval b (mk_move w i j) = WIN))
  (eval w b == LOSS).
Proof.
apply: (iffP eqP) => [|[NWw [Wb | [Mwb Hf]]]]; last 2 first.
- rewrite evalS /= (negPf NWw) Wb.
  case E : has_move => //.
  case/existsP : E => /= i /existsP[/= j Cij].
  apply/anti_leq/andP; split; last first.
    rewrite (bigD1 i) //= (bigD1 j) //= evalS Wb /= wcompWIN.
    apply: leq_trans (leq_maxl _ _).
    by apply: leq_trans (leq_maxl _ _).
  apply/bigmax_leqP => /= i1 _.
  apply/bigmax_leqP => /= j1 _.
  by rewrite evalS Wb /= wcompWIN.
- rewrite evalS /= (negPf NWw) Mwb.
  case/existsP : Mwb => /= i /existsP[/= j Cij].
  apply/anti_leq/andP; split; last first.
    rewrite (bigD1 i) //= (bigD1 j) //= Hf //= wcompWIN.
    apply: leq_trans (leq_maxl _ _).
    by apply: leq_trans (leq_maxl _ _).
  apply/bigmax_leqP => /= i1 _.
  apply/bigmax_leqP => /= j1 Ci1j1.
  by rewrite Hf.
rewrite evalS /=; case: cwin => //; case E : has_move => //=; last first.
  by case: cwin => // _; split => //; left.
move=> He; split => //.
right; split => // i j Cij.
have iLw : i < nwidth by case/and3P : Cij.
have jLh : j < nheight by case/and3P : Cij.
case/or3P : (evalOr b (mk_move w i j)) => /eqP E1 //.
  suff : DRAW <= LOSS by [].
  rewrite -He (bigD1 (Ordinal iLw)) //= (bigD1 (Ordinal jLh)) //=.
  rewrite E1 wcompDRAW.
  apply: leq_trans (leq_maxl _ _).
  by apply: leq_trans (leq_maxl _ _).
suff : WIN <= LOSS by [].
rewrite -He (bigD1 (Ordinal iLw)) //= (bigD1 (Ordinal jLh)) //=.
rewrite E1 wcompLOSS.
apply: leq_trans (leq_maxl _ _).
by apply: leq_trans (leq_maxl _ _).
Qed.

Lemma eval_drawP w b : 
  reflect 
  [/\ ~~ cwin w, ~~ cwin b &
      has_move (w lor b) -> 
      (exists i j, cmove (w lor b) i j /\ eval b (mk_move w i j) = DRAW) /\
      (forall i j, cmove (w lor b) i j -> DRAW <= eval b (mk_move w i j))]
  (eval w b == DRAW).
Proof.
pose f (i : 'I_nwidth) (j : 'I_nheight) := wcomp (eval b (mk_move w i j)).
pose g  (i : 'I_nwidth)  := \max_(j < nheight | cmove (w lor b) i j) f i j.
apply: (iffP eqP) => [|[NWw NWb HC]]; last first.
- rewrite evalS /= (negPf NWw).
  case: has_move HC => [/(_ isT) [[i [j [Cij Eij]] HE]] |]//; last first.
    by rewrite (negPf NWb).
  have iLw : i < nwidth by case/and3P : Cij.
  have jLh : j < nheight by case/and3P : Cij.
  apply/anti_leq/andP; split; last first.
    rewrite (bigD1 (Ordinal iLw)) //= (bigD1 (Ordinal jLh)) //= Eij wcompDRAW.
    apply: leq_trans (leq_maxl _ _).
    by apply: leq_trans (leq_maxl _ _).
  apply/bigmax_leqP => /= i1 _.
  apply/bigmax_leqP => /= j1 Ci1j1.
  have := HE _ _ Ci1j1.
  by case/or3P : (evalOr b (mk_move w i1 j1)) => /eqP ->.
rewrite evalS /=; case E1 : cwin => //.
case E2 : has_move => //=; last by case: cwin.
move=> He.
have F1 i j : cmove (w lor b) i j -> DRAW <= eval b (mk_move w i j).
  move=> Cij.
  suff : wcomp (eval b (mk_move w i j)) <= DRAW.
    by case/or3P : (evalOr b (mk_move w i j)) => /eqP ->.
  rewrite -He.
  have iLw : i < nwidth by case/and3P : Cij.
  have jLh : j < nheight by case/and3P : Cij.
  rewrite (bigD1 (Ordinal iLw)) //= (bigD1 (Ordinal jLh)) //=.
  apply: leq_trans (leq_maxl _ _).
  by apply: leq_trans (leq_maxl _ _).
have [] := boolP [exists i : 'I_nwidth,
                [exists j : 'I_nheight, cmove (w lor b) i j &&
                                        (eval b (mk_move w i j) == DRAW)]].
  move=> /existsP[i /existsP[j /andP[Cij /eqP Eij]]]. 
  split=> // [|_]; first by apply/negP => NWb; move: Eij; rewrite evalS /= NWb.
  by split => //; exists i; exists j.
rewrite negb_exists => /forallP /= HF.
suff : DRAW <= LOSS by [].
rewrite -He; apply/bigmax_leqP => /= i _; apply/bigmax_leqP => /= j Cij.
have := F1 i j Cij.
have := HF i; rewrite negb_exists => /forallP/(_ j).
rewrite negb_and Cij /=.
by case/or3P: (evalOr b (mk_move w i j)) => /eqP->.
Qed.

Lemma find_moves_win w b : 
  wf w b -> find_moves w b = Win -> eval w b = WIN.
Proof.
move=> [wf_wb ncw_w ncw_b] /eqP.
rewrite /find_moves fms_win_corect // => /existsP[i /existsP [j /andP[cM cW]]].
apply/eqP/eval_winP; right; exists i; exists j; split => //.
by apply/eqP/eval_lossP; split => //; left.
Qed.

Lemma find_moves_draw w b : wf w b -> find_moves w b = Draw -> eval w b = DRAW.
Proof.
move=> [wf_wb ncw_w ncw_b] /eqP.
rewrite /find_moves fms_draw_corect // => Nhm.
by apply/eqP/eval_drawP; split; rewrite ?(negPf Nhm).
Qed.

Lemma find_moves_forced w b m : 
  wf w b -> find_moves w b = Forced m -> eval w b = wcomp (eval b (w lor m)).
Proof.
move=> [wf_wb ncw_w ncw_b] /eqP /(fms_forced_corect wf_wb) // => []
   [Hf [i [j [mE cM1 cW1]]]].
have iLw : i < nwidth by case/and3P: cM1.
have jLh : j < nheight by case/and3P: cM1.
have -> : w lor m = mk_move w i j by rewrite mE.
rewrite evalS (negPf ncw_w) /= ifT; last first.
  by apply/existsP; exists (Ordinal iLw); apply/existsP; exists (Ordinal jLh).
rewrite (bigD1 (Ordinal iLw)) //=.
rewrite (bigD1 (Ordinal jLh)) //=.
set u := \max_(_ < _ | _) _.
have -> : u = 0%N.
  apply: big1 => /= j1 /andP[cM2 /eqP/val_eqP/=].
  by rewrite (cmoveE cM1) (cmoveE cM2) eqxx.
rewrite maxn0; set v := \max_(_ < _ | _) _.
apply/maxn_idPl.
suff vLL : v <= LOSS.
  by apply: (leq_trans vLL); case/or3P: (evalOr b (mk_move w i j)) => /eqP->.
apply/bigmax_leqP => /= i1 /eqP/val_eqP/= i1Di.
apply/bigmax_leqP => /= j1 cM2.
suff -> : eval b (mk_move w i1 j1) = WIN by [].
apply/eqP/eval_winP; right.
exists i; exists j; split; first by rewrite lorC; apply: cmoveC.
apply/eqP/eval_lossP; split; first by apply: Hf.
by left.
Qed.

Lemma find_moves_forced_wf w b m : 
  wf w b -> find_moves w b = Forced m -> wf b (w lor m).
Proof.
move=> [wf_wb ncw_w ncw_b] /eqP /(fms_forced_corect wf_wb) // => []
   [Hf [i [j [mE cM1 cW1]]]].
have iLw : i < nwidth by case/and3P: cM1.
have jLh : j < nheight by case/and3P: cM1.
have -> : w lor m = mk_move w i j by rewrite mE.
split => //; first by apply: wf_state_cmove.
by apply: Hf.
Qed.

Lemma find_moves_forced_cmove w b m : 
  wf w b -> find_moves w b = Forced m-> exists i j,
 (m = lsl 1 (of_nat i * horizontal + of_nat j)) /\
 cmove (w lor b) i j.
Proof.
move=> [wf_wb ncw_w ncw_b] /eqP /(fms_forced_corect wf_wb) // => []
   [Hf [i [j [mE cM1 cW1]]]].
by exists i; exists j; split.
Qed.

Lemma find_moves_moves_wf w b l m : 
  wf w b -> find_moves w b = Moves l -> m \in l -> wf b (w lor m.1).
Proof.
move=> [wf_wb ncw_w ncw_b] /eqP /(fms_moves_corect wf_wb) // => []
   [Hww Hwb Hs Hi Hc].
case: m => i j /Hi [i1 [j1 [cM1 iE]]].
have -> : w lor i = mk_move w i1 j1 by rewrite iE.
split => //=; first by apply: wf_state_cmove.
by apply: Hww.
Qed.

Lemma find_moves_moves_cmove_in w b i j l : 
  wf w b -> find_moves w b = Moves l -> cmove (w lor b) i j -> 
  (lsl 1 (of_nat i * horizontal + of_nat j)) \in (map fst l).
Proof.
move=> [wf_wb ncw_w ncw_b] /eqP /(fms_moves_corect wf_wb) // => []
   [Hww Hwb Hs Hi Hc] /Hc [/= v1 Hv1].
by apply/mapP=> /=; exists (lsl 1 (of_nat i * horizontal + of_nat j), v1).
Qed.

Lemma find_moves_moves_size w b l :
  wf w b -> find_moves w b = Moves l -> 0 < size l.
Proof.
move=> [wf_wb ncw_w ncw_b] /eqP /(fms_moves_corect wf_wb) // [].
by move=> _ _ [].
Qed.

Lemma find_moves_moves_uniq w b l :
  wf w b -> find_moves w b = Moves l -> uniq (map fst l).
Proof.
move=> [wf_wb ncw_w ncw_b] /eqP /(fms_moves_corect wf_wb) // [].
by move=> _ _ [].
Qed.

Lemma find_moves_moves_cmove w b l (m : int * int) :
    wf w b -> find_moves w b = Moves l -> m \in l -> 
    exists i j, [/\ cmove (w lor b) i j,  ~~ cwin (mk_move w i j) &
    m.1 = lsl 1 (of_nat i * horizontal + of_nat j)].
Proof.
case: m => m1 l1.
move=> [wf_wb ncw_w ncw_b] /eqP /(fms_moves_corect wf_wb) // => [].
move=> [Hcm _ _ He _] /He [i2 [j2 [i2j2C m1E]]].
by exists i2; exists j2; split => //; apply: Hcm.
Qed.

Lemma find_moves_moves_mem w b l i j :
    wf w b -> find_moves w b = Moves l -> cmove (w lor b) i j -> 
    exists j1, ((lsl 1 (of_nat i * horizontal + of_nat j)), j1) \in l.
Proof.
by move=> [wf_wb ncw_w ncw_b] /eqP /(fms_moves_corect wf_wb) // => []
 [_ _ _ _ Hcm /Hcm].
Qed.

Lemma cmove_transpose s1 s2 i j :
  transpose s1 s2 -> i < nwidth -> cmove s1 i j = cmove s2 (nwidth - i.+1) j.
Proof.
have Hci s3 s4 i1 j1 :
    transpose s3 s4 -> cmove s3 i1 j1 -> cmove s4 (nwidth - i1.+1) j1.
  move=> /transposeP HCE /and3P[iLw jLw /forallP/= HC].
  by rewrite /cmove ltn_subrL /= jLw /=; apply/forallP => z; rewrite -HCE.
move=> Ht iLw; apply/idP/idP => [|Cij]; first by apply: Hci.
have -> : i = (nwidth -  (nwidth - i.+1).+1)%N by rewrite subnS subKn //.
by apply: Hci Cij; rewrite transpose_sym.
Qed.

Lemma has_move_transpose s1 s2 : transpose s1 s2 -> has_move s1 = has_move s2.
Proof.
suff Hhi s3 s4 : transpose s3 s4 -> has_move s3 -> has_move s4.
  by move=> Ht; apply/idP/idP; apply: Hhi => //; rewrite transpose_sym.
move=> Ht.
move=> /existsP[/= i /existsP[/= j Hc]].
apply/existsP; exists (rev_ord i); apply/existsP; exists j => /=.
by rewrite -(cmove_transpose _ Ht).
Qed.

Lemma eval_transpose w1 w2 b1 b2 :
  transpose w1 w2 -> transpose b1 b2 -> eval w1 b1 = eval w2 b2.
Proof.
move:  {-1}(ncells (w1 lor b1)) (refl_equal (ncells (w1 lor b1))).
move=> n; elim: n w1 w2 b1 b2 => /= [|n IH] w1 w2 b1 b2 cE Ht1 Ht2;
   rewrite [LHS]evalS [RHS]evalS -(cwin_transpose Ht1); case E : cwin => //=.
   rewrite -(has_move_transpose (transpose_lor Ht1 Ht2)).
  by rewrite -(cwin_transpose Ht2) [in LHS]ifN 1?[in RHS]ifN //;
     have := ncells_has_move (w1 lor b1); rewrite cE; case: has_move.
have Ht3 := transpose_lor Ht1 Ht2.
rewrite -(has_move_transpose Ht3).
case E1: has_move; last by rewrite -(cwin_transpose Ht2).
pose f i := \max_(j < nheight | cmove (w1 lor b1) i j)  
                 wcomp (eval b1 (mk_move w1 i j)).
rewrite -(big_mkord xpredT f) big_nat_rev /= big_mkord /= add0n /f.
apply: eq_bigr => i _.
under [LHS]eq_bigl => j do 
  rewrite -(@cmove_transpose (w2 lor b2)) 1? transpose_sym //.
under [LHS]eq_bigr => /= j ijC.
  have Ht4 : transpose (mk_move w2 i j) (mk_move w1 (nwidth - i.+1) j)
    by apply: mk_move_transpose; rewrite // transpose_sym.
  rewrite -(IH b2 _ _ _ _ _ Ht4); last 2 first.
  - have := cE; rewrite (ncells_transpose Ht3) // (ncells_cmove ijC) //.
    by case.
  - by rewrite transpose_sym.
  over.
by [].
Qed.

Lemma eval_score_bound w b s :
  (down_score s <= eval w b <= up_score s)%N -> to_nat s < 2 ^ nscoresize.
Proof.
rewrite /down_score /up_score.
by do 6 (case: eqP => [->//|_]); case/or3P: (evalOr w b) => /eqP->.
Qed.
