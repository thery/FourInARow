From Stdlib Require Import ZArith Ascii List String PrimInt63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_boot.
From HB Require Import structures.

From Stdlib Require Import Lia.
Import PrimInt63Notations.
Import Uint63Axioms.
Import Uint63.
Require Import ssr_int.
Require Import Pbasic.
Require Import Pmoves.
Require Import FourInARow.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(******************************************************************************)
(*                                                                            *)
(*                                                                            *)
(*    Hash tables                                                             *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)


Open Scope uint63_scope.

Section Phash.

Variables width height : int.
Notation nhorizontal := (nhorizontal height).
Notation nwidth := (nwidth width).
Notation nheight := (nheight height).

Hypothesis wh_hyp : nwidth * nhorizontal < ndigits.
Hypothesis w_hyp : 3 < nwidth.
Hypothesis h_hypL : 3 < nheight.
Hypothesis h_hypU : nheight.+1 < ndigits.

Notation slocksize := (slocksize width height).

Hypothesis h_hprime : 2 ^ to_nat slocksize < to_nat hprime. 

Notation size := seq.size.
Notation get_border := (get_border width height).
Notation valid_pegs := (valid_pegs width height).
Notation horizontal := (horizontal height).
Notation get_column := (get_column height).
Notation cell := (cell height).
Notation eval := (eval width height).
Notation evalOr := (evalOr wh_hyp h_hypU).
Notation sym_code := (sym_code height).
Notation nhorizontalLwB := (nhorizontalLwB height).
Notation nwidthLwB := (nwidthLwB width).
Notation transpose := (transpose width height).
Notation get_code := (get_code width height).
Notation hget := (hget width height).
Notation get_columnE := (@get_columnE width height).
Notation hput := (hput width height).
Notation number_of_cells := (number_of_cells width height).
Notation "t .[ i ]" := (get t i)
  (at level 1, left associativity, format "t .[ i ]").
Notation "t .[ i <- a ]" := (set t i a)
  (at level 1, left associativity, format "t .[ i <- a ]").

Lemma init_matrix_length1 (A : Type) n nn a (v : A) m : 
  nn <=? length a -> (Z.of_nat n <= φ nn)%Z ->  
  length (init_matrix A n nn a v m) = length a.
Proof.
elim: n nn a  => //= n IH nn a nLa nLm.
have /lebP tnLa := nLa.
have nnB := to_Z_bounded nn.
have nn1E : to_Z (nn - 1) = (to_Z nn - 1)%Z.
  by rewrite sub_spec ?to_Z_1 Z.mod_small; lia.
by rewrite IH ?length_set //; (try apply/lebP); lia.
Qed.

Lemma init_matrix_length2 (A : Type) n nn a (v : A) m i : 
    m <=? max_length ->
    (Z.of_nat n <= to_Z nn)%Z -> nn <=? length a ->
    (to_Z i + Z.of_nat n < wB)%Z ->
    if (nn <=? i + of_nat n) && (i <? nn) then
       length (init_matrix A n nn a v m).[i] = m
    else length (init_matrix A n nn a v m).[i] = length (a.[i]).
Proof.
move=> mLm.
elim: n nn a => [|n IH] nn a Ha.
  rewrite Z.add_0_r => Hn.
  case: lebP => /=; rewrite add_spec //. 
  rewrite to_Z_0 Z.add_0_r Z.mod_small; last by apply: to_Z_bounded.
  by case: ltbP => //; lia.
move=> Hn H1.
have nnB := to_Z_bounded nn.
have nLw : (Z.of_nat n < wB)%Z by lia.
have nB := to_Z_bounded (of_nat n).
have znnsP : (0 < to_Z nn)%Z by lia.
have nn1E : to_Z (nn - 1) = (to_Z nn - 1)%Z.
  by  rewrite sub_spec ?to_Z_1 Z.mod_small; lia.
have F : (Z.of_nat n <= to_Z (nn - 1))%Z by lia.
have F' : nn - 1 <=? length a.[nn - 1<-make m v].
  apply/lebP; rewrite nn1E length_set.
  by have /lebP := Hn; lia.
have iB := to_Z_bounded i.
have n1B := to_Z_bounded (of_nat n.+1).
have F1 : (to_Z i + Z.of_nat n < wB)%Z by lia.
have F2 : to_Z (of_nat n) = (Z.of_nat n)%Z.
  by rewrite of_Z_spec Z.mod_small; lia.
have F3 : to_Z (of_nat n.+1) = (Z.of_nat n + 1)%Z.
  by rewrite of_Z_spec Z.mod_small; lia.
have F4 : φ (i + of_nat n.+1) =  (φ i + Z.of_nat n + 1)%Z.
  by rewrite add_spec Z.mod_small; lia.
have F5 : φ (i + of_nat n) =  (φ i + Z.of_nat n)%Z.
  by rewrite add_spec Z.mod_small; lia.
have n1E : to_Z (nn - 1) = ((to_Z nn) - 1)%Z.
  by rewrite sub_spec ?to_Z_1 Z.mod_small; lia.
case: lebP => //=; last first.
  rewrite F4.
  move/Z.nle_gt => H3.
  have := IH (nn - 1) a.[nn - 1<-make m v] F F'.
  rewrite ifN; last first.
    by case: lebP; rewrite ?n1E  F5 //; lia.
  move=> ->; try lia.
  rewrite get_set_other // => HH.
  by move: H3; rewrite -HH n1E; lia.
rewrite F4 => H3.
case: ltbP => [H4|/Z.nlt_ge H4]; last first.
  have := IH (nn - 1) a.[nn - 1<-make m v] F F'.
  rewrite ifN //.
    rewrite get_set_other //.
    apply; lia.
    by move=> HH; move: H4; rewrite -HH; lia.
  rewrite andbC negb_and; case: ltbP => //.
  by rewrite n1E; lia.
have := IH (nn - 1) a.[nn - 1<-make m v] F F'.
case: lebP; rewrite F5 n1E; try lia.
case: ltbP; rewrite n1E //= => V1 V2 -> //; try lia.
suff H : nn - 1 = i.
  rewrite H get_set_same.
    by rewrite length_make // ?mLm.
  case ltbP; try lia.
  have /lebP := Hn; lia.
apply: to_Z_inj.
by rewrite n1E; lia.
Qed.

Lemma init_matrix_get (A : Type) n nn a (v : A) m i j : 
    m <=? max_length ->
    j <? m ->
    (Z.of_nat n <= to_Z nn)%Z -> nn  <=? length a ->
    (to_Z i + Z.of_nat n < wB)%Z ->
    if (nn <=? i + of_nat n) && (i <? nn) then
      (init_matrix A n nn a v m).[i].[j] = v
    else (init_matrix A n nn a v m).[i].[j] = a.[i].[j].
Proof.
move=> mLm jLn.
elim: n nn a => [|n IH] nn a Ha.
  rewrite Z.add_0_r => Hn.
  case: lebP => //=; rewrite add_spec //. 
  rewrite to_Z_0 Z.add_0_r Z.mod_small; last by apply: to_Z_bounded.
  by case: ltbP => //; lia.
move=> Hn H1.
have nnB := to_Z_bounded nn.
have nLw : (Z.of_nat n < wB)%Z by lia.
have nB := to_Z_bounded (of_nat n).
have znnsP : (0 < to_Z nn)%Z by lia.
have nn1E : to_Z (nn - 1) = (to_Z nn - 1)%Z.
  by  rewrite sub_spec ?to_Z_1 Z.mod_small; lia.
have F : (Z.of_nat n <= to_Z (nn - 1))%Z by lia.
have F' : nn - 1 <=? length a.[nn - 1<-make m v].
  apply/lebP; rewrite nn1E length_set.
  by have /lebP := Hn; lia.
have iB := to_Z_bounded i.
have n1B := to_Z_bounded (of_nat n.+1).
have F1 : (to_Z i + Z.of_nat n < wB)%Z by lia.
have F2 : to_Z (of_nat n) = (Z.of_nat n)%Z.
  by rewrite of_Z_spec Z.mod_small; lia.
have F3 : to_Z (of_nat n.+1) = (Z.of_nat n + 1)%Z.
  by rewrite of_Z_spec Z.mod_small; lia.
have F4 : φ (i + of_nat n.+1) =  (φ i + Z.of_nat n + 1)%Z.
  by rewrite add_spec Z.mod_small; lia.
have F5 : φ (i + of_nat n) =  (φ i + Z.of_nat n)%Z.
  by rewrite add_spec Z.mod_small; lia.
have n1E : to_Z (nn - 1) = ((to_Z nn) - 1)%Z.
  by rewrite sub_spec ?to_Z_1 Z.mod_small; lia.
case: lebP => //=; last first.
  rewrite F4.
  move/Z.nle_gt => H3.
  have := IH (nn - 1) a.[nn - 1<-make m v] F F'.
  rewrite ifN; last first.
    by case: lebP; rewrite ?n1E  F5 //; lia.
  move=> ->; try lia.
  rewrite get_set_other // => HH.
  by move: H3; rewrite -HH n1E; lia.
rewrite F4 => H3.
case: ltbP => [H4|/Z.nlt_ge H4]; last first.
  have := IH (nn - 1) a.[nn - 1<-make m v] F F'.
  rewrite ifN //.
    rewrite get_set_other //.
    apply; lia.
    by move=> HH; move: H4; rewrite -HH; lia.
  rewrite andbC negb_and; case: ltbP => //.
  by rewrite n1E; lia.
have := IH (nn - 1) a.[nn - 1<-make m v] F F'.
case: lebP; rewrite F5 n1E; try lia.
case: ltbP; rewrite n1E //= => V1 V2 -> //; try lia.
suff H : nn - 1 = i.
  rewrite H get_set_same.
    by rewrite get_make //.
  case ltbP; try lia.
  have /lebP := Hn; lia.
apply: to_Z_inj.
by rewrite n1E; lia.
Qed.

Lemma make_matrix_length1 (A : Type) n m (v : A) :
   n <=? max_length -> length (make_matrix A n m v) = n.
Proof.
move=> nLl.
have nB := to_Z_bounded n.
rewrite init_matrix_length1 //.
rewrite length_make // nLl //.
rewrite length_make nLl; apply/lebP; lia.
by rewrite Z2Nat.id; lia.
Qed.

Lemma make_matrix_length2 (A : Type) n m  (v : A) i : 
    n <=? max_length -> 
    m <=? max_length ->
    i <? n -> length (make_matrix A n m v).[i] = m.
Proof.
move=> nLl mLl iLn.
rewrite /make_matrix /=.
have nB := to_Z_bounded n.
have F1 : (Z.of_nat (to_nat n) <= φ (n))%Z by rewrite Z2Nat.id; lia.
have F2 : n ≤? length (make n (make 0 v)).
  by apply/lebP; rewrite length_make nLl; lia.
have F3 : (φ (i) + Z.of_nat (to_nat n) < wB)%Z.
  rewrite Z2Nat.id; try lia.
  have /lebP := nLl; have/ltbP := iLn.
  set u := to_Z max_length; compute in u; rewrite /u.
  set w := wB; compute in w; rewrite /w.
  lia.
have := @init_matrix_length2 _ (to_nat n) n (make n (make 0 v)) 
               v m i mLl F1 F2 F3.  
have := init_matrix_length2 v mLl F1 F2 F3.
have iB := to_Z_bounded i.
rewrite iLn andbT ifT //.
by apply/lebP; rewrite add_spec of_Z_spec !Z.mod_small; try lia.
Qed.

Lemma make_matrix_get (A : Type) n m  (v : A) i j : 
    n <=? max_length -> m <=? max_length ->
    i <? n -> j <? m ->
    (make_matrix A n m v).[i].[j] = v.
Proof.
move=> nLl mLl iLn jLm.
rewrite /make_matrix /=.
have nB := to_Z_bounded n.
have F1 : (Z.of_nat (to_nat n) <= φ (n))%Z by rewrite Z2Nat.id; lia.
have F2 : n ≤? length (make n (make 0 v)).
  by apply/lebP; rewrite length_make nLl; lia.
have F3 : (φ (i) + Z.of_nat (to_nat n) < wB)%Z.
  rewrite Z2Nat.id; try lia.
  have /lebP := nLl; have/ltbP := iLn.
  set u := to_Z max_length; compute in u; rewrite /u.
  set w := wB; compute in w; rewrite /w.
  lia.
have := init_matrix_get v mLl jLm F1 F2 F3.
have iB := to_Z_bounded i.
rewrite iLn andbT ifT //.
by apply/lebP; rewrite add_spec of_Z_spec !Z.mod_small; lia.
Qed.

Lemma make_hash_length1 (u : unit) : length (make_hash u) = nhash.
Proof. by apply: make_matrix_length1. Qed.

Lemma make_hash_length2 (u : unit) i : 
   i <? nhash -> length (make_hash u).[i] = (2 * (hprime/nhash + 1)).
Proof. by move=> iLn; apply: make_matrix_length2. Qed. 

Lemma make_hash_get (u : unit) i j : 
    i <? nhash -> j <? 2 * (hprime/nhash + 1) ->
    (make_hash u).[i].[j] = 0.
Proof. by move=> nLi mLj; apply: make_matrix_get. Qed.

Definition sget_code w b := get_border w b lor w.

Lemma sget_code_uniq w1 w2 b1 b2 : 
  valid_pegs (w1 lor b1) -> valid_pegs (w2 lor b2) -> 
  w1 land b1 = 0 -> w2 land b2 = 0 ->
  sget_code w1 b1 = sget_code w2 b2 -> w1 = w2 /\ b1 = b2.
Proof.
move=> w1b1V w2b2V Aw1 Aw2 CE.
suff : w1 = w2.
  move=> wE; split => //.
  move: CE; rewrite /sget_code -!and_imp_add_or; try by apply get_border_w.
  rewrite /get_border -!and_imp_add_or // wE.
  by move=> /add_cancel_r /add_cancel_l /add_cancel_l.
suff BE : get_border w1 b1 = get_border w2 b2.
  move: CE; rewrite /sget_code -!and_imp_add_or; try by apply get_border_w.
  by rewrite BE => /add_cancel_l.
have [/forallP /= HF|/forallPn /= [x Hx]] :=
    boolP [forall i, bit (get_border w1 b1) i == bit (get_border w2 b2) i].
  by apply: bit_ext => i; exact: (eqP (HF i)).
wlog Hb : w1 w2 b1 b2 w1b1V w2b2V Aw1 Aw2 CE Hx / bit (get_border w1 b1) x.
  move=> HW.
  have [Hb1|Hb1] := boolP (bit (get_border w1 b1) x); first by apply: HW.
  apply/sym_equal/HW => //; first by rewrite eq_sym.
  by case: bit Hb1 Hx => //; case: bit.
have Hb2 : ~~  bit (get_border w2 b2) x by case: bit Hx Hb => //; case: bit.
have : bit (sget_code w2 b2) x  by rewrite -CE lor_spec Hb.
  rewrite lor_spec (negPf Hb2) /= => Hbw2.
have iLw : to_nat x %/ nhorizontal < nwidth.
  by apply: valid_pegs_get_border_width w1b1V Hb.
set i := (_ %/ _) in iLw.
pose j := to_nat x %% nhorizontal.
have jLh : j < nhorizontal by apply: ltn_pmod; rewrite nhorizontalE.
have xE : x = of_nat i * horizontal + of_nat j.
  by have := of_nat_int_add_mod x horizontal.
pose z2 := to_nat (up_log2 (get_column (w2 lor b2) (of_nat i))).
have z2Lh : z2 < nhorizontal.
  have := valid_pegs_opzs iLw w2b2V.
  rewrite opzsE' //; last by apply/nltbP/ltnW.
  move => /andP[/nlebP uLh _].
  by apply: leq_ltn_trans uLh _; rewrite nhorizontalE.
have Hcg2 : cell (get_border w2 b2) i z2.
  by rewrite valid_pegs_up_log2_cell.
have jLz2 : j < z2.
  apply: valid_pegs_up_log2_lt iLw _ _  => //.
  by rewrite cell_lor /cell -xE Hbw2.
have : cell (sget_code w1 b1) i z2 by rewrite CE cell_lor Hcg2.
move: Hb; rewrite xE -[bit _ _ ]/(cell _ _ _) valid_pegs_up_log2_cell //.
move => /eqP iE.
rewrite cell_lor valid_pegs_up_log2_cell //.
rewrite -iE (gtn_eqF jLz2) /= => Ciz2.
suff : z2 < j by case: ltngtP jLz2.
rewrite iE.
apply: valid_pegs_up_log2_lt w1b1V _ _ _ => //.
by rewrite cell_lor Ciz2.
Qed.

Lemma symcode_code_rec_cell s1 s2 i j k : 
  i <= nwidth -> k < nhorizontal -> j < nwidth -> cell (sym_code i s1 s2) j k = 
  if (i <= j) then cell s1 (j - i) k else cell s2 (i - j.+1) k.
Proof.
elim: i j k s1 s2 => /= [j k s1 s2 _ _|i IH j k s1 s2 iLw kLh jLw].
  by rewrite subn0.
have kLw : k < nwB by apply: ltn_trans nhorizontalLwB.
have iLw' : i < nwB by apply: ltn_trans _ nwidthLwB.
have kE : to_nat(of_nat k) = k by rewrite of_natK.
rewrite IH //; last by apply: ltnW.
have ijE :  to_nat(of_nat (i - j.+1)) = (i - j.+1)%N.
  by rewrite of_natK // (leq_ltn_trans (leq_subr _ _ )).
have ijhE : to_nat (of_nat (i - j.+1) * horizontal) = 
               ((i - j.+1) * nhorizontal)%N.
  rewrite to_nat_mul ?ijE //.
  apply: leq_ltn_trans (whLwB wh_hyp).
  rewrite leq_mul2r (leq_trans (leq_subr _ _ )) ?[to_nat _]nhorizontalE //.
  by apply: ltnW.
have ijhkE : to_nat (of_nat (i - j.+1) * horizontal + of_nat k) = 
               ((i - j.+1) * nhorizontal + k)%N.
  rewrite to_nat_add ?ijhE ?kE //.
  apply: leq_ltn_trans (_ : (i - j.+1).+1 * nhorizontal < _).
    by rewrite mulSn addnC leq_add2r // ltnW.
  apply: leq_ltn_trans (whLwB wh_hyp).
  rewrite leq_mul2r (leq_ltn_trans _ iLw) ?nhorizontalE //.
  by apply: leq_subr.
case: ltngtP => [iLj|jLi|<-] //; last first.
- rewrite !subnn cell_lor /cell mul_0_l add_0_l.
  rewrite bit_lsl ifT /=; last first.
    by case: nltbP => // [] []; rewrite of_natK.
  rewrite land_spec (@full_first_column_spec width height) //.
  by case: nltbP; rewrite ?andbT // of_natK.
- rewrite /cell bit_lsr /= ifT.
    suff -> : of_nat (i.+1 - j.+1) = 1 + of_nat (i - j.+1).
      by rewrite mul_add_distr_r mul_1_l add_assoc.
    apply: to_nat_inj; rewrite of_natK //; last first.
      by apply: leq_ltn_trans (leq_subr _ _) (leq_ltn_trans _ nwidthLwB).
    rewrite to_nat_add ?add1n ?ijE ?subSn //.
    rewrite (leq_ltn_trans _ nwidthLwB) //.
    by apply: leq_ltn_trans (leq_subr _ _ ) iLw.
  apply/nlebP.
  rewrite ijhkE to_nat_add ?ijhkE ?leq_addl //.
  apply: leq_trans (_ : nhorizontal + ((i - j.+1).+1 * nhorizontal) <= _).
    by rewrite ltn_add2l mulSn addnC ltn_add2r.
  rewrite -mulSn // (leq_trans _ (_  : i.+2 * nhorizontal <= _)) //.
    by rewrite leq_mul2r ltnS (leq_ltn_trans (leq_subr _ _)) // nhorizontalE.
  rewrite (leq_trans _ (_  : nwidth.+2 * nhorizontal <= _)) //.
    by rewrite leq_mul2r !ltnS ltnW // nhorizontalE.
  apply: leq_trans (_ : ndigits.+2 * ndigits <= _); last first.
    apply: leq_trans (_ : 2 ^ 12 <= _); first by [].
    by rewrite nwB_pow leq_exp2l.
  apply: leq_mul; first by rewrite !ltnS ltnW // (@nwidthLd _ height).
  by apply/ltnW/(@nhorizontalLd width).
rewrite cell_lor cell_land {3}/cell (@full_first_column_spec width) //.
have : (nhorizontal <= (j - i) * nhorizontal + k).
  apply: leq_trans (leq_addr _ _).
  by rewrite -[X in X <= _]mul1n leq_mul2r nhorizontalE // subn_gt0 iLj.
have jLw' : j < nwB by apply: ltn_trans nwidthLwB.
have jiE :  to_nat(of_nat (j - i)) = (j - i)%N.
  by rewrite of_natK // (leq_ltn_trans (leq_subr _ _ )).
have jihE : to_nat (of_nat (j - i) * horizontal) = 
               ((j - i) * nhorizontal)%N.
  rewrite to_nat_mul ?jiE //.
  apply: leq_ltn_trans (whLwB wh_hyp).
  rewrite leq_mul2r [to_nat _]nhorizontalE //.
  by rewrite (leq_trans (leq_subr _ _ )) // ltnW.
have jihkE : to_nat (of_nat (j - i) * horizontal + of_nat k) = 
               ((j - i) * nhorizontal + k)%N.
  by rewrite (@ihjE width height) // (leq_ltn_trans (leq_subr _ _)).
case: nltbP; rewrite jihkE.
  rewrite ltnNge (leq_trans _ (leq_addr _ _)) // -[X in X <= _]mul1n leq_mul2r.
  by rewrite subn_gt0 iLj orbT.
move=> jihkLh hLjihk; rewrite andbF orbF /cell bit_lsl ifN.
  congr bit.
  rewrite minus_addE add_comm -mul_N1_l add_assoc -mul_add_distr_r.
  congr (_ * _ + _).
  rewrite add_comm -minus_addE.
  apply: to_nat_inj.
  rewrite to_nat_sub; last first.
  - by rewrite [X in X < _]of_natK (leq_ltn_trans (leq_subr _ _)).
  - by rewrite jiE leq_subRL ?addn1 // ltnW.
  rewrite subn1 [in LHS]jiE [RHS]of_natK subnS //.
  by rewrite prednK ?subn_gt0 // (leq_trans (leq_subr _ _)) // ltnW.
rewrite negb_or.
case: nltbP; first rewrite jihkE //.
case: nlebP => //.
rewrite leqNgt jihkE => [] /negP[].
apply: leq_ltn_trans (_ : nwidth * nhorizontal < _); last by [].
apply: leq_trans (_ : (j - i) * nhorizontal + nhorizontal <= _).
  by rewrite leq_add2l ltnW.
by rewrite addnC -mulSn leq_mul2r (leq_ltn_trans (leq_subr _ _)) ?orbT.
Qed.

Lemma transpose_sym_code s : transpose (sym_code nwidth zero s) s.
Proof.
apply/transposeP => i j iLw jLh.
by rewrite symcode_code_rec_cell // ifN // -ltnNge.
Qed.

Lemma get_code_correct w b h : 
  get_code w b h = sget_code w b \/
  transpose (get_code w b h) (sget_code w b).
Proof.
rewrite /get_code; case: nlebP => _; last first.
  by left; rewrite /sget_code lorC // get_borderC.
rewrite /FourInARow.min; case: (_ ?= _); first 2 last.
- by left; rewrite /sget_code lorC // get_borderC.
- by left; rewrite /sget_code lorC // get_borderC.
by right; rewrite /sget_code lorC transpose_sym_code.
Qed.

Lemma sym_code_bound k r v :
  k <= nwidth -> 
  to_nat r < 2 ^ ((nwidth - k) * nhorizontal) -> 
  to_nat v < 2 ^ (k * nhorizontal) ->
  to_nat (sym_code k r v) < 2 ^ (nwidth * nhorizontal).
Proof.
elim: k r v => //= [|k IH  r v kLw rLwh vLkh]; first by rewrite subn0.
apply: IH; first by apply: ltnW.
- apply: to_nat_lor_bound.
    rewrite to_nat_lslW modn_small //.
    rewrite -[(nwidth - k)%N]prednK; last by rewrite subn_gt0.
    by rewrite mulSn addnC expnD ltn_mul2r expn_gt0 //= -subnS.
  apply: ltn_trans (_ : 2 ^ (nwidth * nhorizontal) < _); last first.
    by rewrite nwB_pow ltn_exp2l.
  rewrite -[nwidth]prednK; last by apply: ltn_trans w_hyp.
  rewrite mulSn addnC expnD ltn_mul2r expn_gt0 (leq_trans rLwh) //.
  by rewrite leq_exp2l // leq_mul2r // -subn1 leq_sub // nhorizontalE.
- rewrite landC; apply: to_nat_land_bound.
  apply: ltn_bit.
    apply: leq_ltn_trans wh_hyp; rewrite leq_mul2r nhorizontalE //=.
    by rewrite leq_subLR leq_addl.
  move=> i hwH.
  rewrite (@full_first_column_spec width) //; case: nltbP => //.
  rewrite ltnNge (leq_trans _ hwH) // -{1}[to_nat _]mul1n leq_mul2r.
  by rewrite [to_nat _]nhorizontalE //= subn_gt0.
by rewrite to_nat_lsr ltn_divLR ?expn_gt0 // -expnD addnC -mulSn.
Qed.

Lemma get_code_bound w b h :
  valid_pegs (w lor b) -> to_nat (get_code w b h) < 2 ^ (nwidth * nhorizontal).
Proof.
move=> wbV.
have Hv : to_nat (w lor get_border w b) < 
               2 ^ (nwidth * nhorizontal).
  apply: ltn_bit => // i whLi.
  rewrite lor_spec.
  suff -> :  bit (get_border w b) i = false.
    suff : bit (w lor b) i = false.
      by rewrite lor_spec; do 2 case: bit => //.
    by rewrite (negPf (valid_pegs_bit_false _ wbV _)).
  have [Bbi|//] := boolP (bit _ _).
  have : to_nat i %/ nhorizontal < nwidth.
    by apply: valid_pegs_get_border_width Bbi.
  by rewrite ltn_divLR // ltnNge ?whLi // nhorizontalE.
rewrite /get_code; case: ifP => _; last by exact: Hv.
rewrite /FourInARow.min; case: (_ ?= _).
- by exact: Hv.
- by apply: sym_code_bound Hv; rewrite ?expn_gt0.
by exact: Hv.
Qed.

Definition valid_eval w b s := down_score s <= eval w b <= up_score s.

Lemma valid_eval_unknown w b : valid_eval w b unknown.
Proof. by rewrite /valid_eval; case/or3P: (evalOr w b) => /eqP->. Qed.

Lemma valid_evalE w b s : 
  valid_eval w b s -> [\/ s = unknown, s = lossdraw | s = drawwin] \/ 
                        [\/ s = loss, s = draw | s = win].
Proof.
rewrite /valid_eval /up_score /down_score.
case: eqP => [->|_]; first by left; apply: Or31.
case: eqP => [->|_]; first by right; apply: Or31.
case: eqP => [->|_]; first by left; apply: Or32.
case: eqP => [->|_]; first by right; apply: Or32.
case: eqP => [->|_]; first by left; apply: Or33.
case: eqP => [->|_]; first by right; apply: Or33.
by case/andP => H /(leq_trans H).
Qed.

Lemma valid_eval0E w b s : 
  valid_eval w b s -> s land 1 == 0 -> 
  [\/ s = unknown, s = lossdraw | s = drawwin].
Proof.
rewrite /valid_eval /up_score /down_score.
case: eqP => [->/= _ _|_]; first by apply: Or31.
case: eqP => [->//=|_].
case: eqP => [->/= _ _|_]; first by apply: Or32.
case: eqP => [->//=|_].
case: eqP => [->/= _ _|_]; first by apply: Or33.
case: eqP => [->//=|_].
by case/andP => H /(leq_trans H).
Qed.

Lemma valid_eval1E w b s : 
  valid_eval w b s -> s land 1 != 0 -> 
  [\/ s = loss, s = draw | s = win].
Proof.
rewrite /valid_eval /up_score /down_score.
case: eqP => [->//=|_].
case: eqP => [->/= _ _|_]; first by apply: Or31.
case: eqP => [->//=|_].
case: eqP => [->/= _ _|_]; first by apply: Or32.
case: eqP => [->//=|_].
case: eqP => [->/= _ _|_]; first by apply: Or33.
by case/andP => H /(leq_trans H).
Qed.

Definition valid_entries 
         (wstate bstate : int) height
         (htable : array (array int)) := 
   let code := get_code wstate bstate height in
   let fkey := code mod hprime in
   let key := 2 * (fkey >> lhash) in
   let r :=  fkey land mhash in
   let lock := (code >> slocksize) in
   let ht := (htable.[r]) in
   let val1 := (ht.[key]) in
   let val2 := (ht.[key + 1]) in
   let s1 := (val2 >> scorelocksize) in 
   let s2 := (val2 >> locksize) land scoremask in
    (((val1 land lockmask) != lock) || valid_eval wstate bstate s1)%N && 
    (((val2 land lockmask) != lock) || valid_eval wstate bstate s2)%N.

Lemma valid_entries_prop w b h ht :
  valid_entries w b h ht -> valid_eval w b (hget w b h ht).
Proof.
rewrite /valid_entries /hget !neq_eqE.
case: eqP => _ /=; case: eqP => _ //=.
- by case/andP.
- by case/andP.
by move=> _; apply: valid_eval_unknown.
Qed.

Lemma valid_pegs_sym_code w b : 
  valid_pegs (w lor b) -> 
  valid_pegs (sym_code nwidth zero w lor sym_code nwidth zero b).
Proof.
move=> wbV; apply/andP; split.
  apply/forallP => i; apply/implyP; rewrite lor_spec => /orP[Hb|Hb].
    apply/nltbP; rewrite ltnNge; apply/negP => whLi.
    have sLwh : to_nat (sym_code nwidth zero w) < 2 ^ (nwidth * nhorizontal).
      apply: sym_code_bound => //; first by rewrite subnn.
      apply: ltn_bit => [|j whLj] //.
      suff: bit (w lor b) j = false by rewrite lor_spec; case: bit.
      by apply/idP/negP/(valid_pegs_bit_false wh_hyp).
    suff : bit (sym_code nwidth zero w) i = false by rewrite Hb.
    apply: bit_false_lt whLi _ => //.
    by rewrite to_nat_wh.
  apply/nltbP; rewrite ltnNge; apply/negP => whLi.
  have sLwh : to_nat (sym_code nwidth zero b) < 2 ^ (nwidth * nhorizontal).
    apply: sym_code_bound => //; first by rewrite subnn.
    apply: ltn_bit => // j whLj.
    suff: bit (w lor b) j = false by rewrite lor_spec; case: bit.
    by apply/idP/negP/(valid_pegs_bit_false wh_hyp).
  suff : bit (sym_code nwidth zero b) i = false by rewrite Hb.
  by apply: bit_false_lt whLi _  => //; rewrite to_nat_wh.
apply/forallP => i; apply/implyP => /nltbP iLw.
have iSE : to_nat (i + 1) = (to_nat i).+1.
  by rewrite to_nat_add ?addn1 // (leq_ltn_trans iLw nwidthLwB).
have wiSE : to_nat (width - (i + 1)) = (nwidth - (to_nat i).+1)%N.
  by rewrite to_nat_sub ?iSE // nwidthLwB.
suff -> : get_column (sym_code nwidth zero w lor sym_code nwidth zero b) i =
         get_column (w lor b) (width - (i + 1)).
    have /andP[_ /forallP/(_ (width - (i + 1)))/implyP] := wbV.
    apply; apply/nltbP.
    by rewrite wiSE ltn_subLR // addSn ltnS leq_addl.
apply: to_nat_inj.
have -> : width - (i + 1) = of_nat (to_nat (width - (i + 1))) by rewrite to_natK.
have {1}-> : i = of_nat (to_nat i) by rewrite to_natK.
rewrite [LHS]get_columnE // [RHS]get_columnE //; last first.
  by rewrite wiSE ltn_subLR // addSn ltnS leq_addl.
apply: eq_bigr => j _.
rewrite 2!cell_lor.
have /transposeP /(_ _ _ iLw (ltn_ord j)) -> := transpose_sym_code w.
have /transposeP /(_ _ _ iLw (ltn_ord j)) -> := transpose_sym_code b.
by rewrite wiSE.
Qed.

Lemma transpose_sget w1 w2 b1 b2 : 
  valid_pegs (w1 lor b1) -> valid_pegs (w2 lor b2) ->
  w1 land b1 = 0 -> w2 land b2 = 0 ->
  transpose (sget_code w1 b1) (sget_code w2 b2) ->
  transpose w1 w2 && transpose b1 b2.
move=> w1b1V w2b2V w1b1E0 w2b2E0 Hf.
pose w3 := sym_code nwidth zero w1.
pose b3 := sym_code nwidth zero b1.
have wbV3 : valid_pegs (w3 lor b3) by apply: valid_pegs_sym_code.
have Ha3 : w3 land b3 = 0.
  apply: bit_ext => k; rewrite bit_0.
  have [kLwh|whLk] := ltnP (to_nat k) (nwidth * nhorizontal); last first.
    suff : bit (w3 lor b3) k = false.
      by rewrite lor_spec land_spec; case: bit.
    by apply/idP/negP; apply: valid_pegs_bit_false whLk.
  rewrite (@bit_cell height) // cell_land.
  have khLw : to_nat k %/ nhorizontal < nwidth.
    by rewrite ltn_divLR // nhorizontalE.
  have khLh : to_nat k %% nhorizontal < nhorizontal. 
    by apply: ltn_pmod; rewrite nhorizontalE.
  have /transposeP->// := transpose_sym_code w1.
  have /transposeP->// := transpose_sym_code b1.
  by rewrite -cell_land w1b1E0 cell_0.
have Hf1 : transpose (sget_code w3 b3) (sget_code w1 b1).
  apply:transpose_lor; last by apply: transpose_sym_code.
  by apply: transpose_get_border => //; apply: transpose_sym_code.
suff Hw3b3w1b1 : sget_code w3 b3 = sget_code w2 b2.
  have [<- <-] : w3 = w2 /\ b3 = b2 by apply: sget_code_uniq.
  rewrite transpose_sym transpose_sym_code.
  by rewrite transpose_sym transpose_sym_code.
apply: bit_ext => k.
have [kLwh|whLk] := ltnP (to_nat k) (nwidth * nhorizontal); last first.
  have -> : bit (sget_code w2 b2) k = false.
    rewrite lor_spec.
    have -> : bit (get_border w2 b2) k = false.
      apply/idP => HH.
      have : to_nat k %/ nhorizontal < nwidth.
        by apply: valid_pegs_get_border_width w2b2V HH.
      rewrite ltn_divLR //; last by rewrite nhorizontalE.
      by rewrite ltnNge whLk.
    rewrite orFb.
    suff : bit (w2 lor b2) k = false by rewrite lor_spec; case: bit.
    by apply/idP/negP/(valid_pegs_bit_false wh_hyp).
  rewrite lor_spec.
  have -> : bit (get_border w3 b3) k = false.
    apply/idP => HH.
    have : to_nat k %/ nhorizontal < nwidth.
    apply: valid_pegs_get_border_width wbV3 _ => //.
    rewrite ltn_divLR //; last by rewrite nhorizontalE.
    by rewrite ltnNge whLk.
  rewrite orFb.
  suff : bit (w3 lor b3) k = false by rewrite lor_spec; case: bit.
  by apply/idP/negP/(valid_pegs_bit_false wh_hyp).
rewrite !(@bit_cell height).
have khLw : to_nat k %/ nhorizontal < nwidth.
  by rewrite ltn_divLR // nhorizontalE.
have khLh : to_nat k %% nhorizontal < nhorizontal.
 by apply: ltn_pmod; rewrite nhorizontalE.
have /transposeP->// := Hf1.
rewrite transpose_sym in Hf.
by have /transposeP->// := Hf.
Qed.

Lemma transpose_transpose_sget_code_eq w1 w2 b1 b2 a : 
  valid_pegs (w1 lor b1) ->  valid_pegs (w2 lor b2) ->
  w1 land b1 = 0 ->  b2 land w2 = 0 -> 
  transpose a (sget_code w1 b1) ->  transpose a (sget_code w2 b2) -> 
  sget_code w1 b1 = sget_code w2 b2.
Proof.
move=> w1b1V w2b2V Hw1ab1 Hw2ab2 Ht1 Ht2.
apply: bit_ext => k.
have [kLwh|whLk] := ltnP (to_nat k) (nwidth * nhorizontal); last first.
  rewrite lor_spec.
  have -> : bit (get_border w1 b1) k = false.
    apply/idP => HH.
    have : to_nat k %/ nhorizontal < nwidth.
    apply: valid_pegs_get_border_width w1b1V _ => //.
    rewrite ltn_divLR //; last by rewrite nhorizontalE.
    by rewrite ltnNge whLk.
  rewrite lor_spec.
  have -> : bit (get_border w2 b2) k = false.
    apply/idP => HH.
    have : to_nat k %/ nhorizontal < nwidth.
    apply: valid_pegs_get_border_width w2b2V _ => //.
    rewrite ltn_divLR //; last by rewrite nhorizontalE.
    by rewrite ltnNge whLk.
  have -> : bit w1 k = false.
    suff: bit (w1 lor b1) k = false by rewrite lor_spec; case: bit.
    by apply/idP/negP/(valid_pegs_bit_false wh_hyp).
  have -> : bit w2 k = false.
    suff: bit (w2 lor b2) k = false by rewrite lor_spec; case: bit.
    by apply/idP/negP/(valid_pegs_bit_false wh_hyp).
  by [].
rewrite !(@bit_cell height).
have khLw : to_nat k %/ nhorizontal < nwidth.
  by rewrite ltn_divLR // nhorizontalE.
have khLh : to_nat k %% nhorizontal < nhorizontal.
  by apply: ltn_pmod; rewrite nhorizontalE.
rewrite transpose_sym in Ht1.
rewrite transpose_sym in Ht2.
have /transposeP -> // := Ht1.
by have /transposeP -> // := Ht2.
Qed.

Lemma eval_get_code w1 w2 b1 b2 h1 h2 : 
  valid_pegs (w1 lor b1) -> valid_pegs (w2 lor b2) ->
  w1 land b1 = 0 -> w2 land b2 = 0 ->
  get_code w1 b1 h1 = get_code w2 b2 h2 -> 
  eval w1 b1 = eval w2 b2.
Proof.
move=> w1b1V w2b2V Hw1ab1 Hw2ab2.
have := get_code_correct w1 b1 h1.
have := get_code_correct w2 b2 h2.
move=> [-> [->|Ht1]|Ht1 [->|Ht2]].
- by move=> /sget_code_uniq [] // <- <-.
- move=> gcE; rewrite gcE in Ht1.
  apply/sym_equal.
  have /transpose_sget/andP[]// := Ht1.
  by apply: eval_transpose.
- move=> gcE; rewrite -gcE in Ht1.
  have /transpose_sget/andP[]// := Ht1.
  by apply: eval_transpose.
move=> HH.
have : sget_code w1 b1 = sget_code w2 b2.
  apply: transpose_transpose_sget_code_eq Ht1 => //; first by rewrite landC.
  by rewrite -HH.
by move=> /sget_code_uniq[] // -> ->.
Qed.

Lemma to_nat_hprimenS :
  to_nat (2 * (hprime / nhash + 1)) = (to_nat hprime %/ 2 ^ to_nat lhash).+1.*2.
Proof.
have Hc : to_nat (hprime / nhash + 1) = (to_nat hprime %/ 2 ^ to_nat lhash).+1.
  rewrite to_nat_add; last first.
    apply: ltn_trans (_ : (to_nat (hprime / nhash)).*2 < _).
      rewrite -addnn ltn_add2l.
      have : 1 <? hprime /nhash by [].
      by move/nltbP.
    rewrite nwB_pow -[ndigits]prednK; last by [].
    rewrite expnS mul2n ltn_double.
    have /nltbP : hprime / nhash <? lsl one (digits - 1) by [].
    rewrite to_nat_lsl_one; last first.
      by rewrite to_nat_sub // ndigitsLwB.
    by rewrite to_nat_sub ?ndigitsLwB.
  rewrite addn1 to_nat_div to_nat_lsl_one; last by [].
  by congr (_.+1).
rewrite to_nat_mul Hc; last first.
  rewrite nwB_pow  -[ndigits]prednK; last by [].
  rewrite expnS ltn_mul2l andTb.
  rewrite -[ndigits.-1]prednK; last by [].
  rewrite expnS mul2n.
  apply: ltn_trans (_ : (to_nat hprime %/ 2 ^ to_nat lhash).*2 < _).
    rewrite -addnn -[X in X < _]addn1 ltn_add2l.
    have /nltbP : 1 <? hprime / nhash by [].
    by rewrite to_nat_div /nhash to_nat_lsl_one.
  rewrite ltn_double.
  have /nltbP : hprime / nhash <? lsl one (digits - 2) by [].
  rewrite to_nat_div to_nat_lsl_one; last by [].
  rewrite to_nat_sub; last 2 first.
  - by [].
  - by apply: ndigitsLwB.
  by rewrite subn2.
by rewrite mul2n; congr (_.*2).
Qed.

Lemma to_nat_nhprimelh c :
    to_nat c < 2 ^ (nwidth * nhorizontal) ->
    to_nat (2 * lsr (c mod hprime) lhash) = 
    (to_nat (c mod hprime) %/ 2 ^ to_nat lhash).*2.
Proof.
move=> cLwh.
rewrite to_nat_mul to_nat_lsr mul2n // nwB_pow.
apply: ltn_trans (_ : 2 ^ (nwidth * nhorizontal) < _); last first.
  by rewrite ltn_exp2l // nhorizontalE.
have whE : (nwidth * nhorizontal = (nwidth * nhorizontal).-1.+1)%N.
  by rewrite prednK // nhorizontalE; case: nwidth w_hyp.
rewrite whE expnS mul2n ltn_double ltn_divLR //.
rewrite -expnD to_nat_mod.
apply: leq_ltn_trans (leq_mod _ _) _ => //.
rewrite (ltn_trans cLwh) // ltn_exp2l // [X in X < _]whE.
by rewrite -[_.-1.+1]addn1 ltn_add2l.
Qed.

Lemma to_nat_nhprimelhS c : 
    to_nat c < 2 ^ (nwidth * nhorizontal) ->
    to_nat (2 * (c mod hprime) >> lhash + 1) = 
    (to_nat (c mod hprime) %/ 2 ^ to_nat lhash).*2.+1.
Proof.
move=> cLwh.
rewrite to_nat_add; first by rewrite addn1 to_nat_nhprimelh.
rewrite addn1 to_nat_nhprimelh; last by [].
have [->|chNE0]:= (to_nat (c mod hprime)  %/ 2 ^ to_nat lhash =P 0)%N.
  by rewrite nwB_pow (@ltn_exp2l 2 0).
apply: leq_ltn_trans (leq_succ_double _ _) _.
  by case: (_ %/ _) chNE0.
rewrite nwB_pow -[ndigits]prednK; last by [].
rewrite expnS mul2n ltn_double.
rewrite -[ndigits.-1]prednK; last by [].
rewrite expnS mul2n ltn_double.
rewrite ltn_divLR; last by rewrite expn_gt0.
rewrite -expnD to_nat_mod.
apply: leq_ltn_trans (leq_mod _ _) _.
apply: leq_trans cLwh _.
by rewrite leq_exp2l // (leq_trans (ltnW wh_hyp)).
Qed.

Definition valid_htable ht :=
  [/\ 
  length ht = nhash,
  forall i : int, i <? nhash -> length ht.[i] = 2 * (hprime / nhash + 1) &
  forall w b h, valid_pegs (w lor b) -> w land b = 0 -> 
  valid_entries w b h ht].

Lemma valid_htable_make_hash (u : unit) : valid_htable (make_hash u).
Proof.
split.
- by rewrite make_hash_length1.
- by move=> i iLh; apply: make_hash_length2 u i iLh.
move=> w b hg wbV Ha.
rewrite /valid_entries.
set v1 := _.[_]; set v2 := _.[_].
suff -> : v2 = 0.
  by rewrite !lsr0 !land0 valid_eval_unknown !orbT.
rewrite /v2.
set x := _ land _.
set y := _ + 1.
apply: (@make_hash_get u x y).
  apply/nltbP.
  by rewrite to_nat_mhash [X in _ < X]to_nat_lsl_one ?ltn_pmod.
apply/nltbP.
rewrite to_nat_hprimenS to_nat_nhprimelhS; last by apply: get_code_bound.
by rewrite doubleS !ltnS leq_double leq_div2r // to_nat_mod ltnW // ltn_pmod.
Qed.

Lemma length1_hput w1 b1 wg1 s1 h1 ht1 :
  length (hput w1 b1 wg1 s1 h1 ht1) = length ht1.
Proof.
rewrite /hput; case: ifP => _.
  set xx1 := (X in _.[X <- _]).
  set yy1 := (X in _.[_ <- X]).
  by apply: (length_set _ ht1 xx1 yy1).
set xx1 := (X in _.[X <- _]).
set yy1 := (X in _.[_ <- X]).
by apply: (length_set _ ht1 xx1 yy1).
Qed.

Lemma length2_hput w1 b1 wg1 s1 h1 ht1 i :
  length ht1 = nhash ->
  (forall i j,  i <? nhash -> j <? nhash -> length ht1.[i] = length ht1.[j]) ->
  i <? nhash -> length (hput w1 b1 wg1 s1 h1 ht1).[i] = length ht1.[i].
Proof.
move=> Hh Hi iLn.
rewrite /hput; case: ifP => _.
  set xx1 := (X in _.[X <- _]).
  set yy1 := (X in _.[_ <- X]).
  case : (xx1 =P i) => [->|iDxx1]; last first.
    by rewrite [ht1.[_<-_].[_]]get_set_other.
  rewrite [ht1.[_<-_].[_]]get_set_same; last by rewrite Hh.
  rewrite /yy1.
  set ht2 := ht1.[_].
  set ht3 := ht2.[_ <- _].
  set xx2 := (X in ht3.[X <- _]).
  set yy2 := (X in ht3.[_ <- X]).
  rewrite (length_set _ ht3 xx2 yy2).
  rewrite /ht3.
  set xx3 := (X in ht2.[X <- _]).
  set yy3 := (X in ht2.[_ <- X]).
  rewrite (length_set _ ht2 xx3 yy3).
  rewrite /ht2; set v := _ land _.
  apply: (Hi v i) => //.
  apply/nltbP.
  rewrite [X in _ < X]to_nat_lsl_one; last by [].
  by rewrite to_nat_mhash ltn_pmod.
set xx1 := (X in _.[X <- _]).
set yy1 := (X in _.[_ <- X]).
case : (xx1 =P i) => [->|iDxx1]; last first.
  by rewrite [ht1.[_<-_].[_]]get_set_other.
rewrite [ht1.[_<-_].[_]]get_set_same; last by rewrite Hh.
rewrite /yy1.
set ht2 := ht1.[_].
set xx2 := (X in ht2.[X <- _]).
set yy2 := (X in ht2.[_ <- X]).
rewrite (length_set _ ht2 xx2 yy2).
rewrite /ht2; set v := _ land _.
apply: (Hi v) => //.
apply/nltbP.
rewrite [X in _ < X]to_nat_lsl_one; last by [].
by rewrite to_nat_mhash ltn_pmod.
Qed.

Lemma to_nat_slocksize : 
  (to_nat slocksize = nwidth * nhorizontal - to_nat locksize)%N.
Proof.
rewrite /slocksize; case: nltbP; rewrite to_nat_wh //; last first.
  by move/negP; rewrite -leqNgt -subn_eq0 => /eqP.
move=> lLnh; rewrite to_nat_sub  ?to_nat_wh //; first by apply: ltnW.
by apply: ltn_trans ndigitsLwB.
Qed.

Lemma leq_slocksize : to_nat slocksize <= nwidth * nhorizontal.
Proof. by rewrite to_nat_slocksize leq_subr. Qed.

Lemma to_nat_scorelocksize : 
  (to_nat scorelocksize = to_nat locksize + to_nat scoresize)%N.
Proof. by rewrite to_nat_add // (ltn_trans _ ndigitsLwB). Qed.

Lemma valid_has_table_hput w b wg s h ht :
  valid_pegs (w lor b) -> w land b = 0 ->
  valid_eval w b s ->
  valid_htable ht ->
  valid_htable (hput w b wg s h ht).
Proof.
move=> wbV wbA wbE [l1htE l2htE hV].
split; first by rewrite length1_hput.
  move=> i iLn; rewrite length2_hput //.
    by apply: l2htE.
  by move=> i1 j1 i1Ln j1Ln; rewrite l2htE // l2htE.
move=> w1 b1 h1 w1b1V w1b1A.
have gclmE : get_code w b h >> slocksize land lockmask = 
              get_code w b h >> slocksize.
  apply: bit_ext => i; rewrite land_spec bit_decr; last by [].
  rewrite bit_lsr.
  case: nlebP => iLsi; last by [].
  case: nltbP; first by rewrite andbT.
  move=> /negP; rewrite -leqNgt andbF => lLi.
  apply/sym_equal/(bit_false_lt _ _ _ _ (get_code_bound _ wbV)).
  rewrite to_nat_add_le. 
    by rewrite to_nat_slocksize addnC -leq_subLR leq_sub2l.
  apply/nlebP; rewrite add_comm to_nat_add_le; first by apply: leq_addl.
  by rewrite add_comm; apply/nlebP.
have sLs : to_nat s < 2 ^ nscoresize by apply: eval_score_bound wbE.
rewrite /valid_entries /hput /hget.
set c1 := get_code _ _ _ mod _; set c2 := get_code _ _ _ mod _.
have c1lE :
    to_nat (2 * c1 >> lhash) = (to_nat c1 %/ 2 ^ to_nat lhash).*2.
  by rewrite to_nat_nhprimelh; [|apply: get_code_bound].
have c2lE :
    to_nat (2 * c2 >> lhash) = (to_nat c2 %/ 2 ^ to_nat lhash).*2.
  by rewrite to_nat_nhprimelh; [|apply: get_code_bound].
have c1lSE :
    to_nat (2 * c1 >> lhash + 1) = (to_nat c1 %/ 2 ^ to_nat lhash).*2.+1.
  by apply: to_nat_nhprimelhS; apply: get_code_bound.
have c2lSE :
    to_nat (2 * c2 >> lhash + 1) = (to_nat c2 %/ 2 ^ to_nat lhash).*2.+1.
  by apply: to_nat_nhprimelhS; apply: get_code_bound.
have c1B : to_nat c1 < 2 ^ (nwidth * nhorizontal).
  rewrite to_nat_mod.
  apply: leq_ltn_trans (leq_mod _ _) _.
  by apply: get_code_bound.
have c2B : to_nat c2 < 2 ^ (nwidth * nhorizontal).
  rewrite to_nat_mod.
  apply: leq_ltn_trans (leq_mod _ _) _.
  by apply: get_code_bound.
have tclDtclDs c c' :
    to_nat c < 2 ^ (nwidth * nhorizontal) ->
    to_nat c' < 2 ^ (nwidth * nhorizontal) ->
    2 * (c mod hprime) >> lhash != 2 * (c' mod hprime) >> lhash + 1.
  move=> cB c'B; apply/eqP => H.
  suff : odd (to_nat (2 * (c' mod hprime) >> lhash + 1)).
    rewrite -H to_nat_nhprimelh; last by apply: cB.
    by rewrite odd_double.
  rewrite to_nat_nhprimelhS; last by apply: c'B.
  by rewrite oddS odd_double.
have tc1lDtc2lDs : 2 * c1 >> lhash != 2 * c2 >> lhash + 1.
  by apply: tclDtclDs; apply: get_code_bound.
have tc1lDtc1lDs : 2 * c1 >> lhash != 2 * c1 >> lhash + 1.
  by apply: tclDtclDs; apply: get_code_bound.
have tc2lDtc1lDs : 2 * c2 >> lhash != 2 * c1 >> lhash + 1.
  by apply: tclDtclDs; apply: get_code_bound.
have tc2lDtc2lDs : 2 * c2 >> lhash != 2 * c2 >> lhash + 1.
  by apply: tclDtclDs; apply: get_code_bound.
rewrite {tclDtclDs}.
have c2mLn : to_nat (c2 land mhash) < to_nat nhash.
  rewrite land_power2; last by [].
  by rewrite to_nat_mod ltn_pmod.
have evalE : (c1 land mhash = c2 land mhash) -> c1 >> lhash = c2 >> lhash ->
         get_code w b h >> slocksize = get_code w1 b1 h1 >> slocksize ->
         eval w1 b1 = eval w b.
  move=> c1mEc2m c1lEc2l gc1sEgc2l.
  suff : get_code w1 b1 h1 = get_code w b h 
    by apply: eval_get_code.
  apply: to_nat_inj.
  set x1 := to_nat (get_code w _ _).
  set x2 := to_nat (get_code w1 _ _).
  pose m1 := 2 ^ to_nat slocksize.
  have x1m1Ex2m1 : x1 %/ m1 = x2 %/ m1.
    have : to_nat (get_code w b h >> slocksize) = 
            to_nat (get_code w1 b1 h1 >> slocksize).
      by congr (to_nat _).
    by rewrite 2!to_nat_lsr.
  pose m2 := 2 ^ to_nat lhash.
  have x1hm2Ex2hm2 : (x1 %% to_nat hprime) %/ m2 = (x2 %% to_nat hprime) %/ m2.
    have : to_nat (c1 >> lhash) = to_nat (c2 >> lhash) by congr (to_nat _).
    rewrite 2!to_nat_lsr.
    by rewrite [to_nat c1]to_nat_mod [to_nat c2]to_nat_mod.
  have x1hm2mEx2hm2m : (x1 %% to_nat hprime) %% m2 = (x2 %% to_nat hprime) %% m2.
    have : to_nat (c1 land mhash) = to_nat (c2 land mhash) by congr (to_nat _).
    rewrite land_power2; last by [].
    rewrite land_power2; last by [].
    rewrite to_nat_mod [to_nat c1]to_nat_mod -/x1 to_nat_mod.
    by rewrite [to_nat c2]to_nat_mod -/x2 to_nat_lsl_one.
  have x1hEx2h : x1 = x2 %[mod to_nat hprime].
    rewrite (divn_eq (x1 %% to_nat hprime) m2).
    by rewrite x1hm2Ex2hm2 x1hm2mEx2hm2m -divn_eq.
  suff x1m1Ex2m1m : x1 = x2 %[mod m1].
    by rewrite (divn_eq x1 m1) x1m1Ex2m1 x1m1Ex2m1m -divn_eq.
  have m1Lhp :  m1 < to_nat hprime by [].
  rewrite (divn_eq x1 m1) (divn_eq x2 m1) x1m1Ex2m1 in x1hEx2h.
  move/eqP: x1hEx2h; rewrite eqn_modDl modn_small; last first.
    by apply: ltn_trans (ltn_pmod _ _) m1Lhp; rewrite expn_gt0.
  rewrite [_ %% _ %% _]modn_small; last first.
    by apply: ltn_trans (ltn_pmod _ _) m1Lhp; rewrite expn_gt0.
  by move=> /eqP.
set o := (_ =? _) || _.
have [oT|oF] := ifP o.
  have [cx1mEc2m|cx1mDc2m] := (c1 land mhash) =P (c2 land mhash); last first.
    rewrite [ht.[_ <- _].[_]]get_set_other; last by [].
    by have := hV w1 b1 h1 w1b1V w1b1A.
  rewrite cx1mEc2m.
  rewrite [ht.[_ <- _].[_]]get_set_same; last by rewrite l1htE; apply/nltbP.
  set u1 := ht.[_].[_ <- _].
  rewrite [u1.[_ <- _].[_]]get_set_other; last by apply/eqP; rewrite eq_sym.
  have [cx1lEc2l|/eqP cx1lDc2l] := c1 >> lhash =P c2 >> lhash; last first.
    have tc1lE : to_nat (2 * c1 >> lhash) = (to_nat (c1 >> lhash)).*2.
      by rewrite c1lE to_nat_lsr.
    have tc2lE : to_nat (2 * c2 >> lhash) = (to_nat (c2 >> lhash)).*2.
      by rewrite c2lE to_nat_lsr.
    have tc1lDtc2l : 2 * c1 >> lhash != 2 * c2 >> lhash.
      apply/eqP => HH; case/eqP: cx1lDc2l.
      apply/to_nat_inj/double_inj.
      rewrite -!mul2n -[2%N]/(to_nat 2) -to_nat_mul ?HH.
        by rewrite tc2lE mul2n.
      rewrite mul2n to_nat_lsr nwB_pow -[ndigits]prednK; last by [].
      rewrite expnS mul2n ltn_double ltn_divLR; last by [].
      rewrite -expnD to_nat_mod.
      apply: leq_ltn_trans (leq_mod _ _) _.
      apply: ltn_trans (get_code_bound _ wbV) _.
      by rewrite ltn_exp2l // (ltn_trans wh_hyp).
    have tc2lSDtc2lS : 2 * c1 >> lhash + 1 != 2 * c2 >> lhash + 1.
      by apply/eqP => HH; case/eqP: tc1lDtc2l; rewrite -[LHS](addK _ 1) HH addK.
    rewrite /u1 [_.[_ <- _].[2 * (lsr c2 lhash)]]get_set_other; last by apply/eqP.
    rewrite [_.[_ <- _].[_ + 1]]get_set_other; last by apply/eqP.
    rewrite [_.[_ <- _].[_ + 1]]get_set_other; last by apply/eqP.
    by have := hV w1 b1 h1 w1b1V w1b1A.
  rewrite /u1 cx1lEc2l.
  rewrite [_.[_<-_].[2 * c2 >> lhash]]get_set_same; last first.
    apply/nltbP; rewrite c2lE.
    rewrite l2htE; last by apply/nltbP/c2mLn.
    rewrite to_nat_hprimenS ltn_double ltnS.
    apply: leq_div2r.
    rewrite to_nat_mod; apply/ltnW/ltn_pmod.
    by have /nltbP: 0 <? hprime by [].
  rewrite [_.[_<-_].[2 * c2 >> lhash + 1]]get_set_same; last first.
    set v := _ land _; set v1 := _ * _; set v2 := _ lor _.
    rewrite (length_set _ ht.[v] v1 v2).
    rewrite l2htE; last by apply/nltbP.
    apply/nltbP; rewrite to_nat_hprimenS.
    rewrite c2lSE doubleS 2!ltnS leq_double.
    apply: leq_div2r.
    rewrite to_nat_mod; apply/ltnW/ltn_pmod.
    by have /nltbP: 0 <? hprime by [].
  set v := lsr _ scorelocksize; have -> : v = s.
    rewrite /v lsr_lor lsl_lsr_le; last 2 first.
    - apply: ltn_trans (_ : 2 ^  nscoresize * 2 ^ to_nat scorelocksize < _).
        by rewrite ltn_mul2r expn_gt0.
      by rewrite -expnD nwB_pow ltn_exp2l.
    - by apply/nlebP.
    have -> : scorelocksize - scorelocksize = 0 by ring.
    rewrite lsl0_r lsr_land_distr.
    by rewrite land0_r lor0_r. 
  rewrite land_lor_distrl lsl_land_decr; last by [].
  rewrite lor0 gclmE.
  rewrite land_lor_distrl /scorelocksize add_comm lsl_add_distl; last first.
    apply: ltn_trans (_ : 2 ^ 5 < _); first by [].
    by rewrite nwB_pow ltn_exp2l.
  apply/andP; split.
    case: eqP => [c1Ec2|//].
    rewrite orFb.
    rewrite /valid_eval.
    suff -> : eval w1 b1 = eval w b by [].
    by apply: evalE.
  rewrite lsl_land_decr; last by [].
  rewrite lor0 -landA.
  rewrite lsr_lor land_lor_distrl.
  rewrite lsl_lsr_le; last 2 first.
  - rewrite  to_nat_lslW modn_small.
      rewrite -mulnA -expnD nwB_pow.
      have -> : ndigits = ((ndigits - (to_nat scoresize + to_nat locksize)) +
                          (to_nat scoresize + to_nat locksize))%N by apply: refl_equal.
      rewrite [in X in _ < X]expnD ltn_mul2r expn_gt0 andTb.
      by apply: ltn_trans sLs _; rewrite ltn_exp2l.
    apply: ltn_trans (_ : 2 ^ nscoresize * 2 ^ to_nat scoresize < _).
      by rewrite ltn_mul2r expn_gt0.
    by rewrite -expnD nwB_pow ltn_exp2l.
  - by [].
  rewrite lsl0_r lsl_land_decr; last by [].
  rewrite lor0.
  have -> : scorelockmask land lockmask = lockmask by [].
  rewrite lsl_land_distr -landA.
  have -> : (scorelockmask >> locksize land scoremask) = scoremask.
    by apply: bit_ext => i; rewrite bit_decr.
  by have /andP[] := hV w1 b1 h1 w1b1V w1b1A.
have [cx1mEc2m|/eqP cx1mDc2m] := (c1 land mhash) =P (c2 land mhash); last first.
  rewrite [ht.[_ <- _].[_]]get_set_other; last by apply/eqP.
  by have := hV w1 b1 h1 w1b1V w1b1A.
rewrite cx1mEc2m.
rewrite [ht.[_ <- _].[_]]get_set_same; last by rewrite l1htE; apply/nltbP.
set u1 := ht.[_].[_ <- _].
have [cx1lEc2l|/eqP cx1lDc2l] := c1 >> lhash =P c2 >> lhash; last first.
  have tc1lE : to_nat (2 * c1 >> lhash) = (to_nat (c1 >> lhash)).*2.
    by rewrite c1lE to_nat_lsr.
  have tc2lE : to_nat (2 * c2 >> lhash) = (to_nat (c2 >> lhash)).*2.
    by rewrite c2lE to_nat_lsr.
  have tc1lDtc2l : 2 * c1 >> lhash != 2 * c2 >> lhash.
    apply/eqP => HH; case/eqP: cx1lDc2l.
    apply/to_nat_inj/double_inj.
    rewrite -!mul2n -[2%N]/(to_nat 2) -to_nat_mul ?HH.
      by rewrite tc2lE mul2n.
    rewrite mul2n to_nat_lsr nwB_pow -[ndigits]prednK; last by [].
    rewrite expnS mul2n ltn_double ltn_divLR; last by [].
    rewrite -expnD to_nat_mod.
    apply: leq_ltn_trans (leq_mod _ _) _.
    apply: ltn_trans (get_code_bound _ wbV) _.
    by rewrite ltn_exp2l // (ltn_trans wh_hyp).
  have tc1lDtc2lS : 2 * c1 >> lhash + 1 != 2 * c2 >> lhash  + 1.
    apply/eqP=> HH; case/eqP: tc1lDtc2l.
    by rewrite -(addK (2 * c1 >> lhash ) 1) HH addK.
  rewrite /u1 [_.[_ <- _].[2 * c2 >> lhash]]get_set_other; last first.
    by apply/eqP; rewrite eq_sym.
  rewrite [ht.[_].[_ <- _].[2 * c2 >> lhash + 1]]get_set_other; last first.
    by apply/eqP.
  by have := hV w1 b1 h1 w1b1V w1b1A.
rewrite /u1 cx1lEc2l.
rewrite [_.[_<-_].[2 * c2 >> lhash]]get_set_other; last first.
  by apply/eqP; rewrite eq_sym.
rewrite [_.[_<-_].[2 * c2 >> lhash + 1]]get_set_same; last first.
  apply/nltbP.
  rewrite c2lSE l2htE; last by apply/nltbP.
  rewrite to_nat_hprimenS.
  rewrite doubleS 2!ltnS leq_double.
  apply: leq_div2r.
  rewrite to_nat_mod; apply/ltnW/ltn_pmod.
  by have /nltbP: 0 <? hprime by [].
pose v1 := ht.[c2 land mhash].[2 * c2 >> lhash + 1] >> scorelocksize.
rewrite -/v1.
set v2 := (_ lor _ >> slocksize) >> scorelocksize.
have sskLwb : to_nat slocksize + to_nat scorelocksize < nwB.
  rewrite to_nat_slocksize to_nat_scorelocksize addnA.
  have [|lLwh] := leqP (nwidth * nhorizontal) (to_nat locksize).
    by rewrite -subn_eq0 => /eqP->; rewrite add0n (ltn_trans _ ndigitsLwB).
  rewrite subnK //; last by apply: ltnW.
  rewrite (leq_ltn_trans _ (_ : ndigits + to_nat scoresize < _)) //.
    by rewrite leq_add2r ltnW.
  apply: ltn_trans (_ : 2 ^ 10 < _); first by [].
  by rewrite nwB_pow ltn_exp2l.
have -> : v2 = v1.
  rewrite /v2 /v1 lsr_lor.
  have -> : (get_code w b h >> slocksize) >> scorelocksize = 0.
    rewrite lsr_add.
    have -> : scorelocksize ≤? slocksize + scorelocksize.
      by apply/nlebP; rewrite to_nat_add ?leq_addl.
    apply/to_nat_inj.
    rewrite to_nat_lsr; apply: divn_small.
    apply: ltn_trans (get_code_bound _ wbV) _.
    rewrite ltn_exp2l // to_nat_add //.
    rewrite to_nat_slocksize to_nat_scorelocksize.
    have [lLwh|whLl] := leqP (to_nat locksize) (nwidth * nhorizontal); last first.
      move/ltnW : (whLl); rewrite -subn_eq0 => /eqP->; rewrite add0n.
      by rewrite (leq_trans whLl).
    by rewrite addnA subnK // -addn1 leq_add2l.
  rewrite lor0_r lsl_lor lsr_lor.
  have -> : (lsl s locksize) >> scorelocksize = 0.
    rewrite lsl_lsr_ge; last by [].
      have -> : scorelocksize - locksize = scoresize by [].
      apply: to_nat_inj; rewrite to_nat_lsr.
      by apply: divn_small.
    apply: ltn_trans (_ : 2 ^ to_nat scoresize * 2 ^ to_nat locksize < _).
      by rewrite ltn_mul2r expn_gt0.
    by rewrite -expnD nwB_pow ltn_exp2l.
  rewrite lor0_r -lsl_add_distl; last first.
    apply: ltn_trans (_ : 2 ^ 6 < _); first by [].
    by rewrite nwB_pow ltn_exp2l.
  have <- : scorelocksize = scoresize + locksize by [].
  rewrite lsl_lsr_ge; last 2 first.
  - rewrite to_nat_lsr nwB_pow.
    rewrite -[ndigits](@subnK (to_nat scorelocksize)); last by [].
    rewrite [X in _ < X]expnD ltn_mul2r expn_gt0 ltn_divLR; last first.
      by apply: expn_gt0.
    rewrite -expnD subnK; last by [].
    by rewrite -nwB_pow; apply: to_nat_bounded.
  - by [].
  rewrite lsr_0_r.
  have -> : scorelocksize = locksize + scoresize by [].
  rewrite lsr_add_distl; last first.
    apply: ltn_trans (_ : 2 ^ 6 < _); first by [].
    by rewrite nwB_pow ltn_exp2l.
  by [].
rewrite {v2}/v1.
apply/andP; split.
  by case/andP: (hV w1 b1 h1 w1b1V w1b1A).
rewrite land_lor_distrl lsl_land_decr; last by [].
rewrite lor0 lsr_lor -lsr_add_distl; last first.
  apply: ltn_trans sskLwb.
  rewrite addnC ltn_add2l to_nat_scorelocksize.
  by rewrite -addn1 leq_add2l.
have -> : get_code w b h >> (slocksize + locksize) = 0.
  apply: to_nat_inj; rewrite to_nat_lsr.
  apply: divn_small.
  rewrite to_nat_add; last first.
    by apply: leq_ltn_trans sskLwb; rewrite leq_add2l.
  rewrite to_nat_slocksize.
  apply: leq_trans (get_code_bound _ _) _ => //.
  rewrite leq_exp2l //.
  have [lLwh|whLl] := leqP (to_nat locksize) (nwidth * nhorizontal); last first.
    by move/ltnW : (whLl); rewrite -subn_eq0 => /eqP->; rewrite add0n; apply/ltnW.
  by rewrite subnK.
rewrite lor0_r lsl_lsr_ge; last 2 first.
- rewrite nwB_pow.
  rewrite -[ndigits](@subnK (to_nat locksize)); last by [].
  rewrite [X in _ < X]expnD ltn_mul2r expn_gt0 andTb.
  apply: ltn_bit => [|i nlLi]; first by [].
  rewrite !(bit_lsr, bit_lsl, lor_spec).
  case: nltbP.
    move=> iLs; have F := leq_trans nlLi (ltnW iLs).
    rewrite leqNgt in F.
    by case/negP : F.
  rewrite orFb => /negP; rewrite -leqNgt => sLi.
  rewrite (bit_false_lt _ _ _ sLi); last by [].
  rewrite orbF.
  case: nlebP => [//|/negP].
  rewrite -ltnNge => iLd.
  case: nlebP => [isLsis|//].
  apply: (bit_false_lt _ ndigits _ ); last first.
     by rewrite -nwB_pow; apply: to_nat_bounded.
  rewrite add_comm to_nat_add_le; last by rewrite add_comm; apply/nlebP.
  rewrite to_nat_sub; last 2 first.
  - by [].
  - by apply: to_nat_bounded.
  rewrite -addnABC => [|//|//].
  have -> : (to_nat scorelocksize - to_nat scoresize = to_nat locksize)%N.
    by apply: refl_equal.
  by rewrite addnC -leq_subLR.
- by [].
rewrite gclmE.
rewrite lsr_0_r land_lor_distrl lsl_land_decr; last by [].
rewrite lor0.
have -> : s land scoremask = s.
  apply: bit_ext => i.
  rewrite land_spec bit_decr; last by [].
  case: nltbP; first by rewrite andbT.
  move=> /negP; rewrite andbF -leqNgt => sLi.
  by apply/sym_equal; apply: bit_false_lt sLi _.
case: eqP => gc1Egc2; last by [].
rewrite /valid_eval.
suff -> : eval w1 b1 = eval w b by [].
by apply: evalE.
Qed.

End Phash.
