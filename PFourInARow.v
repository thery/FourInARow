
From Stdlib Require Import ssreflect ZArith Ascii List String PrimInt63.
From Stdlib Require Import PArray.
From mathcomp Require Import ssrnat ssrbool div fintype eqtype seq.
From Stdlib Require Import Lia.
Require Import ssr_int.
Require Import FourInARow.

Import PrimInt63Notations.
Import Uint63Axioms.
Import Uint63.

Open Scope uint63_scope.

Lemma init_matrix_length1 (A : Type) n nn a (v : A) m : 
  nn <=? length a -> (Z.of_nat n <= φ nn)%Z ->  
  length (init_matrix n nn a v m) = length a.
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
       length (init_matrix n nn a v m).[i] = m
    else length (init_matrix n nn a v m).[i] = length (a.[i]).
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
      (init_matrix n nn a v m).[i].[j] = v
    else (init_matrix n nn a v m).[i].[j] = a.[i].[j].
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
   n <=? max_length -> length (make_matrix n m v) = n.
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
    i <? n -> length (make_matrix n m v).[i] = m.
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
have := init_matrix_length2 _ (to_nat n) n (make n (make 0 v)) 
               v m i mLl F1 F2 F3.
have iB := to_Z_bounded i.
rewrite iLn andbT ifT //.
by apply/lebP; rewrite add_spec of_Z_spec !Z.mod_small; try lia.
Qed.

Lemma make_matrix_get (A : Type) n m  (v : A) i j : 
    n <=? max_length -> m <=? max_length ->
    i <? n -> j <? m ->
    (make_matrix n m v).[i].[j] = v.
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
have := init_matrix_get _ (to_nat n) n (make n (make 0 v)) 
               v m i j mLl jLm F1 F2 F3.
have iB := to_Z_bounded i.
rewrite iLn andbT ifT //.
by apply/lebP; rewrite add_spec of_Z_spec !Z.mod_small; lia.
Qed.

Lemma bit_decr i j : j <? digits -> bit (decr (one << j)) i = (i <? j).
Proof.
case: ltbP => // => jLs.
have iB := to_Z_bounded i.
have jB := to_Z_bounded j.
have Fi : (1 <= 2 ^ to_Z i)%Z by apply: (Z.pow_le_mono_r _ 0); lia.
have Fn : (1 <= 2 ^ to_Z j)%Z by apply: (Z.pow_le_mono_r _ 0); lia. 
rewrite bitE.
have FE : IntDef.Z.of_nat size = φ (digits) by [].
rewrite  /decr sub_spec ?to_Z_1 Z.mod_small; last first.
  rewrite lsl_spec Z.mul_1_l Z.mod_small; split; try lia.
    suff : (2 ^ φ (j) <= wB)%Z by lia.
    by apply: Z.pow_le_mono_r; rewrite ?FE; lia.
  by apply: Z.pow_lt_mono_r; rewrite ?FE; lia.
rewrite lsl_spec Z.mod_small Z.mul_1_l; last first.
  split; try lia.
  by apply: Z.pow_lt_mono_r; rewrite ?FE; lia.
rewrite Z.testbit_eqb; last by lia.
case: ltbP => [iLn|/Z.nlt_ge nLi]; last first.
  rewrite Z.div_small //; split; try lia.
  suff: (2 ^ to_Z j <= 2 ^ to_Z i)%Z by lia.
  by apply: Z.pow_le_mono_r; rewrite ?FE; lia.
have -> : (2 ^ φ j - 1 = 
           (2 ^ (φ j - φ i) - 1) * 2 ^ φ i + (2 ^ (φ i) - 1))%Z.
  rewrite Z.mul_add_distr_r.
  rewrite -Zpower_exp; try lia.
  have -> : (φ j - φ (i) + φ (i)  = φ j)%Z by lia.
  lia.
rewrite Z.div_add_l; try lia.
rewrite Z.div_small ?Z.add_0_r; try lia.
rewrite Zminus_mod.
have -> : (φ j - φ (i) = (1 + (φ j - φ (i) -1)))%Z by lia.
rewrite Zpower_exp; try lia.
by rewrite Z.mul_mod.
Qed.

Lemma all_set_spec i : bit all_set i = (i <? number_of_cells).
Proof. by apply: bit_decr. Qed.

Lemma first_colum_spec i : bit first_column i = (i <? height).
Proof. by apply: bit_decr. Qed.

Lemma full_first_colum_spec i : bit full_first_column i = (i <? horizontal).
Proof. by apply: bit_decr. Qed.

Lemma bottom_spec i : 
  bit bottom i = ((i mod horizontal =? 0) && (i <? width * horizontal)).
Proof.
have F1 : (1 < 2 ^ φ (horizontal))%Z by apply: (Z.pow_lt_mono_r _ 0).
have F2 : (1 < 2 ^ φ (number_of_cells))%Z by apply: (Z.pow_lt_mono_r _ 0).
have F3 : (2 ^ φ (horizontal) < wB)%Z by apply: Z.pow_lt_mono_r.
have F4 : (2 ^ φ (number_of_cells) < wB)%Z by apply: Z.pow_lt_mono_r.
have F5 := to_Z_bounded i.
have F6 : (0 <= φ (horizontal))%Z by compute.
have F7 : (2 <= 2 ^ φ (horizontal))%Z by compute.
have F8 : (0 <= φ (width))%Z by compute.
have F9 k l : 
  (1 <= l -> 0 <= k -> 
    (2 ^ ((1 + k) * l) - 1) / (2 ^ l - 1)  =
       (2 ^ (k * l) + (2 ^ (k * l) - 1) / (2 ^ l - 1)))%Z.
  move=> lP kP.
  have l2P : (2 <= 2 ^ l)%Z by apply: (Z.pow_le_mono_r 2 1); lia.
  replace (2 ^ ((1 + k) * l) - 1)%Z with
    (2 ^ (k * l) * (2 ^ l - 1) + (2 ^ (k * l) - 1))%Z; last first.
    by rewrite Z.mul_add_distr_r Z.mul_1_l Zpower_exp; lia.
  by rewrite Z_div_plus_full_l //; lia.
have F10 k l : 
  (1 <= l -> 0 <= k -> 
    (2 ^ (k * l) - 1) / (2 ^ l - 1) < 2 ^ (k * l))%Z.
  move=> lP.
  have l2P : (2 <= 2 ^ l)%Z by apply: (Z.pow_le_mono_r 2 1); lia.
  move: k.
  apply: natlike_ind; first by compute.
  move=> k kP IH.
  rewrite -Z.add_1_l F9 //.
  rewrite Z.mul_add_distr_r Z.mul_1_l Zpower_exp; try lia.
  suff : (2 ^ (k * l) * 2 <= 2 ^ (k * l) * 2 ^ l)%Z by lia.
  by apply: Zmult_le_compat_l; lia.
rewrite bitE.
rewrite div_spec !sub_spec to_Z_1 !lsl_spec !Z.mul_1_l !Z.mod_small; 
  try split; try lia.
rewrite Z.testbit_eqb; try lia.
rewrite mul_spec [((_ * _) mod _)%Z]Z.mod_small; last by compute.
case: ltbP => [iLw|/Z.nlt_ge wLi]; last first.
  rewrite mul_spec [((_ * _) mod _)%Z]Z.mod_small in wLi; last by compute.
  rewrite andbF Z.div_small; first by [].
  split; first by compute.
  apply: Z.lt_le_trans; last by apply: Z.pow_le_mono_r wLi.
  by apply: F10.
rewrite andbT.
rewrite mul_spec Z.mod_small in iLw; last by split; try lia; compute.
have -> : (i mod horizontal =? 0) = ((to_Z i mod (to_Z horizontal)) =? 0)%Z.
  case: Uint63.eqbP.
    by rewrite mod_spec => ->.
  by rewrite mod_spec; case: (_ mod _)%Z.
rewrite {1}(Z.div_mod (to_Z i) (to_Z horizontal)); try lia.
rewrite Zpower_exp; last 2 first.
- apply: Z.le_ge.
  apply: Z.mul_nonneg_nonneg; try lia.
  by apply: Z.div_pos; lia.
- apply: Z.le_ge.
  by have := (Z_mod_lt (to_Z i) (to_Z horizontal)); try lia.
rewrite -Z.div_div; last 2 first.
- suff : (0 < 2 ^ (φ (horizontal) * (φ (i) / φ (horizontal))))%Z by lia.
  apply: Z.pow_pos_nonneg; try lia.
  apply: Z.mul_nonneg_nonneg; try lia.
  by apply: Z.div_pos; lia.
- apply: Z.pow_pos_nonneg; try lia.
  by have := (Z_mod_lt (to_Z i) (to_Z horizontal)); try lia.
set q := (_ / to_Z _)%Z; set m := (_ mod to_Z _)%Z.
have qP : (0 <= q)%Z by apply: Z_div_pos; lia.
have mP : (0 <= m < to_Z horizontal)%Z by  apply: Z.mod_bound_pos; lia.
have m2P : (1 <= 2 ^ m)%Z by apply: (Z.pow_le_mono_r 2 0); lia.
have wL : (q < to_Z width)%Z by apply: Z.div_lt_upper_bound; lia.
replace (to_Z width) with ((to_Z width - q - 1) + 1 + q)%Z by lia.
have : (0 <=  φ (width) - q - 1)%Z by lia.
elim/natlike_ind : (_ - _)%Z; last by lia.
  set u := φ (horizontal).
  rewrite Z.add_0_l F9 //.
  have uqP : (1 <= 2 ^ (u * q))%Z by apply: (Z.pow_le_mono_r 2 0); lia.
  replace (q * u)%Z with (u * q)%Z by lia.
  rewrite -{1}[(2  ^ (u * q))%Z]Z.mul_1_l Z.div_add_l; last by lia.
  rewrite [(_ / 2 ^ (_ * _))%Z]Z.div_small.
    case: (Z.eqb_spec m 0) => [->|mPP].
      by compute.
    have l2P : (2 <= 2 ^ m)%Z by apply: (Z.pow_le_mono_r 2 1); lia.
    by rewrite Z.div_small //; lia.
  split.
    apply: Z.div_pos; try lia.
    have uP : (1 <= u)%Z by compute.
    suff : (2 <= 2 ^ u)%Z by lia.
    by apply: (Z.pow_le_mono_r 2 1); lia.
  replace (u * q)%Z with (q * u)%Z by lia.
  by apply: F10; lia.
move=> k kP IH _.
have HH : (1 <= 2 ^ (φ (horizontal) * q))%Z 
  by apply: (Z.pow_le_mono_r 2 0); try lia.
replace (Z.succ k + 1 + q)%Z with (1 + (k + 1 + q))%Z by lia.
rewrite F9; try lia.
rewrite {1}Z.mul_add_distr_r; try lia.
rewrite Zpower_exp; try lia.
replace (q * φ (horizontal))%Z with (φ (horizontal) * q)%Z by lia.
rewrite Z.div_add_l; try lia.
replace ((k + 1) * φ (horizontal))%Z with 
          ((k * φ (horizontal)) + (φ (horizontal) - m) + m)%Z by lia.
rewrite Zpower_exp; try lia.
rewrite Z.div_add_l; try lia.
rewrite Z.add_mod; try lia.
suff : (2 | 2 ^ (k * φ (horizontal) + (φ (horizontal) - m)))%Z.
  rewrite -Z.mod_divide; try lia.
  move=>->.
  by rewrite Z.add_0_l Z.mod_mod; lia.
exists (2 ^ (k * φ (horizontal) + (φ (horizontal) - m) - 1))%Z.
rewrite -(Zpower_exp _ _ 1); try lia.
congr (2 ^ _)%Z.
lia.
Qed.

Lemma top_spec i : 
  bit top i = ((i mod horizontal =? height) && (i <? width * horizontal)).
Proof.
have iP := to_Z_bounded i.
rewrite bit_lsl bottom_spec.
case: lebP=> //.
  rewrite orbT.
  move=> H1; case: ltbP => //.
    have : (to_Z  (width * horizontal) < φ (digits))%Z by compute.
    by lia.
  by rewrite andbF.
have H1 : (to_Z height < to_Z horizontal)%Z by compute.  
rewrite orbF => /Z.nle_gt H2.
case: ltbP=> //.
  move=> H3; case: Uint63.eqbP => //.
  by rewrite mod_spec Z.mod_small; lia.
move/Z.nlt_ge => H4.
have hP : (0 <= to_Z height)%Z by compute.
case: eqbP  => //; 
    rewrite mod_spec to_Z_0 sub_spec (Z.mod_small _ wB); try lia; last first.
  case: Uint63.eqbP => //.
  rewrite mod_spec.
  rewrite Zminus_mod => ->.
  rewrite Zminus_mod Zmod_mod -Zminus_mod.
  by rewrite Z.sub_diag Z.mod_0_l; lia.
move=> H5.
case: eqbP  => //; last first.
  case.
  rewrite mod_spec; try by lia.
  replace (to_Z i) with ((to_Z i - to_Z height) + to_Z height)%Z by lia.
  rewrite Z.add_mod; try lia.
  rewrite H5 Z.add_0_l Z.mod_mod; try lia.
  by rewrite Z.mod_small; lia.
do 2 case: ltbP; try lia; last first.
  by rewrite sub_spec Z.mod_small; lia.
rewrite mul_spec [((_ * _) mod _)%Z]Z.mod_small; last by compute.
move=> /Z.nlt_ge => H6.
rewrite sub_spec Z.mod_small; try lia.
move=> H7.
    rewrite mod_spec.
replace (φ  i) with (φ (width) * φ (horizontal) +
                        (φ i - (φ (width) * φ (horizontal))))%Z by lia.
rewrite Z.add_mod; try lia.
rewrite Z.mul_mod; try lia.
rewrite Z.mod_same; try lia.
rewrite Z.mod_0_l; try lia.
rewrite Z.add_0_l Z.mod_mod; try lia.
by rewrite Z.mod_small; lia.
Qed.

Lemma bit_mhash i : bit mhash i = (i <? lhash).
Proof. by apply: bit_decr. Qed.

Lemma make_hash_length1 (u : unit) : length (make_hash u) = nhash.
Proof. by apply: make_matrix_length1. Qed.

Lemma make_hash_length2 (u : unit) i : 
   i <? nhash -> length (make_hash u).[i] = (2 * (hprime/nhash) + 1).
Proof. by move=> iLn; apply: make_matrix_length2. Qed.

Lemma make_hash_get (u : unit) i j : 
    i <? nhash -> j <? 2 * (hprime/nhash) + 1 ->
    (make_hash u).[i].[j] = 0.
Proof. by move=> nLi mLj; apply: make_matrix_get. Qed.

Lemma bit_logand2_aux s dir i : 
  dir <=? digits ->
  bit (s land s >> dir land (s land s >> dir) >> (2 * dir)) i =
                   [&&
                       bit s i, bit s (i + dir),
                       bit s (i + 2 * dir) & bit s (i + 3 * dir)].
Proof.
case: lebP => // dirP1 _.
have iP := to_Z_bounded i.
have dirP := to_Z_bounded dir.
have dir2P := to_Z_bounded (2 * dir).
have dir3P := to_Z_bounded (3 * dir).
have Fp : (φ (digits) < wB)%Z.
  by rewrite /wB /= /IntDef.Z.pow_pos /= /digits /to_Z /=; lia.
have F2p : (2 * φ (digits) < wB)%Z.
  by rewrite /wB /= /IntDef.Z.pow_pos /= /digits /to_Z /=; lia.
rewrite !(land_spec, bit_lsr).
case: (Z.ltb_spec (φ (i)) (φ (digits))) => Hphi; last first.
  by rewrite bit_M => //; case: lebP; lia.
case: bit => //=. 
(case: lebP; rewrite add_spec) => [_|]; last first.
  by rewrite Z.mod_small; try lia.
rewrite add_comm.
case: (Z.ltb_spec (φ (i) + φ (dir)) (φ (digits))) => Hphi1; last first.
  rewrite bit_M => //; case: lebP; try lia.
  rewrite add_spec Z.mod_small; try lia.
case: bit => //=.
rewrite add_comm. 
case: (Z.ltb_spec (φ (i) + 2 * φ (dir)) (φ (digits))) => Hphi2; last first.
  rewrite bit_M => //; case: lebP; try lia.
  rewrite add_spec Z.mod_small; try lia.
    by rewrite mul_spec -[to_Z 2]/2%Z Z.mod_small; lia.
  by rewrite mul_spec -[to_Z 2]/2%Z Z.mod_small; lia.
case: lebP;  rewrite !(add_spec, mul_spec) -[to_Z 2]/2%Z !Z.mod_small; try lia.
move=> HF.
case bit => //=.
have -> : dir + (i + 2 * dir) = i + 3 * dir.
  apply: to_Z_inj.
  by rewrite !(add_spec, mul_spec) -[to_Z 2]/2%Z -[to_Z 3]/3%Z !Z.mod_small; lia.
case: (Z.ltb_spec (φ (i) + 3 * φ (dir)) (φ (digits))) => Hphi3; last first.
  rewrite bit_M => //; case: lebP; try lia.
  by rewrite !(add_spec, mul_spec) -[to_Z 3]/3%Z !Z.mod_small; lia.
case: lebP => //.
by rewrite !(add_spec, mul_spec) -[to_Z 2]/2%Z -[to_Z 3]/3%Z !Z.mod_small; lia.
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
case: existsP => /= [[i /and4P[H1 H2 H3 H4]]|Hh].
  apply/sym_equal/existsP.
  exists i; apply/existsP; exists horizontal.
  by rewrite inE eqxx H1 H2 H3 H4.
case: existsP => /= [[i /and4P[H1 H2 H3 H4]]|Hv].
  apply/sym_equal/existsP.
  exists i; apply/existsP; exists vertical.
  by rewrite !inE eqxx andTb H1 H2 H3 H4.
case: existsP => /= [[i /and4P[H1 H2 H3 H4]]|Hur].
  apply/sym_equal/existsP.
  exists i; apply/existsP; exists up_right.
  by rewrite !inE eqxx andTb H1 H2 H3 H4.
case: existsP => /= [[i /and4P[H1 H2 H3 H4]]|Hul].
  apply/sym_equal/existsP.
  exists i; apply/existsP; exists up_left.
  by rewrite !inE eqxx andTb H1 H2 H3 H4.
apply/sym_equal/idP => /existsP [i /existsP [dir /and5P[]]].
rewrite !inE; case/or4P => /eqP-> H1 H2 H3 H4.
- by case: Hh; exists i; rewrite H1 H2 H3 H4.
- by case: Hv; exists i; rewrite H1 H2 H3 H4.
- by case: Hul; exists i; rewrite H1 H2 H3 H4.
by case: Hur; exists i; rewrite H1 H2 H3 H4.
Qed.

Definition get_column (state : int) (i : int) :=
  let state1 := if i =? 0 then state else
     (state >> ((i - 1) * horizontal)) in
  state1 land full_first_column.

Lemma eqb_eqb (i j : int) : (i =? j) = (i == j).
Proof.
case: (_ =P _) => [->|]; case: eqbP; try lia.
by move=> iEj []; apply: to_Z_inj.
Qed.

Lemma mul_0_l i : 0 * i = 0.
Proof.
apply: to_Z_inj.
by rewrite mul_spec Z.mul_0_l Z.mod_0_l.
Qed.

Lemma mul_1_l i : 1 * i = i.
Proof.
apply: to_Z_inj.
rewrite mul_spec Z.mul_1_l Z.mod_small //; apply: to_Z_bounded.
Qed.

Lemma add_0_l i : 0 + i = i.
Proof.
apply: to_Z_inj.
by rewrite add_spec Z.add_0_l Z.mod_small //; apply: to_Z_bounded.
Qed.

Lemma bit_get_colum s i j : 
  i <=? width -> j <=? height ->
  bit (get_column s i) j = bit s ((i != 0) * (i - 1) * horizontal + j).
Proof.
have iB := to_Z_bounded i.
have jB := to_Z_bounded j.
case: lebP => // iLw.
case: lebP => // jLh _ _.
have hEh : φ (horizontal) = (φ (height) + 1)%Z by [].
rewrite /get_column eqb_eqb.
case: (_ =P 0) => [_ | /eqP iD0].
  rewrite mul_0_l add_0_l land_spec full_first_colum_spec andbC.
  by case: (ltbP j) => //; lia.
have iP : (0 < φ (i))%Z.
  rewrite -eqb_eqb in iD0; case: eqbP iD0 => //.
  by rewrite -[to_Z 0]/0%Z; lia.
rewrite land_spec full_first_colum_spec andbC mul_1_l.
case: (ltbP j) => [_|]; last by lia.
rewrite andTb bit_lsr; case: lebP => //; try lia.
rewrite !(sub_spec, add_spec, mul_spec) -[to_Z 1]/1%Z.
rewrite [((_ - _) mod wB)%Z]Z.mod_small; last by lia.
rewrite [((_ * _) mod wB)%Z]Z.mod_small; last first.
  split; try nia.
  suff : (φ (width) * φ (horizontal) < wB)%Z by nia.
  by [].
rewrite Z.mod_small; first by nia.
suff : (φ (width) * φ (horizontal) < wB)%Z by nia.
by [].
Qed.

(** (one)^*(zero)^+ *)
Definition opzs (i : int) :=
  [exists j : int, (j <? digits) && [forall k : int,  bit i k == (k <? j)]].

Lemma opzsE i : opzs i = [exists j, (j <? digits) && (i == decr (one << j))].
Proof.
apply/existsP/existsP => [[k /andP[kLd /forallP Hb]]|[k /andP[kLd /eqP iEd]]].
  exists k; rewrite kLd.
  apply/eqP/bit_ext => j.
  by rewrite bit_decr; have := eqP (Hb j).
exists k; rewrite kLd; apply/forallP => j.
by rewrite iEd bit_decr.
Qed.

Lemma is_zero_0 : is_zero 0.
Proof. by apply/is_zero_spec. Qed.

Lemma bit_le i j : (i <? (one << j)) -> bit i j = false.
Proof.
have iB := to_Z_bounded i.
case: ltbP => //.
rewrite lsl_spec Z.mul_1_l.
case: (Z.le_decidable (φ (digits)) (φ (j))) => jLd; last first.
  rewrite Z.mod_small; last first.
    split; try lia.
    apply: Z.pow_lt_mono_r; try lia.
    by rewrite -[IntDef.Z.of_nat size]/(φ (digits)); lia.
  move=> iLj; rewrite /bit.
  suff -> : (i >> j) = 0 by rewrite lsl0 is_zero_0.
  by apply: to_Z_inj; rewrite lsr_spec to_Z_0 Z.div_small; lia.
rewrite Znumtheory.Zdivide_mod; try lia.
exists (2 ^ (φ (j) -  φ (digits)))%Z.
rewrite -Z.pow_add_r; try lia.
rewrite -[IntDef.Z.of_nat size]/(φ (digits)).
by congr (_ ^ _)%Z; lia.
Qed.

Lemma land_power2 i k :
  k <? digits -> i land (decr (one << k)) = i mod (one << k).
Proof.
have iB := to_Z_bounded i.
have kB := to_Z_bounded k.
case: ltbP => // kLd _.
apply: bit_ext => j.
have jB := to_Z_bounded j.
rewrite land_spec bit_decr; last by case: ltbP.
case: ltbP => [jLk|kLj]; rewrite ?(andbT, andbF); last first.
  have kLj' : (φ (k) <= φ (j))%Z by lia.
  case: (Z.le_decidable (φ (digits)) (φ (j))) => jLd.
    by rewrite bit_M //; apply/lebP.
  apply/sym_equal/bit_le.
  apply/ltbP.
  rewrite mod_spec !lsl_spec !Z.mul_1_l.
  rewrite !(Z.mod_small _ wB); last first.
  - split; try lia.
    apply: Z.pow_lt_mono_r; try lia.
    by rewrite -[IntDef.Z.of_nat size]/(φ (digits)); lia.
  - split; try lia.
    apply: Z.pow_lt_mono_r; try lia.
    by rewrite -[IntDef.Z.of_nat size]/(φ (digits)); lia.
  apply: Z.lt_le_trans (_ : (_ < 2 ^ φ (k))%Z) _.
    by have := Z.mod_pos_bound (φ (i)) (2 ^ (φ (k))); lia.
  by apply: Z.pow_le_mono_r; lia.
rewrite /bit.
congr (~~ is_zero _).
apply: to_Z_inj.
rewrite !(lsr_spec, lsl_spec, mod_spec) ?Z.mul_1_l.
rewrite !(Z.mod_small (2 ^ φ (k)) wB); last first.
  split; try lia.
  apply: Z.pow_lt_mono_r; try lia.
  by rewrite -[IntDef.Z.of_nat size]/(φ (digits)); lia.
rewrite {1}(Z_div_mod_eq_full (φ (i)) (2 ^ φ (k))).
have {1}-> : φ (k) = (φ (j) + ((φ (k) - φ (j) - 1) + 1))%Z by lia.
rewrite Z.pow_add_r; try lia.
rewrite -[((2 ^ φ (j) * _) * _)%Z]Z.mul_assoc [(2 ^ φ (j) * _)%Z]Z.mul_comm.
rewrite Z.div_add_l; try lia.
rewrite Z.mul_add_distr_r.
rewrite -Zplus_mod_idemp_l.
set u := ((_ * _ ) mod wB)%Z.
suff -> : u = 0%Z by rewrite Z.add_0_l; lia.
rewrite /u Z.pow_add_r; try lia.
set v := (2 ^ (_ - _))%Z; set w := (_ / _)%Z; set t := (2 ^ (to_Z (_ - _)))%Z.
have -> : (v * 2 ^ 1 * w * t = v * w * (2 ^ 1 * t))%Z by lia.
suff -> : (2 ^ 1 * t = wB)%Z by rewrite Z_mod_mult.
rewrite -Z.pow_add_r; try lia.
  by congr (2 ^ _)%Z.
rewrite /to_Z /=; lia.
Qed.

Definition get_border (wstate bstate : int) :=
  bottom + (wstate lor bstate).

(* Perform a move *)
Definition  make_move move state := move lor state.

(* Get the log 2 of a number *)
Definition get_log2 (v : int) : int :=
   62 - head0 v.

(* List of possible moves, no move = draw *)
Inductive moves := EmptyMove | Move (m : int) (v : int) (l : moves).

(* Moves are ordered by their values *)
Fixpoint insert_fmove m (v : int) l := 
match l with 
| EmptyMove => Move m v EmptyMove
| Move m1 v1 l1 => 
  match v ?= v1 with
  |Lt => Move m1 v1 (insert_fmove m v l1)
  | _ => Move m v l
  end
end.

Inductive fmove := 
 | Win
 | Draw
 | Forced (_ : int)
 | Moves (_: moves).

Definition make_moves l :=
  match l with EmptyMove => Draw | _ => Moves l end.

Section FindMoves.

Variables (wstate bstate border: int).

Fixpoint make_colums i column :=
  match i with
      O => nil 
  | S i => column :: (make_colums i (column << horizontal))
  end.

Definition columns := Eval compute in make_colums nwidth first_column.

(* Check for a direct win after a threat *)
Fixpoint fmt columns res :=
  match columns with 
  | nil => res
  | column :: columns =>
      let move := border land column in
      if is_zero move then fmt columns res
      else
      if is_won (make_move move wstate) then Win
      else fmt columns res
  end.

Fixpoint fms columns res :=
  match columns with 
  | nil => make_moves res
  | column :: columns =>
      let move := border land column in
      if is_zero move then fms columns res
      else
      if is_won (make_move move wstate) then Win
      else
      if is_won (make_move move bstate) then 
        fmt columns (Forced move)
      else
        let v := (values.[get_log2 move]) in
        fms columns (insert_fmove move v res)
   end.

Lemma fmsE columns res :
fms columns res =
  match columns with 
  | nil => make_moves res
  | column :: columns =>
      let move := border land column in
      if is_zero move then fms columns res
      else
      if is_won (make_move move wstate) then Win
      else
      if is_won (make_move move bstate) then 
        fmt columns (Forced move)
      else
        let v := (values.[get_log2 move]) in
        fms columns (insert_fmove move v res)
   end.
Proof.
by case: columns.
Qed.

End FindMoves.

(* Find possible moves *)
Definition find_moves wstate bstate :=
  let border := get_border wstate bstate in
  fms wstate bstate border columns EmptyMove.

(* Auxillary parsing function from string to states *)
Fixpoint parsei s i j wstate bstate (turn : bool) :=
  match
    match width ?= j with 
    |Eq => 
       match i ?= 0 with Eq => None | _ => Some (i-1,0) end
    | _ => Some (i,j) end
  with None => (wstate,bstate,turn)
  | Some (i,j) =>
    match s with
    | EmptyString => (wstate,bstate,turn)
    | String "X"%char s1 =>
       let move := one << (j * horizontal + i) in 
       parsei s1 i (j + 1) (make_move wstate move) bstate (negb turn)
    | String "O"%char s1 =>
       let move := one << (j * horizontal + i) in 
       parsei s1 i (j + 1) wstate (make_move bstate move) (negb turn)
    | String "_"%char s1 => 
       parsei s1 i (j + 1) wstate bstate turn
    | String _ s1 => parsei s1 i j wstate bstate turn
    end
  end.

(* Parsing function from string to states *)
Definition parse_string s :=
  parsei s height width zero zero true.

(* Newline String *)
Definition nl := String "013" EmptyString.

(* Auxillary function that turns states into into a string *)
Fixpoint to_stringi m i j wstate bstate :=
  match m with O => ""%string | (S m1) => 
  match
    match width ?= j with 
    |Eq => 
       match i ?= 0 with Eq => None | _ => Some (i-1,0,nl) end
    | _ => Some (i,j,""%string) end
  with
  | None => nl
  | Some (i,j,ts) =>
    (ts ++
   (let move := one << (j * horizontal + i) in 
    if is_nzero (move land wstate) then "X"%string ++ (to_stringi m1 i (j + 1) wstate bstate) 
    else if is_nzero (move land bstate) then "O"%string ++ (to_stringi m1 i (j + 1) wstate bstate) 
    else "_"%string ++ (to_stringi m1 i (j + 1) wstate bstate)))%string
  end
  end.

(* Turn states into a string *)
Definition to_string wstate bstate :=
 (to_stringi (nheight * nwidth) height width wstate bstate)%string.

(* Turn the score in a string *)
Definition string_of_score (score : int) :=
  if eqb score unknown then "UNKNOWN"%string else
  if eqb score loss then "LOSS"%string else
  if eqb score draw then "DRAW"%string else
  if eqb score win then "WIN"%string else
  if eqb score drawwin then "DRAWWIN"%string else
  if eqb score lossdraw then "LOSSDRAW"%string else
  "????"%string.

(* Reverse the valuation *)
Definition rev_val value := losswin - value.

Fixpoint sym_code i sres res :=
  match i with 
  | O => sres
  | S i =>
      let sres :=  (sres << horizontal) lor
                       (res land full_first_column) in
      let res := res >> horizontal in
      sym_code i sres res
  end.
    
(* Get the unique code of a position *)
Definition get_code wstate bstate turn height :=
  let res := (match turn with true => wstate | false => bstate end) lor
        (get_border wstate bstate) in
  if height <=? sym_level
  then
     let sres := sym_code nwidth zero res in
     min sres res
  else res.

(* Put an element in the hash-table
    The layout of the two-entry hash-table
      at key : high bits = work first entry, low bits = lock first entry
      at key + 1 : high bits = score first entry then score second entry
                   low bits = lock second entry
 *)

Definition hput wstate bstate turn work score hash_table height :=
   if (score land 1) =? 0 then hash_table
   else
   let code := get_code wstate bstate turn height in
   let fkey := code mod hprime in
   let key := 2 * (fkey >> lhash) in
   let r :=  fkey land mhash in
   let lock := (code >> slocksize) in
   let ht := (hash_table.[r]) in
   let val1 := (ht.[key]) in
   let val2 := (ht.[key + 1]) in
   if orb ((val1 land lockmask) =? lock) ((val1 >> locksize) <=? work) then
       let ht := (ht.[key <- (work << locksize) lor lock]) in
       let ht := (ht.[key + 1 <- 
                   ((score << scorelocksize) lor (val2 land scorelockmask))]) in
        (hash_table.[r <- ht])
   else
      let ht := (ht.[key + 1 <-
        ((((val2 >> scorelocksize) << scoresize) lor score) << locksize)
              lor lock]) in
        (hash_table.[r <- ht]).

(* Get an element in the hash-table *)
Definition hget (wstate bstate : int) (turn : bool) 
         (hash_table : array (array int)) height := 
   let code := get_code wstate bstate turn height in
   let fkey := code mod hprime in
   let key := 2 * (fkey >> lhash) in
   let r :=  fkey land mhash in
   let lock := (code >> slocksize) in
   let ht := (hash_table.[r]) in
   let val1 := (ht.[key]) in
   let val2 := (ht.[key + 1]) in
   if ((val1 land lockmask) =? lock) then
       val2 >> scorelocksize
   else if ((val2 land lockmask) =? lock) then
       (val2 >> locksize) land scoremask
   else unknown.

Definition is_nempty_move m :=
  match m with EmptyMove => false | Move _ _ _ => true end.

(* Process result *)
Inductive pres := PRes (s : int) (v : int) (t : array (array int)).

Section Process.

Variables (wstate bstate : int) (turn : bool) (beta : int) (lvisited : int) 
          (height hscore :  int)
          (alpha_beta : int -> int -> bool -> int -> int -> int -> 
                         array (array int) -> pres).
Fixpoint process ms alpha score visited hash_table :=
  match ms with
  | EmptyMove =>
      let score := if (score =? losswin - hscore) then draw else score in
      let work := get_log2 (sub visited lvisited) in
      let hash_table := hput wstate bstate turn work score hash_table height in
      PRes score (incr visited) hash_table
  | Move move _ ms1 =>
    let (nscore,visited,hash_table) := 
      alpha_beta bstate (make_move move wstate) (negb turn)
           (rev_val beta) (rev_val alpha) visited hash_table in
    let nscore := rev_val nscore in
    if nscore <=? score then process ms1 alpha score visited hash_table 
    else
    let score := nscore in
    if score <=? alpha then process ms1 alpha score visited hash_table                 
    else
    let alpha := score in
    if alpha <? beta  then process ms1 alpha score visited hash_table 
    else
      let score :=
        if (andb (score =? draw) (is_nempty_move ms1)) then drawwin 
        else score in
      let score := if (score =? losswin - hscore) then draw else score in
      let work := get_log2 (sub visited  lvisited) in
      let hash_table := hput wstate bstate turn work score hash_table height in
      PRes score (incr visited) hash_table
    end.

End Process.

(* alpha-beta result *)
Inductive ares := ARes (a : int) (b : int) (c : bool).

Section Alpha.

(* alpha beta pruning search *)
Fixpoint alpha_beta nstruct height wstate bstate turn alpha beta 
                    visited hash_table :=
  let hscore := hget wstate bstate turn hash_table height in
  let (alpha,beta,flag) :=
    (if (hscore =? unknown) then ARes alpha beta false else
    if negb ((hscore land 1) =? 0) then ARes alpha beta true else
    if (hscore =? drawwin) then
      if (beta =? draw) then ARes alpha beta true else ARes draw beta false
    else
      if (alpha =? draw) then ARes alpha beta true 
      else ARes alpha draw false) in
  if flag then PRes hscore visited hash_table else
  match find_moves wstate bstate with
  | Win => PRes win visited hash_table
  | Draw => PRes draw visited hash_table
  | Forced move =>
      match nstruct with 
     | 0%nat => PRes unknown visited hash_table
     | S nstruct =>
      let (score,visited,hash_table) := 
        alpha_beta nstruct (height + 1) bstate (make_move move wstate) 
                   (negb turn) (rev_val beta) (rev_val alpha) 
                    visited hash_table : pres in
      PRes (rev_val score) visited hash_table 
     end
  | Moves ms =>
     match nstruct with 
     | 0%nat => PRes unknown visited hash_table
     | S nstruct =>
     process wstate bstate turn beta visited height hscore 
            (alpha_beta nstruct (height + 1))
             ms alpha loss visited hash_table
     end
  end.

Lemma alpha_betaE nstruct height wstate bstate turn alpha beta 
                    visited hash_table  :
 alpha_beta nstruct height wstate bstate turn alpha beta 
                    visited hash_table =
  let hscore := hget wstate bstate turn hash_table height in
  let (alpha,beta,flag) :=
    (if (hscore =? unknown) then ARes alpha beta false else
    if negb ((hscore land 1) =? 0) then ARes alpha beta true else
    if (hscore =? drawwin) then
      if (beta =? draw) then ARes alpha beta true else ARes draw beta false
    else
      if (alpha =? draw) then ARes alpha beta true 
      else ARes alpha draw false) in
  if flag then PRes hscore visited hash_table else
  match find_moves wstate bstate with
  | Win => PRes win visited hash_table
  | Draw => PRes draw visited hash_table
  | Forced move =>
      match nstruct with 
     | 0%nat => PRes unknown visited hash_table
     | S nstruct =>
      let (score,visited,hash_table) := 
        alpha_beta nstruct (height + 1) bstate (make_move move wstate) 
                   (negb turn) (rev_val beta) (rev_val alpha) 
                    visited hash_table : pres in
      PRes (rev_val score) visited hash_table 
     end
  | Moves ms =>
     match nstruct with 
     | 0%nat => PRes unknown visited hash_table
     | S nstruct =>
     process wstate bstate turn beta visited height hscore 
            (alpha_beta nstruct (height + 1))
             ms alpha loss visited hash_table
     end
  end.
Proof. by case: nstruct. Qed.

Definition eval_position s :=
   match parse_string s with
   (wstate,bstate,turn) =>
   let (wstate,bstate) := if turn then (wstate,bstate) else (bstate,wstate) in
   let (score, _, _) :=
     alpha_beta (1 + nheight * nwidth)%nat 0 wstate bstate turn loss win zero
                (make_hash tt) in
   score
   end.

End Alpha.

Definition ex1 := (
                 "___O___"
              ++ "___X___"
              ++ "___O___"
              ++ "___X___"
              ++ "__OO___"
              ++ "__XX___")%string.


Definition ex2 := (
                 "___X___"
              ++ "__OX___"
              ++ "__XO___"
              ++ "__OX___"
              ++ "__XO___"
              ++ "__OX__O")%string.


Definition ex3 := (
                 "___O___"
              ++ "___X___" 
              ++ "___O___"
              ++ "___X___"
              ++ "___O___"
              ++ "XO_X___")%string.

Definition ex4 := ("______" ++ "______" ++ "______" ++
                   "______" ++ "______" ++ "______" ++ "______")%string.

Time Eval native_compute in string_of_score (eval_position ex1).
Time Eval native_compute in string_of_score (eval_position ex2).
Time Eval native_compute in string_of_score (eval_position ex3).
Time Eval native_compute in string_of_score (eval_position ex4).


