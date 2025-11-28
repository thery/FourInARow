
From Stdlib Require Import ZArith Ascii List String PrimInt63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_boot.

From Stdlib Require Import Lia.
Require Import ssr_int.
Require Import FourInARow.

Import PrimInt63Notations.
Import Uint63Axioms.
Import Uint63.
Open Scope uint63_scope.

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

Lemma nwihoLwB : nwidth * nhorizontal < nwB.
Proof.
apply: ltn_trans (_ : 2 ^ 6 < _); first by [].
by rewrite nwBE Z2Nat.inj_pow.
Qed.

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

Notation "t .[ i ]" := (get t i)
  (at level 1, left associativity, format "t .[ i ]").
Notation "t .[ i <- a ]" := (set t i a)
  (at level 1, left associativity, format "t .[ i <- a ]").


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

Lemma bit_decr i j : j <? digits -> bit (decr (lsl one j)) i = (i <? j).
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

Lemma first_column_spec i : bit first_column i = (i <? height).
Proof. by apply: bit_decr. Qed.

Lemma full_first_column_spec i : bit full_first_column i = (i <? horizontal).
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
  apply: leq_ltn_trans (_ : Z.to_nat (2 ^ 6) < _)%nat; first by [].
  rewrite nwBE.
  by apply/ltP/Z2Nat.inj_lt.
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
move=> bLd; rewrite (opzsE _ _ bLd).
apply/existsP/andP=> [[/= j /andP[H1 H2]]|[/nlebP H1 /eqP H2]]; last first.
  exists (up_log2 i); rewrite -H2 eqxx andbT.
  by apply/nlebP.
rewrite /up_log2; case: eqP => [->|i_neq0].
  by split => //; apply/nlebP.
case: (neqbP j 0) => [/to_nat_inj jE|jD0].
  by rewrite (eqP H2) jE in i_neq0.
have j_pos : 0 < to_nat j by case: (to_nat _) jD0.
have jB := to_nat_bounded j.
have tjE : to_nat (decr j) = (to_nat j).-1 by apply/to_nat_decr/nltbP.
have jE : log2 i = decr j.
  apply: log2E; rewrite tjE prednK //.
  have jLd : to_nat j < ndigits.
    apply: leq_trans (_ : to_nat b < ndigits)%N; last by apply/nltbP.
    by rewrite ltnS; apply/nlebP.
  rewrite (eqP H2) to_nat_decr; last first.
    by apply/nltbP; rewrite to_nat_lsl_one ?expn_gt0.
  rewrite -ltnS to_nat_lsl_one // prednK ?leqnn ?andbT ?expn_gt0 //.
  by rewrite ltn_exp2l // prednK.
rewrite jE; split; last first.
  suff -> : incr (decr j) = j by [].
  apply: to_nat_inj.
  by rewrite to_nat_incr ?tjE ?prednK.
apply/nlebP.
rewrite to_nat_incr tjE prednK //.
by apply/nlebP.
Qed.

Lemma opzsE'' b i :
  b <? digits -> 
  opzs b i = 
  (to_nat (up_log2 i) <= to_nat b) && (to_nat i == (2 ^ to_nat (up_log2 i)).-1).
Proof.
move => bLd; rewrite opzsE' //.
apply/andP/andP => [] [H1 H2].
  have F : to_nat (up_log2 i) < ndigits.
    by apply: leq_ltn_trans (_ : to_nat b < _); [apply/nlebP | apply/nltbP].
  split; first by apply/nlebP.
  rewrite {1}(eqP H2) to_nat_decr 1?to_nat_lsl_one //.
  by apply/nltbP; rewrite to_nat_lsl_one ?expn_gt0.
split; first by apply/nlebP.
have F : to_nat (up_log2 i) < ndigits.
  by apply: leq_ltn_trans (_ : to_nat b < _); [done | apply/nltbP].
apply/eqP/to_nat_inj; rewrite (eqP H2) to_nat_decr 1?to_nat_lsl_one //.
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
  [forall i, 
    ((get_column w i) != 0) ==> (i <? width) && opzs height (get_column w i)].  

Lemma wf_state0 : wf_state 0.
Proof. by apply/forallP => i; rewrite get_column0 eqxx. Qed.

Lemma wf_state_opzs w i : wf_state w -> opzs height (get_column w i).
Proof.
by move=> /forallP/(_ i); case: eqP => [-> _|_ /= /andP[] //]; apply: opzs0.
Qed.

Lemma wf_states_width w i : wf_state w -> width <=? i -> get_column w i = 0.
Proof.
move=> /forallP/(_ i); case: eqP => //= _; case: nlebP; case: nltbP => //.
by rewrite ltnNge => /negP.
Qed.

Lemma wf_state_true_width w j : 
  wf_state w -> bit w j = true -> (to_nat j %/ nhorizontal < nwidth).
Proof.
have jB := to_nat_bounded j.
move=> wf_state Hb; case: ltnP => // jL.
pose u := (to_nat j %/ nhorizontal).
pose v := (to_nat j %% nhorizontal).
have vLb : (v < nwB)%nat by apply: leq_ltn_trans (leq_mod _ _) jB.
have uLb : (u < nwB)%nat by apply: leq_ltn_trans (leq_div _ _) jB.
have jE : j = (of_nat u * horizontal + of_nat v).
  have pE : to_nat (of_nat u * horizontal) = (u * nhorizontal)%nat.
    rewrite to_nat_mul of_natK // (leq_ltn_trans _ jB) //.
    by rewrite (divn_eq (to_nat j) nhorizontal) leq_addr.
  apply: to_nat_inj.
  by rewrite to_nat_add ?pE of_natK // -divn_eq.
rewrite jE -bit_get_column // in Hb; last 2 first.
  - case: nlebP => //.
    by rewrite of_natK -ltnS //; case; rewrite ltn_pmod.
  by rewrite of_natK // of_natK // -divn_eq.
rewrite wf_states_width ?bit_0 // in Hb.
by case: nlebP; rewrite // of_natK.
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
  apply: leq_ltn_trans nwihoLwB.
  by rewrite leq_pmul2r // ltnW.
rewrite to_nat_mul 1?of_natK // -[to_nat _]/nhorizontal in khLl; last first.
  apply: leq_ltn_trans nwihoLwB.
  by rewrite leq_pmul2r // ltnW.
wlog : j k kLw jLw  jhLl khLl kB jB / (j <= k)%nat.
  move=> H H1 H2.
  case: (leqP j k) => H3; first by apply: H. 
  by apply/sym_equal/H => //; apply: ltnW.
rewrite leq_eqVlt => /orP[/eqP //|jLk].
rewrite bit_get_column0 //.
case: nltbP => // [] [].
have hE : to_nat (of_nat j * horizontal) = (j * nhorizontal)%nat.
  by rewrite to_nat_mul 1?of_natK // (leq_ltn_trans jhLl _).
rewrite to_nat_sub // hE //.
have -> : (to_nat height).+1 = nhorizontal by [].
by rewrite leq_subRL // addnC -mulSn (leq_trans _ khLl) // leq_pmul2r.
Qed.

Lemma wf_stateE w : 
  wf_state w -> w = \big[add/0]_(i < nwidth) (lsl (get_column w (of_nat i)) (of_nat i * horizontal)).
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
  have -> := (big_bit_lor xpredT 
                      (fun i1 : nat => lsl (get_column w (of_nat i1)) (of_nat i1 * horizontal))).
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
  have jhE : to_nat (of_nat j * horizontal) = (j * nhorizontal)%nat.
    rewrite to_nat_mul 1?of_natK //.
    apply: ltn_trans nwihoLwB.
    by rewrite ltn_pmul2r.
  rewrite jhE in jhLi.
  have := bit_get_column0 w (of_nat j) (i - of_nat j * horizontal).
  case: nltbP => [_|/negP]; first by apply.
  rewrite -leqNgt to_nat_sub ?jhE // -ltnS -[(to_nat height).+1]/nhorizontal
        => ijLh _.
  rewrite wf_states_width ?bit_0 1?of_natK //.
  apply/nlebP; rewrite of_natK //.
  suff <- : u = j by [].
  apply: divn_inv => //.
  by rewrite jhLi mulSn addnC -ltn_subLR.
have uLwB : (u < nwB)%nat by apply: ltn_trans nwidthLwB.
pose uo := Ordinal uLw.
rewrite (bigD1 uo) //= /olor lor_spec.
have HP : (fun i : 'I_nwidth => i != uo) =i (fun i : 'I_nwidth => i != u :> nat).
  move=> j.
  rewrite /in_mem /=.
  apply/idP/idP; first by move=> /eqP/val_eqP.
  by move=> H; apply/eqP/val_eqP.
rewrite (eq_bigl _ _ HP) /in_mem /=.
have -> := (big_bit_lor (fun i1 : nat =>  i1 != u)) 
                      (fun i1 : nat => lsl (get_column w (of_nat i1)) (of_nat i1 * horizontal)).
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
  rewrite to_nat_mul 1?of_natK // (leq_ltn_trans _ nwihoLwB) //.
  by rewrite leq_pmul2r // ltnW.
rewrite jhE in jhLi.
have := bit_get_column0 w (of_nat j) (i - of_nat j * horizontal).
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
by rewrite of_natK // (leq_trans (ltn_ord _)) // ndigitsLwB.
Qed.

Lemma wf_state_to_natE w : 
  wf_state w -> 
  to_nat w = 
    \sum_(i < nwidth) (to_nat (get_column w (of_nat i)) * 2 ^ (i * nhorizontal)).
Proof.
move=> Hw.
rewrite [in LHS](wf_stateE _ Hw).
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
  apply: ltn_trans nwihoLwB.
  by rewrite ltn_pmul2r.
by move=> j k l jLw kLw _ _; apply: bit_get_column_exclude.
Qed.

Lemma bit_le i j : (i <? (lsl one j)) -> bit i j = false.
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
  k <? digits -> i land (decr (lsl one k)) = i mod (lsl one k).
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
  have := wf_state_opzs _ (of_nat i) Hw.
  rewrite opzsE'' // => /andP[Hle _].
  apply: leq_ltn_trans (_ : 2 ^ to_nat height < _); first by rewrite leq_exp2l.
  by rewrite ltn_exp2l.
rewrite bottomE wf_state_to_natE // -big_split /=.
apply: eq_bigr => i _.
rewrite -mulSn; congr (_ * _)%N.
have := wf_state_opzs _ (of_nat i) Hw.
by rewrite opzsE'' // => /andP[_ /eqP->]; rewrite prednK // expn_gt0.
Qed.

Lemma cell_lor s1 s2 i j : 
  cell (s1 lor s2) i j =  (cell s1 i j)  ||  (cell s2 i j).
Proof. by rewrite [LHS]lor_spec. Qed.

Lemma cell_height w b  i : 
  i < nwidth -> wf_state (w lor b) -> ~~ cell w i nheight.
Proof.
move=> iLw sWf; apply/negP => Hc.
have : cell (w lor b) i nheight by rewrite cell_lor Hc.
set s := w lor b in iLw *.
rewrite cell_get_column //.
have /existsP[/= k /andP[kLh /forallP/(_ height)]/eqP->] :=
   wf_state_opzs _ (of_nat i) sWf.
case: nltbP => //.
by case: nlebP kLh => //; rewrite ltnNge => ->.
Qed.

Lemma cell_width w b j :
  j < nhorizontal -> wf_state (w lor b) -> ~~ cell w nwidth j.
Proof.
move=> jLh sWf; apply/negP => Hc.
have jLw : j < nwB by rewrite (leq_trans jLh) // ltnW // nhorizontalLwB.
have : cell (w lor b) nwidth j by rewrite cell_lor Hc.
set s := w lor b in sWf *.
rewrite /cell => Hcc.
have : to_nat (width * horizontal + of_nat j) %/ nhorizontal < nwidth.
  by apply: wf_state_true_width sWf _.
suff -> : to_nat (width * horizontal + of_nat j) %/ nhorizontal = nwidth.
  by [].
rewrite to_nat_add ?of_natK //.
  rewrite to_nat_mul; last by apply: nwihoLwB.
  by rewrite divnMDl // divn_small.
rewrite to_nat_mul; last by apply: nwihoLwB.
apply: leq_trans (_ : to_nat width * to_nat horizontal + nhorizontal <= _).
  by rewrite ltn_add2l.
apply: leq_trans (_ : 2 ^ 8 <= _); first by [].
by rewrite nwB_pow leq_exp2l.
Qed.


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
  rewrite !inE => /or4P[]/eqP-> /and4P[H1 H2 H3 H4].
  - apply: Or41; apply/existsP=> /=.
    pose v := x / horizontal.
    have vB : (to_nat v < nwidth)%N.
      by rewrite to_nat_div (wf_state_true_width _ _ Hw) // lor_spec H1.
    exists (Ordinal vB) => /=.
    pose r := x mod horizontal.
    have rB : (to_nat r < nheight)%N.
      have : to_nat r < nhorizontal by rewrite to_nat_mod ltn_mod.
      rewrite leq_eqVlt => /orP[/eqP He|//].
      have He1 : to_nat r = nheight by case: He.
      have /negP[] : ~~ cell w (to_nat v) (to_nat r).
        by rewrite He1 (cell_height _ _ _ _ Hw).
      by rewrite /cell !to_natK // -int_add_mod.
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
      have /negP[] : ~~ cell w (to_nat v).+1 (to_nat r).
        rewrite He.
        apply: cell_width Hw => //.
        by apply: leq_trans rB _.
      rewrite /cell !to_natK // -addn1 Fv //.
      rewrite mul_add_distr_r mul_1_l -add_assoc [_ + r]add_comm add_assoc.
      by rewrite -int_add_mod.
    move: vB; rewrite  leq_eqVlt => /orP[/eqP He |vB].
      have /negP[] : ~~ cell w (to_nat v).+2 (to_nat r).
        rewrite He.
        apply: cell_width Hw => //.
        by apply: leq_trans rB _.
      rewrite /cell !to_natK // -addn2 Fv //.
      rewrite mul_add_distr_r -add_assoc [_ + r]add_comm add_assoc.
      by rewrite -int_add_mod.
    move: vB; rewrite  leq_eqVlt => /orP[/eqP He |vB].
      have /negP[] : ~~ cell w (to_nat v).+3 (to_nat r).
        rewrite He.
        apply: cell_width Hw => //.
        by apply: leq_trans rB _.
      rewrite /cell !to_natK // -addn3 Fv //.
      rewrite mul_add_distr_r -add_assoc [_ + r]add_comm add_assoc.
      by rewrite -int_add_mod.
    rewrite vB //=.
    rewrite /cell !to_natK.
    rewrite -addn3 Fv // -Hv -addn2 Fv // -Hv -addn1 Fv // -Hv.
    by rewrite -int_add_mod H1 H2 H3 H4.
  - apply: Or42; apply/existsP=> /=.
    pose v := x / horizontal.
    have vB : (to_nat v < nwidth)%N.
      by rewrite to_nat_div (wf_state_true_width _ _ Hw) // lor_spec H1.
    exists (Ordinal vB) => /=.
    pose r := x mod horizontal.
    have rB : (to_nat r < nheight)%N.
      have : to_nat r < nhorizontal by rewrite to_nat_mod ltn_mod.
      rewrite leq_eqVlt => /orP[/eqP He|//].
      have He1 : to_nat r = nheight by case: He.
      have /negP[] : ~~ cell w (to_nat v) (to_nat r).
        by rewrite He1 (cell_height _ _ _ _ Hw).
      by rewrite /cell !to_natK // -int_add_mod.
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
      have /negP[] : ~~ cell w (to_nat v) (to_nat r).+1.
        by rewrite He; apply: cell_height Hw.
      rewrite /cell !to_natK //.
      by rewrite -addn1 Fr // add_assoc -int_add_mod.
    move: rB; rewrite  leq_eqVlt => /orP[/eqP He |rB].
      have /negP[] : ~~ cell w (to_nat v) (to_nat r).+2.
        by rewrite He; apply: cell_height Hw.
      rewrite /cell !to_natK //.
      by rewrite -addn2 Fr // add_assoc -int_add_mod.
    move: rB; rewrite  leq_eqVlt => /orP[/eqP He |rB].
      have /negP[] : ~~ cell w (to_nat v) (to_nat r).+3.
        by rewrite He; apply: cell_height Hw.
      rewrite /cell !to_natK //.
      by rewrite -addn3 Fr // add_assoc -int_add_mod.
    rewrite rB //=.
    rewrite /cell !to_natK.
    rewrite -addn3 Fr // -addn2 Fr // -addn1 Fr // !add_assoc.
    by rewrite -int_add_mod H1 H2 H3 H4.
  - apply: Or44; apply/existsP=> /=.
    pose v := x / horizontal.
    have vB : (to_nat v < nwidth)%N.
      by rewrite to_nat_div (wf_state_true_width _ _ Hw) // lor_spec H1.
    exists (Ordinal vB) => /=.
    pose r := x mod horizontal.
    have rB : (to_nat r < nheight)%N.
      have : to_nat r < nhorizontal by rewrite to_nat_mod ltn_mod.
      rewrite leq_eqVlt => /orP[/eqP He|//].
      have He1 : to_nat r = nheight by case: He.
      have /negP[] : ~~ cell w (to_nat v) (to_nat r).
        by rewrite He1 (cell_height _ _ _ _ Hw).
      by rewrite /cell !to_natK // -int_add_mod.
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
      have /negP[] : ~~ cell w (to_nat v) nheight.
        by apply: cell_height Hw.
      rewrite /cell to_natK //.
      suff -> : v * horizontal = x by [].
      rewrite (int_add_mod x horizontal) -/v -/r.
      suff -> : r = 0 by rewrite add_comm add_0_l.
      by apply: to_nat_inj.
    move: vB; rewrite  leq_eqVlt => /orP[/eqP He |vB].
      have /negP[] : ~~ cell w (to_nat v).+1 (to_nat r).-1.
        rewrite He.
        apply: cell_width Hw => //.
        rewrite prednK // ltnW //.
        by apply: leq_trans rB _.
      rewrite /cell -addn1 -subn1 Fv // Fr //=.
      by rewrite -Hl mul_1_l -int_add_mod.
    move: r1B; rewrite  leq_eqVlt => /orP[/eqP He |r1B].
      have /negP[] : ~~ cell w (to_nat v).+1 nheight.
        by apply: cell_height Hw.
      rewrite /cell // -addn1 Fv // mul_add_distr_r mul_1_l -add_assoc.
      have -> : (horizontal + of_nat nheight) = 1 + 2 * up_left by [].
      have <- : r = 1 by apply: to_nat_inj.
      by rewrite add_assoc -int_add_mod.
    move: vB; rewrite  leq_eqVlt => /orP[/eqP He |vB].
      have /negP[] : ~~ cell w (to_nat v).+2 (to_nat r).-2.
        rewrite He.
        apply: cell_width Hw => //.
        by rewrite -subn2 (leq_ltn_trans (leq_subr _ _)) // (leq_trans rB).
      rewrite /cell -addn2 -subn2 Fv // Fr//=.
      by rewrite -Hl -int_add_mod.
    move: r1B; rewrite  leq_eqVlt => /orP[/eqP He |r1B].
      have /negP[] : ~~ cell w (to_nat v).+2 nheight.
        by apply: cell_height Hw.
      rewrite /cell // -addn2 Fv // mul_add_distr_r -add_assoc.
      have -> : (2 * horizontal + of_nat nheight) = 2 + 3 * up_left by [].
      have <- : r = 2 by apply: to_nat_inj.
      by rewrite add_assoc -int_add_mod.
    move: vB; rewrite  leq_eqVlt => /orP[/eqP He |vB].
      have /negP[] : ~~ cell w (to_nat v).+3 (to_nat r).-1.-2.
        rewrite He.
        apply: cell_width Hw => //.
        by rewrite -subn3 (leq_ltn_trans (leq_subr _ _)) // (leq_trans rB).
      rewrite /cell -addn3 -subn3  Fv // Fr //=.
      by rewrite -Hl -int_add_mod.
    rewrite r1B vB /=.
    rewrite /cell !to_natK.
    rewrite -addn3 -subn3 Fv // Fr // -Hl.
    rewrite -addn2 -subn2 Fv // Fr // 1?ltnW // -Hl.
    rewrite -addn1 -subn1 Fv // Fr // 2?ltnW // -Hl.
    by rewrite -int_add_mod H1 H2 H3 H4.
  apply: Or43; apply/existsP=> /=.
  pose v := x / horizontal.
  have vB : (to_nat v < nwidth)%N.
    by rewrite to_nat_div (wf_state_true_width _ _ Hw) // lor_spec H1.
  exists (Ordinal vB) => /=.
  pose r := x mod horizontal.
  have rB : (to_nat r < nheight)%N.
    have : to_nat r < nhorizontal by rewrite to_nat_mod ltn_mod.
    rewrite leq_eqVlt => /orP[/eqP He|//].
    have He1 : to_nat r = nheight by case: He.
    have /negP[] : ~~ cell w (to_nat v) (to_nat r).
      by rewrite He1 (cell_height _ _ _ _ Hw).
    by rewrite /cell !to_natK // -int_add_mod.
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
    have /negP[] : ~~ cell w (to_nat v).+1 (to_nat r).+1.
      rewrite He.
      by apply: cell_width Hw.
    rewrite /cell -addn1 Fv // -[(to_nat r).+1]addn1 Fr //=.
    by rewrite -Hr mul_1_l -int_add_mod.
  move: rB; rewrite  leq_eqVlt => /orP[/eqP He |rB].
    have /negP[] : ~~ cell w (to_nat v).+1 nheight.
      by apply: cell_height Hw.
    rewrite /cell -He -addn1 Fv // -[(to_nat r).+1]addn1 Fr //=.
    by rewrite -Hr mul_1_l -int_add_mod.
  move: vB; rewrite  leq_eqVlt => /orP[/eqP He |vB].
    have /negP[] : ~~ cell w (to_nat v).+2 (to_nat r).+2.
      rewrite He.
      by apply: cell_width Hw.
    rewrite /cell -addn2 Fv // -[(to_nat r).+2]addn2 Fr //=.
    by rewrite -Hr -int_add_mod.
  move: rB; rewrite  leq_eqVlt => /orP[/eqP He |rB].
    have /negP[] : ~~ cell w (to_nat v).+2 nheight.
      by apply: cell_height Hw.
    rewrite /cell -He -addn2 Fv // -[(to_nat r).+2]addn2 Fr //=.
    by rewrite -Hr -int_add_mod.
  move: vB; rewrite  leq_eqVlt => /orP[/eqP He |vB].
    have /negP[] : ~~ cell w (to_nat v).+3 (to_nat r).+3.
      rewrite He.
      by apply: cell_width Hw.
    rewrite /cell -addn3 Fv // -[(to_nat r).+3]addn3 Fr //=.
    by rewrite -Hr -int_add_mod.
  move: rB; rewrite  leq_eqVlt => /orP[/eqP He |rB].
    have /negP[] : ~~ cell w (to_nat v).+3 nheight.
      by apply: cell_height Hw.
    rewrite /cell -He -addn3 Fv // -[(to_nat r).+3]addn3 Fr //=.
    by rewrite -Hr -int_add_mod.
  rewrite rB vB /=.
  rewrite /cell !to_natK.
  rewrite -addn3 -[(to_nat r).+3]addn3 Fv // Fr // -Hr.
  rewrite -addn2 -[(to_nat r).+2]addn2 Fv // Fr // -Hr.
  rewrite -addn1 -[(to_nat r).+1]addn1 Fv // Fr // -Hr.
  by rewrite -int_add_mod H1 H2 H3 H4.
case => [] /existsP[/= x] /existsP[/= y] /and5P[].
- move=> xLw; rewrite /cell => H1 H2 H3 H4.
  exists (of_nat x * horizontal + of_nat y).
  apply/existsP; exists horizontal; rewrite !inE eqxx !andTb.
  suff F k : k < 4 -> of_nat x * horizontal + of_nat y + of_nat k * horizontal = 
    of_nat (x + k) * horizontal + of_nat y.
    by rewrite (F 1%N) // addn1 (F 2%N) // addn2 (F 3%N) // addn3 H1 H2 H3 H4.
  move=> kL4.
  have kLnwB : k < nwB by apply: leq_trans kL4 _; rewrite ltnW.
  have xkLnwB : x + k < nwB. 
    rewrite (leq_trans _ wLwB) // ltnS (leq_trans _ xLw) // -addn4 leq_add2l.
    by rewrite ltnW. 
  have xLnwB : x < nwB by apply: leq_trans xkLnwB; rewrite ltnS leq_addr.
  have -> : of_nat (x + k) = of_nat x + of_nat k.
    by apply: to_nat_inj; rewrite to_nat_add !of_natK.
  by rewrite mul_add_distr_r -!add_assoc; congr (_ + _); rewrite add_comm.
- move=> yLh; rewrite /cell => H1 H2 H3 H4.
  exists (of_nat x * horizontal + of_nat y).
  apply/existsP; exists vertical; rewrite !inE eqxx !andTb.
  suff F k : k < 4 -> of_nat x * horizontal + of_nat y + of_nat k = 
    of_nat x * horizontal + of_nat (k + y).
    by rewrite (F 1%N) // (F 2%N) // (F 3%N) // H1 H2 H3 H4.
  move=> kL4.
  rewrite -add_assoc; congr (_ + _).
  have kLnwB : k < nwB by apply: leq_trans kL4 _; rewrite ltnW.
  have ykLnwB : y + k < nwB. 
    rewrite (leq_trans _ hLwB) // ltnS (leq_trans _ yLh) // -addn4 leq_add2l.
    by rewrite ltnW. 
  have yLnwB : y < nwB by apply: leq_trans ykLnwB; rewrite ltnS leq_addr.
  by apply: to_nat_inj; rewrite to_nat_add !of_natK // addnC.
- move=> xLw yLh; rewrite /cell => H1 H2 /andP[H3 H4].
  exists (of_nat x * horizontal + of_nat y).
  apply/existsP; exists up_right; rewrite !inE eqxx !andTb.
  suff F k : k < 4 -> of_nat x * horizontal + of_nat y + of_nat k * up_right = 
    of_nat (k + x) * horizontal + of_nat (k + y).
    by rewrite (F 1%N) // (F 2%N) // (F 3%N) // H1 H2 H3 H4.
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
move=> xLw yG2; rewrite /cell => H1 H2 /andP[H3 H4].
exists (of_nat x * horizontal + of_nat y).
apply/existsP; exists up_left; rewrite !inE eqxx !andTb.
suff F k : k < 4 -> of_nat x * horizontal + of_nat y + of_nat k * up_left = 
  of_nat (k + x) * horizontal + of_nat (y - k).
  rewrite (F 1%N) // subn1 (F 2%N) // subn2 (F 3%N) // subnS subn2.
  by rewrite H1 H2 H3 H4.
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

(*
Definition get_border (wstate bstate : int) :=
  bottom + (wstate lor bstate).

(* Perform a move *)
Definition  make_move move state := move lor state.
*)

(*
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
*)

Lemma in_insert_fmove m1 m2 v1 v2 l : 
  (m1, v1) \in (insert_fmove m2 v2 l) = 
  (m1 == m2) && (v1 == v2) || ((m1,v1) \in l).
Proof.
elim: l m2 v2  => [|[m3 v3] l IH] m2 v2 /=; rewrite ?inE ?xpair_eqE ?orbF //.
case: (_ ?= _); rewrite ?inE ?xpair_eqE ?orbF ?IH //.
by do 2 case: (_ && _).
Qed.

Definition cmove s (x : nat) (y : nat) :=
 [&& x < nwidth, y < nheight & 
   [forall z : 'I_nheight, cell s x z == (z < y)]].
  
Lemma cmove_cell s x y : cmove s x y -> ~~ cell s x y.
Proof.
by move/and3P => [xLw yLh /forallP/(_ (Ordinal yLh))/eqP->]; rewrite ltnn.
Qed.

Lemma cmove_lt s x y z : cmove s x y -> z < y -> cell s x z.
Proof.
move/and3P => [xLw yLh /forallP Hf] zLy.
by have /eqP-> := Hf (Ordinal (ltn_trans zLy yLh)).
Qed.

Lemma cmove_ge s x y z : cmove s x y -> y <= z < nheight -> ~~ cell s x z.
Proof.
move/and3P => [xLw yLh /forallP Hf] /andP[yLz zLh].
by have /eqP-> /= := Hf (Ordinal zLh); rewrite ltnNge yLz.
Qed.

Lemma cmoveE s x y : cmove s x y -> y = 
(*

Fixpoint make_columns i column :=
  match i with
      O => nil 
  | S i => column :: (make_columns i (lsl column horizontal))
  end.

Definition columns := Eval compute in make_columns nwidth first_column.

*)

Lemma columns_size : seq.size columns = nwidth.
Proof.
have -> : columns = make_columns nwidth first_column by [].
by elim: nwidth first_column => //= ? IH c; rewrite IH.
Qed.

Lemma lsl_add_distl x m n :
  (to_nat n + to_nat m < nwB)%nat -> lsl x (m + n) = lsl (lsl x m) n.
Proof.
move=> mnLw; apply: to_nat_inj.
rewrite 3!to_nat_lslW to_nat_add; last by rewrite addnC.
by rewrite expnD mulnA modnMml.
Qed.

Lemma columns_val i : 
  i < nwidth -> nth 0 columns i = lsl first_column (of_nat i * horizontal).
Proof.
move=> iLw.
have: i * nhorizontal < nwB by apply: ltn_trans nwihoLwB; rewrite ltn_mul2r.
have -> : columns = make_columns nwidth first_column by [].
have {1}-> : first_column = lsl first_column (of_nat 0 * horizontal).
  by rewrite lsl0_r.
have {1 3}-> : i = (0 + i)%N by [].
move: 0%nat => j.
elim: nwidth i j iLw  => //= w IH [|i] j; first by rewrite addn0.
rewrite ltnS => iLw ijLw /=.
rewrite -lsl_add_distl.
  have -> : of_nat j * horizontal + horizontal = of_nat (j.+1) * horizontal.
    have ->: of_nat j.+1 = of_nat j + 1.
      apply: to_nat_inj.
    rewrite -addn1.
Search lsl (_ + _).
rewrite IH.
rewrite [in LHS]/=.
by [].
  case => //. 


elim: nwidth i first_column=> [[]//|w IH [|i]/=].
rewrite lsl0_r.
Search lsl 0.
Search lsl.



(*
Section FindMoves.

Variables (wstate bstate border: int).

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
        let v := (values.[log2 move]) in
        fms columns (insert_fmove move v res)
   end.
*)

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

(*
End FindMoves.
*)

Check 
(*
(* Find possible moves *)
Definition find_moves wstate bstate :=
  let border := get_border wstate bstate in
  fms wstate bstate border columns [::].
*)

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
       let move := lsl one (j * horizontal + i) in 
       parsei s1 i (j + 1) (make_move wstate move) bstate (negb turn)
    | String "O"%char s1 =>
       let move := lsl one (j * horizontal + i) in 
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
   (let move := lsl one (j * horizontal + i) in 
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
      let sres :=  (lsl sres horizontal) lor
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
       let ht := (ht.[key <- (lsl work locksize) lor lock]) in
       let ht := (ht.[key + 1 <- 
                   ((lsl score scorelocksize) lor (val2 land scorelockmask))]) in
        (hash_table.[r <- ht])
   else
      let ht := (ht.[key + 1 <-
        (lsl ((lsl (val2 >> scorelocksize) scoresize) lor score) locksize)
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
      let work := log2 (sub visited lvisited) in
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
      let work := log2 (sub visited  lvisited) in
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

(*
Time Eval native_compute in string_of_score (eval_position ex1).
Time Eval native_compute in string_of_score (eval_position ex2).
Time Eval native_compute in string_of_score (eval_position ex3).
Time Eval native_compute in string_of_score (eval_position ex4).

*)
