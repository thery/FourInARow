From Stdlib Require Import ZArith Ascii List String PrimInt63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_boot.
From HB Require Import structures.

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
Proof. by move=> ? ?; apply: ltn_trans (ihjLwh _ _ _ _) _. Qed.

Lemma ihjLw i j : 
  i < nwidth  -> j < nhorizontal -> i * nhorizontal + j < nwB.
Proof. by move=> ? ?; apply: ltn_trans (ihjLd _ _ _ _) ndigitsLwB. Qed.

Lemma ihjE i j : 
  i < nwidth  -> j < nhorizontal -> 
  to_nat (of_nat i * horizontal + of_nat j) = (i * nhorizontal + j)%N.
Proof.
move=> iLw jLh.
have jLw : j < nwB by apply: ltn_trans nwidthLwB.
by rewrite to_nat_add ihE // of_natK // ihjLw.
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


Lemma lsl_add_distl x m n :
  (to_nat n + to_nat m < nwB)%nat -> lsl x (m + n) = lsl (lsl x m) n.
Proof.
move=> mnLw; apply: to_nat_inj.
rewrite 3!to_nat_lslW to_nat_add; last by rewrite addnC.
by rewrite expnD mulnA modnMml.
Qed.

Lemma lslC x m n : lsl (lsl x m) n = lsl (lsl x n) m.
Proof.
apply: to_nat_inj.
rewrite [LHS]to_nat_lslW [in LHS]to_nat_lslW.
rewrite modnMml mulnAC -modnMml.
by rewrite [RHS]to_nat_lslW [in RHS]to_nat_lslW.
Qed.

Lemma lsr_add_distl x m n :
  (to_nat n + to_nat m < nwB)%nat -> lsr x (m + n) = lsr (lsr x m) n.
Proof.
move=> mnLw; apply: to_nat_inj.
rewrite [LHS]to_nat_lsr to_nat_add; last by rewrite addnC.
rewrite expnD divnMA.
by rewrite [RHS]to_nat_lsr [in RHS]to_nat_lsr.
Qed.

Lemma lsrC x m n : lsr (lsr x m) n = lsr (lsr x n) m.
Proof.
apply: to_nat_inj.
rewrite [LHS]to_nat_lsr [in LHS]to_nat_lsr.
rewrite -divnMA mulnC divnMA.
by rewrite [RHS]to_nat_lsr [in RHS]to_nat_lsr.
Qed.

Lemma lsl_lsr_le x m n :
  to_nat x * 2 ^ (to_nat m) < nwB -> n <=? m ->
  lsr (lsl x m) n = lsl x (m - n).
Proof.
move=> xLw /nlebP nLm; apply: to_nat_inj.
rewrite [LHS]to_nat_lsr [in LHS]to_nat_lslW modn_small //.
rewrite -(subnK nLm) expnD mulnA mulnK ?expn_gt0 //.
rewrite [RHS]to_nat_lslW to_nat_sub ?to_nat_bounded // modn_small //.
apply: leq_ltn_trans xLw.
by rewrite leq_mul2l leq_exp2l // leq_subr orbT.
Qed.

Lemma lsl_lsr_ge x m n :
  to_nat x * 2 ^ (to_nat m) < nwB -> m <=? n ->
  lsr (lsl x m) n = lsr x (n - m).
Proof.
move=> xLw /nlebP mLn; apply: to_nat_inj.
rewrite [LHS]to_nat_lsr [in LHS]to_nat_lslW modn_small //.
rewrite -(subnK mLn) expnD [X in _ %/ X]mulnC divnMA mulnK ?expn_gt0 //.
by rewrite [RHS]to_nat_lsr to_nat_sub // to_nat_bounded.
Qed.

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
  move=> H H1 H2.
  case: (leqP j k) => H3; first by apply: H. 
  by apply/sym_equal/H => //; apply: ltnW.
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
  have := bit_get_column0 w (of_nat j) (i - of_nat j * horizontal).
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
by rewrite of_natK // (leq_trans (ltn_ord _)) // (ltnW ndigitsLwB).
Qed.

Lemma wf_state_to_natE w : 
  wf_state w -> 
  to_nat w = 
    \sum_(i < nwidth) 
      (to_nat (get_column w (of_nat i)) * 2 ^ (i * nhorizontal)).
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

Lemma cell_lor s1 s2 i j : 
  cell (s1 lor s2) i j =  (cell s1 i j)  ||  (cell s2 i j).
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
      have /negP[] : ~~ cell (w lor b) (to_nat v) (to_nat r).
        by rewrite He1 (cell_height _ _ _ Hw).
      by rewrite cell_lor /cell !to_natK // -int_add_mod // H1.
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
      have /negP[] : ~~ cell (w lor b) (to_nat v) (to_nat r).
        by rewrite He1 (cell_height _ _ _ Hw).
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
      have /negP[] : ~~ cell (w lor b) (to_nat v) (to_nat r).
        by rewrite He1 (cell_height _ _ _ Hw).
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
    have /negP[] : ~~ cell (w lor b) (to_nat v) (to_nat r).
      by rewrite He1 (cell_height _ _ _ Hw).
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
*)


(*

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

Lemma addK m n : (m + n) - n = m.
Proof. ring. Qed.

Lemma subK m n : (m - n) + n = m.
Proof. ring. Qed.

Lemma incrK m : decr (incr m) = m.
Proof. by apply: addK. Qed.

Lemma decrK m : incr (decr m) = m.
Proof. by apply: subK. Qed.

Lemma up_log2E x y : 
  2 ^ (to_nat y).-1 <= to_nat x < 2 ^ (to_nat y) -> up_log2 x = y.
Proof.
rewrite /up_log2; case: eqP => [->|xDz]; first by rewrite leqNgt expn_gt0.
case: nltbP (to_nat_decr y); last by case: (to_nat y) => //=; case: (to_nat x).
move=> y_gt0 He Hx.
by rewrite -[y]decrK; congr incr; apply: log2E; rewrite He // prednK.
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
case: nltbP (bit_get_column0 s (of_nat x) (of_nat i));
    (rewrite of_natK; last by apply: leq_trans (ltn_ord i) (ltnW ndigitsLwB)).
  by move=> H /(_ isT) ->; rewrite ifN // -leqNgt.
move/negP; rewrite -leqNgt -ltnS.
rewrite ltnS -[to_nat height]/nheight => iLh _.
by rewrite ifT // -cell_get_column.
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

Lemma sum_pow_incr_lt b f n : 
  1 < b -> (forall j k, j < k < n -> f j < f k) -> 
  \sum_(i < n) b ^ (f i) < b ^ (f n.-1).+1.
Proof.
move=> b_gt1; elim: n => [|[|n] IH f_incr].
- by rewrite big_ord0 expn_gt0 ltnW.
- by rewrite big_ord1 /= expnS -[X in X < _]mul1n ltn_mul2r expn_gt0 b_gt1 ltnW.
rewrite big_ord_recr /=.
apply: leq_trans (_ : (b ^ (f n.+1)).*2 <= _); last first.
  by rewrite -mul2n expnS leq_mul2r b_gt1 orbT.
rewrite -addnn ltn_add2r (leq_trans (IH _)) //.
  by move=> j k /andP[jLk kLn]; rewrite f_incr // jLk ltnW.
by rewrite leq_exp2l // f_incr //= !leqnn.
Qed.

Lemma sum_pow_incr_div b k f n : 
  1 < b -> (forall j k, j < k < n -> f j < f k) -> 
  (\sum_(i < n) b ^ (f i)) %/ b ^ k = \sum_(i < n) b ^ (f i) %/ b ^ k.
Proof.
move=> b_gt1; elim: n => [|n IH f_incr].
  by rewrite !big_ord0 div0n.
have [kLf|fLk] := leqP k (f n).
  rewrite !big_ord_recr /=.
  rewrite -(subnK kLf) expnD divnDMl //; last by rewrite expn_gt0 ltnW.
  rewrite mulnK ?expn_gt0 1?ltnW // IH // => j1 k1 /andP[jLk1 k1Ln].
  by apply: f_incr; rewrite jLk1 ltnW.
rewrite [RHS]big1 => /= [|i _].
  rewrite divn_small // (leq_trans (sum_pow_incr_lt _ _ _ _ _)) //.
  by rewrite leq_exp2l.
rewrite divn_small // ltn_exp2l // (leq_ltn_trans _ fLk) //.
have [iLn|nLi|->//]:= ltngtP i n.
  by rewrite ltnW // f_incr // iLn leqnn.
by have := ltn_ord i; rewrite leqNgt ltnS nLi.
Qed.

Lemma sum_pow_incr_div_mod f b k n : 
  1 < b -> (forall j k, j < k < n -> f j < f k) -> 
  (\sum_(i < n) b ^ (f i)) %/ b ^ k =  
    (k \in  [seq f x | x <- iota 0 n]) %[mod b].
Proof.
move=> b_gt1 f_incr.
rewrite sum_pow_incr_div //.
elim: n f_incr => [|n IH f_incr]; first by rewrite !big_ord0.
rewrite -[in RHS]addn1 iotaD map_cat mem_cat /= inE add0n.
rewrite !big_ord_recr /=.
have [kLf|fLk|->] := ltngtP k (f n); rewrite ?(orbF, orbT).
- rewrite -(subnK (ltnW kLf)) expnD mulnK ?expn_gt0 1?ltnW //.
  rewrite -[(f n - k)%N]prednK ?subn_gt0 //.
  rewrite -modnDmr expnS modnMr addn0.
  apply: IH => j1 k1 /andP[j1Lk1 k1Ln]; apply: f_incr.
  by rewrite j1Lk1 ltnS ltnW.
- rewrite divn_small ?ltn_exp2l // addn0.
  apply: IH => j1 k1 /andP[j1Lk1 k1Ln]; apply: f_incr.
  by rewrite j1Lk1 ltnS ltnW.
rewrite divnn expn_gt0 1?ltnW //= big1 => // i _.
by rewrite divn_small // ltn_exp2l ?f_incr // ltn_ord leqnn.
Qed.

Lemma cmoveE1 s x (y := to_nat (up_log2 (get_column s (of_nat x)))) : 
  wf_state s -> x < nwidth -> y < nheight -> cmove s x y.
Proof.
move=> sWf xLw yLh; apply/and3P; split => //; apply/forallP => /= z; apply/eqP.
have zLnwB : z < nwB by apply: ltn_trans nhorizontalLwB.
have := wf_state_opzs _ x xLw sWf.
rewrite cell_get_column // opzsE' // => /andP[uLh /eqP ->].
case: nlebP uLh => // uLh _.
rewrite bit_decr; last first.
  by case: nltbP => // [] []; apply: leq_ltn_trans (_ : nheight < ndigits).
by case: nltbP; rewrite -/y of_natK //; case: ltngtP.
Qed.

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

Lemma is_zeronE n : is_zero n = (to_nat n == 0%N).
Proof. by apply/neqbP/idP => /eqP. Qed.

Lemma bitE w i : bit w i = (to_nat w %/ 2 ^ to_nat i == 1 %[mod 2]).
Proof.
rewrite /bit is_zeronE to_nat_lslW to_nat_lsr.
set w1 := _ %/ _.
have -> : 2 ^ to_nat (digits - 1) = 2 ^ ndigits.-1 by [].
rewrite nwB_pow (divn_eq w1 2) mulnDl -mulnA -expnS prednK //.
do 2 rewrite -modnDml modnMl add0n.
case: (_ %% 2) (ltn_pmod w1 (isT : 0 < 2)) => [|[|n]].
- by rewrite mul0n mod0n.
- by rewrite mul1n modn_small ?expn_eq0 ?ltn_exp2l?prednK.
by rewrite 2!ltnS ltn0 => H; case: notF.
Qed.


Lemma bool1E b : (nat_of_bool b == 1%N) = b.
Proof. by case: b. Qed.

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
  have := wf_state_opzs _ _ jLw Hwf.
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
    have := wf_state_opzs _ _ x1Lw Hwf.
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

Print fmove.
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

Definition has_move s := 
  [exists i : 'I_nwidth, exists j : 'I_nheight, cmove s i j].

Lemma ncells_has_move s : has_move s <= ncells s.
Proof.
rewrite /has_move; case: existsP => [[/= x /existsP[/= y Csxy]]|//].
by rewrite /ncells (bigD1 x) //= (bigD1 y) //= cmove_cell.
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

Definition make_move s i j :=  s lor (lsl 1 (of_nat i * horizontal + of_nat j)).

Lemma bit_onenn m n : 
  m <? digits -> n <? digits -> bit (lsl one m) n = (m == n).
Proof.
move=> /nltbP mLd /nltbP nLd.
rewrite /bit is_zeronE to_nat_lslW to_nat_lsr to_nat_lsl_one //.
rewrite to_nat_sub  ?ndigitsLwB // subn1.
have [mLn|nLm|mEn] := ltngtP (to_nat m) (to_nat n).
- rewrite divn_small ?mod0n ?eqxx ?ltn_exp2l //.
  by apply/sym_equal/idP=> /eqP mEn; rewrite mEn ltnn in mLn.
- rewrite -[in LHS](subnK (ltnW nLm)) expnD mulnK ?expn_gt0 // -expnD.
  have /subnK<- : ndigits <= to_nat m - to_nat n + ndigits.-1.
    by rewrite -{1}(@prednK ndigits) // -add1n leq_add2r subn_gt0.
  rewrite expnD nwB_pow modnMl eqxx.
  by apply/sym_equal/idP=> /eqP mEn; rewrite mEn ltnn in nLm.
rewrite mEn divnn expn_gt0 mul1n modn_small; last by rewrite nwB_pow ltn_exp2l.
rewrite expn_eq0 -ltnS prednK //.
by apply/sym_equal/idP/neqbP.
Qed.

Lemma cell_make_movel s i j : 
  i < nwidth -> j < nhorizontal -> cell (make_move s i j) i j.
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
  by rewrite /make_move cell_lor /cell bit_onenn ?eqxx ?orbT.
apply/nltbP/(leq_ltn_trans _ (_ : nwidth * nhorizontal < _)) => //.
rewrite HE -(@prednK nwidth) // mulSn addnC.
by rewrite leq_add ?(leq_trans (ltnW jLh)) // leq_mul2r.
Qed.

Lemma cell_make_mover s i1 i2 j1 j2 : 
  i1 < nwidth -> j1 < nhorizontal -> i2 < nwidth -> j2 < nhorizontal ->
 ((i1 != i2) || (j1 != j2)) ->
  cell (make_move s i1 j1) i2 j2 = cell s i2 j2.
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
  ncells (w lor b) = (ncells (b lor make_move w i j)).+1.
Proof.
move=> cm.
have /and3P[iLw jLh _] := (cm).
have jLh' : j < nhorizontal by apply: leq_trans jLh _.
pose i1 := Ordinal iLw; pose j1 := Ordinal jLh.
rewrite /ncells [LHS](bigD1 i1) //= [in RHS](bigD1 i1) //= -addSn.
congr (_ + _)%N; last first.
  apply: eq_bigr => k kDj; apply: eq_bigr => l _.
  have lLh' : l < nhorizontal by apply: leq_trans (ltn_ord _) _.
  by rewrite 2!cell_lor cell_make_mover 1?orbC // orbC eq_sym kDj.
rewrite [LHS](bigD1 j1) //= [in RHS](bigD1 j1) //=.
have F1 : ~~ cell (w lor b) i j by apply: cmove_cell.
have F2 : ~~ cell b i j.
  by move: F1; rewrite cell_lor; case: (cell b _ _); case: cell.
rewrite F1 cell_lor negb_or F2 cell_make_movel //= add1n add0n.
congr (_).+1; apply: eq_bigr => k kDj.
have kLh' : k < nhorizontal by apply: leq_trans (ltn_ord _) _.
by rewrite 2!cell_lor cell_make_mover 1?orbC // eq_sym kDj.
Qed.

Fixpoint eval_aux (n : nat) w b := 
  let s := w lor b in 
  if cwin w then WIN else
  if has_move s then
    if n is n1.+1 then
      \max_(i < nwidth) \max_(j < nheight | cmove s i j) 
                wcomp (eval_aux n1 b (make_move w i j))
    else UNKNOWN
  else if cwin b then LOSS else DRAW.

Definition eval w b := eval_aux (ncells (w lor b)) w b.

Lemma evalS w b : 
  eval w b = 
  let s := w lor b in 
  if cwin w then WIN else
  if has_move s then
      \max_(i < nwidth) \max_(j < nheight | cmove s i j) 
                wcomp (eval b (make_move w i j))
  else if cwin b then LOSS else DRAW.
Proof.
rewrite /eval; have := refl_equal (ncells (w lor b)).
move: {-1}(ncells _)=> n; elim: n w b => /= [|n IH] w b nE.
  case Ew: cwin => //; case Em: has_move => //.
  by have := ncells_has_move (w lor b); rewrite nE Em.
case Ew: cwin => //; case Em: has_move => //.
apply: eq_bigr => i _; apply: eq_bigr => j Cij.
congr (wcomp (eval_aux _ _ _)).
by move: nE; rewrite (ncells_cmove _ _ _ _ Cij) => [] [].
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
                    wcomp (eval b (make_move w i j)) in
    [|| m == UNKNOWN,  m == WIN,  m == DRAW  | m == LOSS].
  elim:  k => /= [|k IHk]; first by rewrite big_ord0.
  rewrite big_mkcond /= big_ord_recr /=  -big_mkcond /=.
  case E1 : (cmove _ _ _) => /=; last by rewrite maxn0.
  have {E1}/idP E1 := E1.
  case: (P k) => //=.
  suff /IH/or3P[/eqP->|/eqP->|/eqP->] :
       ncells (b lor (make_move w i k)) = n by case/or4P : IHk => /eqP->.
  by have := ncells_cmove _ _ _ _ E1; rewrite cE => [] [].
have : [|| m1 == UNKNOWN, m1 == WIN, m1 == DRAW  | m1 == LOSS].
  by rewrite /= (IH1 i1 nheight (fun n => n != \val j1)).
pose gf i := \max_(j < nheight | cmove (w lor b) i j )
                    wcomp (eval b (make_move w i j)).
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
  by have := ncells_cmove _ _ _ _ Hj1; rewrite cE => [] [].
by case/or3P => /eqP-> /or4P[]/eqP->/or4P[]/eqP->.
Qed.

Lemma eval_winP w b : 
  reflect 
  (cwin w \/ exists i j, cmove (w lor b) i j /\ eval b (make_move w i j) = LOSS)
  (eval w b == WIN).
Proof.
pose f (i : 'I_nwidth) (j : 'I_nheight) := wcomp (eval b (make_move w i j)).
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
by case/or3P : (evalOr  b (make_move w i j)) => /eqP->.
Qed.

Lemma eval_lossP w b : 
  reflect 
  (~~ cwin w /\ 
    (cwin b \/ 
      has_move (w lor b) /\  
      forall i j, cmove (w lor b) i j -> eval b (make_move w i j) = WIN))
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
case/or3P : (evalOr b (make_move w i j)) => /eqP E1 //.
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
      (exists i j, cmove (w lor b) i j /\ eval b (make_move w i j) = DRAW) /\
      (forall i j, cmove (w lor b) i j -> DRAW <= eval b (make_move w i j))]
  (eval w b == DRAW).
Proof.
pose f (i : 'I_nwidth) (j : 'I_nheight) := wcomp (eval b (make_move w i j)).
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
  by case/or3P : (evalOr b (make_move w i1 j1)) => /eqP ->.
rewrite evalS /=; case E1 : cwin => //.
case E2 : has_move => //=; last by case: cwin.
move=> He.
have F1 i j : cmove (w lor b) i j -> DRAW <= eval b (make_move w i j).
  move=> Cij.
  suff : wcomp (eval b (make_move w i j)) <= DRAW.
    by case/or3P : (evalOr b (make_move w i j)) => /eqP ->.
  rewrite -He.
  have iLw : i < nwidth by case/and3P : Cij.
  have jLh : j < nheight by case/and3P : Cij.
  rewrite (bigD1 (Ordinal iLw)) //= (bigD1 (Ordinal jLh)) //=.
  apply: leq_trans (leq_maxl _ _).
  by apply: leq_trans (leq_maxl _ _).
have [] := boolP [exists i : 'I_nwidth,
                [exists j : 'I_nheight, cmove (w lor b) i j &&
                                        (eval b (make_move w i j) == DRAW)]].
  move=> /existsP[i /existsP[j /andP[Cij /eqP Eij]]]. 
  split=> // [|_]; first by apply/negP => NWb; move: Eij; rewrite evalS /= NWb.
  by split => //; exists i; exists j.
rewrite negb_exists => /forallP /= HF.
suff : DRAW <= LOSS by [].
rewrite -He; apply/bigmax_leqP => /= i _; apply/bigmax_leqP => /= j Cij.
have := F1 i j Cij.
have := HF i; rewrite negb_exists => /forallP/(_ j).
rewrite negb_and Cij /=.
by case/or3P: (evalOr b (make_move w i j)) => /eqP->.
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
move=> /transposeP H1 /transposeP H2; apply/transposeP => i j iLw jLh.
by rewrite !cell_lor H1 // H2.
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

Lemma cmove_transpose s1 s2 i j :
  transpose s1 s2 -> i < nwidth -> cmove s1 i j = cmove s2 (nwidth - i.+1) j.
Proof.
have Hci s3 s4 i1 j1 :
    transpose s3 s4 -> cmove s3 i1 j1 -> cmove s4 (nwidth - i1.+1) j1.
  move=> /transposeP H1 /and3P[iLw jLw /forallP/= HC].
  by rewrite /cmove ltn_subrL /= jLw /=; apply/forallP => z; rewrite -H1.
move=> Ht iLw; apply/idP/idP => [|Cij]; first by apply: Hci.
have -> : i = (nwidth -  (nwidth - i.+1).+1)%N by rewrite subnS subKn //.
by apply: Hci Cij; rewrite transpose_sym.
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

Lemma has_move_transpose s1 s2 : transpose s1 s2 -> has_move s1 = has_move s2.
Proof.
suff Hhi s3 s4 : transpose s3 s4 -> has_move s3 -> has_move s4.
  by move=> Ht; apply/idP/idP; apply: Hhi => //; rewrite transpose_sym.
move=> Ht.
move=> /existsP[/= i /existsP[/= j Hc]].
apply/existsP; exists (rev_ord i); apply/existsP; exists j => /=.
by rewrite -(cmove_transpose _ _ _ _ Ht).
Qed.

Lemma make_move_transpose s1 s2 i j :
   transpose s1 s2 -> i < nwidth -> j < nheight ->
   transpose (make_move s1 i j) (make_move s2 (nwidth - i.+1) j).
Proof.
move=> /transposeP Ht iLw jLh.
have jLh' : j < nhorizontal by apply: leq_trans jLh _.
apply/transposeP => i1 j1 i1Lw j1Lh.
have /= niLw := (ltn_ord (rev_ord (Ordinal iLw))).
have /= ni1Lw := (ltn_ord (rev_ord (Ordinal i1Lw))).
have [<-|/eqP jDj1] := (j =P j1); last first.
  by rewrite !cell_make_mover -?Ht // jDj1 orbT.
have [<-|/eqP iDi1] := (i =P i1); last first.
  by rewrite !cell_make_mover -?Ht ?iDi1 // eqn_sub2lE // eqSS iDi1.
by rewrite !cell_make_movel.
Qed.

Lemma eval_transpose w1 w2 b1 b2 :
  transpose w1 w2 -> transpose b1 b2 -> eval w1 b1 = eval w2 b2.
Proof.
move:  {-1}(ncells (w1 lor b1)) (refl_equal (ncells (w1 lor b1))).
move=> n; elim: n w1 w2 b1 b2 => /= [|n IH] w1 w2 b1 b2 cE Ht1 Ht2;
   rewrite [LHS]evalS [RHS]evalS -(cwin_transpose _ _ Ht1); case E : cwin => //=.
   rewrite -(has_move_transpose _ _ (transpose_lor _ _ _ _ Ht1 Ht2)).
  by rewrite -(cwin_transpose _ _ Ht2) [in LHS]ifN 1?[in RHS]ifN //;
     have := ncells_has_move (w1 lor b1); rewrite cE; case: has_move.
have Ht3 := transpose_lor _ _ _ _ Ht1 Ht2.
rewrite -(has_move_transpose _ _ Ht3).
case E1: has_move; last by rewrite -(cwin_transpose _ _ Ht2).
pose f i := \max_(j < nheight | cmove (w1 lor b1) i j)  
                 wcomp (eval b1 (make_move w1 i j)).
rewrite -(big_mkord xpredT f) big_nat_rev /= big_mkord /= add0n /f.
apply: eq_bigr => i _.
under [LHS]eq_bigl => j do 
  rewrite -(@cmove_transpose (w2 lor b2)) 1? transpose_sym //.
under [LHS]eq_bigr => /= j Hc.
  have Ht4 : transpose (make_move w2 i j) (make_move w1 (nwidth - i.+1) j)
    by apply: make_move_transpose; rewrite // transpose_sym.
  rewrite -(IH b2 _ _ _ _ _ Ht4); last 2 first.
  have := cE; rewrite (ncells_transpose _ _ Ht3) // (ncells_cmove w2 b2 i j) //.
    by case.
  by rewrite transpose_sym.
  over.
by [].
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
  have := wf_state_opzs _ _ j1Lw Hwf.
  rewrite opzsE' //; case: nlebP => // uLh _.
  apply: leq_trans (_ : j1.+1 * nhorizontal <= _).
    by rewrite mulSn ltn_add2r.
  apply: leq_trans (_ : k1 * nhorizontal <= _); last by apply: leq_addl.
  by rewrite leq_mul2r j1Lk1 orbT.
rewrite big1 //= => i _; rewrite /f.
rewrite divn_small // ltn_exp2l //.
have := wf_state_opzs _ _ (ltn_ord i) Hwf.
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

Lemma get_border_w w b : wf_state (w lor b) -> get_border w b land w = 0.
Proof.
move=> Hwf; apply/is_zero_spec; rewrite is_zeroP; apply/forallP=> /= i.
rewrite land_spec negb_and.
have [/= Hb|//] := boolP (bit _ _).
have Hwidth := wf_state_get_border_width _ _ _ Hwf Hb.
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

Lemma get_borderC w b : get_border w b = get_border b w.
Proof. by rewrite /get_border lorC. Qed.

Lemma get_border_b w b : wf_state (w lor b) -> get_border w b land b = 0.
Proof. by rewrite lorC get_borderC; exact: get_border_w. Qed.

Definition sget_code w b := get_border w b lor w.

Lemma and_imp_add_or x y : x land y = 0 -> x + y = x lor y.
Proof.
move=> /is_zero_spec; rewrite is_zeroP => /forallP /= Axy.
apply/bit_add_or => n Bx By; case/negP: (Axy n).
by rewrite land_spec Bx.
Qed.

Lemma wf_state_up_log2_lt (s : int) (x z : nat) :
   let y := to_nat (up_log2 (get_column s (of_nat x))) in 
    wf_state s -> x < nwidth -> z < nhorizontal -> cell s x z -> z < y.
Proof.
move=> y sWf xLw zLh.
rewrite cell_get_column //.
have := wf_state_opzs _ _ xLw sWf.
rewrite opzsE' => [/andP[/nlebP uLh /eqP->]|]; last by case: nltbP.
rewrite bit_decr; last by apply/nltbP/(leq_trans uLh).
case: nltbP => //.
by rewrite -/y of_natK // (ltn_trans _ nhorizontalLwB).
Qed.

Lemma sget_code_uniq w1 w2 b1 b2 : 
  wf_state (w1 lor b1) -> wf_state (w2 lor b2) -> 
  w1 land b1 = 0 -> w2 land b2 = 0 ->
  sget_code w1 b1 = sget_code w2 b2 -> w1 = w2 /\ b1 = b2.
Proof.
move=> Hwf1 Hwf2 Aw1 Aw2 CE.
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
wlog Hb : w1 w2 b1 b2 Hwf1 Hwf2 Aw1 Aw2 CE Hx / bit (get_border w1 b1) x.
  move=> HW.
  have [Hb1|Hb1] := boolP (bit (get_border w1 b1) x); first by apply: HW.
  apply/sym_equal/HW => //; first by rewrite eq_sym.
  by case: bit Hb1 Hx => //; case: bit.
have Hb2 : ~~  bit (get_border w2 b2) x by case: bit Hx Hb => //; case: bit.
have : bit (sget_code w2 b2) x  by rewrite -CE lor_spec Hb.
  rewrite lor_spec (negPf Hb2) /= => Hbw2.
have iLw := wf_state_get_border_width _ _ _ Hwf1 Hb.
set i := (_ %/ _) in iLw.
pose j := to_nat x %% nhorizontal.
have jLh : j < nhorizontal by apply: ltn_mod.
have xE : x = of_nat i * horizontal + of_nat j.
  by have := of_nat_int_add_mod x horizontal.
pose z2 := to_nat (up_log2 (get_column (w2 lor b2) (of_nat i))).
have z2Lh : z2 < nhorizontal.
  have := wf_state_opzs _ _ iLw Hwf2.
  rewrite opzsE' => [/andP[/nlebP uLh _]|]; last by case: nltbP.
  by apply: leq_ltn_trans uLh _.
have Hcg2 : cell (get_border w2 b2) i z2.
  by rewrite wf_state_up_log2_cell.
have jLz2 : j < z2.
  apply: wf_state_up_log2_lt => //.
  by rewrite cell_lor /cell -xE Hbw2.
have : cell (sget_code w1 b1) i z2 by rewrite CE cell_lor Hcg2.
move: Hb; rewrite xE -[bit _ _ ]/(cell _ _ _) wf_state_up_log2_cell //.
move => /eqP iE.
rewrite cell_lor wf_state_up_log2_cell //.
rewrite -iE (gtn_eqF jLz2) /= => Ciz2.
suff : z2 < j by case: ltngtP jLz2.
rewrite iE.
apply: wf_state_up_log2_lt Hwf1 _ _ _ => //.
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
  apply: leq_ltn_trans whLw.
  by rewrite leq_mul2r (leq_trans (leq_subr _ _ )) // ltnW.
have ijhkE : to_nat (of_nat (i - j.+1) * horizontal + of_nat k) = 
               ((i - j.+1) * nhorizontal + k)%N.
  rewrite to_nat_add ?ijhE ?kE //.
  apply: leq_ltn_trans (_ : (i - j.+1).+1 * nhorizontal < _).
    by rewrite mulSn addnC leq_add2r // ltnW.
  apply: leq_ltn_trans whLw.
  by rewrite leq_mul2r (leq_ltn_trans _ iLw) // (leq_trans (leq_subr _ _)).
case: ltngtP => [iLj|jLi|<-] //; last first.
- rewrite subnn /cell subnn !add_0_l lor_spec.
  rewrite bit_lsl ifT /=; last first.
    by case: nltbP => // [] []; rewrite of_natK.
  rewrite land_spec full_first_column_spec.
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
    by rewrite leq_mul2r ltnS (leq_ltn_trans (leq_subr _ _)).
  rewrite (leq_trans _ (_  : nwidth.+2 * nhorizontal <= _)) //.
    by rewrite leq_mul2r !ltnS ltnW.
  apply: ltn_trans (_ : 2 ^7 < _); first by [].
  by rewrite nwB_pow ltn_exp2l.
rewrite cell_lor cell_land {3}/cell full_first_column_spec.
have : (nhorizontal <= (j - i) * nhorizontal + k).
  apply: leq_trans (leq_addr _ _).
  by rewrite -[X in X <= _]mul1n leq_mul2r subn_gt0 iLj.
have jLw' : j < nwB by apply: ltn_trans nwidthLwB.
have jiE :  to_nat(of_nat (j - i)) = (j - i)%N.
  by rewrite of_natK // (leq_ltn_trans (leq_subr _ _ )).
have jihE : to_nat (of_nat (j - i) * horizontal) = 
               ((j - i) * nhorizontal)%N.
  rewrite to_nat_mul ?jiE //.
  apply: leq_ltn_trans whLw.
  by rewrite leq_mul2r (leq_trans (leq_subr _ _ )) // ltnW.
have jihkE : to_nat (of_nat (j - i) * horizontal + of_nat k) = 
               ((j - i) * nhorizontal + k)%N.
  rewrite to_nat_add ?jihE ?kE //.
  apply: leq_ltn_trans (_ : (j - i).+1 * nhorizontal < _).
    by rewrite mulSn addnC leq_add2r // ltnW.
  apply: leq_ltn_trans whLw.
  by rewrite leq_mul2r (leq_ltn_trans _ jLw) // (leq_trans (leq_subr _ _)).
case: nltbP; rewrite jihkE.
  rewrite ltnNge (leq_trans _ (leq_addr _ _)) // -[X in X <= _]mul1n leq_mul2r.
  by rewrite subn_gt0.
move=> H1 H2; rewrite andbF orbF /cell bit_lsl ifN.
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
by rewrite addnC -mulSn leq_mul2r (leq_ltn_trans (leq_subr _ _)).
Qed.


Lemma transpose_sym_code s : transpose (sym_code nwidth zero s) s.
Proof.
apply/transposeP => i j iLw jLh.
by rewrite symcode_code_rec_cell // ifN // -ltnNge.
Qed.

Lemma get_code_correct w b t h : 
  let: (w1, b1) := if t then (w, b) else (b, w) in
  get_code w b t h = sget_code w1 b1 \/
  transpose (get_code w b t h) (sget_code w1 b1).
Proof.
rewrite /get_code; case: nlebP => _; last first.
  by case: t; left; rewrite /sget_code lorC // get_borderC.
rewrite /FourInARow.min; case: (_ ?= _); first 2 last.
- by case: t; left; rewrite /sget_code lorC // get_borderC.
- by case: t; left; rewrite /sget_code lorC // get_borderC.
case: t; right; rewrite /sget_code lorC ?transpose_sym_code // get_borderC.
by apply: transpose_sym_code.
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
have iE := bit_lsl_first_column_divE _ _ iLw Hb.
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

Lemma lsl_lor s1 s2 i : lsl (s1 lor s2) i = lsl s1 i lor lsl s2 i.
Proof.
apply: bit_ext => j.
by rewrite !(lor_spec, bit_lsl); case: ifP.
Qed.

Lemma lsr_lor s1 s2 i : lsr (s1 lor s2) i = lsr s1 i lor lsr s2 i.
Proof.
apply: bit_ext => j.
by rewrite !(lor_spec, bit_lsr); case: ifP.
Qed.

Lemma land_lor_distrl s1 s2 s3 :
   (s1 lor s2) land s3 =  (s1 land s3) lor (s2 land s3).
Proof.
apply: bit_ext => j.
by rewrite !(lor_spec, land_spec); do 3 case: bit.
Qed.

Lemma lor_eq0 s1 s2 : (s1 lor s2 == 0) = (s1 == 0) && (s2 == 0).
Proof.
apply/eqP/andP => [s1s2_eq0|[/eqP-> /eqP->] //].
suff H s3 s4 : s3 lor s4 = 0 -> s3 = 0.
  (split; apply/eqP); [apply: (H _ s2) => // | apply: (H _ s1)].
  by rewrite lorC.
move=> s3s4_eq0; apply: bit_ext => i.
have := bit_0 i; rewrite -s3s4_eq0 lor_spec.
by do 2 case: bit.
Qed.

Lemma get_column_lor s1 s2 i :
    get_column (s1 lor s2) i = get_column s1 i lor get_column s2 i.
Proof. by rewrite /get_column lsr_lor land_lor_distrl. Qed.

Lemma lornn n : (n lor n) = n.
Proof. by apply: bit_ext => i; rewrite lor_spec; case: bit. Qed.

Lemma wf_state_cmove w b i j : 
  wf_state (w lor b) -> cmove (w lor b) i j -> 
  wf_state (b lor (make_move w i j)).
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
  by apply: leq_ltn_trans xLij (ihjLwh _ _ _ _).
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
have jE : j = to_nat i1 by have := cmoveE _ _ _ Hc; rewrite -xE to_natK.
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

Lemma fmt_rect_corect w b res i cols : 
  wf_state (w lor b) -> 
  (seq.size cols + i = nwidth)%N ->
  (forall j, j < seq.size cols -> 
      nth 0 cols j = lsl first_column (of_nat (j + i) * horizontal)) ->
  (fmt w (get_border w b) cols res == Win) = 
    ((res == Win) ||
     [exists i1 : 'I_nwidth, exists j1 : 'I_nheight, 
      [&& i <= i1, j1 < nheight, cmove (w lor b) i1 j1 & cwin (make_move w i1 j1)]]).
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
have Hf'  j : j < seq.size cols -> nth 0 cols j =
                    lsl  first_column (of_nat (j + i.+1) * horizontal).
  by move=> jLs; rewrite -addSnnS -Hf.
have Hs : (seq.size cols + i.+1)%N = nwidth by rewrite -addSnnS.
have IH' := IH _ Hs Hf'.
case: ifP => Hif1.
  rewrite IH'; congr (_ || _).
  apply/existsP/existsP=> [] [i1 /existsP[j1 /and4P[H1 H2 H3 H4]]].
    exists i1; apply/existsP; exists j1.
    by rewrite (ltnW H1) H2 H3.
  have j1LwB : j1 < nwB by apply: ltn_trans nheightLwB.
  move: H1; case: ltngtP => // [H1|iEi1] _ /=.
    exists i1; apply/existsP; exists j1.
    by rewrite H1 H2 H3.
  rewrite -get_border_correct // -iEi1 in H3.
  suff : cell (get_border w b land c) i j1.
    by have /is_zero_spec-> := Hif1; rewrite cell_0.
  rewrite cell_land H3 Hc /cell bit_lsl ifN.
    rewrite add_comm addK first_column_spec.
    by apply/nltbP; rewrite of_natK // (ltn_trans _ nheightLwB).
  have ihE : to_nat (of_nat i * horizontal) = (i * nhorizontal)%N.
    by rewrite to_nat_mul of_natK // (ltn_trans _ whLw) // ltn_mul2r iLw.
  have ihj1E : to_nat (of_nat i * horizontal + of_nat j1) = 
               (i * nhorizontal + j1)%N.
    rewrite to_nat_add ?ihE ?of_natK //.
    apply: leq_ltn_trans (_ : i.+1 * nhorizontal < _).
      by rewrite mulSn addnC leq_add2r // ltnW // (ltn_trans H2).
    apply: leq_ltn_trans whLw.
    by rewrite leq_mul2r (leq_ltn_trans _ iLw) // (leq_trans (leq_subr _ _)).
  rewrite negb_or; apply/andP; (split; apply/negP) => [/nltbP|/nlebP].
    by rewrite ihj1E ihE ltnNge leq_addr.
  rewrite ihj1E leqNgt (leq_trans (_ : _ < i.+1 * nhorizontal)) //.
    by rewrite mulSn addnC ltn_add2r (leq_trans H2).
  apply: leq_trans (_ : nwidth * nhorizontal <= _) => //.
  by rewrite leq_mul2r iLw.
have /negP/negP := Hif1; rewrite is_zeroNP =>/existsP[/= k kE].
have : bit c k by move: kE; rewrite land_spec; case: bit.
rewrite {1}Hc => /(bit_lsl_first_column_divE _ _ iLw) iE.
have : bit c k by move: kE; rewrite land_spec; case: bit.
rewrite {1}Hc => /(bit_lsl_first_column_mod_lt _ _ iLw) => kLh.
have cM :  cmove (w lor b) i (to_nat k %% nhorizontal).
  rewrite -get_border_correct // iE -bit_cell.
  by move: (kE); rewrite land_spec; case/andP.
have cmE : cwin (make_move w i (to_nat k %% nhorizontal)) = 
       is_won (FourInARow.make_move (get_border w b land c) w).
  rewrite -(is_won_cwin _ b) //; last first.
    by rewrite lorC; apply: wf_state_cmove.
  rewrite /make_move iE -(of_nat_int_add_mod k horizontal) lorC.
  rewrite /FourInARow.make_move.
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
  rewrite Hc => /(bit_lsl_first_column_divE _ _ iLw) // iE'.
  case: (boolP (bit _ _)) => //.
  rewrite bit_cell get_border_correct //; last 2 first.
  - by rewrite -iE'.
  - by move: bck1; rewrite Hc => /(bit_lsl_first_column_mod_lt _ _ iLw).
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
  by rewrite leqnn kLh cM cmE HE.
rewrite IH'; case: eqP => //= _.
apply/existsP/existsP => [] [/= i2 /existsP[j2 /and4P[H1 H2 H3 H4]]]; 
  exists i2; apply/existsP; exists j2; apply/and4P; split => //.
  by apply: ltnW.
move: H1; case: ltngtP => // iEi2.
case/idP: HE; rewrite -cmE iEi2.
rewrite (cmoveE _ _ _ cM) .
-(cmoveE _ _ _ H3).
Search cmove up_log2.





move=> H.

rewrite IH'.
have Hsi1 : (seq.size cols + i.+1)%N = nwidth by rewrite -addSnnS.

have := (orP (IH i.+1 )).

(*
End FindMoves.
*)

 
(*
(* Find possible moves *)
Definition find_moves wstate bstate :=
  let border := get_border wstate bstate in
  fms wstate bstate border columns [::].
*)
(* 

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
*)


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
