From Stdlib Require Import ssreflect ZArith Ascii List String PrimInt63.
From Stdlib Require Import -(notations) PArray.
From Stdlib Require Import Lia.
From mathcomp Require Import all_boot.
From HB Require Import structures.

Import PrimInt63Notations.
Import Uint63Axioms.
Import Uint63.

(* Missing in mathcomp *)

Lemma nat_pow_exp m n : Nat.pow m n = m ^ n.
Proof. by elim: n => //= n ->; rewrite expnS. Qed.

Lemma divE x y : x / y = x %/ y.
Proof.
case: y => // y.
apply/sym_equal/(Nat.div_unique); last first.
  by rewrite Nat.mul_comm; exact: divn_eq.
by apply/ltP; rewrite ltn_mod.
Qed.

Lemma leq_succ_double n : 0 < n -> n < n.*2.
Proof. by case: n => // n _; rewrite -addnn -addn1 leq_add2l. Qed.

Lemma sum_pow2 n : \sum_(i < n) 2 ^ i < 2 ^ n.
Proof.
elim: n => [|n IH]; first by rewrite big_ord0.
by rewrite big_ord_recr /= expnS mul2n -addnn ltn_add2r.
Qed.

Lemma sum_exp_bound j k f : 
  (forall i, i < j -> f i < 2 ^ k) ->
  \sum_(i < j)  (f i) * 2 ^ (i * k)  < 2 ^ (j * k).
Proof.
elim: j => [|j IH] Hi; first by rewrite big_ord0.
rewrite big_ord_recr /= -addSn.
apply: leq_trans (_ : 2 ^ (j * k) + f j * 2 ^ (j * k) <= _).
  by rewrite leq_add2r IH // => i iLj; apply: Hi; rewrite ltnS ltnW.
by rewrite mulSn expnD -mulSn leq_mul2r Hi ?orbT.
Qed.

Lemma sum_rev i (f : nat -> nat) : \sum_(j < i) f j = \sum_(j < i) f (i.-1 - j).
Proof.
rewrite -(big_mkord xpredT) big_nat_rev /= big_mkord.
apply: eq_bigr => /= k _; congr f.
by rewrite add0n /= -[in RHS]subSS prednK //; case: k => /=; case: (i).
Qed.

Lemma subn3 n : (n - 3 = n.-1.-2).
Proof. by case: n => // [] [|[|[]]]. Qed.

Lemma divn_inv i j d : (d * j <= i < d.+1 * j -> i %/ j = d).
Proof.
case: j => [|j /andP[djLi iLdj]]; first by rewrite !muln0 ltn0 andbF.
apply/eqP; rewrite eqn_leq; apply/andP; split; last by rewrite leq_divRL.
by rewrite -ltnS ltn_divLR.
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
  rewrite -[f n - k]prednK ?subn_gt0 //.
  rewrite -modnDmr expnS modnMr addn0.
  apply: IH => j1 k1 /andP[j1Lk1 k1Ln]; apply: f_incr.
  by rewrite j1Lk1 ltnS ltnW.
- rewrite divn_small ?ltn_exp2l // addn0.
  apply: IH => j1 k1 /andP[j1Lk1 k1Ln]; apply: f_incr.
  by rewrite j1Lk1 ltnS ltnW.
rewrite divnn expn_gt0 1?ltnW //= big1 => // i _.
by rewrite divn_small // ltn_exp2l ?f_incr // ltn_ord leqnn.
Qed.

Lemma bool1E b : (nat_of_bool b == 1) = b.
Proof. by case: b. Qed.

Lemma xm1_sum x n : (x ^ n).-1 = (x.-1 * \sum_(i < n) x^ i)%N.
Proof.
have [x_gt1|] := ltnP 1 x; last first.
  case: x => [|[|//]]; first by case: n => //= n; rewrite exp0n.
  by rewrite exp1n.
rewrite -[in RHS]subn1 mulnBl mul1n big_distrr /= -sumnB => [|i _]; last first.
  by rewrite -expnS leq_exp2l.
under eq_bigr do rewrite -expnS.
pose f i := x ^ i.
rewrite -subn1  -[x^ n]/(f n).
have -> : 1%N = f 0%N by rewrite /f expn0.
rewrite -telescope_sumn => [|i j iLj]; first by rewrite big_mkord.
by apply: leq_pexp2l => //; apply: ltn_trans x_gt1.
Qed.

(* 63 Arithmetic *)

Definition one := of_Z 1.
Definition zero := of_Z 0.

Definition decr s := (s - 1)%uint63.
Definition incr s := (s + 1)%uint63.
Definition is_nzero s := negb (eqb s zero).
(* Get the log 2 of a number *)
Definition log2 (v : int) : int :=
  (if v =? 0 then 0 else 62 - head0 v)%uint63.

Module Type nwBT.

Parameter def : nat.
Parameter defE : def = Z.to_nat wB.

End nwBT.

Module nwB : nwBT.

Definition def := Z.to_nat wB.

Lemma defE : def = Z.to_nat wB.
Proof. by []. Qed.

End nwB.

Definition nwB := nwB.def.

Lemma nwBE : nwB = Z.to_nat wB.
Proof. by exact: nwB.defE. Qed.

Lemma wBE : wB = Z.of_nat nwB.
Proof. by rewrite nwBE Z2Nat.id. Qed.

Definition ndigits := to_nat digits.

Lemma nwB_pow : nwB = 2 ^ ndigits.
Proof.
rewrite nwBE Z2Nat.inj_pow => [|//|//].
by rewrite nat_pow_exp; congr (_ ^ _).
Qed.

Lemma ndigitsLwB : ndigits < nwB.
Proof.
apply: leq_ltn_trans (_ : (2 ^ 6) < _); first by [].
by rewrite nwB_pow ltn_exp2l.
Qed.

Lemma nlebP x y : reflect (to_nat x <= to_nat y) (x <=? y)%uint63.
Proof.
have xB := to_Z_bounded x.
have yB := to_Z_bounded y.
apply: (iffP idP)=> [/lebP H|H]; first by apply/leP/Z2Nat.inj_le; lia.
by apply/lebP/Z2Nat.inj_le/leP => //; lia.
Qed.

Lemma nltbP x y : reflect (to_nat x < to_nat y) (x <? y)%uint63.
Proof.
have xB := to_Z_bounded x.
have yB := to_Z_bounded y.
apply: (iffP idP)=> [/ltbP H|H]; first by apply/ltP/Z2Nat.inj_lt; lia.
by apply/ltbP/Z2Nat.inj_lt/ltP => //; lia.
Qed.

Lemma neqbP x y : reflect (to_nat x = to_nat y) (x =? y)%uint63.
Proof.
have xB := to_Z_bounded x.
have yB := to_Z_bounded y.
apply: (iffP idP); first by case: eqbP => [->|].
case: eqbP => // H H1; case: H.
by apply/Z2Nat.inj_iff; lia.
Qed.

Lemma to_nat_0 : to_nat 0 = 0.
Proof. by rewrite to_Z_0. Qed.

Lemma to_nat_1 : to_nat 1 = 1.
Proof. by rewrite to_Z_1. Qed.

Lemma Z_of_nat_exp a b : Z.of_nat (a ^ b) = (Z.of_nat a ^ Z.of_nat b)%Z.
Proof.
elim: b a => // n IH a.
rewrite expnS Nat2Z.inj_mul IH Nat2Z.inj_succ /= Z.pow_succ_r //.
by apply: Zle_0_nat.
Qed.

Lemma Z_of_nat_div a b : Z.of_nat (a %/ b) = (Z.of_nat a / Z.of_nat b)%Z.
case: b => [|b]; first by rewrite divn0 Zdiv_0_r.
have [m] := ubnP a; elim: m a b => // c IH a b aLc.
have [bLa|aLb] := leqP b.+1 a; last first.
  rewrite divn_small ?Z.div_small //.
  by split; [| move/leP : aLb]; lia.
rewrite -(subnK bLa) divnDr // divnn !Nat2Z.inj_add IH; last first.
  by rewrite ltn_subLR // addSnnS (leq_trans aLc) // leq_addl.
by rewrite -{2}(Z.mul_1_l (Z.of_nat b.+1)) (Z_div_plus _ 1%Z).
Qed.

Lemma Z_of_nat_mod a b : Z.of_nat (a %% b) = (Z.of_nat a mod Z.of_nat b)%Z.
Proof.
case : b => [|b]; first by rewrite Zmod_0_r.
have [m] := ubnP a; elim: m a b => // c IH a b aLc.
have [aLb|bLa] := leqP a b.
  rewrite modn_small ?Z.mod_small //.
  by split; [| move/leP : aLb]; lia.
rewrite -(subnK bLa) modnDr IH; last first.
  by rewrite ltn_subLR // addSnnS ltn_addl.
  rewrite Nat2Z.inj_add.
by rewrite -Zplus_mod_idemp_r Z_mod_same_full Z.add_0_r.
Qed.

Lemma to_nat_addW i j : to_nat (i + j) = (to_nat i + to_nat j) %% nwB.
Proof.
have iB := to_Z_bounded i.
have jB := to_Z_bounded j.
apply: Nat2Z.inj; rewrite !Z2Nat.id; last first.
  by have := to_Z_bounded (i + j); lia.
by rewrite add_spec Z_of_nat_mod Nat2Z.inj_add nwBE !Z2Nat.id //; lia.
Qed.

Lemma to_nat_add m n : 
  to_nat m + to_nat n < nwB -> to_nat (m + n) = to_nat m + to_nat n.
Proof. by move=> mnLw; rewrite to_nat_addW modn_small. Qed.

Lemma to_nat_incrW i : to_nat (incr i) = (to_nat i).+1 %% nwB.
Proof. by rewrite to_nat_addW addn1. Qed.

Lemma to_nat_incr i : (to_nat i).+1 < nwB -> to_nat (incr i) = (to_nat i).+1.
Proof. by move=> iLw; rewrite to_nat_add ?addn1. Qed.

Lemma to_nat_bounded n : to_nat n < nwB.
Proof.
have nZ := to_Z_bounded n.
have := to_Z_bounded n.
rewrite nwBE -(Z2Nat.id (to_Z n)); try lia.
rewrite wBE => [] [_ /Nat2Z.inj_lt/ltP].
by rewrite !Nat2Z.id.
Qed.

Lemma to_nat_subW i j : to_nat (i - j) = (nwB + to_nat i - to_nat j) %% nwB.
Proof.
have iB := to_Z_bounded i.
have jB := to_Z_bounded j.
apply: Nat2Z.inj; rewrite !Z2Nat.id; last first.
  by have := to_Z_bounded (i - j); lia.
rewrite sub_spec Z_of_nat_mod Nat2Z.inj_sub; last first.
  apply/leP; apply: leq_trans (ltnW (to_nat_bounded j)) _.
  by apply: leq_addr.
rewrite  Nat2Z.inj_add /Z.sub -Z.add_assoc.
rewrite -[in RHS]Zplus_mod_idemp_l Z_mod_same_full Z.add_0_l.
by rewrite -wBE !Z2Nat.id //; lia.
Qed.

Lemma to_nat_sub m n : 
  to_nat n <= to_nat m -> to_nat m < nwB ->
  to_nat (m - n )= to_nat m - to_nat n.
Proof.
move=> nLm mLw.
rewrite to_nat_subW addnC subDnCA // modnDl modn_small //.
by apply: leq_ltn_trans (leq_subr _ _) mLw.
Qed.

Lemma to_nat_decrW i : to_nat (decr i) = (nwB.-1 + to_nat i) %% nwB.
Proof. by rewrite to_nat_subW subDnCA ?(to_nat_bounded 0) // subn1 addnC. Qed.

Lemma to_nat_decr i : (0 <? i)%uint63 -> to_nat (decr i) = (to_nat i).-1.
Proof. by move=> /nltbP iP; rewrite to_nat_sub ?subn1 // to_nat_bounded. Qed.

Lemma to_nat_oppW m : to_nat (- m) = (nwB - to_nat m) %% nwB.
Proof.
rewrite opp_spec.
have [phi_pos phiB] := to_Z_bounded m.
have -> : (- (to_Z m) mod wB = (wB - (to_Z m)) mod wB)%Z.
  by rewrite -[in RHS]Zminus_mod_idemp_l Z_mod_same_full Z.sub_0_l.
rewrite nwBE -[(_ - _)]Z2Nat.inj_sub //.
apply/Nat2Z.inj.
rewrite Z_of_nat_mod !Z2Nat.id //; first by lia.
suff : (0 <= (wB - (to_Z m)) mod wB < wB)%Z by lia.
by apply: Z.mod_pos_bound; lia.
Qed.

Lemma of_natK n : n < nwB -> to_nat (of_nat n) = n.
Proof.
move => nLw.
rewrite of_Z_spec Z.mod_small ?Nat2Z.id //.
split; first apply: Zle_0_nat.
by rewrite wBE; apply/inj_lt/ltP.
Qed.

Lemma to_natK i : of_nat (to_nat i) = i.
Proof.
rewrite Z2Nat.id ?of_to_Z //.
by have := to_Z_bounded i; lia.
Qed.

Lemma to_nat_inj i j : to_nat i = to_nat j -> i = j.
Proof. by move=> iEj; rewrite -[i]to_natK iEj to_natK. Qed.

Lemma int_add_mod i j : (i = i / j * j + i mod j)%uint63.
Proof.
have iB := to_Z_bounded i.
have jB := to_Z_bounded j.
apply: to_Z_inj.
rewrite add_spec mul_spec div_spec mod_spec.
by rewrite Zplus_mod_idemp_l Z.mul_comm -Z_div_mod_eq_full Z.mod_small.
Qed. 

Lemma mul_0_l i : (0 * i = 0)%uint63.
Proof.
apply: to_Z_inj.
by rewrite mul_spec Z.mul_0_l Z.mod_0_l.
Qed.

Lemma mul_1_l i : (1 * i = i)%uint63.
Proof.
apply: to_Z_inj.
rewrite mul_spec Z.mul_1_l Z.mod_small //; apply: to_Z_bounded.
Qed.

Lemma add_0_l i : (0 + i = i)%uint63.
Proof.
apply: to_Z_inj.
by rewrite add_spec Z.add_0_l Z.mod_small //; apply: to_Z_bounded.
Qed.

Notation "t .[ i <- a ]" := (set t i a)
  (at level 1, left associativity, format "t .[ i <- a ]").

Lemma nlength_set {A : Type} (t : array A) i a : length t.[ i <- a ] = length t.
Proof. by rewrite length_set. Qed.

Lemma Z_of_nat_sub m n :
  n <= m -> Z.of_nat (m - n) = (Z.of_nat m - Z.of_nat n)%Z.
Proof. by move=> nLm; rewrite Nat2Z.inj_sub //; apply/leP. Qed.

Lemma Z_of_nat_add m n :
  Z.of_nat (m + n) = (Z.of_nat m + Z.of_nat n)%Z.
Proof. by rewrite Nat2Z.inj_add. Qed.

Lemma Z_of_nat_mul m n : Z.of_nat (m * n) = (Z.of_nat m * Z.of_nat n)%Z.
Proof. by rewrite Nat2Z.inj_mul. Qed.

Lemma to_nat_mulW i j : to_nat (i * j) = (to_nat i * to_nat j) %% nwB.
Proof.
have iB := to_Z_bounded i.
have jB := to_Z_bounded j.
apply: Nat2Z.inj; rewrite !Z2Nat.id; last first.
  by have := to_Z_bounded (i * j); lia.
rewrite mul_spec Z_of_nat_mod Nat2Z.inj_mul nwBE !Z2Nat.id //; lia.
Qed.

Lemma to_nat_mul m n : 
  to_nat m * to_nat n < nwB -> to_nat (m * n) = to_nat m * to_nat n.
Proof. by move=> mnLw; rewrite to_nat_mulW modn_small. Qed.

Lemma to_nat_lslW x p : to_nat (lsl x p) = (to_nat x * 2 ^ to_nat p) %% nwB.
Proof.
have xB := to_Z_bounded x.
have pB := to_Z_bounded p.
rewrite lsl_spec; apply: Nat2Z.inj.
rewrite Z_of_nat_mod nwBE !Z2Nat.id //; last by apply: Z_mod_nonneg_nonneg; lia.
by rewrite Nat2Z.inj_mul Z_of_nat_exp !Z2Nat.id; lia.
Qed.

Lemma to_nat_div x y : to_nat (x / y) = to_nat x %/ to_nat y.
Proof.
have xB := to_Z_bounded x; have yB := to_Z_bounded y.
rewrite div_spec.
apply: Nat2Z.inj.
by rewrite Z_of_nat_div !Z2Nat.id //; try apply: Z_div_nonneg_nonneg; lia.
Qed.

Lemma to_nat_lsr x p : to_nat (lsr x p) = to_nat x %/ 2 ^ to_nat p.
Proof.
have xB := to_Z_bounded x.
have pB := to_Z_bounded p.
rewrite -divE lsr_spec; apply: Nat2Z.inj.
rewrite Nat2Z.inj_div Z_of_nat_exp !Z2Nat.id //; try lia.
by apply: Z_div_nonneg_nonneg; lia.
Qed.

Lemma to_nat_mod i j : to_nat (i mod j) = to_nat i %% to_nat j.
Proof.
have iB := to_Z_bounded i.
have jB := to_Z_bounded j.
apply: Nat2Z.inj.
rewrite mod_spec Z_of_nat_mod !Z2Nat.id; try lia.
by apply: Z_mod_nonneg_nonneg; lia.
Qed.

Lemma eq_int : Equality.axiom Uint63.eqb.
Proof.
move=> x y.
by apply: (iffP idP) => [/eqb_spec//|->]; apply: eqb_refl.
Qed.

HB.instance Definition _ := hasDecEq.Build int eq_int.

Lemma eqb_eqb (i j : int) : (i =? j)%uint63 = (i == j).
Proof.
case: (_ =P _) => [->|]; case: eqbP; try lia.
by move=> iEj []; apply: to_Z_inj.
Qed.

Lemma neq_eqE m1 m2 : (m1 =? m2)%uint63 = (m1 == m2).
Proof. by apply/neqbP/eqP => [/to_nat_inj|->//]. Qed.

Definition int_enum := map (fun x => of_nat x) (iota 0 nwB).

Lemma int_enum_uniq : uniq int_enum.
Proof.
rewrite map_inj_in_uniq; first by apply: iota_uniq.
move=> /= i j; rewrite !mem_iota !add0n => iB jB ijE.
by rewrite -(of_natK i iB) ijE of_natK.
Qed.

Lemma mem_int_enum i : i \in int_enum.
Proof.
apply/mapP; exists (to_nat i).
rewrite mem_iota add0n; first by exact: to_nat_bounded.
rewrite Z2Nat.id ?of_to_Z //.
by have := to_Z_bounded i; lia.
Qed.

Lemma int_pcancel : pcancel (fun i => to_nat i) 
                      (fun n => if n < nwB then Some (of_nat n) else None).
Proof.
move=> x; rewrite to_natK; case: leqP => //; rewrite leqNgt.
by case/negP; apply: to_nat_bounded.
Qed.

HB.instance Definition _ := Countable.copy int
  (pcan_type int_pcancel).

HB.instance Definition _ := isFinite.Build int
  (Finite.uniq_enumP int_enum_uniq mem_int_enum).

Lemma is_zero_0 : is_zero 0.
Proof. by apply/is_zero_spec. Qed.

Lemma is_zeroP i : is_zero i = [forall j, ~~ bit i j].
Proof.
apply/idP/forallP => /= [/is_zero_spec-> j|Fi]; first by rewrite bit_0.
apply/is_zero_spec/bit_ext => j.
by rewrite (negPf (Fi j)) bit_0.
Qed.

Lemma is_zeroNP i : ~~ is_zero i = [exists j, bit i j].
Proof. 
by rewrite is_zeroP negb_forall; 
   apply/existsP/existsP => [[j Hj]|[j Hj]]; exists j; case: bit Hj.
Qed.

Definition olor x y := (x lor y)%uint63 .

Lemma lorC x y :  (x lor y)%uint63 = (y lor x)%uint63.
Proof. by apply: bit_ext => i; rewrite !lor_spec orbC. Qed.

Lemma lorA  x y z : (x lor (y lor z))%uint63 = (x lor y lor z)%uint63.
Proof. by apply: bit_ext => i; rewrite !lor_spec orbA. Qed.

Lemma lor0n  x : (0 lor x)%uint63 = x.
Proof. by apply: bit_ext => i; rewrite lor_spec bit_0. Qed.

HB.instance Definition _ :=
  Monoid.isComLaw.Build int 0%uint63 olor lorA lorC lor0n.

Lemma laddC : commutative add.
Proof.
by move=> x y; apply: to_nat_inj; rewrite to_nat_addW addnC -to_nat_addW.
Qed.

Lemma laddA : associative add.
Proof. 
move=> x y z; apply: to_nat_inj.
by rewrite 2! to_nat_addW modnDmr addnA -modnDml -!to_nat_addW.
Qed.

Lemma ladd0n : left_id 0%uint63 add.
Proof.
move=> x; apply: to_nat_inj; rewrite to_nat_addW add0n modn_small //.
by apply: to_nat_bounded.
Qed.

HB.instance Definition _ :=
  Monoid.isComLaw.Build int 0%uint63 add laddA laddC ladd0n.

Lemma big_bit_lor (P : nat -> bool) (f : nat -> int) j n : 
  bit (\big[olor/0%uint63]_(i < n | P (i : nat)) f (i : nat)) j = 
  \big[orb/false]_(i < n | P i) bit (f i) j.
Proof.
rewrite [in LHS]big_mkcond [in RHS]big_mkcond.
elim: n => [|n IH]; first by rewrite !big_ord0 bit_0.
rewrite !big_ord_recr /= lor_spec IH.
by case: (P _); rewrite ?bit_0.
Qed.

Lemma to_nat_split x : to_nat x = to_nat (x >> 1) * 2 + to_nat (bit x 0).
Proof.
rewrite to_Z_split !(Z2Nat.inj_add, Z2Nat.inj_mul) //.
- by have := to_Z_bounded (x >> 1); lia.
- by have := to_Z_bounded (x >> 1); lia.
by have := to_Z_bounded (bit x 0); lia.
Qed.

Lemma to_nat_sum x : to_nat x = \sum_(i < ndigits) bit x (of_nat i) * 2 ^ i.
Proof.
have := to_nat_bounded x.
elim: nwB x => // n IH x H.
have [xE0|xNE0] := to_nat x =P 0.
  have -> : x = 0%uint63 by apply: to_nat_inj.
  by rewrite big1 //= => i _; rewrite bit_0.
have x_pos : (0 < to_nat x)%nat by case: (to_nat x) xNE0.
rewrite to_nat_split (IH (lsr x 1)); last first.
  rewrite to_nat_lsr expn1 ltn_divLR // (leq_trans H _) //.
  rewrite muln2 -addnn -[X in X < _]add0n ltn_add2r.
  case: (n) H => //.
  by rewrite ltnS leqNgt x_pos.
rewrite -[ndigits in RHS]/ndigits.-1.+1.
rewrite [in RHS]big_ord_recl muln1 addnC; congr (_ + _).
  by case: bit.
rewrite -[ndigits in LHS]/ndigits.-1.+1.
rewrite big_distrl /= big_ord_recr /=.
have -> : bit (x >> 1) (of_pos 62) = false.
  by rewrite bit_lsr /= bit_M.
rewrite addn0; apply: eq_bigr => i _.
rewrite -mulnA; congr (_ * _); last by rewrite mulnC expnS.
rewrite -[of_pos _]/((of_nat (lift ord0 i))).
have iLwB : i < nwB.
  apply: (ltn_trans (ltn_ord _)).
  apply/ltP/Nat2Z.inj_lt.
  by rewrite nwBE Z2Nat.id.
have ipE : to_nat (1 + of_nat i) = i.+1.
  rewrite to_nat_add 1?of_natK //.
  rewrite add1n (leq_trans (_ : _ < 63)) //; first by rewrite ltnS.
  apply/ltP/Nat2Z.inj_lt.
  by rewrite nwBE Z2Nat.id.
rewrite bit_lsr; case: nlebP; last first.
  by rewrite ipE 1?of_natK.
move=> _; congr bit.
apply: to_nat_inj.
rewrite ipE of_natK //.
have := to_nat_bounded (1 + of_nat i).
by rewrite ipE.
Qed.

Lemma to_nat_add_lor x y :
  (forall n : int, bit x n = true -> bit y n = true -> False) ->
  to_nat (x + y) = to_nat x + to_nat y.
Proof.
move=> H.
have -> : (x + y = x lor y)%uint63 by apply/bit_add_or.
rewrite !to_nat_sum -big_split /=.
apply: eq_bigr => /= i _.
rewrite lor_spec.
case: bit (H (of_nat i)); case: bit => //; first by case.
by rewrite addn0.
Qed.

Lemma to_nat_lor_add x y :
  (forall n : int, bit x n = true -> bit y n = true -> False) ->
  to_nat (x lor y) = to_nat x + to_nat y.
Proof.
move=> H.
by case: (bit_add_or x y) => <-  // _; apply: to_nat_add_lor.
Qed.

Lemma big_lor_add n (P : nat -> bool) (f : nat -> int) : 
  (forall j k l,  j < n -> k < n -> P j -> P k -> 
     bit (f j) l = true -> bit (f k) l = true -> j = k) ->
  (\big[add/0%uint63]_(i < n | P i) f i) = 
   \big[olor/0%uint63]_(i < n | P i) f i.
Proof.
rewrite [in LHS]big_mkcond [in RHS]big_mkcond.
elim: n => [|n IH] H; first by rewrite !big_ord0.
rewrite !big_ord_recr /= /olor IH; last first.
  by move=> j k l jLn kLn; apply: H; rewrite ltnS ltnW.
apply/bit_add_or => i /=.
rewrite -big_mkcond big_bit_lor big_mkcond => Hi Hbi.
case E : (P _) Hbi => // Hbi; last by rewrite bit_0 in Hbi.
have [/existsP[ /= j /andP[Pn Hj]]|/existsPn /= Hj]:= 
     boolP [exists j : 'I_n, P j && bit (f j) i].
  suff nE : n = j by have := ltn_ord j; rewrite -nE ltnn.
  apply: (H _ _ i) => //.
  by rewrite ltnS ltnW.
rewrite big1 //= in Hi.
move=> k _; case E1 : (P _) => //.
by have := Hj k; rewrite E1 andTb; case: bit.
Qed.

Lemma to_nat_lor_exclude n (P : nat -> bool) (f : nat -> int) : 
  (forall j k l,  j < n -> k < n -> P j -> P k -> 
     bit (f j) l = true -> bit (f k) l = true -> j = k) ->
  to_nat (\big[olor/0%uint63]_(i < n | P i) f i) = 
  \sum_(i < n | P i) to_nat (f i).
Proof.
rewrite [in LHS]big_mkcond [in RHS]big_mkcond.
elim: n => [|n IH] H; first by rewrite !big_ord0.
rewrite !big_ord_recr /= {1}/olor /= to_nat_lor_add.
  congr (_ + _); last by case: (P n).
  by apply: IH => j k l hLn kLn; apply: H; rewrite ltnS ltnW.
move=> i.
rewrite (big_bit_lor xpredT (fun i : nat => (if P i then f i else 0%uint63))).
case E : (P n); last by rewrite bit_0.
move=> H1 H2.
have [/existsP[ /= j /andP[Pn Hj]]|/existsPn /= Hj] := 
     boolP [exists j : 'I_n, P j && bit (f j) i].
  suff nE : n = j by have := ltn_ord j; rewrite -nE ltnn.
  apply: (H _ _ i) => //.
  by rewrite ltnS ltnW.
rewrite big1 // in H1.
move=> j _.
case: (P j) (Hj j); last by rewrite bit_0.
by case: bit.
Qed.

Lemma to_nat_add_exclude n (P : nat -> bool) (f : nat -> int) : 
  (forall j k l,  j < n -> k < n -> P j -> P k -> 
     bit (f j) l = true -> bit (f k) l = true -> j = k) ->
  to_nat (\big[add/0%uint63]_(i < n | P i) f i) = 
  \sum_(i < n | P i) to_nat (f i).
Proof.
move=> H.
by rewrite big_lor_add // to_nat_lor_exclude.
Qed.

Lemma to_nat_head0 x : 
  0 < to_nat x-> nwB %/ 2 <= 2 ^ (to_nat (head0 x)) * to_nat x < nwB.
Proof.
move=> xP.
have [xzP _] := to_Z_bounded x.
have [hxzP _]:= to_Z_bounded (head0 x).
have [|L1 L2] := head0_spec x.
  rewrite -[0%Z]/(to_Z 0).
  by apply/Z2Nat.inj_lt/ltP; have [] := to_Z_bounded x.
apply/andP; split.
- apply/leP/Nat2Z.inj_le.
  by rewrite Z_of_nat_div -wBE Z_of_nat_mul Z_of_nat_exp !Z2Nat.id.
apply/ltP/Nat2Z.inj_lt.
by rewrite -wBE Z_of_nat_mul Z_of_nat_exp !Z2Nat.id.
Qed.

Lemma to_nat_lsl_one i :
  to_nat i < ndigits-> to_nat (lsl one i) = 2 ^ to_nat i.
Proof.
move=> iLd.
by rewrite to_nat_lslW mul1n modn_small // nwB_pow ltn_exp2l.
Qed.

Lemma head0_digits x : (head0 x <=? digits)%uint63.
Proof.
have [->//|x_pos]:= x =P 0%uint63.
have x_tpos : 0 < to_nat x.
  rewrite ltnNge; apply/negP => H; case: x_pos.
  by apply/to_nat_inj; case: (to_nat _) H.
apply/nlebP.
rewrite -(leq_exp2l _ _ (isT : 1 < 2)) -nwB_pow.
apply: leq_trans (leq_pmulr _ x_tpos) (ltnW _).
by have /andP[_] := (@to_nat_head0 x x_tpos).
Qed.

Lemma head0_pos_digits x : 0 < to_nat x -> (head0 x <? digits)%uint63.
Proof.
move=> x_tpos; apply/nltbP.
rewrite -(ltn_exp2l _ _ (isT : 1 < 2)) -nwB_pow.
apply: leq_ltn_trans (leq_pmulr _ x_tpos) _.
by have /andP[_] := (@to_nat_head0 x x_tpos).
Qed.

Lemma log2_0 : log2 0 = 0%uint63.
Proof.  by []. Qed.

Lemma log2_digits x : (log2 x <? digits)%uint63.
Proof.
have H62 := to_nat_bounded 62.
rewrite /log2; case: neqbP => [//|x_pos].
apply/nltbP.
rewrite to_nat_sub //; first by rewrite (leq_ltn_trans (leq_subr _ _)).
rewrite -ltnS -[(to_nat 62).+1]/(to_nat digits).
apply/nltbP/head0_pos_digits.
by case: (to_nat _) x_pos.
Qed.

Lemma ltn_log2 x : to_nat x < 2 ^ (to_nat (log2 x)).+1.
Proof.
rewrite /log2; case: (neqbP x) => [/to_nat_inj -> //|x_D].
have x_tpos : 0 < to_nat x by case: (to_nat _) x_D.
have hL62 : to_nat (head0 x) <= to_nat 62.
  by have /nltbP := head0_pos_digits _ x_tpos.
rewrite to_nat_sub //; last by apply: leq_trans ndigitsLwB.
rewrite -(ltn_pmul2l (_ : 0 < 2 ^ (to_nat (head0 x)))); last by rewrite expn_gt0.
rewrite -expnD addnS addnC subnK //.
by have /andP[] := to_nat_head0 _ x_tpos; rewrite nwB_pow.
Qed.

Lemma leq_log2 x : 0 < to_nat x -> 2 ^ to_nat (log2 x) <= to_nat x.
Proof.
rewrite /log2; case: (neqbP x) => [|_ x_tpos]; first by case: (to_nat _).
have hL62 : to_nat (head0 x) <= to_nat 62.
  by have /nltbP := head0_pos_digits _ x_tpos.
rewrite to_nat_sub //; last by apply: leq_trans ndigitsLwB.
rewrite -(leq_pmul2l (_ : 0 < 2 ^ (to_nat (head0 x)))); last by rewrite expn_gt0.
rewrite -expnD addnC subnK //.
suff -> : 2 ^ to_nat 62 = nwB %/2.
  by have /andP[] := to_nat_head0 _ x_tpos; rewrite nwB_pow.
rewrite nwB_pow -[ndigits]/63 expnS mul2n divn2.
by rewrite -[_.*2]add0n (half_bit_double _ false).
Qed.

Lemma log2E x y : 2 ^ to_nat y <= to_nat x < 2 ^ (to_nat y).+1 -> log2 x = y.
Proof.
case: (neqbP x 0) => [-> //|x_D].
  by rewrite leqNgt => /andP[/negP[]]; rewrite expn_gt0.
move=> /andP[yLx xLy];  have x_tpos : 0 < to_nat x by case: (to_nat _) x_D.
apply: to_nat_inj; case: (ltngtP (to_nat (log2 x)) (to_nat y)) => // [xLy'|yLx'].
  move: yLx; rewrite leqNgt => /negP[].
  by rewrite (leq_trans (ltn_log2 _)) // leq_pexp2l.
 move: xLy; rewrite ltnNge => /negP[].
by rewrite (leq_trans _ (leq_log2 _ x_tpos)) // leq_pexp2l.
Qed.

Definition up_log2 i := if i == 0%uint63 then 0%uint63 else incr (log2 i).

Lemma ltn_up_log2 x : to_nat x < 2 ^ (to_nat (up_log2 x)).
Proof.
rewrite /up_log2; case: eqP => [-> //|x_neq0].
rewrite to_nat_incr.
apply: ltn_log2.
apply: leq_trans (_ : ndigits.+1 <= _).
  by rewrite ltnS; apply/nltbP/log2_digits.
by have := to_nat_bounded digits.
Qed.

Lemma leq_up_log2 x : 0 < to_nat x -> 2 ^ (to_nat (up_log2 x)).-1 <= to_nat x.
Proof.
rewrite /up_log2; case: eqP => [->//|xD x_pos].
rewrite to_nat_incr ?leq_log2 //=.
apply: leq_trans (_ : ndigits.+1 <= _).
  by rewrite ltnS; apply/nltbP/log2_digits.
by have := to_nat_bounded digits.
Qed.

Lemma head0_lt i : i <> 0%uint63 -> (head0 i <? digits)%uint63.
Proof.
have iB := to_Z_bounded i.
move=> iD0.
case: ltbP => // /Z.nlt_ge dLh.
have iP : (0 < to_Z i)%Z.
  suff : (to_Z i <> 0)%Z by lia.
  by contradict iD0; apply: to_Z_inj; rewrite to_Z_0. 
have F1 : (2 ^ (to_Z (head0 i)) * to_Z i < wB)%Z.
  by have := head0_spec _ iP; lia.
have F2 : (2 ^ to_Z (head0 i) < wB)%Z by nia.
suff : (wB <= 2 ^ to_Z (head0 i))%Z by lia.
apply: Z.pow_le_mono_r; try lia.
by rewrite -[IntDef.Z.of_nat size]/(to_Z digits); lia.
Qed.
Lemma minus_addE m n : (m - n = m + (- n))%uint63.
Proof.
apply: to_nat_inj; rewrite to_nat_addW to_nat_subW.
rewrite -addnBAC; last by apply/ltnW/to_nat_bounded.
by rewrite to_nat_oppW modnDmr addnC.
Qed.

Lemma mul_N1_l m : ((-(1)) * m = - m)%uint63.
Proof.
apply: to_nat_inj.
rewrite to_nat_mulW to_nat_oppW modnMml.
rewrite [RHS]to_nat_oppW.
rewrite mulnBl mul1n.
have := to_nat_bounded m.
case: (to_nat m) => [|k kLwB]; first by rewrite !subn0 muln0 modnn mod0n.
rewrite mulnS -addnBAC; last by rewrite ltnW.
by rewrite -modnDmr modnMr addn0.
Qed.

Lemma mul_add_distr_r n m p : ((n + m) * p = n * p + m * p)%uint63.
Proof.
apply: to_nat_inj.
rewrite to_nat_mulW to_nat_addW modnMml mulnDl [RHS]to_nat_addW.
by rewrite to_nat_mulW modnDml to_nat_mulW modnDmr.
Qed.

Lemma mul_add_distr_l n m p : (n * (m + p) = n * m + n * p)%uint63.
Proof.
apply: to_nat_inj.
rewrite to_nat_mulW to_nat_addW modnMmr mulnDr [RHS]to_nat_addW.
by rewrite -modnDml -to_nat_mulW -modnDmr -to_nat_mulW.
Qed.

Lemma mul_comm m n : (m * n = n * m)%uint63.
Proof. by apply: to_nat_inj; rewrite to_nat_mulW mulnC -to_nat_mulW. Qed.

Lemma mul_assoc m n p : (m * (n * p)  = m * n * p)%uint63.
Proof.
by apply: to_nat_inj; rewrite 4!to_nat_mulW modnMml modnMmr mulnA.
Qed.

Lemma add_opp m : (m + - m = 0)%uint63.
Proof.
apply: to_nat_inj.
rewrite to_nat_addW to_nat_oppW modnDmr addnC subnK ?modnn //.
by apply/ltnW/to_nat_bounded.
Qed.

Definition Ring_int:  ring_theory 0%uint63 1%uint63 add mul sub opp (@eq int).
split => [||||||||].
- by apply: add_0_l.
- by apply: add_comm.
- by apply: add_assoc.
- by apply: mul_1_l.
- by apply: mul_comm.
- by apply: mul_assoc.
- by apply: mul_add_distr_r.
- by apply: minus_addE.
apply: add_opp.
Defined.

Add Ring int : Ring_int.

Lemma is_zeronE n : is_zero n = (to_nat n == 0).
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

Lemma bit_decr i j : 
  (j <? digits)%uint63 -> bit (decr (lsl one j)) i = (i <? j)%uint63.
Proof.
case: nltbP => // => jLs _.
have iLw := to_nat_bounded i.
have jLw := to_nat_bounded j.
have tpi_gt0 : 0 < 2 ^ to_nat i by rewrite expn_gt0.
have tpj_gt0 : 0 < 2 ^ to_nat j by rewrite expn_gt0. 
rewrite bitE to_nat_decr; last first.
  by apply/nltbP; rewrite to_nat_lsl_one.
rewrite to_nat_lsl_one //.
have [iLj|/negP] := nltbP; last first.
  rewrite -leqNgt => jLi.
  by rewrite divn_small // prednK ?expn_gt0 // leq_exp2l.
rewrite -[X in X %% _ == _]add0n.
have {1}<- : 2 %% 2 = 0 by rewrite modnn.
rewrite modnDml -divnMDl // mul2n -addnn.
rewrite -{1}[2 ^ to_nat i]prednK ?expn_gt0 // !addSn -addnS prednK ?expn_gt0 //.
rewrite -(subnK (ltnW iLj)) expnD -addnA -mulSn addnC divnMDl //.
rewrite divn_small ?ltn_predL ?expn_gt0 //; last first.
rewrite addn0 -[(_ - _)%N]prednK ?subn_gt0 // expnS.
by rewrite -addn1 -modnDml modnMr .
Qed.

Lemma lsl_add_distl x m n :
  to_nat n + to_nat m < nwB -> lsl x (m + n) = lsl (lsl x m) n.
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
  to_nat n + to_nat m < nwB -> lsr x (m + n) = lsr (lsr x m) n.
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
  to_nat x * 2 ^ (to_nat m) < nwB -> (n <=? m)%uint63 ->
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
  to_nat x * 2 ^ (to_nat m) < nwB -> (m <=? n)%uint63 ->
  lsr (lsl x m) n = lsr x (n - m).
Proof.
move=> xLw /nlebP mLn; apply: to_nat_inj.
rewrite [LHS]to_nat_lsr [in LHS]to_nat_lslW modn_small //.
rewrite -(subnK mLn) expnD [X in _ %/ X]mulnC divnMA mulnK ?expn_gt0 //.
by rewrite [RHS]to_nat_lsr to_nat_sub // to_nat_bounded.
Qed.

Lemma bit_le i j : (i <? (lsl one j))%uint63 -> bit i j = false.
Proof.
have iB := to_nat_bounded i.
case: nltbP => //.
have [jLd|dLj] := ltnP (to_nat j) ndigits; last first.
  by rewrite bit_M //; apply/nlebP.
rewrite to_nat_lsl_one // => iLj.
by rewrite bitE // divn_small.
Qed.

Lemma land_power2 i k :
  (k <? digits -> i land (decr (lsl one k)) = i mod (lsl one k))%uint63.
Proof.
have iLw := to_nat_bounded i.
have kLw := to_nat_bounded k.
case: nltbP => // kLd _.
apply: bit_ext => j.
have jLw := to_nat_bounded j.
rewrite land_spec bit_decr; last by case: nltbP.
case: nltbP => [jLk|/negP]; rewrite ?(andbT, andbF); last first.
  rewrite -leqNgt => kLj.
  have [jLd|dLj] := ltnP (to_nat j) ndigits; last first.
    by rewrite bit_M //; apply/nlebP. 
  apply/sym_equal/bit_le.
  apply/nltbP.
  rewrite to_nat_mod to_nat_lsl_one; last by apply: leq_ltn_trans jLd.
  rewrite to_nat_lsl_one //.
  case: (ltngtP (to_nat k)) kLj => // [kLj|<-] _.
    apply: ltn_trans (ltn_pmod _ _) _; first by apply: expn_gt0.
    by rewrite ltn_exp2l.
  by apply: ltn_pmod; rewrite expn_gt0.
rewrite /bit.
congr (~~ is_zero _); apply: to_nat_inj.
have d1E : to_nat (digits - 1) = ndigits.-1.
  by rewrite to_nat_sub ?subn1 // ndigitsLwB.
rewrite 2!to_nat_lslW d1E 2!to_nat_lsr to_nat_mod to_nat_lsl_one; last by [].
rewrite {1}(divn_eq (to_nat i) (2 ^ to_nat k)).
rewrite -{2}(subnK jLk) expnD expnS 2!mulnA divnMDl ?expn_gt0 //.
by rewrite mulnDl -mulnA -expnS prednK // -nwB_pow modnMDl.
Qed.

Lemma addK m n : ((m + n) - n = m)%uint63.
Proof. ring. Qed.

Lemma subK m n : ((m - n) + n = m)%uint63.
Proof. ring. Qed.

Lemma incrK m : (decr (incr m) = m)%uint63.
Proof. by apply: addK. Qed.

Lemma decrK m : (incr (decr m) = m)%uint63.
Proof. by apply: subK. Qed.

Lemma up_log2E x y : 
  2 ^ (to_nat y).-1 <= to_nat x < 2 ^ (to_nat y) -> up_log2 x = y.
Proof.
rewrite /up_log2; case: eqP => [->|xDz]; first by rewrite leqNgt expn_gt0.
case: nltbP (to_nat_decr y); last by case: (to_nat y) => //=; case: (to_nat x).
move=> y_gt0 He Hx.
by rewrite -[y]decrK; congr incr; apply: log2E; rewrite He // prednK.
Qed.

Lemma bit_onenn m n : 
  (m <? digits)%uint63 -> (n <? digits)%uint63 -> bit (lsl one m) n = (m == n).
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

Lemma and_imp_add_or x y : (x land y = 0 -> x + y = x lor y)%uint63.
Proof.
move=> /is_zero_spec; rewrite is_zeroP => /forallP /= Axy.
apply/bit_add_or => n Bx By; case/negP: (Axy n).
by rewrite land_spec Bx.
Qed.

Lemma lsl_lor s1 s2 i : (lsl (s1 lor s2) i = lsl s1 i lor lsl s2 i)%uint63.
Proof.
apply: bit_ext => j.
by rewrite !(lor_spec, bit_lsl); case: ifP.
Qed.

Lemma lsr_lor s1 s2 i : (lsr (s1 lor s2) i = lsr s1 i lor lsr s2 i)%uint63.
Proof.
apply: bit_ext => j.
by rewrite !(lor_spec, bit_lsr); case: ifP.
Qed.

Lemma land_lor_distrl s1 s2 s3 :
   ((s1 lor s2) land s3 =  (s1 land s3) lor (s2 land s3))%uint63.
Proof.
apply: bit_ext => j.
by rewrite !(lor_spec, land_spec); do 3 case: bit.
Qed.

Lemma lor_eq0 s1 s2 : ((s1 lor s2 == 0) = (s1 == 0) && (s2 == 0))%uint63.
Proof.
apply/eqP/andP => [s1s2_eq0|[/eqP-> /eqP->] //].
suff H s3 s4 : (s3 lor s4 = 0 -> s3 = 0)%uint63.
  (split; apply/eqP); [apply: (H _ s2) => // | apply: (H _ s1)].
  by rewrite lorC.
move=> s3s4_eq0; apply: bit_ext => i.
have := bit_0 i; rewrite -s3s4_eq0 lor_spec.
by do 2 case: bit.
Qed.

Lemma ltn_bit v n : n < ndigits ->
  (forall i, n <= to_nat i -> bit v i = false) -> to_nat v < 2 ^ n.
Proof.
move=> nLd Hf.
have nLw : n < nwB by apply: ltn_trans nLd ndigitsLwB.
suff lsrE0 : ((lsr v (of_nat n)) = 0)%uint63.
  rewrite (divn_eq (to_nat v) (2 ^ n)) -{1}(of_natK n) // -to_nat_lsr lsrE0.
  by rewrite mul0n add0n ltn_mod expn_gt0.
apply: bit_ext => k.
rewrite bit_0 bit_lsr; case: nlebP => // kLnk.
rewrite Hf //.
have kLw : to_nat k < nwB by apply: to_nat_bounded.
move: kLnk; rewrite to_nat_addW of_natK ?(ltn_trans nLd ndigitsLwB) //.
have [nkLw|wLnk] := ltnP (n + to_nat k) nwB.
  by rewrite modn_small ?leq_addr.
rewrite -(subnK wLnk) modnDr modn_small; last first.
  by rewrite ltn_subLR // (ltn_trans (_ : _ < n + nwB)) // 
              (ltn_add2r, ltn_add2l).
by rewrite !leq_subRL // leq_add2r leqNgt nLw.
Qed.

Lemma bit_false_lt a i j : i <= to_nat j -> to_nat a < 2 ^ i -> bit a j = false.
Proof.
move=> iLj aLi.
have [jLd|dLj] := ltnP (to_nat j) ndigits; last first.
  by rewrite bit_M //; apply/nlebP.
apply/bit_le/nltbP.
by rewrite to_nat_lsl_one // (leq_trans aLi) // leq_exp2l.
Qed.

Lemma to_nat_lor_bound a b i : 
  to_nat a < 2 ^ i -> to_nat b < 2 ^ i -> to_nat (a lor b) < 2 ^ i.
Proof.
move=> aLi bLi; have [iLd|dLi] := ltnP i ndigits; last first.
  apply: leq_trans (_ : 2 ^ ndigits <= _); last by rewrite leq_exp2l.
  by rewrite -nwB_pow to_nat_bounded.
apply: ltn_bit => // j iLj.
by rewrite lor_spec !(bit_false_lt _ _ _ iLj).
Qed.

Lemma to_nat_land_bound a b i : 
  to_nat a < 2 ^ i -> to_nat (a land b) < 2 ^ i.
Proof.
move=> aLi; have [iLd|dLi] := ltnP i ndigits; last first.
  apply: leq_trans (_ : 2 ^ ndigits <= _); last by rewrite leq_exp2l.
  by rewrite -nwB_pow to_nat_bounded.
apply: ltn_bit => // j iLj.
by rewrite land_spec (bit_false_lt _ _ _ iLj).
Qed.

Lemma div_one_lsl_lsr n c : (n <? digits -> lsr c n = c / (lsl one n))%uint63.
Proof.
move=> nLd; apply: to_nat_inj.
rewrite to_nat_lsr to_nat_div to_nat_lsl_one //.
by apply/nltbP.
Qed.

Lemma lsr_land_distr a b c : 
  (lsr (a land b) c = (lsr a c) land (lsr b c))%uint63.
Proof.
by apply: bit_ext => i; rewrite !(land_spec, bit_lsr); case: nlebP. 
Qed.

Lemma to_nat_add_le m n : 
  (m <=? m + n)%uint63 -> to_nat (m + n) = to_nat m + to_nat n.
Proof.
move=> /nlebP; rewrite to_nat_addW.
have mLw := to_nat_bounded m.
have nLw := to_nat_bounded n.
have [mnLw|wLmn] := ltnP (to_nat m + to_nat n) nwB; first by rewrite modn_small.
rewrite leqNgt => /negP[].
rewrite -(subnK wLmn) modnDr modn_small ltn_subLR //.
  by rewrite addnC ltn_add2r.
by rewrite (ltn_trans (_ : _ < nwB + to_nat n)) // (ltn_add2r, ltn_add2l).
Qed.

Lemma lsl_land_decr i j : 
  (j <? digits -> (lsl i j) land decr (lsl one j) = 0)%uint63.
Proof.
move=> jLd; apply: bit_ext => k; rewrite bit_0 land_spec bit_lsl bit_decr //.
by case: nltbP; rewrite ?andbF.
Qed.

Lemma lornn n : (n lor n = n)%uint63.
Proof. by apply: bit_ext => i; rewrite lor_spec; case: bit. Qed.

Lemma lsl_land_distr a b c : 
  ((a land b) >> c = (a >> c) land (b >> c))%uint63.
Proof.
by apply: bit_ext => i; rewrite !(land_spec, bit_lsr); case: nlebP.
Qed.


