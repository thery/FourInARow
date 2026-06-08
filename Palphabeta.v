From Stdlib Require Import ZArith Ascii List String PrimInt63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_boot.
From HB Require Import structures.

From Stdlib Require Import Lia.
Require Import ssr_int.
Require Import Pbasic.
Require Import Pmoves.
Require Import Phash.
Require Import FourInARow.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(*                                                                            *)
(*    Alpha beta                                                              *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)


Import PrimInt63Notations.
Import Uint63Axioms.
Import Uint63.
Open Scope uint63_scope.

(*
(* Process result *)
Inductive pres := PRes (s : int) (v : int) (t : array (array int)).
*)

Section  Alpha.


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
Notation valid_eval := (valid_eval width height).
Notation valid_pos := (valid_pos width height).
Notation has_move := (has_move width height).
Notation cwin := (cwin width height).
Notation cmove := (cmove width height).
Notation mk_move := (mk_move height).
Notation ncells := (ncells width height).
Notation valid_htable := (valid_htable width height).
Notation ihjE := (@ihjE width height).
Notation ihjLd := (@ihjLd width height).

Notation "t .[ i ]" := (get t i)
  (at level 1, left associativity, format "t .[ i ]").
Notation "t .[ i <- a ]" := (set t i a)
  (at level 1, left associativity, format "t .[ i <- a ]").

Section Process.

Variables w b : int.
Variable beta : int.
Variable lv  : int.
Variable hg : int.
Variable hs : int.
Variable ab : int -> int -> int -> int -> int -> 
                         array (array int) -> pres.
Hypothesis hsV : valid_eval w b hs.
Hypothesis hsL : hs land 1 == 0.
Hypothesis wbV : valid_pos w b.
Hypothesis wbH : has_move (w lor b).

Let wNw : ~~ cwin w.
Proof. by case: wbV. Qed.
Let wNb : ~~ cwin b.
Proof. by case: wbV. Qed.
Let wbWf : valid_pegs (w lor b).
Proof. by case: wbV. Qed.
Let wbL : w land b = 0.
Proof. by case: wbV. Qed.

Lemma ufixE v : ufix v land 1 = 1.
Proof.
rewrite /ufix; case: neqbP; first by apply: to_nat_inj.
by case: neqbP.
Qed.

Lemma hs_range : [\/ hs = unknown, hs = lossdraw | hs = drawwin].
Proof. by apply: valid_eval0E hsV _. Qed.

Definition valid_ab (a b : int) :=
  if a == loss then (b == draw) || (b == win) else (a == draw) && (b== win).

Definition LOSSWIN := to_nat losswin.

Lemma to_nat_rev_val a : 
  a <=? losswin -> to_nat (rev_val a) = (LOSSWIN - to_nat a)%N.
Proof. by move=> /nlebP aLl; rewrite to_nat_sub // to_nat_bounded. Qed.

Lemma valid_ab_rev a1 b1 : 
  valid_ab a1 b1 -> valid_ab (rev_val b1) (rev_val a1).
Proof.
rewrite /valid_ab; case: eqP => [-> /orP[]/eqP->//|_].
by case: eqP => [-> /eqP->|].
Qed.

Definition valid_list (l : seq (int * int)) := forall m : int * int,
    m \in l -> 
    exists i j : nat, [/\ cmove (w lor b) i j,  ~~ cwin (mk_move w i j) &
    m.1 = lsl 1 (of_nat i * horizontal + of_nat j)].

Definition get_max (ms : seq (int * int)) := 
  maxn LOSS 
    (\max_(i < nwidth) \max_(j < nheight | cmove (w lor b) i j && 
            (lsl 1 (of_nat i * horizontal + of_nat j) \notin map fst ms))
           wcomp (eval b (mk_move w i j))).

Lemma get_max_range ms : 
  [\/ get_max ms = LOSS, get_max ms = DRAW | get_max ms = WIN].
Proof.
rewrite /get_max; set u := \max_(_ < _) _.
suff : [\/ u = 0%N, u = LOSS, u = DRAW | u = WIN].
  by case=> ->; (try by apply: Or31); (try by apply: Or32); apply: Or33.
rewrite /u; elim: {-2}nwidth (leqnn nwidth) => [|n IH nLw].
  by rewrite big_ord0 => _; apply: Or41.
rewrite big_ord_recr /=.
set v := \max_(j < nheight | _) _.
suff : [\/ v = 0%N, v = LOSS, v = DRAW | v = WIN].
  by case => ->; case: (IH (ltnW nLw)) => ->;
       (try by apply: Or41); (try by apply: Or42); (try by apply: Or43); 
      apply: Or44.
rewrite /v big_mkcond /=.
elim: {-2}nheight (leqnn nheight) => [|m IH1 mLh].
  by rewrite big_ord0 => _; apply: Or41.
rewrite big_ord_recr /=.
by case/or3P: (evalOr b (mk_move w n m)) => /eqP->; 
   case: ifP => _; case: (IH1 (ltnW mLh)) => ->;
       (try by apply: Or41); (try by apply: Or42); (try by apply: Or43); 
      apply: Or44.
Qed.

Lemma get_max_nil : get_max [::] = eval w b.
Proof.
rewrite evalS // (negPf wNw) (negPf wNb) /= wbH /get_max.
case/existsP : wbH => /= i /existsP [/= j ijM].
rewrite (bigD1 i) //= maxnA [in RHS](bigD1 i) //=; congr maxn.
  rewrite (bigD1 j) ?andbT //= maxnA [in RHS](bigD1 j) //=; congr maxn.
    by case/or3P: (evalOr b (mk_move w i j)) => /eqP->.
  by apply: eq_bigl => k; rewrite andbT.
by apply: eq_bigr => i1 _; apply: eq_bigl => j1; rewrite andbT.
Qed.

Lemma get_max_cons m i j ms :
  uniq (map fst (m :: ms)) ->
  m.1 = (lsl one (of_nat i * horizontal + of_nat j)) -> cmove (w lor b) i j -> 
  get_max ms = maxn (wcomp (eval b (mk_move w i j))) (get_max (m :: ms)).
Proof.
move=> msU mmE ijM. 
have iLw : i < nwidth by case/and3P: ijM.
have jLh : j < nheight by case/and3P: ijM.
rewrite /get_max.
rewrite (bigD1 (Ordinal iLw)) //= [in RHS](bigD1 (Ordinal iLw)) //= !maxnA; congr maxn.
  rewrite (bigD1 (Ordinal jLh)) //=; last first.
    by rewrite ijM; move: msU => /= /andP[]; rewrite mmE => ->.
  rewrite maxnA; congr maxn; first by rewrite maxnC.
  apply: eq_bigl => k /=; rewrite -andbA; congr (_ && _).
  rewrite inE negb_or andbC mmE; congr (_ && _).
  (apply/idP/idP => /=; 
  move=> /eqP HH1; apply/eqP; contradict HH1); last first.
    by move/val_eqP : HH1 => /= /eqP->.
  apply/val_eqP/eqP => /=.
  move/(congr1 (fun x => to_nat x)) : HH1 => /eqP HH2.
  have kLhe : k < nhorizontal by apply: ltn_trans (ltn_ord _) _; rewrite nhorizontalE.
  have jLhe : j < nhorizontal by apply: ltn_trans jLh _; rewrite nhorizontalE.
  rewrite [X in X == _]to_nat_lsl_one ihjE // in HH2; last by apply: ihjLd.
  rewrite [X in _ == X]to_nat_lsl_one ihjE // in HH2; last by apply: ihjLd.
  rewrite eqn_exp2l // eqn_add2l in HH2 .
  by apply/eqP.
apply: eq_bigr => i1 /eqP /val_eqP /= i1Di.
apply: eq_bigl => j1; congr (_ && _); rewrite inE negb_or.
rewrite -{1}[LHS]andbT [RHS]andbC.
congr (_ && _); apply/sym_equal/idP.
rewrite mmE; move/eqP: i1Di => i1Di; apply/eqP; contradict i1Di.
move/(congr1 (fun x => to_nat x)) : i1Di => /eqP HH2.
have j1Lhe : j1 < nhorizontal by apply: ltn_trans (ltn_ord _) _; rewrite nhorizontalE.
have jLhe : j < nhorizontal by apply: ltn_trans jLh _; rewrite nhorizontalE.
rewrite [X in X == _]to_nat_lsl_one ihjE // in HH2; last by apply: ihjLd.
rewrite [X in _ == X]to_nat_lsl_one ihjE // in HH2; last by apply: ihjLd.
rewrite eqn_exp2l // in HH2.
case: (ltngtP i1 i) => // [i1Li | iLi1].
  suff : i1 * nhorizontal + j1 < i * nhorizontal + j by rewrite (eqP HH2) ltnn.
  apply: leq_trans (_ : i1.+1  * nhorizontal <= _).
    by rewrite mulSn addnC ltn_add2r.
  by apply: leq_trans (leq_addr _ _); rewrite leq_mul2r // nhorizontalE.
suff : i * nhorizontal + j < i1 * nhorizontal + j1 by rewrite (eqP HH2) ltnn.
apply: leq_trans (_ : i.+1  * nhorizontal <= _).
  by rewrite mulSn addnC ltn_add2r.
by apply: leq_trans (leq_addr _ _); rewrite leq_mul2r nhorizontalE.
Qed.

Definition valid_answer sc :=
   [\/ sc = loss, sc = draw | sc = win] \/
   [\/ sc = lossdraw | sc = drawwin].

Lemma valid_answer_rev sc : 
  valid_answer sc -> valid_answer (rev_val sc).
Proof.
by case; case=> ->; try (by left; (try by apply: Or31); (try by apply: Or32); apply: Or33);
  try (by right; (try by left); (try by right)).
Qed.

Lemma valid_eval_answer w1 b1 sc : 
  valid_eval w1 b1 sc -> sc != unknown -> valid_answer sc.
Proof.
by case/valid_evalE; case => -> //;
  (try by (left; (try by apply: Or31); (try by apply: Or32); apply Or33));
  (try by right; left); right; right.
Qed.

Definition valid_scores (ms : seq (int * int)) sc := 
   down_score sc <= get_max ms <= up_score sc.

Lemma valid_score_range ms sc :
  valid_scores ms sc -> 
   [\/ sc = loss, sc = draw | sc = win] \/
   [\/ sc = unknown, sc = lossdraw | sc = drawwin].
Proof.
rewrite /valid_scores => /andP[] /leq_trans H /(H _).
rewrite /down_score /up_score.
case: eqP => [->//|_]; first by right; apply: Or31.
case: eqP => [->//|_]; first by left; apply: Or31.
case: eqP => [->//|_]; first by right; apply: Or32.
case: eqP => [->//|_]; first by left; apply: Or32.
case: eqP => [->//|_]; first by right; apply: Or33.
by case: eqP => [->//|]; first by left; apply: Or33.
Qed.

Lemma valid_cons m (l : seq (int * int)) :
   valid_list (m :: l) -> 
    valid_list l /\ 
    exists i j, [/\ cmove (w lor b) i j, ~~ cwin (mk_move w i j) &
    m.1 = lsl 1 (of_nat i * horizontal + of_nat j)].
Proof.
by move=> lV; split => [m1 m1Il|]; apply: lV; rewrite inE ?eqxx ?m1Il ?orbT.
Qed.

Hypothesis ab_correct : forall w1 b1 (alpha1 beta1 : int) sc v v1 ht ht1, 
  ncells (w1 lor b1) < ncells (w lor b) ->
  valid_pos w1 b1 ->
  valid_htable ht ->
  valid_ab alpha1 beta1 ->
  ab w1 b1 alpha1 beta1 v ht =  PRes sc v1 ht1 ->
  [/\ valid_answer sc, valid_eval w1 b1 sc & valid_htable ht1].

Lemma cmove_has_move wb i j : cmove wb i j -> has_move wb.
Proof.
move=> ijM.
have iLw : i < nwidth by case/and3P: ijM.
have jLh : j < nheight by case/and3P: ijM.
by apply/existsP; exists (Ordinal iLw); apply/existsP; exists (Ordinal jLh).
Qed.

Lemma leq_eval_move i j : 
  cmove (w lor b) i j -> wcomp (eval b (mk_move w i j)) <= eval w b.
Proof.
move => ijM.
have iLw : i < nwidth by case/and3P: ijM.
have jLh : j < nheight by case/and3P: ijM.
rewrite [X in _ <= X]evalS //= (negPf wNw) (negPf wNb) ifT; last first.
  by apply: cmove_has_move ijM.
rewrite (bigD1 (Ordinal iLw)) //= (leq_trans  _ (leq_maxl _ _)) //.
by rewrite (bigD1 (Ordinal jLh)) //= leq_maxl.
Qed.

Lemma leq_wcomp a1 b1 : a1 <= b1 -> wcomp b1 <= wcomp a1.
Proof. by move=> a1Lb1; rewrite leq_sub. Qed.

Lemma leq_eval_win w1 b1 : eval w1 b1 <= WIN.
Proof. by have /or3P[] := evalOr w1 b1 => /eqP->. Qed.

Lemma leq_loss_eval w1 b1 : LOSS <= eval w1 b1.
Proof. by have /or3P[] := evalOr w1 b1 => /eqP->. Qed.

Lemma leq_down_score (a1 c1 : int) (b1 d1 : nat) :
  [\/ b1 = LOSS, b1 = DRAW | b1 = WIN] ->
  [\/ d1 =  LOSS, d1 = DRAW | d1 = WIN] ->
  [\/ a1 =  loss, a1 = draw | a1 = win] \/
  [\/  a1 = lossdraw | a1 = drawwin]  ->
  [\/ c1 =  loss, c1 = draw | c1 = win] \/
  [\/ c1 = lossdraw | c1 = drawwin]  ->
  down_score a1 <= b1 <= up_score a1 ->
  down_score c1 <= d1 <= up_score c1 ->
  to_nat a1 <= to_nat c1 ->
  down_score c1 <= maxn b1 d1 <= up_score c1.
Proof.
case => ->; case => -> //; case; case => -> //; case; case => -> //.
Qed.

Lemma ltn_down_score (a1 c1 : int) (b1 d1 : nat) :
  [\/ b1 = LOSS, b1 = DRAW | b1 = WIN] ->
  [\/ d1 =  LOSS, d1 = DRAW | d1 = WIN] ->
  [\/ a1 =  loss, a1 = draw | a1 = win] \/
  [\/  a1 = lossdraw | a1 = drawwin]  ->
  [\/ c1 =  loss, c1 = draw | c1 = win] \/
  [\/ c1 = lossdraw | c1 = drawwin]  ->
  down_score a1 <= b1 <= up_score a1 ->
  down_score c1 <= d1 <= up_score c1 ->
  to_nat c1 < to_nat a1 ->
  down_score a1 <= maxn b1 d1 <= up_score a1.
Proof.
case => ->; case => -> //; case; case => -> //; case; case => -> //.
Qed.

Notation process := (process width height w b beta lv hg hs ab).

Lemma process_correct ms alpha sc sc1 v v1 ht ht1 :
  valid_answer sc -> valid_list ms -> valid_scores ms sc ->
  valid_htable ht -> valid_ab alpha beta -> uniq (map fst ms) -> 
  process ms alpha sc v ht =  PRes sc1 v1 ht1 ->
  [/\ valid_answer sc1, valid_eval w b sc1 & valid_htable ht1].
Proof.
elim: ms alpha sc sc1 v v1 ht ht1 =>
   [|[m x] ms IH] alpha sc sc1 v v1 ht ht1 scDu Vms Vsc Vh Vab Ums /=.
  case: neqbP.
    move=> HH.
    suff eD : DRAW <= eval w b <= DRAW.
      case => dE _ <-; split.
      - by rewrite -dE; left; apply: Or32.
      - by rewrite -dE.
      by apply: valid_has_table_hput.
    have hsE : (hs = lossdraw) \/ (hs = drawwin).
      have := HH; have := hs_range => [] [] -> //;  (try by left); (try by right).
      by have /valid_score_range := Vsc; case; case => ->.
    case: hsE => hsE.
      apply/andP; split; last by case/andP : hsV; rewrite hsE.
      have scE : sc = drawwin by apply/to_nat_inj; rewrite HH hsE.
      by have := Vsc; rewrite /valid_scores get_max_nil scE; case/andP.
    have scE : sc = lossdraw by apply/to_nat_inj; rewrite HH hsE.
    apply/andP; split; first by case/andP : hsV; rewrite hsE.
    by have := Vsc; rewrite /valid_scores get_max_nil scE; case/andP.
  move=> HH.
  suff eD : valid_eval w b sc.
    case => dE _ <-; split; first by rewrite -dE.
      by rewrite -dE.
    by apply: valid_has_table_hput.
  by have := Vsc; rewrite /valid_scores get_max_nil.
case E : ab => [s2 v2 h2].
have [Vms1 [i [j [ijM inNW mE]]]] := valid_cons Vms. 
have mmE : make_move m w = mk_move w i j.
  by rewrite [m]mE /mk_move /make_move lorC.
case: (ab_correct _ _ _ _ E) => // [|||s2Nu vEs2 h2V].
- by rewrite mmE -ncells_cmove //.
- by split; rewrite ?mmE // ?valid_pegs_cmove // (@land_cmove width).
- by apply: valid_ab_rev.
have us2Le : wcomp (up_score s2) <= eval w b.
  have /(leq_trans _)-> // := leq_eval_move ijM.
  by apply: leq_wcomp; rewrite -mmE; case/andP: vEs2.
case: nltbP => [rs2Lb|/negP].
  case: nlebP => [HH|/negP].
    apply: IH => //; last by case/andP:  Ums.
    rewrite /valid_scores (@get_max_cons (m, x) i j) //.
    apply: leq_down_score HH => //.
    - by have := evalOr b (mk_move w i j); case/or3P => /eqP->;
        try (by apply: Or31); try (by apply: Or32); apply: Or33.
    - by apply: get_max_range.
    - by case: s2Nu; case=> -> //;
      try(by left; (try by apply: Or31);(try by apply: Or32); apply: Or33);
        right; (try by left); right.
    by have := vEs2; have := s2Nu; rewrite /valid_eval -mmE; case; case=> ->;
          case /or3P: (evalOr b (make_move m w)) => /eqP->.
  rewrite -ltnNge=> scLrs2.
  case: nlebP => [Hd|/negP].
    apply: IH => //; last by case/andP: Ums.
      by apply: valid_answer_rev.
    rewrite /valid_scores (@get_max_cons (m, x) i j) //. 
    apply: ltn_down_score scLrs2 => //.
    - by have := evalOr b (mk_move w i j); case/or3P => /eqP->;
        try (by apply: Or31); try (by apply: Or32); apply: Or33.
    - by apply: get_max_range.
    - by move: s2Nu; case; case=> -> //;
      try(by left; (try by apply: Or31);(try by apply: Or32); apply: Or33);
        right; (try by left); right.
    have := s2Nu; have := vEs2.
    by have := vEs2; have := s2Nu; rewrite /valid_eval -mmE; case; case=> ->;
          case /or3P: (evalOr b (make_move m w)) => /eqP->.
  rewrite -ltnNge => aLrs2. 
  apply: IH => //; last by case/andP: Ums.
  - by apply: valid_answer_rev.
  - rewrite /valid_scores (@get_max_cons (m, x) i j) //. 
    apply: ltn_down_score scLrs2 => //.
    - by have := evalOr b (mk_move w i j); case/or3P => /eqP->;
        try (by apply: Or31); try (by apply: Or32); apply: Or33.
    - by apply: get_max_range.
    - by move: s2Nu; case; case=> -> //;
      try(by left; (try by apply: Or31);(try by apply: Or32); apply: Or33);
        right; (try by left); right.
    have := vEs2; have := s2Nu.
    by rewrite /valid_eval; rewrite mmE;
          case; case=> ->;
          case /or3P: (evalOr b (mk_move w i j)) => /eqP->.
  have betaE : (beta == draw) || (beta == win).
    by move: Vab; rewrite /valid_ab; case: eqP => // _ /andP[_ ->]; rewrite orbT.
  have alphaE : (alpha == loss) || (alpha == draw).
    by move: Vab; rewrite /valid_ab; case: eqP => // _ /andP[].
  rewrite /valid_ab.
  have := rs2Lb.
  by have [] := valid_evalE vEs2; case=> -> //=;
    case/orP : betaE => /eqP-> //.
rewrite -leqNgt => bLrs2.
case: nlebP => [Hd|/negP].
  apply: IH => //; last by case/andP: Ums.
  rewrite /valid_scores (@get_max_cons (m, x) i j) //.
  apply: leq_down_score Hd => //.
  - by have := evalOr b (mk_move w i j); case/or3P => /eqP->;
      try (by apply: Or31); try (by apply: Or32); apply: Or33.
  - by apply: get_max_range.
  - by move: s2Nu; case; case=> -> //;
    try(by left; (try by apply: Or31);(try by apply: Or32); apply: Or33);
      right; (try by left); right.
  have := vEs2; have := s2Nu.
  by rewrite /valid_eval mmE;
        case; case=> ->;
        case /or3P: (evalOr b (mk_move w i j)) => /eqP->.
rewrite -ltnNge => scLrs2.
case: nlebP => [_|/negP].
  apply: IH => //; last by case/andP: Ums.
    by apply: valid_answer_rev.
  rewrite /valid_scores (@get_max_cons (m, x) i j) //. 
  apply: ltn_down_score scLrs2 => //.
  - by have := evalOr b (mk_move w i j); case/or3P => /eqP->;
      try (by apply: Or31); try (by apply: Or32); apply: Or33.
  - by apply: get_max_range.
  - by move: s2Nu; case; case=> -> //;
    try(by left; (try by apply: Or31);(try by apply: Or32); apply: Or33);
      right; (try by left); right.
  have := vEs2; have := s2Nu.
  by rewrite /valid_eval mmE;
          case; case=> ->;
          case /or3P: (evalOr b (mk_move w i j)) => /eqP->.
rewrite -ltnNge => aLrs2.
case: (neqbP _ draw) => rs2Ed; last first.
  rewrite andFb.
  case: neqbP => rs2El.
    have s2E : s2 = lossdraw.
      by have := rs2El; have [] := valid_evalE vEs2 => [] [] ->.
    case: neqbP => hsE.
      suff eD : DRAW <= eval w b <= DRAW.
        rewrite andTb; case => dE _ <-; split.
        - by rewrite -dE; left; apply: Or32.
        - by rewrite -dE.
        by apply: valid_has_table_hput.
      have hsE1 : hs = lossdraw by apply: to_nat_inj.
      have {vEs2} := vEs2.
      rewrite s2E /valid_eval -[down_score _]/LOSS -[up_score _]/DRAW => vEs2.
      have := hsV.
      rewrite hsE1 /valid_eval -[down_score _]/LOSS -[up_score _]/DRAW => hsV1.
      apply/andP; split; last by case/andP: hsV1.
      by have := us2Le; rewrite s2E. 
    suff eD : down_score (rev_val s2) <= eval w b <= up_score (rev_val s2).
      rewrite andTb; case => dE _ <-; split.
      - by rewrite -dE; apply: valid_answer_rev.
      - by rewrite -dE.
      by apply: valid_has_table_hput.
    have {vEs2} := vEs2.
    rewrite s2E /valid_eval -[down_score _]/LOSS -[up_score _]/DRAW => vEs2.
    rewrite -[down_score _]/DRAW -[up_score _]/WIN.
    apply/andP; split; last by apply: leq_eval_win.
    by have := us2Le; rewrite s2E.  
  suff eD : down_score (rev_val s2) <= eval w b <= up_score (rev_val s2).
    rewrite andFb; case => dE _ <-; split.
    - by rewrite -dE; apply: valid_answer_rev.
    - by rewrite -dE.
    by apply: valid_has_table_hput.
  have s2El : s2 = loss.
    move: bLrs2 rs2Ed rs2El.
    have /orP[/eqP->|/eqP->] : (beta == draw) || (beta == win).
    - by move: Vab; rewrite /valid_ab; case: eqP => // _ /andP[_ ->]; rewrite orbT.
    - by move/valid_evalE: vEs2; case; case => ->.
    by move/valid_evalE: vEs2; case; case => ->.
  suff -> : eval w b = WIN by rewrite s2El.
  apply/eqP/eval_winP => //; right; split => //.
  exists i; exists j; split => //.
  rewrite -mmE.
  move: vEs2; rewrite /valid_eval s2El.
  by have /or3P[] := evalOr b (make_move m w) => /eqP->.
have s2E : s2 = draw.
  by move: rs2Ed; move/valid_evalE: vEs2; case; case => ->.
case: (boolP (is_nempty_move ms)) => ems.
  rewrite andTb eqb_refl.
  case: neqbP => hD.
    have hsE : hs = lossdraw by apply: to_nat_inj.
    suff eD : DRAW <= eval w b <= DRAW.
      case => dE _ <-; split.
      - by rewrite -dE; left; apply: Or32.
      - by rewrite -dE.
      by apply: valid_has_table_hput.
    apply/andP; split; last first.
      by move: hsV; rewrite /valid_eval hsE; case/andP.
    by have := us2Le; rewrite s2E.
  suff eD : DRAW <= eval w b <= WIN.
    case => dE _ <-; split.
    - by rewrite -dE; right; right.
    - by rewrite -dE.
    by apply: valid_has_table_hput.
  apply/andP; split; last by apply: leq_eval_win.
  by have := us2Le; rewrite s2E.
suff eD : DRAW <= eval w b <= DRAW.
  rewrite s2E andFb; case => dE _ <-; split.
  - by rewrite -dE; left; apply: Or32.
  - by rewrite -dE.
  by apply: valid_has_table_hput.
case: ms {IH}ems Ums Vms Vsc Vms1 => // ems Ums Vms Vsc Vms1.
rewrite -get_max_nil (@get_max_cons (m,x) i j) //.
rewrite -{1}[DRAW]/(down_score (rev_val draw)) -{1}[DRAW]/(up_score (rev_val draw)).
rewrite -s2E.
apply: ltn_down_score scLrs2 => //.
- by have /or3P[] := evalOr  b (mk_move w i j) => /eqP->; try (by apply: Or31);
     try (by apply: Or32); apply: Or33.
- by apply: get_max_range.
- by rewrite s2E; left; apply: Or32.
have := vEs2.
rewrite /valid_eval s2E mmE.
by have /or3P[] := evalOr  b (mk_move w i j) => /eqP->.
Qed.

End Process.

Notation alpha_beta := (alpha_beta width height).

Lemma alphabeta_correct ns h w b (alpha beta : int) v ht sc v1 ht1 : 
  ncells (w lor b) < ns ->
  valid_pos w b ->
  valid_htable ht ->
  valid_ab alpha beta ->
  alpha_beta ns h w b alpha beta v ht =  PRes sc v1 ht1 ->
  [/\ valid_answer sc, valid_eval w b sc & valid_htable ht1].
Proof.
elim: ns h w b alpha beta sc v v1 ht ht1 => //= 
     ns IH h w b alpha beta sc v v1 ht ht1 nsL wbV Vh Vab.
have Vhget : valid_eval w b (hget w b h ht).
  have [wbV1 Ha _ _] := wbV.
  case: Vh => _ _  /(_ w b h wbV1 Ha) /valid_entries_prop.
  by apply.
case: (ifP (_ =? unknown)) => Hh; last first.
  have Vahget : valid_answer (hget w b h ht).
    apply: valid_eval_answer Vhget _.
    by apply/eqP=> HH; case/eqP: Hh.
  case: (ifP (~~ _)) => Hh1; first by case=> <- _ <-.
  case: (ifP (_ =? drawwin)) => Hh2.
    case: (ifP (_ =? draw)) => Hh3; first by case=> <- _ <-.
    case E : find_moves => [||m|ms] //.
    - case => <- _ <-; split => //.
        by left; apply: Or33.
      by rewrite /valid_eval (find_moves_win _ _ _ _ _ E).
    - case => <- _ <-; split => //.
        by left; apply: Or32.
      by rewrite /valid_eval (find_moves_draw _ _ _ _ E).
    - case E1 : alpha_beta => [sc2 v2 ht2] [rsc2E v2E h2E].
      have [] := IH (h + 1) b (make_move m w) (rev_val beta) 
                    (rev_val draw) sc2 v v2 ht ht2 => //.
      - case/find_moves_forced_cmove : E => // i1 [j1 [mE i1j1M]].
        rewrite -ltnS; move/ncells_cmove :  i1j1M.
        by rewrite /make_move mE /mk_move [_ lor w]lorC => <-.
      - move/find_moves_forced_valid_pos : E.
        by rewrite lorC; apply.
      - suff -> : beta = win by [].
        move: Vab Hh3; rewrite /valid_ab; case: eqP => // _.
          by case/orP => /eqP->.
        by case/andP=> _ /eqP.
      move=> Vasce Vesc2 Vth2; split => //.
      - by rewrite -rsc2E; apply: valid_answer_rev.
      - have:= Vesc2; rewrite /make_move [_ lor w]lorC.
        rewrite /valid_eval (find_moves_forced _ _ _ _ _ E) // -rsc2E.
        by case/or3P: (evalOr b (w lor m))=> /eqP ->; case: Vasce; case=> ->.
      by rewrite -h2E.
    apply: process_correct => //.
    - by move/eqP: Hh2 => ->.
    - have : 0 < seq.size ms by apply: find_moves_moves_size E.
      case: ms E => // m ms /find_moves_moves_cmove HH _.
      case: (HH _ _ _ _ m) => //; first by rewrite inE eqxx.
      move=> i1 [j1 [i1j1C _ _]].
      have i1Lw : i1 < nwidth by case/and3P: i1j1C.
      have j1Lh : j1 < nheight by case/and3P: i1j1C.
      by apply/existsP; exists (Ordinal i1Lw); apply/existsP; exists (Ordinal j1Lh).
    - move=> w1 b1 alpha2 beta2 sc1 v2 v3 n2 ht3 cLc.
      apply: IH => //.
      by apply: leq_trans cLc _.
    - by left; apply: Or31.
    - by move=> m; apply: find_moves_moves_cmove.
    - rewrite /valid_scores /get_max big1 //=  => i _.
      rewrite big1 => // j /andP[ijM /negP[]].
      by apply: find_moves_moves_cmove_in E _.
    - suff -> : beta = win by [].
      move: Vab Hh3; rewrite /valid_ab; case: eqP => // _.
        by case/orP => /eqP->.
      by case/andP=> _ /eqP.
    by apply: find_moves_moves_uniq E.
  case: (ifP (_ =? draw)) => Hh3; first by case=> <- _ <-; split.
  case E : find_moves => [||m|ms] //.
  - case => <- _ <-; split => //.
      by left; apply: Or33.
    by rewrite /valid_eval (find_moves_win _ _ _ _ _ E).
  - case => <- _ <-; split => //.
      by left; apply: Or32.
    by rewrite /valid_eval (find_moves_draw _ _ _ _ E).
  - case E1 : alpha_beta => [sc2 v2 ht2] [rsc2E v2E ht2E].
    have [] := IH (h + 1) b (make_move m w) (rev_val draw) 
                  (rev_val alpha) sc2 v v2 ht ht2 => //.
    - case/find_moves_forced_cmove : E => // i1 [j1 [mE i1j1M]].
      rewrite -ltnS; move/ncells_cmove :  i1j1M.
      by rewrite /make_move mE /mk_move [_ lor w]lorC => <-.
    - move/find_moves_forced_valid_pos : E.
      by rewrite lorC; apply.
    - suff -> : alpha = loss by [].
        move: Vab Hh3; rewrite /valid_ab; case: eqP => // _.
      by case/andP=> /eqP->.    
    move=> Hasc2 Hesc2 Hth2; split => //.
    - by rewrite -rsc2E; apply: valid_answer_rev.
    - have:= Hesc2; rewrite /make_move [_ lor w]lorC.
      rewrite /valid_eval (find_moves_forced _ _ _ _ _ E) // -rsc2E.
      by case/or3P: (evalOr b (w lor m))=> /eqP ->; case: Hasc2; case=> ->.
    by rewrite -ht2E.
  apply: process_correct => //.
  - by move/eqP: Hh1 => ->.
  - have : 0 < seq.size ms by apply: find_moves_moves_size E.
    case: ms E => // m ms /find_moves_moves_cmove HH _.
    case: (HH _ _ _ _ m) => //; first by rewrite inE eqxx.
    move=> i1 [j1 [i1j1C _ _]].
    have i1Lw : i1 < nwidth by case/and3P: i1j1C.
    have j1Lh : j1 < nheight by case/and3P: i1j1C.
    by apply/existsP; exists (Ordinal i1Lw); apply/existsP; exists (Ordinal j1Lh).
  - move=> w1 b1 alpha2 beta2 sc1 v2 v3 n2 h3 cLc.
    apply: IH => //.
    by apply: leq_trans cLc _.
  - by left; apply: Or31.
  - by move=> m; apply: find_moves_moves_cmove.
  - rewrite /valid_scores /get_max big1 //=  => i _.
    rewrite big1 => // j /andP[ijM /negP[]].
    by apply: find_moves_moves_cmove_in E _.
  - suff -> : alpha = loss by [].
      move: Vab Hh3; rewrite /valid_ab; case: eqP => // _.
    by case/andP=> /eqP->.    
  by apply: find_moves_moves_uniq E.
case E : find_moves => [||m|ms] //.
- case => <- _ <-; split => //.
    by left; apply: Or33.
  by rewrite /valid_eval (find_moves_win _ _ _ _ _ E).
- case => <- _ <-; split => //.
    by left; apply: Or32.
  by rewrite /valid_eval (find_moves_draw _ _ _ _ E).
- case E1 : alpha_beta => [sc2 v2 ht2] [rsc2E v2E ht2E].
  have [] := IH (h + 1) b (make_move m w) (rev_val beta) 
                 (rev_val alpha) sc2 v v2 ht ht2 => //.
  - case/find_moves_forced_cmove : E => // i1 [j1 [mE i1j1M]].
    rewrite -ltnS; move/ncells_cmove :  i1j1M.
    by rewrite /make_move mE /mk_move [_ lor w]lorC => <-.
  - move/find_moves_forced_valid_pos : E.
    by rewrite lorC; apply.
  - by apply: valid_ab_rev.
  move=> Hasc2 Hesc2 Hth2; split => //.
  - by rewrite -rsc2E; apply: valid_answer_rev.
  - have:= Hesc2; rewrite /make_move [_ lor w]lorC.
    rewrite /valid_eval (find_moves_forced _ _ _ _ _ E) // -rsc2E.
    by case/or3P: (evalOr b (w lor m))=> /eqP ->; case: Hasc2; case=> ->.
  by rewrite -ht2E.
apply: process_correct => //.
- by move/eqP: Hh => ->.
- have : 0 < seq.size ms by apply: find_moves_moves_size E.
  case: ms E => // m ms /find_moves_moves_cmove HH _.
  case: (HH _ _ _ _ m) => //; first by rewrite inE eqxx.
  move=> i1 [j1 [i1j1C _ _]].
  have i1Lw : i1 < nwidth by case/and3P: i1j1C.
  have j1Lh : j1 < nheight by case/and3P: i1j1C.
  by apply/existsP; exists (Ordinal i1Lw); apply/existsP; exists (Ordinal j1Lh).
- move=> w1 b1 alpha2 beta2 sc1 v2 v3 n2 h3 cLc.
  apply: IH => //.
  by apply: leq_trans cLc _.
- by left; apply: Or31.
- by move=> m; apply: find_moves_moves_cmove.
- rewrite /valid_scores /get_max big1 //=  => i _.
  rewrite big1 => // j /andP[ijM /negP[]].
  by apply: find_moves_moves_cmove_in E _.
by apply: find_moves_moves_uniq E.
Qed.

Notation is_won := (is_won height).

Definition valid_posb w b := 
  [&& (w lor b) >> (width * horizontal) == 0, ~~ is_won w, ~~ is_won b, 
     w land b == 0 & all (fun x =>         
      let i := get_column (w lor b) (of_nat x) in 
        has (fun j => 
              (i == decr (lsl one (of_nat j)))) (iota 0 nhorizontal))
       (iota 0 nwidth)].

Lemma valid_posb_correct w b : valid_posb w b -> valid_pos w b.
Proof.
case/and5P => /eqP wbswh_eq0 NWw Nwb /eqP wb_eq0 /allP HiE.
suff wbV : valid_pegs (w lor b).
  split => //; first by rewrite -(@is_won_cwin _ _ _ _ _ _ w b).
  by rewrite -(@is_won_cwin _ _ _ _ _ _ b w) // lorC.
apply/andP; split.
  apply/forallP => i; apply/implyP => Hb.
  case: nltbP => // /negP.
  rewrite -leqNgt => whLi.
  rewrite (bit_false_lt _ _ _ whLi) // in Hb.
  rewrite -[X in _ < X]mul1n.
  rewrite -ltn_divLR //; last by rewrite expn_gt0.
  have : to_nat 0 = 0%N by [].
  by rewrite -wbswh_eq0 to_nat_lsr => ->.
apply/forallP => i; apply/implyP => /nltbP iLw.
rewrite opzsE; last by apply/nltbP/(ltn_trans _ h_hypU).
have := HiE (to_nat i).
rewrite mem_iota => /(_ iLw) /hasP[j Hj1 Hj2].
rewrite mem_iota /= add0n in Hj1.
apply/existsP; exists (of_nat j); apply/andP; split.
  apply/nlebP; rewrite of_natK //; last first.
    by apply: ltn_trans nhorizontalLwB.
  by rewrite -ltnS -nhorizontalE.
by rewrite to_natK in Hj2.
Qed.

Definition htop_eval w b ht :=
  let: PRes sc _ _ := 
    alpha_beta (1 + nheight * nwidth) 0 w b loss win zero ht in sc.

Lemma htopeval_correct w b ht : 
 valid_posb w b -> valid_htable ht -> valid_eval w b (htop_eval w b ht).
Proof.
move=> /valid_posb_correct wbV Hht.
have := @alphabeta_correct (1 + nheight * nwidth) 0 w b loss win zero ht.
rewrite /htop_eval.
case: alpha_beta => sc1 v1 ht1 /(_ sc1 v1 ht1) [] //.
rewrite ltnS (leq_trans (leq_ncells_landr _ _ empty_state _)) // land0.
by rewrite ncells_empty_state mulnC.
Qed.

Definition top_eval w b := htop_eval w b (make_hash tt) .

Lemma topeval_correct w b : valid_posb w b -> valid_eval w b (top_eval w b).
Proof.
move=> wbVb; apply: htopeval_correct => //.
by apply: valid_htable_make_hash.
Qed.

Notation parse_string := (parse_string width height).

Definition get_position s :=
   match parse_string s with
   (wstate,bstate,turn) =>
   if turn then (wstate,bstate) else (bstate,wstate)
   end.

End Alpha.
