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
Hypothesis wNw : ~~ cwin w.
Hypothesis wNb : ~~ cwin b.
Hypothesis wbWf : wf_state (w lor b).
Hypothesis wbL : w land b = 0.
Hypothesis wbH : has_move (w lor b).

Lemma ufixE v : ufix v land 1 = 1.
Proof.
rewrite /ufix; case: neqbP; first by apply: to_nat_inj.
by case: neqbP.
Qed.

Lemma hs_range : [\/ hs = unknown, hs = lossdraw | hs = drawwin].
Proof. by apply: valid_eval0E hsV _. Qed.

Notation process := (process w b beta lv hg hs ab).

Definition valid_ab a b :=
  if a == loss then (b == draw) || (b == win) else (a == draw) && (b== win).

Definition LOSSWIN := to_nat losswin.

Lemma to_nat_rev_val a1 : 
  a1 <=? losswin -> to_nat (rev_val a1) = (LOSSWIN - to_nat a1)%N.
Proof. by move=> /nlebP a1Ll; rewrite to_nat_sub // to_nat_bounded. Qed.

Lemma valid_ab_rev a1 b1 : valid_ab a1 b1 -> valid_ab (rev_val b1) (rev_val a1).
Proof.
rewrite /valid_ab; case: eqP => [-> /orP[]/eqP->//|_].
by case: eqP => [-> /eqP->|].
Qed.

Definition valid_list (l : seq (int * int)) := forall m : int * int,
    m \in l -> 
    exists i j : nat, cmove (w lor b) i j /\
    m.1 = lsl 1 (of_nat i * horizontal + of_nat j).


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
by case/or3P: (evalOr b (mk_move w n m)) => /eqP->; case: ifP => _; case: (IH1 (ltnW mLh)) => ->;
       (try by apply: Or41); (try by apply: Or42); (try by apply: Or43); 
      apply: Or44.
Qed.

Lemma get_max_nil : get_max [::] = eval w b.
Proof.
rewrite evalS (negPf wNw) /= wbH /get_max.
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
  have kLhe : k < nhorizontal by apply: ltn_trans (ltn_ord _) _.
  have jLhe : j < nhorizontal by apply: ltn_trans jLh _.
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
have j1Lhe : j1 < nhorizontal by apply: ltn_trans (ltn_ord _) _.
have jLhe : j < nhorizontal by apply: ltn_trans jLh _.
rewrite [X in X == _]to_nat_lsl_one ihjE // in HH2; last by apply: ihjLd.
rewrite [X in _ == X]to_nat_lsl_one ihjE // in HH2; last by apply: ihjLd.
rewrite eqn_exp2l // in HH2.
case: (ltngtP i1 i) => // [i1Li | iLi1].
  suff : i1 * nhorizontal + j1 < i * nhorizontal + j by rewrite (eqP HH2) ltnn.
  apply: leq_trans (_ : i1.+1  * nhorizontal <= _).
    by rewrite mulSn addnC ltn_add2r.
  by apply: leq_trans (leq_addr _ _); rewrite leq_mul2r.
suff : i * nhorizontal + j < i1 * nhorizontal + j1 by rewrite (eqP HH2) ltnn.
apply: leq_trans (_ : i.+1  * nhorizontal <= _).
  by rewrite mulSn addnC ltn_add2r.
by apply: leq_trans (leq_addr _ _); rewrite leq_mul2r.
Qed.


Definition valid_sc (ms : seq (int * int)) sc := 
  down_score sc <= get_max ms <= up_score sc. 

Lemma valid_sc_range ms sc :
  valid_sc ms sc -> 
   [\/ sc = loss, sc = draw | sc = win] \/
   [\/ sc = unknown, sc = lossdraw | sc = drawwin].
Proof.
rewrite /valid_sc => /andP[] /leq_trans H /(H _).
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
    exists i j, cmove (w lor b) i j /\
    m.1 = lsl 1 (of_nat i * horizontal + of_nat j).
Proof.
by move=> lV; split => [m1 m1Il|]; apply: lV; rewrite inE ?eqxx ?m1Il ?orbT.
Qed.

Hypothesis ab_correct : forall w b alpha1 beta1 sc v v1 h h1, 
  valid_hash_table h ->
  valid_ab alpha1 beta1 ->
  ab w b alpha1 beta1 v h =  PRes sc v1 h1 ->
  [/\ sc != unknown, valid_hash_table h1 & valid_eval w b sc].

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
rewrite [X in _ <= X]evalS /= (negPf wNw) ifT; last by apply: cmove_has_move ijM.
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

Lemma process_correct ms alpha sc sc1 v v1 h h1 :
  sc != unknown ->
  uniq (map fst ms) -> valid_list ms -> valid_sc ms sc ->
  valid_hash_table h -> valid_ab alpha beta ->
  process ms alpha sc v h =  PRes sc1 v1 h1 ->
  valid_eval w b sc1 /\ valid_hash_table h1.
Proof.
elim: ms alpha sc sc1 v v1 h h1 =>
   [|[m x] ms IH] alpha sc sc1 v v1 h h1 scDu Ums Vms Vsc Vh Vab /=.
  case: neqbP.
    move=> HH.
    suff eD : DRAW <= eval w b <= DRAW.
      case => dE _ <-; split; first by rewrite -dE.
      by apply: valid_has_table_valid_hput.
    have hsE : (hs = lossdraw) \/ (hs = drawwin).
      have := HH; have := hs_range => [] [] -> //;  (try by left); (try by right).
      by have /valid_sc_range := Vsc; case; case => ->.
    case: hsE => hsE.
      apply/andP; split; last by case/andP : hsV; rewrite hsE.
      have scE : sc = drawwin by apply/to_nat_inj; rewrite HH hsE.
      by have := Vsc; rewrite /valid_sc get_max_nil scE; case/andP.
    have scE : sc = lossdraw by apply/to_nat_inj; rewrite HH hsE.
    apply/andP; split; first by case/andP : hsV; rewrite hsE.
    by have := Vsc; rewrite /valid_sc get_max_nil scE; case/andP.
  move=> HH.
  suff eD : down_score sc <= eval w b <= up_score sc.
    case => dE _ <-; split; first by rewrite -dE.
    by apply: valid_has_table_valid_hput.
  by have := Vsc; rewrite /valid_sc get_max_nil.
case E : ab => [s2 v2 h2].
case: (ab_correct _ _ _ _ _ _ _ _ _ _ _ E) => // [|s2Nu h2V vEs2].
  by apply: valid_ab_rev.
have [Vms1 [i [j [ijM mE]]]] := valid_cons _ _ Vms. 
have mmE : make_move m w = mk_move w i j.
  by rewrite [m]mE /mk_move /make_move lorC.
have us2Le : wcomp (up_score s2) <= eval w b.
  have /(leq_trans _)-> // := leq_eval_move _ _ ijM.
  by apply: leq_wcomp; rewrite -mmE; case/andP: vEs2.
case: nltbP => [rs2Lb|/negP].
  case: nlebP => [HH|/negP].
    apply: IH => //; first by case/andP:  Ums.
    rewrite /valid_sc (@get_max_cons (m, x) i j) //.
    apply: leq_down_score HH => //.
    - by have := evalOr b (mk_move w i j); case/or3P => /eqP->;
        try (by apply: Or31); try (by apply: Or32); apply: Or33.
    - by apply: get_max_range.
    - by move: s2Nu; move/valid_evalE: vEs2; case; case=> -> //;
      try(by left; (try by apply: Or31);(try by apply: Or32); apply: Or33);
        right; (try by left); right.
    - by move: scDu; move/valid_sc_range: Vsc; case; case=> -> //;
      try(by left; (try by apply: Or31);(try by apply: Or32); apply: Or33);
        right; (try by left); right.
    have := s2Nu; have := vEs2.
    by rewrite /valid_eval; move/valid_evalE : vEs2; rewrite mmE;
          case; case=> ->;
          case /or3P: (evalOr b (mk_move w i j)) => /eqP->.
  rewrite -ltnNge=> scLrs2.
  case: nlebP => [Hd|/negP].
    apply: IH => //.
    - by move/valid_evalE : vEs2; case; case => ->.
    - by case/andP: Ums.
    rewrite /valid_sc (@get_max_cons (m, x) i j) //. 
    apply: ltn_down_score scLrs2 => //.
    - by have := evalOr b (mk_move w i j); case/or3P => /eqP->;
        try (by apply: Or31); try (by apply: Or32); apply: Or33.
    - by apply: get_max_range.
    - by move: s2Nu; move/valid_evalE: vEs2; case; case=> -> //;
      try(by left; (try by apply: Or31);(try by apply: Or32); apply: Or33);
        right; (try by left); right.
    - by move: scDu; move/valid_sc_range: Vsc; case; case=> -> //;
      try(by left; (try by apply: Or31);(try by apply: Or32); apply: Or33);
        right; (try by left); right.
    have := s2Nu; have := vEs2.
    by rewrite /valid_eval; move/valid_evalE : vEs2; rewrite mmE;
          case; case=> ->;
          case /or3P: (evalOr b (mk_move w i j)) => /eqP->.    
  rewrite -ltnNge => aLrs2. 
  apply: IH => //.
  - by move/valid_evalE : vEs2; case; case => ->.
  - by case/andP: Ums.
  - rewrite /valid_sc (@get_max_cons (m, x) i j) //. 
    apply: ltn_down_score scLrs2 => //.
    - by have := evalOr b (mk_move w i j); case/or3P => /eqP->;
        try (by apply: Or31); try (by apply: Or32); apply: Or33.
    - by apply: get_max_range.
    - by move: s2Nu; move/valid_evalE: vEs2; case; case=> -> //;
      try(by left; (try by apply: Or31);(try by apply: Or32); apply: Or33);
        right; (try by left); right.
    - by move: scDu; move/valid_sc_range: Vsc; case; case=> -> //;
      try(by left; (try by apply: Or31);(try by apply: Or32); apply: Or33);
        right; (try by left); right.
    have := s2Nu; have := vEs2.
    by rewrite /valid_eval; move/valid_evalE : vEs2; rewrite mmE;
          case; case=> ->;
          case /or3P: (evalOr b (mk_move w i j)) => /eqP->.
  have betaE : (beta == draw) || (beta == win).
    by move: Vab; rewrite /valid_ab; case: eqP => // _ /andP[_ ->]; rewrite orbT.
  have alphaE : (alpha == loss) || (alpha == draw).
    by move: Vab; rewrite /valid_ab; case: eqP => // _ /andP[].
  rewrite /valid_ab.
  have := rs2Lb.
  by have [] := valid_evalE _ _ _ vEs2; case=> -> //=;
    case/orP : betaE => /eqP-> //.
rewrite -leqNgt => bLrs2.
case: nlebP => [Hd|/negP].
  apply: IH => //; first by case/andP: Ums.
  rewrite /valid_sc (@get_max_cons (m, x) i j) //.
  apply: leq_down_score Hd => //.
  - by have := evalOr b (mk_move w i j); case/or3P => /eqP->;
      try (by apply: Or31); try (by apply: Or32); apply: Or33.
  - by apply: get_max_range.
  - by move: s2Nu; move/valid_evalE: vEs2; case; case=> -> //;
    try(by left; (try by apply: Or31);(try by apply: Or32); apply: Or33);
      right; (try by left); right.
  - by move: scDu; move/valid_sc_range: Vsc; case; case=> -> //;
    try(by left; (try by apply: Or31);(try by apply: Or32); apply: Or33);
      right; (try by left); right.
  have := s2Nu; have := vEs2.
  by rewrite /valid_eval; move/valid_evalE : vEs2; rewrite mmE;
        case; case=> ->;
        case /or3P: (evalOr b (mk_move w i j)) => /eqP->.
rewrite -ltnNge => scLrs2.
case: nlebP => [_|/negP].
  apply: IH => //.
  - by move/valid_evalE : vEs2; case; case => ->.
  - by case/andP: Ums.
- rewrite /valid_sc (@get_max_cons (m, x) i j) //. 
  apply: ltn_down_score scLrs2 => //.
  - by have := evalOr b (mk_move w i j); case/or3P => /eqP->;
      try (by apply: Or31); try (by apply: Or32); apply: Or33.
  - by apply: get_max_range.
  - by move: s2Nu; move/valid_evalE: vEs2; case; case=> -> //;
    try(by left; (try by apply: Or31);(try by apply: Or32); apply: Or33);
      right; (try by left); right.
  - by move: scDu; move/valid_sc_range: Vsc; case; case=> -> //;
    try(by left; (try by apply: Or31);(try by apply: Or32); apply: Or33);
      right; (try by left); right.
  have := s2Nu; have := vEs2.
  by rewrite /valid_eval; move/valid_evalE : vEs2; rewrite mmE;
          case; case=> ->;
          case /or3P: (evalOr b (mk_move w i j)) => /eqP->.
rewrite -ltnNge => aLrs2.
case: (neqbP _ draw) => rs2Ed; last first.
  rewrite andFb.
  case: neqbP => rs2El.
    have s2E : s2 = lossdraw.
      by have := rs2El; have [] := valid_evalE _ _ _ vEs2 => [] [] ->.
    case: neqbP => hsE.
      suff eD : DRAW <= eval w b <= DRAW.
        rewrite andTb; case => dE _ <-; split; first by rewrite -dE.
        by apply: valid_has_table_valid_hput => //.
      have hsE1 : hs = lossdraw by apply: to_nat_inj.
      have {vEs2} := vEs2.
      rewrite s2E /valid_eval -[down_score _]/LOSS -[up_score _]/DRAW => vEs2.
      have := hsV.
      rewrite hsE1 /valid_eval -[down_score _]/LOSS -[up_score _]/DRAW => hsV1.
      apply/andP; split; last by case/andP: hsV1.
      by have := us2Le; rewrite s2E. 
    suff eD : down_score (rev_val s2) <= eval w b <= up_score (rev_val s2).
      rewrite andTb; case => dE _ <-; split; first by rewrite -dE.
      by apply: valid_has_table_valid_hput.
    have {vEs2} := vEs2.
    rewrite s2E /valid_eval -[down_score _]/LOSS -[up_score _]/DRAW => vEs2.
    rewrite -[down_score _]/DRAW -[up_score _]/WIN.
    apply/andP; split; last by apply: leq_eval_win.
    by have := us2Le; rewrite s2E.  
  suff eD : down_score (rev_val s2) <= eval w b <= up_score (rev_val s2).
    rewrite andFb; case => dE _ <-; split; first by rewrite -dE.
    by apply: valid_has_table_valid_hput.
  have s2El : s2 = loss.
    move: bLrs2 rs2Ed rs2El.
    have /orP[/eqP->|/eqP->] : (beta == draw) || (beta == win).
    - by move: Vab; rewrite /valid_ab; case: eqP => // _ /andP[_ ->]; rewrite orbT.
    - by move/valid_evalE: vEs2; case; case => ->.
    by move/valid_evalE: vEs2; case; case => ->.
  suff -> : eval w b = WIN by rewrite s2El.
  apply/eqP/eval_winP; right.
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
      case => dE _ <-; split; first by rewrite -dE.
      by apply: valid_has_table_valid_hput.
    apply/andP; split; last first.
      by move: hsV; rewrite /valid_eval hsE; case/andP.
    by have := us2Le; rewrite s2E.
  suff eD : DRAW <= eval w b <= WIN.
    case => dE _ <-; split; first by rewrite -dE.
    by apply: valid_has_table_valid_hput.
  apply/andP; split; last by apply: leq_eval_win.
  by have := us2Le; rewrite s2E.
suff eD : DRAW <= eval w b <= DRAW.
  rewrite s2E andFb; case => dE _ <-; split; first by rewrite -dE.
  by apply: valid_has_table_valid_hput.
case: ms {IH}ems Ums Vms Vsc Vms1 => // ems Ums Vms Vsc Vms1.
rewrite -get_max_nil (get_max_cons (m,x) i j) //.
rewrite -{1}[DRAW]/(down_score (rev_val draw)) -{1}[DRAW]/(up_score (rev_val draw)).
rewrite -s2E.
apply: ltn_down_score scLrs2 => //.
- by have /or3P[] := evalOr  b (mk_move w i j) => /eqP->; try (by apply: Or31);
     try (by apply: Or32); apply: Or33.
- by apply: get_max_range.
- by rewrite s2E; left; apply: Or32.
- by move: scDu; move/valid_sc_range : Vsc; case; case => -> //;
     try(by left; (try by apply: Or31);(try by apply: Or32); apply: Or33);
     right; (try by left); right.
have := vEs2.
rewrite /valid_eval s2E mmE.
by have /or3P[] := evalOr  b (mk_move w i j) => /eqP->.
Qed.

Variables (wstate bstate : int) (beta : int) (lvisited : int) 
          (height hscore :  int)
          (alpha_beta : int -> int -> int -> int -> int -> 
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
