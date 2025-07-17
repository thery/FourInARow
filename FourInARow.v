(******************************************************************************)
(*        A program that performs a perfect play for 4 in a row               *)
(*        This is directly inspired by a program by John Tromp                *)
(******************************************************************************)

From Stdlib Require Import ssreflect ZArith Ascii List String PrimInt63.
From Stdlib Require Import PArray.

Open Scope int63_scope.

Import PrimInt63Notations.
Import Uint63Axioms.


Notation " x - y " := (sub x y).
Notation " x + y " := (add x y).
Notation " x * y " := (mul x y).
Notation " x / y " := (div x y).
Notation " x <=? y " := (leb x y).
Notation " x <? y " := (leb x y).
Notation " x ?= y " := (compare x y).
Notation " x =? y " := (eqb x y).
Notation " x << y " := (lsl x y) (at level 10).
Notation " x >> y " := (lsr x y) (at level 10).
Infix "land" := land (at level 10).
Infix "lor" := lor (at level 10).
Infix "mod" := Uint63.mod (at level 40).



(*
Parameter array : Type -> Type.
Parameter set : forall {T : Type}, array T -> int -> T -> array T.
Parameter get : forall {T : Type}, array T -> int -> T.
Parameter foldi : forall {A : Type}, (int -> A -> A) -> int -> int -> A -> A.
*)

(* Naive implementation of foldi *)
Fixpoint nfoldi {A : Type} (f : int -> A -> A) n (v : int) r :=
  if n is (S n1) then nfoldi f n1 (v - 1) (f v r) else f v r.
Definition foldi {A : Type} (f : int -> A -> A) v1 v2 r :=
  if v1 <=? v2 then nfoldi f (Z.to_nat (to_Z (v2 - v1))) v2 r
  else r.

(*
Notation " a '.[' b ']' " := (get a b) (at level 32,
  format " a '.[' b ] ").
Notation " a '.[' b '<-' c ']' " := (set a b c) (at level 32,
  format " a '.[' b  '<-'  c ] ").
*)

(* 
Module PArray.


Parameter make : forall {T : Type}, int -> T -> array T.

End PArray.
*)

Fixpoint init_matrix (A : Type) n nn a (v : A) m {struct n} :=
  match n with 
  | O => a
  | S n1 => init_matrix A n1 (nn - 1) a.[nn - 1 <- make m v] v m
  end.
Arguments init_matrix[A].

Definition to_nat n := Z.to_nat (to_Z n).

Definition make_matrix (A: Type) n m (v : A) :=
  let a := make n (make 0 v) in 
  init_matrix (to_nat n) n a v m.

Arguments make_matrix[A].

(* 63 Arithmetic *)

Definition one := of_Z 1.
Definition zero := of_Z 0.

Definition decr s := s - 1.
Definition incr s := s + 1.
Definition is_zero s := eqb s zero.
Definition is_nzero s := negb (eqb s zero).

(* Width of the board *)
Definition width := 7.
Definition nwidth := 7%nat.
(* Height of the board *)
Definition height := 6.
Definition nheight := 6%nat.
(* Shift for moving horizontally *)
Definition horizontal := Eval compute in height + 1.
Definition horizontal2 := Eval compute in 2 * horizontal.
(* Shift for moving vertically *)
Definition vertical := 1.
Definition vertical2 := Eval compute in 2 * vertical.
(* Shift for moving up right *)
Definition up_right := Eval compute in horizontal + 1.
Definition up_right2 := Eval compute in 2 * up_right.
(* Shift for moving up left *)
Definition up_left := Eval compute in horizontal - 1.
Definition up_left2 := Eval compute in 2 * up_left.

Register horizontal as Inline.
Register horizontal2 as Inline.
Register vertical as Inline.
Register vertical2 as Inline.
Register up_right as Inline.
Register up_right2 as Inline.
Register up_left as Inline.
Register up_left2 as Inline.

(* Size of the board *)
Definition size := width * height.
(* Real size of the board *)
Definition number_of_cells := width * horizontal.
(* All the cells are set to one *)
Definition all_set := decr (one << number_of_cells).
(* Cells of the first column *)
Definition first_column := decr (one << height).
(* Cells of the first column + border *)
Definition full_first_column := decr (one << horizontal).
(* Cells at the bottom of the board *)
Definition bottom := div all_set (decr (one << horizontal)).

(* Cells at the top *)
Definition top := bottom << height.
(* Unknown valuation *)
Definition unknown := 0.
(* Loss valuation *)
Definition loss := 1.
(* Loss or draw valuation *)
Definition lossdraw := 2.
(* Draw valuation *)
Definition draw := 3.
(* Draw or win valuation *)
Definition drawwin := 4.
(* Win valuation *)
Definition win := 5.
(* Loss + win valuation (to reverse) *)
Definition losswin := loss + win.
(* Size of the lock 25 bits *)
Definition locksize := 25.
(* Size of the remain bits that are not in the lock *)
Definition slocksize := number_of_cells - locksize.
(* Size of hash table should have HPRIME > 2^SLOCKSIZE *)
(* Definition hprime := 8388609. *)
Definition hprime := 16777121.
(* Mask for the lock  *)
Definition lockmask := (1 << locksize) - 1.
(* Size of the score 3 *)
Definition scoresize := 3.
(* Mask for the size *)
Definition scoremask := (1 << scoresize) - 1.
(* Size of the lock + score *)
Definition scorelocksize := locksize + scoresize.
(* Size of the lock + score *)
Definition scorelockmask := (1 << scorelocksize) - 1.
(* Log of the number of hash tables *)
Definition lhash := 3.
(* Number of hash tables *)
Definition nhash := 1 << lhash.
(* Mask for hash tables *)
Definition mhash := nhash - 1.
(* Symmetry level *)
Definition sym_level := 10.

(* Hash table because of size limitation we crea(* Size of the board *)
te a matrix *)
Definition make_hash (u : unit) := 
  make_matrix nhash (2 * (hprime/nhash) + 1) 0.

Definition min m n := match m ?= n with Lt => m | _ => n end.
Definition max m n := match m ?= n with Lt => n | _ => m end.

(* Score of the different cells *)
Definition values :=
  let t := PArray.make number_of_cells 0 in 
  foldi (fun i t =>
    foldi (fun j t =>
      let v := 3 + min 3 i  
                 + min 3 (min i j) + min 3 j
                 + min 3 (min ((width + 1) / 2 - i) j) in
      let t := (t.[horizontal * i + j <- v]) in
      let t := (t.[horizontal * (width - 1 - i) + height - 1 - j <- v]) in
      let t := (t.[horizontal * i + height - 1 - j <- v]) in
      (t.[horizontal * (width - 1 - i) + j <- v]))
      0 ((horizontal / 2) - 1) t)
    0 ((width + 1) / 2 - 1) t.

Definition logand2 s dir dir2 :=
  let s1 := s land (s >> dir) in
  let s2 := s1 land (s1 >> dir2) in is_zero s2.

Register logand2 as Inline.

(* Check if the position is won *)
Definition is_won state :=
   (* horizontal win *)
  if logand2 state horizontal horizontal2 then
  if logand2 state vertical vertical2 then
  if logand2 state up_right up_right2 then
  if logand2 state up_left up_left2 then false
  else true
  else true
  else true
  else true.

(* Get the border *)
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

Check get_code.
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


