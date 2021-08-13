(*
   Ripple Carry Adder Definition and Proof.
*)

Require Import Bool.

Infix "(+)" := xorb  (at level 38, left associativity)  : bool_scope.

Definition nandb a b := negb (andb a b).
Infix "!&" := nandb  (at level 40, left associativity)  : bool_scope.

Definition norb a b := negb (orb a b).

Definition bool_to_nat (b : bool) :=
  match b with
  | true => 1
  | false => 0
  end.

Coercion bool_to_nat : bool >-> nat.

(* functional half_adder and full_adder. *)

Definition half_adder (a b : bool) : bool * bool := (* sum,carry *)
  pair (a (+) b) (a && b).

Definition full_adder (a b cin : bool) : bool * bool := (* sum,carry *)
  let (s1,c1) := half_adder a b in
  let (s2,c2) := half_adder s1 cin in
    pair s2 (c1 || c2).


(* circuit design based on signal data structure. *)

Inductive Signal : Set :=
  | And2  : Signal -> Signal -> Signal
  | Or2   : Signal -> Signal -> Signal
  | Xor2  : Signal -> Signal -> Signal
  | Eq2   : Signal -> Signal -> Signal
  | Nand2 : Signal -> Signal -> Signal
  | Nor2  : Signal -> Signal -> Signal
  | Not1  : Signal -> Signal
  | Bit1  : Signal
  | Bit0  : Signal
.

Fixpoint s2b (s:Signal) : bool :=
 match s with
   | Bit0 => false
   | Bit1 => true
   | Not1 r => negb (s2b r)
   | And2  r1 r2 => andb  (s2b r1) (s2b r2)
   | Or2   r1 r2 => orb   (s2b r1) (s2b r2)
   | Xor2  r1 r2 => xorb  (s2b r1) (s2b r2)
   | Eq2   r1 r2 => eqb   (s2b r1) (s2b r2)
   | Nand2 r1 r2 => nandb (s2b r1) (s2b r2)
   | Nor2  r1 r2 => norb  (s2b r1) (s2b r2)
 end.

Declare Scope Signal_scope.
Open Scope Signal_scope.
Infix "||"  := Or2   (at level 50, left associativity)  : Signal_scope.
Infix "&&"  := And2  (at level 40, left associativity)  : Signal_scope.
Infix "!&"  := Nand2 (at level 40, left associativity)  : Signal_scope.
Infix "=="  := Eq2   (at level 38, left associativity)  : Signal_scope.
Infix "(+)" := Xor2  (at level 38, left associativity)  : Signal_scope.
Infix "(-)" := Nor2  (at level 38, left associativity)  : Signal_scope.


Definition Signal2 := (Signal * Signal)%type.

Definition half_adder_s (a b : Signal) : Signal2 := 
 pair (a (+) b) (a && b).
 
Definition full_adder_s (a b cin : Signal) : Signal2 :=
  let (s1,c1) := half_adder_s a b in
  let (s2,c2) := half_adder_s s1 cin in
    pair s2 (c1 || c2).

Compute half_adder true false.
Compute half_adder_s Bit1 Bit0.

Definition signal2bool (s:Signal) : bool := s2b s.

Definition b2s (b:bool) : Signal :=
  match b with
   | true  => Bit1
   | false => Bit0
  end.

Definition half_adder_b (a b: bool) : bool * bool :=
   let (sum,cout) := half_adder_s (b2s a) (b2s b) in
      pair (s2b sum) (s2b cout).  

Compute half_adder_b true false.

Definition full_adder_s_tp := Signal -> Signal -> Signal -> Signal2.

Definition mk_full_adder_b (full_adder_s:full_adder_s_tp)
   (a b cin: bool) : bool * bool :=
   let (sum,cout) := full_adder_s (b2s a) (b2s b) (b2s cin) in
      pair (s2b sum) (s2b cout).

Definition full_adder_b (a b cin: bool) : bool * bool :=
   mk_full_adder_b full_adder_s a b cin.

(* parameterized full_adder verification. *)
Definition ck_full_adder_truth_tbl full_adder : Prop :=
  forall a b cin : bool,
  full_adder a b cin (* (sum, carry) *) =  
    match a,b,cin with
    | false,false,false  => (false, false)
    | false,false,true   => (true,  false)
    | false,true, false  => (true,  false)
    | false,true, true   => (false, true)
    | true, false,false  => (true,  false)
    | true, false,true   => (false, true)
    | true, true, false  => (false, true)
    | true, true, true   => (true,  true)
   end.

Definition full_adder_tp := bool -> bool -> bool -> bool * bool.

(* 2nd verification of the correctness of full_adder. *)
Definition ck_full_adder_ok
 (full_adder : full_adder_tp) : Prop :=
 forall a b cin : bool,
   let (sum,cout) := full_adder a b cin in 
     a + b + cin = 2 * cout + sum.

Theorem full_adder_b_truth_tbl : 
 ck_full_adder_truth_tbl full_adder_b.
Proof.
  unfold ck_full_adder_truth_tbl.
  destruct a, b, cin; reflexivity.
Qed.  

Theorem full_adder_ok_b : ck_full_adder_ok full_adder_b.
  unfold ck_full_adder_ok.
  destruct a,b,cin; reflexivity.
Qed.

Definition full_adder_syn1_s (a b cin : Signal) : Signal2 := 
  let sum  := a (+) b (+) cin in
  let cout := cin && (a (+) b) || (a && b) in
   (sum, cout).

Definition full_adder_syn1_b (a b cin : bool) : bool*bool := 
   mk_full_adder_b full_adder_syn1_s a b cin.

Theorem full_adder_syn1_b_truth_tbl : 
 ck_full_adder_truth_tbl full_adder_syn1_b.
Proof.
  unfold ck_full_adder_truth_tbl.
  destruct a, b, cin; reflexivity.
Qed.  

Theorem full_adder_ok_syn1_b : ck_full_adder_ok full_adder_syn1_b.
  unfold ck_full_adder_ok.
  destruct a,b,cin; reflexivity.
Qed.

Definition full_adder_syn2_s (a b cin : Signal) : Signal2 :=
  let sum  := a (+) b (+) cin in
  let cout := (a && b) || (b && cin) || (a && cin) in
   (sum, cout).

Definition full_adder_syn2_b (a b cin : bool) : bool * bool := (* sum,carry *)
   mk_full_adder_b full_adder_syn2_s a b cin.

Theorem full_adder_syn2_b_truth_tbl : 
 ck_full_adder_truth_tbl full_adder_syn2_b.
Proof.
  unfold ck_full_adder_truth_tbl.
  destruct a, b, cin; reflexivity.
Qed.

Theorem full_adder_syn2_b_ok : 
  ck_full_adder_ok full_adder_syn2_b.
  unfold ck_full_adder_ok.
  destruct a,b,cin; reflexivity.
Qed.

Definition full_adder_nand_s (a b cin : Signal) : Signal2 := 
 let n1 := a !& b in
 let n21 := a !& n1 in let n22 := b !& n1 in
 let n3  := n21 !& n22 in
 let n4  := n3 !& cin in
 let n51 := n3 !& n4 in let n52 := n4 !& cin in
 let sum := n51 !& n52 in
 let cout := n4 !& n1 in
  (sum, cout).

Definition full_adder_nand_b (a b cin : bool) : bool * bool := 
   mk_full_adder_b full_adder_nand_s a b cin.

Theorem full_adder_nand_b_truth_tbl : 
 ck_full_adder_truth_tbl full_adder_nand_b.
Proof.
  unfold ck_full_adder_truth_tbl.
  destruct a, b, cin; reflexivity.
Qed.

Theorem full_adder_nand_b_ok : 
  ck_full_adder_ok full_adder_nand_b.
  unfold ck_full_adder_ok.
  destruct a,b,cin; reflexivity.
Qed.

(* structures of each full adder. *)
Compute (full_adder_s Bit0 Bit0 Bit0).
Compute (full_adder_syn1_s Bit0 Bit0 Bit0).
Compute (full_adder_syn2_s Bit0 Bit0 Bit0).
Compute (full_adder_nand_s Bit0 Bit0 Bit0).


(* reference: Ripple Carry and Carry Lookahead Adders / add_with_delay.pdf *)

(* calculate gate delay. *)
Fixpoint gdelay (s:Signal) : nat :=
 match s with
   | Bit0 => 0
   | Bit1 => 0
   | Not1 r => 1 + (gdelay r)
   | And2  r1 r2 => 2 + (max (gdelay r1) (gdelay r2))
   | Or2   r1 r2 => 2 + (max (gdelay r1) (gdelay r2))
   | Xor2  r1 r2 => 3 + (max (gdelay r1) (gdelay r2))
   | Eq2   r1 r2 => 3 + (max (gdelay r1) (gdelay r2))
   | Nand2 r1 r2 => 1 + (max (gdelay r1) (gdelay r2))
   | Nor2  r1 r2 => 1 + (max (gdelay r1) (gdelay r2))
 end.

Definition gdelay2 (sc : Signal2) : nat :=
  let (sum,cout) := sc in
   max (gdelay sum) (gdelay cout).

(* calculation of delays of full adders. *)
Compute gdelay2 (full_adder_s Bit0 Bit0 Bit0).
Compute gdelay2 (full_adder_syn1_s Bit0 Bit0 Bit0).
Compute gdelay2 (full_adder_syn2_s Bit0 Bit0 Bit0).
Compute gdelay2 (full_adder_nand_s Bit0 Bit0 Bit0).

Definition critical2 (sc : Signal2) : nat*nat :=
  let (sum,cout) := sc in
   ((gdelay sum), (gdelay cout)).

Compute critical2 (full_adder_s Bit0 Bit0 Bit0).
Compute critical2 (full_adder_syn1_s Bit0 Bit0 Bit0).
Compute critical2 (full_adder_syn2_s Bit0 Bit0 Bit0).
Compute critical2 (full_adder_nand_s Bit0 Bit0 Bit0).

(* This is not correct aera estimation since duplicated gates counted more than one times. *)
Fixpoint garea (s:Signal) : nat :=
 match s with
   | Bit0 => 0
   | Bit1 => 0
   | Not1 r => 1 + (garea r)
   | And2  r1 r2 => 4  + (garea r1) + (garea r2)
   | Or2   r1 r2 => 4  + (garea r1) + (garea r2)
   | Xor2  r1 r2 => 11 + (garea r1) + (garea r2)
   | Eq2   r1 r2 => 11 + (garea r1) + (garea r2)
   | Nand2 r1 r2 => 3  + (garea r1) + (garea r2)
   | Nor2  r1 r2 => 3  + (garea r1) + (garea r2)
 end.

Definition garea2 (sc : Signal2) : nat :=
  let (sum,cout) := sc in
     (garea sum) + (garea cout).
 
Compute garea2 (full_adder_s Bit0 Bit0 Bit0).
Compute garea2 (full_adder_syn1_s Bit0 Bit0 Bit0).
Compute garea2 (full_adder_syn2_s Bit0 Bit0 Bit0).
Compute garea2 (full_adder_nand_s Bit0 Bit0 Bit0).


Reset Signal.
Require Import Strings.String.

Open Scope string_scope.
 
Inductive Signal : Set :=
  | And2  : Signal -> Signal -> Signal
  | Or2   : Signal -> Signal -> Signal
  | Xor2  : Signal -> Signal -> Signal
  | Eq2   : Signal -> Signal -> Signal
  | Nand2 : Signal -> Signal -> Signal
  | Nor2  : Signal -> Signal -> Signal
  | Not1  : Signal -> Signal
  | Bit1  : Signal
  | Bit0  : Signal
  | Bitv  : string -> Signal
.

Fixpoint s2b (s:Signal) : bool :=
 match s with
   | Bit0 => false
   | Bit1 => true
   | Bitv v => true
   | Not1 r => negb (s2b r)
   | And2  r1 r2 => andb  (s2b r1) (s2b r2)
   | Or2   r1 r2 => orb   (s2b r1) (s2b r2)
   | Xor2  r1 r2 => xorb  (s2b r1) (s2b r2)
   | Eq2   r1 r2 => Bool.eqb   (s2b r1) (s2b r2)
   | Nand2 r1 r2 => nandb (s2b r1) (s2b r2)
   | Nor2  r1 r2 => norb  (s2b r1) (s2b r2)
 end.

Declare Scope Signal_scope.
Open Scope Signal_scope.
Infix "||"  := Or2   (at level 50, left associativity)  : Signal_scope.
Infix "&&"  := And2  (at level 40, left associativity)  : Signal_scope.
Infix "!&"  := Nand2 (at level 40, left associativity)  : Signal_scope.
Infix "=="  := Eq2   (at level 38, left associativity)  : Signal_scope.
Infix "(+)" := Xor2  (at level 38, left associativity)  : Signal_scope.
Infix "(-)" := Nor2  (at level 38, left associativity)  : Signal_scope.


Definition Signal2 := (Signal * Signal)%type.

Definition half_adder_s (a b : Signal) : Signal2 := 
 pair (a (+) b) (a && b).
 
Definition full_adder_s (a b cin : Signal) : Signal2 :=
  let (s1,c1) := half_adder_s a b in
  let (s2,c2) := half_adder_s s1 cin in
    pair s2 (c1 || c2).

Definition full_adder_syn1_s (a b cin : Signal) : Signal2 := 
  let sum  := a (+) b (+) cin in
  let cout := cin && (a (+) b) || (a && b) in
   (sum, cout).

Definition b2s (b:bool) : Signal :=
  match b with
   | true  => Bit1
   | false => Bit0
  end.

Definition full_adder_s_tp := Signal -> Signal -> Signal -> Signal2.

Definition mk_full_adder_b (full_adder_s:full_adder_s_tp)
   (a b cin: bool) : bool * bool :=
   let (sum,cout) := full_adder_s (b2s a) (b2s b) (b2s cin) in
      pair (s2b sum) (s2b cout).

Definition ck_full_adder_truth_tbl full_adder : Prop :=
  forall a b cin : bool,
  full_adder a b cin (* (sum, carry) *) =  
    match a,b,cin with
    | false,false,false  => (false, false)
    | false,false,true   => (true,  false)
    | false,true, false  => (true,  false)
    | false,true, true   => (false, true)
    | true, false,false  => (true,  false)
    | true, false,true   => (false, true)
    | true, true, false  => (false, true)
    | true, true, true   => (true,  true)
   end.

Definition full_adder_tp := bool -> bool -> bool -> bool * bool.

Definition ck_full_adder_ok
 (full_adder : full_adder_tp) : Prop :=
 forall a b cin : bool,
   let (sum,cout) := full_adder a b cin in 
     a + b + cin = 2 * cout + sum.

Definition half_adder_b (a b: bool) : bool * bool :=
   let (sum,cout) := half_adder_s (b2s a) (b2s b) in
      pair (s2b sum) (s2b cout).  

Compute half_adder_b true false.

Definition full_adder_b (a b cin: bool) : bool * bool :=
   mk_full_adder_b full_adder_s a b cin.

Theorem full_adder_b_truth_tbl : 
 ck_full_adder_truth_tbl full_adder_b.
Proof.
  unfold ck_full_adder_truth_tbl.
  destruct a, b, cin; reflexivity.
Qed.  

Theorem full_adder_ok_b : ck_full_adder_ok full_adder_b.
  unfold ck_full_adder_ok.
  destruct a,b,cin; reflexivity.
Qed.


Definition full_adder_syn1_b (a b cin : bool) : bool*bool := 
   mk_full_adder_b full_adder_syn1_s a b cin.

Definition full_adder_syn2_s (a b cin : Signal) : Signal2 :=
  let sum  := a (+) b (+) cin in
  let cout := (a && b) || (b && cin) || (a && cin) in
   (sum, cout).

Definition full_adder_syn2_b (a b cin : bool) : bool * bool := (* sum,carry *)
   mk_full_adder_b full_adder_syn2_s a b cin.

Definition full_adder_nand_s (a b cin : Signal) : Signal2 := 
 let n1 := a !& b in
 let n21 := a !& n1 in let n22 := b !& n1 in
 let n3  := n21 !& n22 in
 let n4  := n3 !& cin in
 let n51 := n3 !& n4 in let n52 := n4 !& cin in
 let sum := n51 !& n52 in
 let cout := n4 !& n1 in
  (sum, cout).

Definition full_adder_nand_b (a b cin : bool) : bool * bool := 
   mk_full_adder_b full_adder_nand_s a b cin.

(* generate verilog code. *)
Fixpoint gv (s:Signal) : string :=
 match s with
   | Bit0        => "1'b0"
   | Bit1        => "1'b1"
   | Bitv v      => v
   | Not1 r      => "~ (" ++ (gv r) ++ ")"
   | And2  r1 r2 => "(" ++ (gv r1) ++ ") & ("  ++ (gv r2) ++ ")"
   | Or2   r1 r2 => "(" ++ (gv r1) ++ ") | ("  ++ (gv r2) ++ ")"
   | Xor2  r1 r2 => "(" ++ (gv r1) ++ ") ^ ("  ++ (gv r2) ++ ")"
   | Eq2   r1 r2 => "(" ++ (gv r1) ++ ") == (" ++ (gv r2) ++ ")"
   | Nand2 r1 r2 => "~(" ++ (gv r1) ++ " & " ++ (gv r2) ++ ")"
   | Nor2  r1 r2 => "(" ++ (gv r1) ++ ") ~| (" ++ (gv r2) ++ ")"
 end.

Definition gv2 (sc : Signal2) : string :=
  let (sum,cout) := sc in
"
    assign sum = " ++ (gv sum) ++ ";
    " ++
    "assign cout = " ++ (gv cout) ++ ";
".

Definition a := Bitv "a".
Definition b := Bitv "b".
Definition c := Bitv "c".
Compute gv2 (full_adder_s      a b c).
Compute gv2 (full_adder_syn1_s a b c).
Compute gv2 (full_adder_syn2_s a b c).
Compute gv2 (full_adder_nand_s a b c).
 
Reset Signal.
Inductive Signal : Set :=
  | And2  : Signal -> Signal -> Signal
  | Or2   : Signal -> Signal -> Signal
  | Xor2  : Signal -> Signal -> Signal
  | Eq2   : Signal -> Signal -> Signal
  | Nand2 : Signal -> Signal -> Signal
  | Nor2  : Signal -> Signal -> Signal
  | Not1  : Signal -> Signal
  | Bit1  : Signal
  | Bit0  : Signal
  | Bitv  : string -> Signal
  | Letb  : string -> Signal -> Signal -> Signal
with Signal_Pair : Set :=
  | Spair : Signal -> Signal -> Signal_Pair
  | Letb2 : string -> Signal -> Signal_Pair -> Signal_Pair
.

Fixpoint subst (s:Signal) (v:string) (e:Signal) : Signal :=
  let st s := subst s v e in
  match s with
   | Bit0 => Bit0
   | Bit1 => Bit1
   | Not1 r => Not1 (st r)
   | And2  r1 r2 => And2  (st r1) (st r2)
   | Or2   r1 r2 => Or2   (st r1) (st r2)
   | Xor2  r1 r2 => Xor2  (st r1) (st r2)
   | Eq2   r1 r2 => Eq2   (st r1) (st r2)
   | Nand2 r1 r2 => Nand2 (st r1) (st r2)
   | Nor2  r1 r2 => Nor2  (st r1) (st r2)
   | Letb v e1 e2 => subst e1 v e2
   | Bitv v' => if eqb v v' then e else s
  end.



Declare Scope Signal_scope.
Open Scope Signal_scope.
Infix "||"  := Or2   (at level 50, left associativity)  : Signal_scope.
Infix "&&"  := And2  (at level 40, left associativity)  : Signal_scope.
Infix "!&"  := Nand2 (at level 40, left associativity)  : Signal_scope.
Infix "=="  := Eq2   (at level 38, left associativity)  : Signal_scope.
Infix "(+)" := Xor2  (at level 38, left associativity)  : Signal_scope.
Infix "(-)" := Nor2  (at level 38, left associativity)  : Signal_scope.


Definition Signal2 := (Signal * Signal)%type.


Definition half_adder_s (a b : Signal) : Signal2 := 
 pair (a (+) b) (a && b).
 
Definition full_adder_s (a b cin : Signal) : Signal2 :=
  let (s1,c1) := half_adder_s a b in
  let (s2,c2) := half_adder_s s1 cin in
    pair s2 (c1 || c2).

Compute half_adder true false.
Compute half_adder_s Bit1 Bit0.

Definition b2s (b:bool) : Signal :=
  match b with
   | true  => Bit1
   | false => Bit0
  end.

Fail Definition full_adder_nand_s (a b cin : Signal) : Signal2 := 
 let n1 := Bitv "n1" in 
 let n21 := Bitv "n21" in let n22 := Bitv "n22" in
 let n3 := Bitv "n3" in
 let n4 := Bitv "n4" in
 let n51 := Bitv "n51" in let n52 := Bitv "n52" in
 let sum := Bitv "sum" in let cout := Bitv "cout" in
 Letb "n1"  (a !& b)
 (Letb "n21" (a !& n1) (Letb "n22" (b !& n1)
 (Letb "n3"  (n21 !& n22)
 (Letb "n4"  (n3 !& cin)
 (Letb "n51" (n3 !& n4) (Letb "n52" (n4 !& cin)
 (Letb "sum" (n51 !& n52)
 (Letb "cout" (n4 !& n1)
    (pair sum cout))))))))).

Definition full_adder_nand_s (a b cin : Signal) : Signal_Pair := 
 let n1 := Bitv "n1" in 
 let n21 := Bitv "n21" in let n22 := Bitv "n22" in
 let n3 := Bitv "n3" in
 let n4 := Bitv "n4" in
 let n51 := Bitv "n51" in let n52 := Bitv "n52" in
 let sum := Bitv "sum" in let cout := Bitv "cout" in
 Letb2 "n1"  (a !& b)
 (Letb2 "n21" (a !& n1) (Letb2 "n22" (b !& n1)
 (Letb2 "n3"  (n21 !& n22)
 (Letb2 "n4"  (n3 !& cin)
 (Letb2 "n51" (n3 !& n4) (Letb2 "n52" (n4 !& cin)
 (Letb2 "sum" (n51 !& n52)
 (Letb2 "cout" (n4 !& n1)
   (Spair sum cout))))))))).
(*
 let n1 := a !& b in
 let n21 := a !& n1 in let n22 := b !& n1 in
 let n3  := n21 !& n22 in
 let n4  := n3 !& cin in
 let n51 := n3 !& n4 in let n52 := n4 !& cin in
 let sum := n51 !& n52 in
 let cout := n4 !& n1 in
  (sum, cout).
*)

Definition full_adder_syn1_s (a b cin : Signal) : Signal2 := 
  let sum  := a (+) b (+) cin in
  let cout := cin && (a (+) b) || (a && b) in
   (sum, cout).

Definition full_adder_syn2_s (a b cin : Signal) : Signal2 :=
  let sum  := a (+) b (+) cin in
  let cout := (a && b) || (b && cin) || (a && cin) in
   (sum, cout).


(* structures of each full adder. *)
Compute (full_adder_s Bit0 Bit0 Bit0).
Compute (full_adder_syn1_s Bit0 Bit0 Bit0).
Compute (full_adder_syn2_s Bit0 Bit0 Bit0).
Compute (full_adder_nand_s (Bitv "a") (Bitv "b") (Bitv "c")).

(* generate verilog code. *)
Fixpoint gv (s:Signal) : string :=
 match s with
   | Bit0        => "1'b0"
   | Bit1        => "1'b1"
   | Bitv v      => v
   | Not1 r      => "~ (" ++ (gv r) ++ ")"
   | And2  r1 r2 => "(" ++ (gv r1) ++ ") & ("  ++ (gv r2) ++ ")"
   | Or2   r1 r2 => "(" ++ (gv r1) ++ ") | ("  ++ (gv r2) ++ ")"
   | Xor2  r1 r2 => "(" ++ (gv r1) ++ ") ^ ("  ++ (gv r2) ++ ")"
   | Eq2   r1 r2 => "(" ++ (gv r1) ++ ") == (" ++ (gv r2) ++ ")"
   | Nand2 r1 r2 => "(" ++ (gv r1) ++ ") ~& (" ++ (gv r2) ++ ")"
   | Nor2  r1 r2 => "(" ++ (gv r1) ++ ") ~| (" ++ (gv r2) ++ ")"
   | Letb v r1 r2 => "
      assign " ++ v ++ " = " ++ (gv r1) ++ ";
   " ++ (gv r2) ++ ";"
 end
.

Definition gv2 (sc : Signal2) : string :=
  let (sum,cout) := sc in
"
    assign sum = " ++ (gv sum) ++ ";
    assign cout = " ++ (gv cout) ++ ";
".


(*
with Signal_Pair : Set :=
  | Spair : Signal -> Signal -> Signal_Pair
  | Letb2 : string -> Signal -> Signal_Pair -> Signal_Pair
.
*)
 
Fixpoint gv_pair (s2:Signal_Pair) : string :=
  match s2 with
   | Spair r1 r2   => "" (* gv2 (r1,r2) *)
   | Letb2 v r1 r2 => 
"
   assign " ++ v ++ " = " ++ (gv r1) ++ ";" ++ (gv_pair r2) 
 end
.
Definition x := Bitv "a".
Definition y := Bitv "b".
Definition z := Bitv "c".
Compute gv2 (full_adder_s      x y z).
Compute gv2 (full_adder_syn1_s x y z).
Compute gv2 (full_adder_syn2_s x y z).
Compute gv_pair (full_adder_nand_s x y z).


Fixpoint signal2bool (s:Signal) (env : string -> bool) {struct s} : bool :=
 let s2b s := signal2bool s env in
 match s with
   | Bit0 => false
   | Bit1 => true
   | Not1 r => negb (s2b r)
   | And2  r1 r2 => andb  (s2b r1) (s2b r2)
   | Or2   r1 r2 => orb   (s2b r1) (s2b r2)
   | Xor2  r1 r2 => xorb  (s2b r1) (s2b r2)
   | Eq2   r1 r2 => negb (xorb  (s2b r1) (s2b r2))
   | Nand2 r1 r2 => nandb (s2b r1) (s2b r2)
   | Nor2  r1 r2 => negb (orb (s2b r1) (s2b r2))
   | Bitv v => env v
   | Letb v e1 e2 => 
       let v1 := s2b e1 in
       let env1 x := if eqb x v then v1 else env x in
          signal2bool e2 env1
 end.

Definition s2b s := signal2bool s (fun x => true).

Definition half_adder_b (a b: bool) : bool * bool :=
   let (sum,cout) := half_adder_s (b2s a) (b2s b) in
      pair (s2b sum) (s2b cout).  

Compute half_adder_b true false.
 
Definition full_adder_s_tp := Signal -> Signal -> Signal -> Signal2.

Definition mk_full_adder_b (full_adder_s:full_adder_s_tp)
   (a b cin: bool) : bool * bool :=
   let (sum,cout) := full_adder_s (b2s a) (b2s b) (b2s cin) in
      pair (s2b sum) (s2b cout).

Definition full_adder_b (a b cin: bool) : bool * bool :=
   mk_full_adder_b full_adder_s a b cin.

Definition full_adder_tp := bool -> bool -> bool -> bool * bool.

(* 2nd verification of the correctness of full_adder. *)
Definition ck_full_adder_ok
 (full_adder : full_adder_tp) : Prop :=
 forall a b cin : bool,
   let (sum,cout) := full_adder a b cin in 
     a + b + cin = 2 * cout + sum.

(* parameterized full_adder verification. *)
Definition ck_full_adder_truth_tbl full_adder : Prop :=
  forall a b cin : bool,
  full_adder a b cin (* (sum, carry) *) =  
    match a,b,cin with
    | false,false,false  => (false, false)
    | false,false,true   => (true,  false)
    | false,true, false  => (true,  false)
    | false,true, true   => (false, true)
    | true, false,false  => (true,  false)
    | true, false,true   => (false, true)
    | true, true, false  => (false, true)
    | true, true, true   => (true,  true)
   end.

Theorem full_adder_b_truth_tbl : 
 ck_full_adder_truth_tbl full_adder_b.
Proof.
  unfold ck_full_adder_truth_tbl.
  destruct a, b, cin; reflexivity.
Qed.  

Theorem full_adder_ok_b : ck_full_adder_ok full_adder_b.
  unfold ck_full_adder_ok.
  destruct a,b,cin; reflexivity.
Qed.

Definition full_adder_syn1_b (a b cin : bool) : bool*bool := 
   mk_full_adder_b full_adder_syn1_s a b cin.

Theorem full_adder_syn1_b_truth_tbl : 
 ck_full_adder_truth_tbl full_adder_syn1_b.
Proof.
  unfold ck_full_adder_truth_tbl.
  destruct a, b, cin; reflexivity.
Qed.  

Theorem full_adder_ok_syn1_b : ck_full_adder_ok full_adder_syn1_b.
  unfold ck_full_adder_ok.
  destruct a,b,cin; reflexivity.
Qed.



Definition full_adder_syn2_b (a b cin : bool) : bool * bool := (* sum,carry *)
   mk_full_adder_b full_adder_syn2_s a b cin.

Theorem full_adder_syn2_b_truth_tbl : 
 ck_full_adder_truth_tbl full_adder_syn2_b.
Proof.
  unfold ck_full_adder_truth_tbl.
  destruct a, b, cin; reflexivity.
Qed.

Theorem full_adder_syn2_b_ok : 
  ck_full_adder_ok full_adder_syn2_b.
  unfold ck_full_adder_ok.
  destruct a,b,cin; reflexivity.
Qed.

Definition ck_nand_full_adder_truth_tbl full_adder : Prop :=
  forall a b cin : bool,
  full_adder a b cin (* (sum, carry) *) =  
    match a,b,cin with
    | false,false,false  => (false, false)
    | false,false,true   => (true,  false)
    | false,true, false  => (true,  false)
    | false,true, true   => (false, true)
    | true, false,false  => (true,  false)
    | true, false,true   => (false, true)
    | true, true, false  => (false, true)
    | true, true, true   => (true,  true)
   end.

Fixpoint sigpair2bool (s:Signal_Pair) (env:string -> bool) {struct s} : bool * bool :=
 let s2b s := signal2bool s env in
  match s with
   | Spair r1 r2 => pair (s2b r1) (s2b r2)
   | Letb2 v e1 e2 => 
       let v1 := s2b e1 in
       let env1 x := if eqb x v then v1 else env x in
          sigpair2bool e2 env1
  end.

Definition sp2b s := sigpair2bool s (fun x => true).

Definition nand_full_adder_s_tp := 
  Signal -> Signal -> Signal -> Signal_Pair.

Definition mk_nand_full_adder_b (full_adder_s:nand_full_adder_s_tp)
   (a b cin: bool) : bool * bool :=
    sp2b (full_adder_s (b2s a) (b2s b) (b2s cin)).

Definition full_adder_nand_b (a b cin : bool) : bool * bool := 
   mk_nand_full_adder_b full_adder_nand_s a b cin.

Theorem full_adder_nand_b_truth_tbl : 
 ck_full_adder_truth_tbl full_adder_nand_b.
Proof.
  unfold ck_full_adder_truth_tbl.
  destruct a, b, cin; reflexivity.
Qed.

Theorem full_adder_nand_b_ok : 
  ck_full_adder_ok full_adder_nand_b.
  unfold ck_full_adder_ok.
  destruct a,b,cin; reflexivity.
Qed.


