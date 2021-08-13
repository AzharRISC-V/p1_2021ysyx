
Require Import Bool.


(* 1.5 逻辑门。接受1个或多个输入并产生1个输出，用布尔表达式来实现。 *)
Module LogicGate_1_5.
  
  (** ** Bool expressions *)
  Declare Scope Bool_scope.
  Delimit Scope Bool_scope with bool.
  Open Scope Bool_scope.

  Notation "0" := false : Bool_scope.
  Notation "1" := true : Bool_scope.
  
  Definition nandb a b := negb (andb a b).
  Definition norb a b := negb (orb a b).
  
  
  (** ** logic gate expressions *)
  
  Declare Scope Signal_scope.
  Delimit Scope Signal_scope with signal.
  Open Scope Signal_scope.
  
  Inductive Signal : Set :=
    | Bit0  : Signal
    | Bit1  : Signal
    | Not1  : Signal -> Signal
    | Eq2   : Signal -> Signal -> Signal
    | And2  : Signal -> Signal -> Signal
    | Or2   : Signal -> Signal -> Signal
    | Nand2 : Signal -> Signal -> Signal
    | Nor2  : Signal -> Signal -> Signal
    | Xor2  : Signal -> Signal -> Signal
    .

  Infix "||"  := Or2   (at level 50, left associativity)  : Signal_scope.
  Infix "&&"  := And2  (at level 40, left associativity)  : Signal_scope.
  Infix "!&"  := Nand2 (at level 40, left associativity)  : Signal_scope.
  Infix "=?"  := Eq2   (at level 38, left associativity)  : Signal_scope.
  Infix "(+)" := Xor2  (at level 38, left associativity)  : Signal_scope.
  Infix "(-)" := Nor2  (at level 38, left associativity)  : Signal_scope.

  Fixpoint s2b (s:Signal) : bool :=
   match s with
     | Bit0 => false
     | Bit1 => true
     | Not1 r => negb (s2b r)
     | Eq2   r1 r2 => eqb   (s2b r1) (s2b r2)
     | And2  r1 r2 => andb  (s2b r1) (s2b r2)
     | Or2   r1 r2 => orb   (s2b r1) (s2b r2)
     | Nand2 r1 r2 => nandb (s2b r1) (s2b r2)
     | Nor2  r1 r2 => norb  (s2b r1) (s2b r2)
     | Xor2  r1 r2 => xorb  (s2b r1) (s2b r2)
   end.
   
  Definition b2s (b:bool) : Signal :=
    match b with
    | true  => Bit1
    | false => Bit0
    end.
  
  Definition Signal2 := (Signal * Signal)%type.
  Definition Signal3 := (Signal2 * Signal)%type.
  Definition Signal4 := (Signal3 * Signal)%type.
  
  (** ** 半加器 half adder *)
  
  (** specification. A B : (S, Cout) *)
  Definition half_adder_tp := Signal -> Signal -> Signal2.
  
  Definition half_adder_spec (f : half_adder_tp) := forall (a b : bool),
    let (s,cout) := f (b2s a) (b2s b) in
      (s2b s, s2b cout) = match a, b with
      | 0, 0 => (0, 0)
      | 0, 1 => (1, 0)
      | 1, 0 => (1, 0)
      | 1, 1 => (0, 1)
      end.
  
  (** implementation *)
  Definition half_adder1 : half_adder_tp :=
    fun a b : Signal => (a (+) b, a && b).
  
  Lemma half_adder1_ok : half_adder_spec half_adder1.
  unfold half_adder_spec. destruct a,b; simpl; auto. Qed.
  
  
  (** ** 全加器 *)
  
  (** specification: A B Cin -> (S, Cout) *)
  Definition full_adder_tp := Signal -> Signal -> Signal -> Signal2.
  
  Definition full_adder_spec (f : full_adder_tp) := forall (a b cin : bool),
    let (s,cout) := f (b2s a) (b2s b) (b2s cin) in
      (s2b s, s2b cout) = match a, b, cin with
      | 0, 0, 0 => (0, 0)
      | 0, 0, 1 => (1, 0)
      | 0, 1, 0 => (1, 0)
      | 0, 1, 1 => (0, 1)
      | 1, 0, 0 => (1, 0)
      | 1, 0, 1 => (0, 1)
      | 1, 1, 0 => (0, 1)
      | 1, 1, 1 => (1, 1)
      end.
  
  (** implementation *)
  Definition full_adder1 : full_adder_tp :=
    fun a b cin : Signal => (a (+) b (+) cin, 
      (a && b) || (a && cin) || (b && cin)).
  
  Lemma full_adder1_ok : full_adder_spec full_adder1.
  unfold full_adder_spec. destruct a,b,cin; simpl; auto. Qed.
  
  (** 进位传播加法器 carry propagate adder, CPA *)
  (* 有三种常见的CPA实现：行波进位加法器、先行进位加法器、前缀加法器 *)
  
  (** 行波进位加法器 Ripple-Carry Adder *)
  
  (* 2位：Cin (A0,B0) (A1,B1) : (Cout, S0, S1) *)
  Definition rc_adder2_tp := Signal -> Signal2 -> Signal2 -> Signal3.
  
  Definition rc_adder2_spec (f : rc_adder2_tp) := 
    forall (cin a0 b0 a1 b1 : bool),
    let '(cout, s0, s1) := f (b2s cin) (b2s a0, b2s b0) (b2s a1, b2s b1) in
      (s2b cout, s2b s0, s2b s1) = match cin, a0, b0, a1, b1 with
      | 0, 0, 0, 0, 0 => (0, 0, 0)
      | 0, 0, 0, 0, 0 => (0, 0, 0)
      )
      | 0, 0, 1 => (1, 0)
      | 0, 1, 0 => (1, 0)
      | 0, 1, 1 => (0, 1)
      | 1, 0, 0 => (1, 0)
      | 1, 0, 1 => (0, 1)
      | 1, 1, 0 => (0, 1)
      | 1, 1, 1 => (1, 1)
      end.
  
  
  (* 这里需要引入定长数组，也就是向量 *)
End LogicGate_1_5.