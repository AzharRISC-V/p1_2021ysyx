(*
  电路设计的一些概念，在Coq中模型化
  
  参考书：数字设计和计算机体系结构
  1: 物理学，电子
  2: 器件，晶体管/二极管
  3: 模拟电路，放大器/滤波器
  4: 数字电路，与门/或门
  5: 逻辑，加法器/存储器
  6: 微结构，数据路径/控制器
  7: 体系结构，指令
  8: 操作系统，设备驱动程序
  9: 应用程序，程序
  
  目的：
  1. 理解数字系统的构造
  2. 用Coq来建立一些模型，改善可靠性
*)

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
  Infix "=="  := Eq2   (at level 38, left associativity)  : Signal_scope.
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
  
  (** Cin * (A0,B0) * (A1,B1) * (A2,B2) * (A3,B3)
  Definition rc_adder_tp := Signal
  
  Lemma half_adder1_ok : half_adder_spec half_adder1.
  unfold half_adder_spec. destruct a,b; simpl; auto. Qed.
  
  (* 输入数据的类型 *)
  Inductive InDat : Set :=
  | InDat1 (i1 : bool)
  | InDat2 (i1 i2 : bool)
  | InDat3 (i1 i2 i3 : bool)
  | InDat4 (i1 i2 i3 i4 : bool).
  
  
  (* 函数类型. type of function *)
  Definition tpfun1 := bool -> bool.
  Definition tpfun2 := bool -> bool -> bool.
  Definition tpfun3 := bool -> bool -> bool -> bool.
  Definition tpfun4 := bool -> bool -> bool -> bool -> bool.
  
  (* 输入数据. input data. 以后最好能自动生成，防止有错 *)
  Definition indat1 : list InDat1 := [0;1].
  Definition indat2 : list (bool*bool) := [(0,0);(0,1);(1,0);(1,1)].
  Definition indat3 : list (bool*bool*bool) := 
    [(0,0,0);(0,0,1);(0,1,0);(0,1,1);
     (1,0,0);(1,0,1);(1,1,0);(1,1,1)].
  
  (* 测试平台 *)
  Definition tb1 (f : kind_1_1) (i :  (l : list (bool * bool)) : bool := match indat_1 with
    | [] => true
    | x :: l => tb1 f l
  
  
  (* 1输入测试平台 *)
  Definition tb1 (f : bool -> bool) (of ot : bool) :=
    andb (eqb (f false) of) (eqb (f true) ot) .
  
  (* 2输入测试平台 *)
  Definition TestBench2 (f : bool -> bool -> bool) 
    (off oft otf ott : bool) : bool :=
    andb
      (andb (eqb (f false false) off) (eqb (f false true) oft))
      (andb (eqb (f false false) otf) (eqb (f true true) ott))
      
       (eqb (f false) o2).
  
  
  (* 非门 *)
  Definition NOT (a : bool) : bool := negb a.
  Lemma NOT_ok : forall a, NOT a = match a with
    | true => false
    | false => true
    end.
  tauto. Qed.
  Goal TestBench1 NOT false true = true.
  auto. Qed.
  
  
  (* 缓冲 *)
  Definition BUF (a : bool) : bool := a.
  
  Goal TestBench1 NOT false true = true.
  auto. Qed.
  
  Lemma BUF_ok : forall a, NOT a = match a with
    | true => false
    | false => true
    end.
  tauto. Qed.
  Lemma BUF_ok : forall a, BUF a = a.
  tauto. Qed.
  
  (* 与门 *)
  Definition AND (a b : B) : B := andb a b.
  Lemma AND_ok : NOT t = f /\ NOT f = t.
  tauto. Qed.
  
  (* 或门 *)
  Definition OR (A B : b) : b := orb A B.
  Lemma NOT_ok : NOT t = f /\ NOT f = t.
  tauto. Qed.
  
  (* 
  
End LogicGate_1_5.

(* 1.6 数字抽象之下 *)
(* 晶体管级 *)
Module 

(* 门级 *)
Module GateLevel.


End Implementation.



(* 组合逻辑电路，看做一个黑盒 *)
Record Box : Set := {
  Bi : list bool;   (* input terminal *)
  Bo : list bool;   (* output terminal *)
  Bfs : bool;       (* functional specification *)
  Bts : bool        (* timing specification *)
}.

(* 同样的功能，可以有不同的实现 *)

(* Or box *)
Definition BOr (A B : b) : b := A || B.


  