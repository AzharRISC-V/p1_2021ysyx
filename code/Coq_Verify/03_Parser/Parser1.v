(*
  parser
  一种简单情形：
  1. 算术表达式
  2. 只允许出现以下的token类型
    十进制整数
    +, -, *, /
    (, )
    空格
*)

Require Import Nat.
Require Import Bool.
Require Import Byte.
Require Import Ascii.
Require Import String.
Require Import List.
Import ListNotations.

Open Scope byte.
Open Scope char.
Open Scope string.

Open Scope nat.
Open Scope bool_scope.

Print byte.
Print ascii.
Print string.

Check "A"%char.
Check "065"%char.

Definition exp_str1 := "3 * (2 + 1 * 3)".

(* 逻辑
  1. 只能出现十进制数字、加减乘除符号、左右小括号、空格
  2. 首先给每个字符分类
  3. 然后再按顺序处理字符类别。
*)
Search (nat -> ascii).
Search (ascii -> nat).
Compute nat_of_ascii (ascii_of_nat 65).
Compute ascii_of_nat 49.
Compute "31"%string.
Check "3"%char.     (* Ascii字符 3，=0x33 *)
Check "003"%char.   (* 值为 3 的字符，=0x03 *)

(* 操作符类型 *)
Inductive OperatorType : Set :=
  | OTAdd
  | OTSub
  | OTMul
  | OTDiv
  .

(* 特殊符号类型 *)
Inductive SpecialType : Set :=
  | STBraceL
  | STBraceR
  | STSpace
  .

(* 字符类型 *)
Inductive CharType : Set :=
  | CTNum (val : nat)
  | CTOp (ot : OperatorType)
  | CTSp (st : SpecialType)
  | CTUnknown.

Definition AsciiEqb c1 c2 : bool := nat_of_ascii c1 =? nat_of_ascii c2.
Definition AsciiLeb c1 c2 : bool := nat_of_ascii c1 <=? nat_of_ascii c2.

Definition IsSymAdd c := AsciiEqb c "+".
Definition IsSymSub c := AsciiEqb c "-".
Definition IsSymMul c := AsciiEqb c "*".
Definition IsSymDiv c := AsciiEqb c "/".
Definition IsSymBraceL c := AsciiEqb c "(".
Definition IsSymBraceR c := AsciiEqb c ")".
Definition IsSymSpace c := AsciiEqb c " ".
Definition IsDigit c := andb (AsciiLeb "0" c) (AsciiLeb c "9").
(* 输入 "0" ~ "9"，其他输入无意义 *)
Definition Ascii2Nat c := nat_of_ascii c - nat_of_ascii "0".

Definition Ascii2ct (c : ascii) : CharType :=
  if IsSymAdd c then
    CTOp (OTAdd)
  else if IsSymSub c then
    CTOp (OTSub)
  else if IsSymMul c then
    CTOp (OTMul)
  else if IsSymDiv c then
    CTOp (OTDiv)
  else if IsSymBraceL c then
    CTSp (STBraceL)
  else if IsSymBraceR c then
    CTSp (STBraceR)
  else if IsSymSpace c then
    CTSp (STSpace)
  else if IsDigit c then
    CTNum (Ascii2Nat c)
  else
    CTUnknown.

(* 字符串转换为字符类型列表 *)
Fixpoint str2ctlst (s : string) : list CharType :=
  match s with
  | EmptyString => []
  | String x s1 => (Ascii2ct x) :: (str2ctlst s1)
  end.

Compute str2ctlst exp_str1.

Inductive exp : Set :=
  | ENum (a : nat)
  | EAdd (a b : exp)
  | ESub (a b : exp)
  | EMul (a b : exp)
  | EDiv (a b : exp).


(* 字符类型列表转换为表达式
逻辑：
1. 接收到数字，
  如果上一个是数字，则合并为更大的数字
  如果上一个是加减乘除、空格、左括号，则入栈这个数字
  否则错误
2. 接收到左括号
  如果表达式为空、或上一个是加减乘数
1. 初始状态S0，接收数字进入S1，接收左括号进入S0
 *)
Fixpoint ctlst2exp (l : list CharType) : option exp :=
  match l with
  | [] => None
  | x :: l1 => match l1 with
    | [] =>
    | y :: l2 =>
  | EmptyString => None
  | String a s1 => 
  end.

  
Inductive TokenTp : Set :=
  | 



Inductive Brace : Set :=
| BraceTp (isLeft : bool) (level : nat)

Inductive Token : Set :=
  | 