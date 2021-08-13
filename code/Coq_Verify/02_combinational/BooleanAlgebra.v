(*
  布尔代数
  
  数字设计和计算机体系结构
  2.3节 布尔代数
*)

Require Import List.
Import ListNotations.

Module BooleanAlgebra.

  Inductive Boolean : Set :=
  | B0
  | B1.
  
  Parameter AND OR : Boolean -> Boolean -> Boolean.
  Parameter NOT : Boolean -> Boolean.
  
  Declare Scope Boolean_scope.
  Delimit Scope Boolean_scope with bool.
  Open Scope Boolean_scope.
  
  Notation "0" := B0 : Boolean_scope.
  Notation "1" := B1 : Boolean_scope.
  Notation "! b" := (NOT b) (at level 1) : Boolean_scope.
  Infix "#" := AND (at level 10) : Boolean_scope.
  Infix "+" := OR : Boolean_scope.

  Fixpoint ANDLst (l : list Boolean) : Boolean :=
    match l with
    | [] => 1
    | x :: l' => x # (ANDLst l')
    end.

  Fixpoint ORLst (l : list Boolean) : Boolean :=
    match l with
    | [] => 0
    | x :: l' => x + (ORLst l')
    end.

  Axiom A1 : forall b : Boolean, b <> 1 -> b = 0.
  Axiom A1' : forall b : Boolean, b <> 0 -> b = 1.  
  Axiom A2 : !0 = 1.
  Axiom A2' : !1 = 0.
  Axiom A3 : 0 # 0 = 0.
  Axiom A3' : 1 + 1 = 1.
  Axiom A4 : 1 # 1 = 1.
  Axiom A4' : 0 + 0 = 0.
  Axiom A5 : 0 # 1 = 0.
  Axiom A5_0 : 1 # 0 = 0.
  Axiom A5' : 1 + 0 = 1.
  Axiom A5_0' : 0 + 1 = 1.
  
  Hint Rewrite A2 A2' A3 A3' A4 A4' A5 A5' A5_0 A5_0'
    : bool.
  
  (* 单变量定理 *)
  Theorem T1 : forall b, b # 1 = b.
  intros. destruct b; autorewrite with bool; auto. Qed.
  
  Theorem T1' : forall b, b + 0 = b.
  intros. destruct b; autorewrite with bool; auto. Qed.
  
  Theorem T2 : forall b, b # 0 = 0.
  intros. destruct b; autorewrite with bool; auto. Qed.
  
  Theorem T2' : forall b, b + 1 = 1.
  intros. destruct b; autorewrite with bool; auto. Qed.
  
  Theorem T3 : forall b, b # b = b.
  intros. destruct b; autorewrite with bool; auto. Qed.
  
  Theorem T3' : forall b, b + b = b.
  intros. destruct b; autorewrite with bool; auto. Qed.
  
  Theorem T4 : forall b, !(!b) = b.
  intros. destruct b; autorewrite with bool; auto. Qed.
  
  Theorem T5 : forall b, b # (!b) = 0.
  intros. destruct b; autorewrite with bool; auto. Qed.
  
  Theorem T5' : forall b, b + (!b) = 1.
  intros. destruct b; autorewrite with bool; auto. Qed.
  
  (* 多变量定理 *)
  
  Theorem T6 : forall b c, b # c = c # b.
  intros. destruct b,c; autorewrite with bool; auto. Qed.
  
  Theorem T6' : forall b c, b + c = c + b.
  intros. destruct b,c; autorewrite with bool; auto. Qed.
  
  Theorem T7 : forall b c d, (b # c) # d = b # (c # d).
  intros. destruct b,c,d; autorewrite with bool; auto. Qed.
  
  Theorem T7' : forall b c d, (b + c) + d = b + (c + d).
  intros. destruct b,c,d; autorewrite with bool; auto. Qed.
  
  Theorem T8 : forall b c d, (b # c) + (b # d) = b # (c + d).
  intros. destruct b,c,d; autorewrite with bool; auto. Qed.
  
  Theorem T8' : forall b c d, (b + c) # (b + d) = b + (c # d).
  intros. destruct b,c,d; autorewrite with bool; auto. Qed.
  
  Theorem T9 : forall b c, b # (b + c) = b.
  intros. destruct b,c; autorewrite with bool; auto. Qed.
  
  Theorem T9' : forall b c, b + (b # c) = b.
  intros. destruct b,c; autorewrite with bool; auto. Qed.
  
  Theorem T10 : forall b c, (b # c) + (b # !c) = b.
  intros. destruct b,c; autorewrite with bool; auto. Qed.
  
  Theorem T10' : forall b c, (b + c) # (b + !c) = b.
  intros. destruct b,c; autorewrite with bool; auto. Qed.
  
  Theorem T11 : forall b c d, (b # c) + (!b # d) + (c # d) =
    (b # c) + (!b # d).
  intros. destruct b,c,d; autorewrite with bool; auto. Qed.
  
  Theorem T11' : forall b c d, (b + c) # (!b + d) # (c + d) =
    (b + c) # (!b + d).
  intros. destruct b,c,d; autorewrite with bool; auto. Qed.
  
  Theorem T12_0 : forall b c, !(b # c) = !b + !c.
  intros. destruct b,c; autorewrite with bool; auto. Qed.
  
  Theorem T12_0' : forall b c, !(b + c) = !b # !c.
  intros. destruct b,c; autorewrite with bool; auto. Qed.
  
  Theorem T12 : forall l : list Boolean,
    NOT (fold_right OR 1 l) = fold_right AND 0 (map NOT l).
  induction l.
  - simpl. autorewrite with bool; auto.
  - simpl. rewrite <- IHl. rewrite T12_0'. auto.
  Qed.
  
  Theorem T12' : forall l : list Boolean,
    NOT (fold_right AND 0 l) = fold_right OR 1 (map NOT l).
  induction l.
  - simpl. autorewrite with bool; auto.
  - simpl. rewrite <- IHl. rewrite T12_0. auto.
  Qed.
  
  (** 2.3.5 等式化简 *)
  Lemma ex1 : forall b c d, b#c + !b#d + c#d = b#c + !b#d.
  destruct b,c,d; autorewrite with bool; auto.
  
  (* 化简过程，Coq好像没有用处 
     !A!B!C + A!B!C + A!BC
   = (!A!B!C + A!B!C) + (A!B!C + A!BC)
   = !B!C + A!B
   
   1. 只使用布尔代数定理，则可能结果不是最简。
   2. 有几个处理手法，不一定是化简，属于构造。
    (1). 展开蕴含项。 A = AB + A!B
    (2). 重叠率。 B = B + B + ...
   3. 后续介绍的卡诺图方法会处理的简单一些。
  *)
  
End BooleanAlgebra.
