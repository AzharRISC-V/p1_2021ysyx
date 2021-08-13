(*
  file:     mat_def.v
  purpose:  matrix definition
*)

From Digital Require Export List_aux.

Require Export Setoid.
Require Export Relation_Definitions.


(** ** Definition of Matrix Type *)

Section mat_def.

  Variable A : Type.
  
  Record mat {r c : nat} : Type := mk_mat {
    mat_data : list (list A);
    mat_height : length mat_data = r;
    mat_width : width mat_data c
  }.

End mat_def.

Arguments mat {A}.
Arguments mk_mat {A r c}.
Arguments mat_data {A r c}.
Arguments mat_height {A r c}.
Arguments mat_width {A r c}.

(** Examples *)

Definition ex_dl1 := [[1;2];[3;4]].
Definition ex_dl1_len : length ex_dl1 = 2. auto. Qed.
Definition ex_dl1_wid : width ex_dl1 2. compute. auto. Qed.

Definition ex_mat1 : @mat nat 2 2 := mk_mat ex_dl1 ex_dl1_len ex_dl1_wid.
Definition ex_mat2 : mat 2 2 := mk_mat ex_dl1 ex_dl1_len ex_dl1_wid.
Definition ex_mat3 : mat 2 2 := {|
  mat_data := ex_dl1; 
  mat_height := ex_dl1_len; 
  mat_width := ex_dl1_wid
|}.

Compute mat_data ex_mat1.
Compute ex_mat1.(mat_data).


(** ** matrix equality *)
Section mat_eq.

  Variable A : Type.
  
  Definition mat_eq {r c} (m1 m2 : @mat A r c) :=
    mat_data m1 = mat_data m2.

  Lemma mat_eq_refl : forall {r c}, reflexive _ (@mat_eq r c).
  Proof. intros. compute. auto. Qed.
  
  Lemma mat_eq_sym : forall {r c}, symmetric _ (@mat_eq r c).
  Proof. intros. compute. auto. Qed.
  
  Lemma mat_eq_trans : forall {r c}, transitive _ (@mat_eq r c).
  Proof. intros. compute. intros. rewrite H,H0. auto. Qed.
  
End mat_eq.

Arguments mat_eq {A r c}.
Arguments mat_eq_refl {A}.
Arguments mat_eq_sym {A}.
Arguments mat_eq_trans {A}.

Notation "m1 == m2" := (mat_eq m1 m2) (at level 50).


(** ** Support mat_eq rewrite *)

(** Examples show that rewrite on mat_eq is FAIL *)
Section mat_eq_rewrite_FAIL.

  Example ex_sym : forall A r c (m1 m2 : @mat A r c),
    mat_eq m1 m2 -> mat_eq m2 m1.
  Proof. intros. Fail rewrite H. Abort.

End mat_eq_rewrite_FAIL.

(** tell coq that mat_eq is a equivalence relation, so rewrite will work *) 
Add Parametric Relation {A r c} : (@mat A r c) (@mat_eq A r c)
  reflexivity proved by (mat_eq_refl r c)
  symmetry proved by (mat_eq_sym r c)
  transitivity proved by (mat_eq_trans r c)
  as mat_eq_rel.

(** Examples show that rewrite on mat_eq is SUCCESS *)
Section mat_eq_rewrite_SUCCESS.

  Example ex_sym : forall A r c (m1 m2 : @mat A r c),
    mat_eq m1 m2 -> mat_eq m2 m1.
  Proof. intros. rewrite H. reflexivity. Qed.

End mat_eq_rewrite_SUCCESS.


(** ** matrix with specific size *)

(** mat_1_1 *)
Section mat_1_1.
  
  Variable A : Type.
  Variable a : A.
  
  Let data := [[a]].
  Let cond_h : length data = 1. auto. Qed.  
  Let cond_w : width data 1. simpl. auto. Qed.
  
  Definition mk_mat_1_1 : @mat A 1 1 := mk_mat data cond_h cond_w.

End mat_1_1.

Arguments mk_mat_1_1 {A}.

Compute mk_mat_1_1 3.


(** mat_1_2 *)
Section mat_1_2.
  
  Variable A : Type.
  Variable a b : A.
  
  Let data : list (list A) := [[a; b]].
  Let cond_h : length data = 1. auto. Qed.  
  Let cond_w : width data 2. simpl. auto. Qed.
  
  Definition mk_mat_1_2' : @mat A 1 2 := mk_mat data cond_h cond_w.

End mat_1_2.

Compute mk_mat_1_2' nat 1 2.


(** mat_0_c *)
Section mat_0_c.
  
  Variable A : Type.
  Variable c : nat.

  Let data : list (list A) := [].
  Let cond_h : length data = 0. auto. Qed.  
  Let cond_w : width data c. simpl. auto. Qed.
  
  Definition mk_mat_0_c : @mat A 0 c := mk_mat data cond_h cond_w.

End mat_0_c.

Arguments mk_mat_0_c {A}.

Compute mk_mat_0_c 3.


(** mat_1_c *)
Section mat_1_c.
  
  Variable A : Type.
  Variable l : list A.
  Variable c : nat.
  Variable H1 : length l = c.
  
  Let data : list (list A) := [l].
  Let cond_h : length data = 1. auto. Qed.  
  Let cond_w : width data c. simpl. auto. Qed.
  
  Definition mk_mat_1_c : @mat A 1 c := mk_mat data cond_h cond_w.

End mat_1_c.

Arguments mk_mat_1_c {A}.

Compute mk_mat_1_c [1;2;3] 3 eq_refl.


(** mat_1_2, mat_1_3, ... *)
Definition mk_mat_1_2 {A} (a1 a2 : A) : mat 1 2 := 
  mk_mat_1_c [a1;a2] 2 eq_refl.
  
Compute mk_mat_1_2 5 6.

Definition mk_mat_1_3 {A} (a1 a2 a3 : A) : mat 1 3 := 
  mk_mat_1_c [a1;a2;a3] 3 eq_refl.
  
Compute mk_mat_1_3 5 6 7.

Definition mk_mat_1_4 {A} (a1 a2 a3 a4 : A) : mat 1 4 := 
  mk_mat_1_c [a1;a2;a3;a4] 4 eq_refl.
  
Compute mk_mat_1_4 5 6 7 8.


(** mat_r_0 *)
Section mat_r_0.
  
  Variable A : Type.
  Variable l : list A.
  Variable r : nat.
  Variable H1 : length l = r.
  
  Let data : list (list A) := @dnil A r.
  Let cond_h : length data = r. unfold data. simpl. rewrite dnil_height. auto. 
    Qed.
  Let cond_w : width data 0. unfold data. apply dnil_width. Qed.
  
  Definition mk_mat_r_0 : @mat A r 0 := mk_mat data cond_h cond_w.

End mat_r_0.

Arguments mk_mat_r_0 {A}.

Compute mk_mat_r_0 3.


(** mat_r_1 *)
Section mat_r_1.
  
  Variable A : Type.
  Variable l : list A.
  Variable r : nat.
  Variable H1 : length l = r.
  
  Let data : list (list A) := cvt_row2col l.
  Let cond_h : length data = r. unfold data. rewrite cvt_row2col_height. auto. 
    Qed.
  Let cond_w : width data 1. unfold data. apply cvt_row2col_width; auto. Qed.
  
  Definition mk_mat_r_1 : @mat A r 1 := mk_mat data cond_h cond_w.

End mat_r_1.

Arguments mk_mat_r_1 {A}.

Compute mk_mat_r_1 [1;2;3] 3 eq_refl.


(** mat_2_1, mat_3_1, ... *)
Definition mk_mat_2_1 {A} (a1 a2 : A) : mat 2 1 := 
  mk_mat_r_1 [a1;a2] 2 eq_refl.

Compute mk_mat_2_1 5 6.

Definition mk_mat_3_1 {A} (a1 a2 a3 : A) : mat 3 1 := 
  mk_mat_r_1 [a1;a2;a3] 3 eq_refl.

Compute mk_mat_3_1 5 6 7.

Definition mk_mat_4_1 {A} (a1 a2 a3 a4 : A) : mat 4 1 := 
  mk_mat_r_1 [a1;a2;a3;a4] 4 eq_refl.

Compute mk_mat_4_1 5 6 7 8.

(** !Notice, this example might be error, HOW to explainate it?
  the base element could be a list, and list could be any length. *)
Compute mk_mat_4_1 [1;2] [2;3;4] [] [].


(** mat_3_3 *)
Section mat_3_3.
  
  Variable A : Type.
  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : A.
  
  Let data : list (list A) := [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  Let cond_h : length data = 3. auto. Qed.
  Let cond_w : width data 3. unfold data. simpl. tauto. Qed.
  
  Definition mk_mat_3_3 : @mat A 3 3 := mk_mat data cond_h cond_w.

End mat_3_3.

Arguments mk_mat_3_3 {A}.

Compute mk_mat_3_3 1 2 3 4 5 6 7 8 9.


(** TEST code, unfinished *)

Require Import Reals.
Open Scope R_scope.

Require Import Arith.


Section Complex.

  Record Complex := mkComplex {
    Re : R;
    Im : R
  }.

End Complex.

Section HermitonMatrix.
  Check mat.
  Variable mat_mul : forall {A r c t}, @mat A r c -> @mat A c t -> @mat A r t.
  Variable mat_H : forall {A r c}, @mat A r c -> @mat A r c.
  Record HMat {A r c} := mkHMat {
    hmmat : @mat A r c;
    hmcond : mat_H hmmat = hmmat
  }.
  
End HermitonMatrix.
