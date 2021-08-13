(*
  file:     matsub.v
  purpose:  matrix substraction.
*)

From Digital Require Export 
  Mat_def
  Mat_map
  Mat_IO.


(** ** matrix substraction and negation *)
Section matsub_neg.
  
  Variable A : Type.
  Variable A0 : A.
  Variable fneg : A -> A.
  Variable fsub fadd : A -> A -> A.
  Variable fsub_comm : forall a b, fsub a b = fneg (fsub b a).
  Variable fsub_assoc1 : forall a b c, fsub (fsub a b) c = fsub a (fsub c b).
  Variable fsub_assoc2 : forall a b c, fsub (fsub a b) c = fsub a (fadd b c).
  Variable fsub_0_l : forall a, fsub A0 a = fneg a.
  Variable fsub_0_r : forall a, fsub a A0 = a.
  Variable fsub_self : forall a, fsub a a = A0.
  
  Definition matsub {r c} (m1 m2 : @mat A r c) : @mat A r c :=
    matmap2 fsub m1 m2.
  
  Definition matneg {r c} (m : @mat A r c) : @mat A r c :=
    matmap fneg m.
    
  Lemma matsub_comm : forall {r c} (m1 m2 : @mat A r c),
    matsub m1 m2 == matneg (matsub m2 m1).
  Proof.
    intros. unfold mat_eq; simpl. unfold matmapdl,matmap2dl; simpl.
    apply dlistsub_comm with (c:=c); try apply mat_width;
    repeat rewrite mat_height; auto.
  Qed.
  
  Lemma matsub_assoc2 : forall {r c} (m1 m2 m3 : @mat A r c),
    matmap2 fsub (matmap2 fsub m1 m2) m3 == 
    matmap2 fsub m1 (matmap2 fadd m2 m3).
  Proof.
    intros. unfold mat_eq; simpl.
    apply dlistsub_assoc2 with (r:=r) (c:=c); try apply mat_width;
    repeat rewrite mat_height; auto.
  Qed.
  
  (** 0 - m = - m *)
  Lemma matsub_zero_l : forall {r c} (m : @mat A r c),
    matmap2 fsub (matzero A0 r c) m == matmap fneg m.
  Proof.
    intros. unfold mat_eq; simpl. unfold matmap2dl.
    apply dlistsub_zero_l; auto. apply mat_height. apply mat_width.
  Qed.
  
  (** m - 0 = m *)
  Lemma matsub_zero_r : forall {r c} (m : @mat A r c),
    matmap2 fsub m (matzero A0 r c) == m.
  Proof.
    intros. unfold mat_eq; simpl. unfold matmap2dl.
    apply dlistsub_zero_r; auto. apply mat_height. apply mat_width.
  Qed.
  
  (** m - m = 0 *)
  Lemma matsub_self : forall {r c} (m : @mat A r c),
    matmap2 fsub m m == (matzero A0 r c).
  Proof.
    intros. unfold mat_eq; simpl. unfold matmap2dl.
    apply dlistsub_self; auto. apply mat_height. apply mat_width.
  Qed.

End matsub_neg.

Arguments matsub {A} fsub {r c}.
Arguments matneg {A} fneg {r c}.

Compute matsub Nat.sub ex_mat1 ex_mat1.
Compute matneg Nat.succ ex_mat1.

