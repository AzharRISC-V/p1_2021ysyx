(*
  file:     matadd.v
  purpose:  matrix addition.
*)

From Digital Require Export 
  Mat_def
  Mat_map
  Mat_IO.


(** ** matrix addition *)
Section matadd.
  
  Variable A : Type.
  Variable A0 : A.
  Variable fadd : A -> A -> A.
  Variable fadd_0_l : forall a, fadd A0 a = a.
  Variable fadd_comm : forall a b, fadd a b = fadd b a.
  
  (** matadd *)
  Definition matadd {r c} (m1 m2 : @mat A r c) : @mat A r c :=
    matmap2 fadd m1 m2.
  
  (** 0 + m = m *)
  Lemma matadd_zero_l : forall {r c} (m : @mat A r c),
    matadd (matzero A0 r c) m == m.
  Proof.
    intros. unfold mat_eq; simpl. unfold matmap2dl.
    apply dladd_zero_l; auto. apply mat_height. apply mat_width.
  Qed.
  
  (** m + 0 = m *)
  Lemma matadd_zero_r : forall {r c} (m : @mat A r c),
    matadd m (matzero A0 r c) == m.
  Proof.
    intros. unfold matadd. rewrite matmap2_comm; auto. apply matadd_zero_l.
  Qed.

End matadd.

Arguments matadd {A} fadd {r c}.

Compute matadd Nat.add ex_mat1 ex_mat1.

