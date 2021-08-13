(*
  file:     mat_trans.v
  purpose:  matrix transpose.
*)

From Digital Require Export 
  Mat_def
  Mat_map
  Mat_IO.


(** ** matrix transpose *)
Section mat_trans.
  
  Variable A : Type.
  Variable A0 : A.
  Variable fadd : A -> A -> A.
  Variable fadd_0_l : forall a, fadd A0 a = a.
  Variable fadd_comm : forall a b, fadd a b = fadd b a.
  
  Definition mat_trans {r c} (m : @mat A r c) : @mat A c r :=
    let dl := mat_data m in
      mk_mat (dltrans dl c) 
        (dltrans_height dl c (mat_width m))
        (dltrans_width dl r c (mat_height m) (mat_width m)).
  
  (** Transpose twice return back *)
  Lemma mat_trans_trans : forall {r c} (m : @mat A r c),
    mat_trans (mat_trans m) == m.
  Proof.
    intros. unfold mat_eq in *. destruct m; simpl in *.
    rewrite dltrans_trans; auto.
  Qed.
  
End mat_trans.

Arguments mat_trans {A} {r c}.

Compute mat_trans ex_mat1.
Compute mat_trans (mk_mat_r_0 5).
Compute mat_trans (mk_mat_0_c 5).


(** ** mat_trans compat with mat_eq *)

(** tell coq the morphism *)
Add Parametric Morphism {A r c} : (mat_trans)
  with signature (@mat_eq A r c) ==> (@mat_eq A c r)
  as mat_trans_mor.
Proof.
  intros. unfold mat_eq in *. destruct x,y. simpl in *. subst. auto.
Qed.

