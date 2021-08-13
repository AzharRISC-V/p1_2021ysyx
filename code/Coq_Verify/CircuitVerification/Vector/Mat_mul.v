(*
  file:     matmul.v
  purpose:  matrix multiplication.
*)

From Digital Require Export 
  Mat_def
  Mat_map
  Mat_IO
  Mat_trans
  Mat_add
  Mat_sub.


(** ** matrix multiplication *)
Section matmul.
  
  Variable A : Type.
  Variable A0 : A.
  Variable fadd fmul : A -> A -> A.
 
  Variable r c t : nat.
  Variable m1 : @mat A r c.
  Variable m2 : @mat A c t.
  
  Let data : list (list A) :=
      dldotdl A0 fadd fmul (mat_data m1) (mat_data (mat_trans m2)).
  
  Let cond_h : length (data) = r.
  Proof.
    intros. unfold data. destruct m1,m2; simpl in *.
    rewrite dldotdl_height with (r1:=r) (r2:=t) (c:=c); auto.
    apply dltrans_height; auto. apply dltrans_width; auto.
  Qed.
  
  Let cond_w : width (data) t.
  Proof.
    intros. unfold data. destruct m1,m2; simpl in *.
    apply dldotdl_width with (r1:=r) (r2:=t) (c:=c); auto.
    apply dltrans_height; auto. apply dltrans_width; auto.
  Qed.
  
  (** matrix multiplication *)
  Definition matmul : @mat A r t := mk_mat data cond_h cond_w.
  
End matmul.

Arguments matmul {A} A0 fadd fmul {r c t}.

Compute matmul 0 Nat.add Nat.mul ex_mat1 ex_mat1.


(** ** Multiplication with a constant and a matrix *)
Section matcmul_matmulc.
  
  Variable A : Type.
  Variable A0 : A.
  Variable fadd fmul : A -> A -> A.
  Variable fmul_comm : forall a b, fmul a b = fmul b a.
  Variable fmul_assoc : forall a b c, fmul (fmul a b) c = fmul a (fmul b c).
  Variable fmul_add_distr_l : forall a b1 b2,
    fmul a (fadd b1 b2) = fadd (fmul a b1) (fmul a b2).
  Variable fmul_add_distr_r : forall a1 a2 b,
    fmul (fadd a1 a2) b = fadd (fmul a1 b) (fmul a2 b).

  Variable r c : nat.
  
  Section matcmul.
    Variable a : A.
    Variable m : @mat A r c.
  
    Let data : list (list A) :=
      dlmap (fun x => fmul a x) (mat_data m).
    
    Let cond_h : length (data) = r.
    Proof.
      intros. unfold data. destruct m; simpl in *.
      rewrite dlmap_height. apply mat_height.
    Qed.
    
    Let cond_w : width (data) c.
    Proof.
      intros. unfold data. destruct m; simpl in *.
      apply dlmap_width. apply mat_width.
    Qed.
    
    Definition matcmul : @mat A r c := mk_mat data cond_h cond_w.
  End matcmul.
  
  Section matmulc.
    Variable m : @mat A r c.
    Variable a : A.
    
    Let data : list (list A) :=
      dlmap (fun x => fmul x a) (mat_data m).
    
    Let cond_h : length (data) = r.
    Proof.
      intros. unfold data. destruct m; simpl in *.
      rewrite dlmap_height. apply mat_height.
    Qed.
    
    Let cond_w : width (data) c.
    Proof.
      intros. unfold data. destruct m; simpl in *.
      apply dlmap_width. apply mat_width.
    Qed.
    
    Definition matmulc : @mat A r c := mk_mat data cond_h cond_w.
  End matmulc.
  
  (** a * M = M * a *)
  Lemma matcmul_matmulc a m : matcmul a m == matmulc m a.
  Proof.
    destruct m. unfold mat_eq. simpl. f_equal. apply functional_extensionality.
    auto.
  Qed.
  
  (** (a * b) * M = a * (b * M) *)
  Lemma matcmul_assoc_l : forall m a1 a2,
    matcmul (fmul a1 a2) m == matcmul a1 (matcmul a2 m).
  Proof.
    intros. destruct m as [dl]. unfold mat_eq. simpl. unfold dlmap.
    rewrite map_map. f_equal. apply functional_extensionality. intros.
    rewrite map_map. f_equal. apply functional_extensionality. auto.
  Qed.
  
  (** (a1 + a2) * M = (a1 * M) + (a2 * M) *)
  Lemma matcmul_distr_l : forall a1 a2 m,
    matcmul (fadd a1 a2) m == matadd fadd (matcmul a1 m) (matcmul a2 m).
  Proof.
    intros. destruct m as [dl dlH dlW]. unfold mat_eq; simpl.
    unfold matmap2dl; simpl.
    gd c. gd r. gd a2. gd a1. clear c r. induction dl; intros; auto.
    repeat rewrite dlmap_cons. simpl in *. destruct dlW.
    rewrite IHdl with (r:=pred r) (c:=c); auto.
    - f_equal. remember (dlmap (fun x : A => fmul a1 x) dl) as dl1.
      rewrite lmap2_map_map with (g:=(fun x : A => fmul (fadd a1 a2) x)).
      auto. auto.
    - subst. auto.
  Qed.
  
  (** a * (M1 + M2) = (a * M1) + (a * M2) *)
  Lemma matcmul_distr_r : forall a m1 m2,
    matcmul a (matadd fadd m1 m2) == matadd fadd (matcmul a m1) (matcmul a m2).
  Proof.
    intros. destruct m1 as [d1 d1H d1W], m2 as [d2 d2H d2W].
    unfold mat_eq. simpl. unfold matmap2dl; simpl.
    rewrite dlmap2_dlmap_hom; auto.
  Qed.

End matcmul_matmulc.

Arguments matcmul {A} fmul {r c}.
Arguments matmulc {A} fmul {r c}.

Compute matcmul Nat.mul 3 ex_mat1.
Compute matmulc Nat.mul ex_mat1 3.


(** ** matrix multiplication properties *)
Section matmul_props.

  Variable A : Type.
  Variable A0 A1 : A.
  Variable fadd fmul : A -> A -> A.
  Variable fadd_comm : forall a b, fadd a b = fadd b a.
  Variable fmul_comm : forall a b, fmul a b = fmul b a.
  Variable fadd_assoc : forall a b c, fadd (fadd a b) c = fadd a (fadd b c).
  Variable fmul_assoc : forall a b c, fmul (fmul a b) c = fmul a (fmul b c).
  Variable fmul_add_distr_l : forall a b1 b2,
    fmul a (fadd b1 b2) = fadd (fmul a b1) (fmul a b2).
  Variable fmul_add_distr_r : forall a1 a2 b,
    fmul (fadd a1 a2) b = fadd (fmul a1 b) (fmul a2 b).
  Variable fadd_0_l : forall a, fadd A0 a = a.
  Variable fmul_0_l : forall a, fmul A0 a = A0.
  Variable fmul_1_l : forall a, fmul A1 a = a.
  
  Notation matadd := (matadd fadd).
  Notation matmul := (matmul A0 fadd fmul).
  
  (** matrix muliplication left distributve over addition. 
    (A + B) * C = A * C + B * C *)
  Lemma matmul_add_distr_l : forall {r c t} (m1 m2 : @mat A r c) 
    (m3 : @mat A c t),
    matmul (matadd m1 m2) m3 == matadd (matmul m1 m3) (matmul m2 m3).
  Proof.
    intros. unfold mat_eq in *. destruct m1,m2,m3; simpl in *.
    unfold matmul, matadd; simpl. unfold matmap2dl; simpl in *.
    rewrite dldotdl_dlmap2_distr_l with (r:=r) (c:=c) (t:=t); auto.
    rewrite dltrans_height; auto.
    apply dltrans_width; auto.
  Qed.
  
  (** matrix muliplication right distributve over addition. 
    A * (B + C) = A * B + A * C *)
  Lemma matmul_add_distr_r : forall {r c t} (m1 : @mat A r c) 
    (m2 m3 : @mat A c t),
    matmul m1 (matadd m2 m3) == matadd (matmul m1 m2) (matmul m1 m3).
  Proof.
    intros. unfold mat_eq in *. destruct m1,m2,m3; simpl in *.
    unfold matmul, matadd; simpl. unfold matmap2dl; simpl in *.
    rewrite dltrans_dlmap2 with (r:=c) (c:=t); auto.
    rewrite dldotdl_dlmap2_distr_r with (r:=r) (c:=c) (t:=t); auto;
    try apply dltrans_height; try apply dltrans_width; auto.
  Qed.
  
  (** matrix muliplication association. 
    (A * B) * C = A * (B * C) *)
  Lemma matmul_assoc : forall {r c t s} (m1 : @mat A r c) (m2 : @mat A c t)
    (m3 : @mat A t s),
    matmul (matmul m1 m2) m3 == matmul m1 (matmul m2 m3).
  Proof.
    intros. unfold mat_eq in *. destruct m1,m2,m3; simpl in *.
    rewrite dldotdl_assoc with (r:=r) (c:=c) (t:=t) (s:=s); auto;
    try rewrite dltrans_height; try apply dltrans_width; auto.
  Qed.
  
  (** 0 * A = 0 *)
  Lemma matmul_0_l : forall {r c t} (m : @mat A c t),
    matmul (matzero A0 r c) m == matzero A0 r t.
  Proof.
    intros. unfold mat_eq in *. destruct m; simpl in *.
    rewrite dldotdl_zero_l with (t:=t); auto.
    apply dltrans_height; auto. apply dltrans_width; auto.
  Qed.
  
  (** A * 0 = 0 *)
  Lemma matmul_0_r : forall {r c t} (m : @mat A r c),
    matmul m (matzero A0 c t) == matzero A0 r t.
  Proof.
    intros. unfold mat_eq in *. destruct m; simpl in *.
    rewrite dltrans_zero. rewrite dldotdl_zero_r with (r:=r); auto.
  Qed.
  
  (** 1 * A = A *)
  Lemma matmul_1_l : forall {r c} (m : @mat A r c),
    matmul (matunit A0 A1 r) m == m.
  Proof.
    intros. unfold mat_eq in *. destruct m; simpl in *.
    rename mat_data into dl.
    rewrite dldotdl_dlunit_l with (r:=c); auto;
    try apply dltrans_height; try apply dltrans_width; auto.
    apply dltrans_trans; auto.
  Qed.
  
  (** A * 1 = A *)
  Lemma matmul_1_r : forall {r c} (m : @mat A r c),
    matmul m (matunit A0 A1 c) == m.
  Proof.
    intros. unfold mat_eq in *. destruct m; simpl in *.
    rename mat_data into dl. rewrite dltrans_dlunit.
    rewrite dldotdl_dlunit_r with (r:=r); auto;
    try apply dltrans_height; try apply dltrans_width; auto.
  Qed.

End matmul_props.


(** ** matmul compat with mat_eq *)

(** tell coq the morphism *)
Add Parametric Morphism {A A0 fadd fmul r c t} : (matmul A0 fadd fmul)
  with signature (@mat_eq A r c) ==> (@mat_eq A c t) ==> (@mat_eq A r t)
  as matmul_mor.
Proof.
  intros. unfold mat_eq in *. destruct x,y,x0,y0; simpl in *. subst. auto.
Qed.


(** ** constant multiply matrix *)
Section mat_cmul.
  
  Variable A : Type.
  Variable fmul : A -> A -> A.
(*   Variable fadd_0_l : forall a, fadd A0 a = a.
  Variable fadd_comm : forall a b, fadd a b = fadd b a.
 *)
 
  Variable r c : nat.
  Variable Ax : A.
  Variable m : @mat A r c.
  
  Let data : list (list A) := dlmap (fmul Ax) (mat_data m).
  
  Let cond_h : length (data) = r.
  Proof. 
    unfold data. destruct m; simpl in *. rewrite dlmap_height; auto.
  Qed.
  
  Let cond_w : width (data) c.
  Proof.
    unfold data. destruct m; simpl in *. rewrite <- dlmap_width; auto.
  Qed.
  
  (** constant multiply matrix *)
  Definition mat_cmul : @mat A r c := mk_mat data cond_h cond_w.
  
End mat_cmul.

Arguments mat_cmul {A} fmul {r c}.

Compute mat_cmul Nat.mul 2 ex_mat1.


(** ** mat_cmul compat with mat_eq *)

(** tell coq the morphism *)
Add Parametric Morphism {A fmul r c} : (mat_cmul fmul)
  with signature (@eq A) ==> (@mat_eq A r c) ==> (@mat_eq A r c)
  as mat_cmul_mor.
Proof.
  intros. unfold mat_eq in *. destruct x,y0; simpl in *. subst. auto.
Qed.


(** ** matmulc compat with mat_eq *)

(** tell coq the morphism *)
Add Parametric Morphism {A fmul r c} : (matmulc fmul)
  with signature (@mat_eq A r c) ==> (@eq A) ==> (@mat_eq A r c)
  as matmulc_mor.
Proof.
  intros. unfold mat_eq in *. destruct x,y; simpl in *. subst. auto.
Qed.

