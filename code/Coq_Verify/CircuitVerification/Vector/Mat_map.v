(*
  file:    matmap.v
  purpose:  matrix mapping
*)


From Digital Require Export Mat_def.


(** ** Matrix map to a dlist *)
Section matmapdl.
  
  Variable A B : Type.
  Variable f : A -> B.
  
  Definition matmapdl {r c} (m : @mat A r c) : list (list B) :=
    dlmap f (mat_data m).

  Lemma matmapdl_height : forall r c (m : @mat A r c), 
    length (matmapdl m) = r.
  Proof. 
    intros; simpl. unfold matmapdl. rewrite dlmap_height.
    apply mat_height.
  Qed.

  Lemma matmapdl_width : forall r c (m : @mat A r c), 
    width (matmapdl m) c.
  Proof. 
    intros; simpl. unfold matmapdl. rewrite <- dlmap_width.
    apply mat_width.
  Qed.

End matmapdl.

Arguments matmapdl {A B} f {r c}.
Arguments matmapdl_height {A B} f {r c}.
Arguments matmapdl_width {A B} f {r c}.

Compute matmapdl Nat.succ ex_mat1.


(** ** Matrix map2 to a dlist *)
Section matmap2dl.
  
  Variable A B C : Type.
  Variable f : A -> B -> C.
  
  Definition matmap2dl {r c} (m1 : @mat A r c) (m2 : @mat B r c) 
    : list (list C) :=
    dlmap2 f (mat_data m1) (mat_data m2).

  Lemma matmap2dl_height : forall {r c} (m1 : @mat A r c) (m2 : @mat B r c),
    length (matmap2dl m1 m2) = r.
  Proof. 
    intros; simpl. unfold matmap2dl. rewrite dlmap2_height;
    repeat rewrite mat_height; auto.
  Qed.

  Lemma matmap2dl_width : forall {r c} (m1 : @mat A r c) (m2 : @mat B r c),
    width (matmap2dl m1 m2) c.
  Proof. 
    intros; simpl. unfold matmap2dl. apply dlmap2_width;
    apply mat_width.
  Qed.

End matmap2dl.

Arguments matmap2dl {A B C} f {r c}.
Arguments matmap2dl_height {A B C} f {r c}.
Arguments matmap2dl_width {A B C} f {r c}.

Compute matmap2dl Nat.add ex_mat1 ex_mat1.

(* 
(** ** Matrix map2 to a dlist with same base type *)
Section matmap2dl_sametype.
  
  Variable A : Type.
  Variable A0 : A.
  Variable fneg : A -> A.
  Variable fsub : A -> A -> A.
  Variable fsub_comm : forall a b, fsub a b = fneg (fsub b a).
  
  Lemma matmapdl_sub_comm : forall dl1 dl2 c, 
    length dl1 = length dl2 ->
    width dl1 c -> width dl2 c ->
    matmap2dl fsub dl1 dl2 = dlmap fneg (matmap2dl fsub dl2 dl1).
  Proof.
    induction dl1,dl2; simpl; intros; auto. f_equal; auto.
    - apply list_sub_comm; auto.
    - destruct H0,H1. apply IHdl1 with (c:=c); auto.
  Qed.

End matmap2dl. *)


(** ** Matrix map *)
Section matmap.

  Variable A B : Type.
  Variable f : A -> B.
  
  Definition matmap {r c} (m : @mat A r c) : @mat B r c :=
    mk_mat (matmapdl f m) (matmapdl_height f m) (matmapdl_width f m).

End matmap.

Arguments matmap {A B} f {r c}.

Compute matmap Nat.succ ex_mat1.


(** ** matmap is compat with mat_eq *)
(** that means: ma1 == mb1 -> ma2 == mb2 -> matmap ma1 ma2 == matmap2 mb1 mb2
Mathematical explaination:
  f x = f y -> f (g x) = f (g y)
  f is mat_eq
  g is matmap
  NOTICE: although the mathematical requirement is abstract, but we just need 
    to prove this specific proposition is ok. The proof is easy.
*)

(** Examples for test BEFORE *)
Section examples_BEFORE.
  
  Example ex_matmap_compat : forall A r c (f : A -> A) 
    (ma mb : @mat A r c), ma == mb -> matmap f ma == matmap f mb.
  Proof. intros. Fail rewrite H. Abort.
  
End examples_BEFORE.

(** tell coq the morphism *)
Add Parametric Morphism {A r c f} : (matmap f)
  with signature (@mat_eq A r c) ==> (@mat_eq A r c)
  as matmap_mor.
Proof.
  intros. unfold mat_eq in *. destruct x,y; simpl in *.
  unfold matmapdl. simpl. subst. auto.
Qed.

(** Examples for test AFTER *)
Section examples_AFTER.
  
  Example ex_matmap_compat : forall A r c (f : A -> A) 
    (ma mb : @mat A r c), ma == mb -> matmap f ma == matmap f mb.
  Proof. intros. rewrite H. Abort.

End examples_AFTER.


(** ** Matrix map2 *)
Section matmap2.

  Variable A B C : Type.
  Variable f : A -> B -> C.
  
  Definition matmap2 {r c} (m1 : @mat A r c) (m2 : @mat B r c) 
    : @mat C r c :=
    mk_mat (matmap2dl f m1 m2) (matmap2dl_height f m1 m2) 
      (matmap2dl_width f m1 m2).
  
  (** matmap2 operation is compat with mat_eq *)
(*   Lemma matmap2_compat : forall r c,
    @mat_eq A rc *)
End matmap2.

Arguments matmap2 {A B C} f {r c}.

Compute matmap2 Nat.add ex_mat1 ex_mat1.


(** ** matmap2 is compat with mat_eq *)
(** that means: ma1 == mb1 -> ma2 == mb2 -> 
 matmap2 ma1 ma2 == matmap2 mb1 mb2
 
Mathematical explaination:
  f x1 = f y1 -> f x2 = f y2 -> f (g x1 x2) = f (g y1 y2)
  f is mat_eq
  g is matmap2
  NOTICE: although the mathematical requirement is abstract, but we just need 
    to prove this specific proposition is ok. The proof is easy.
*)

(** Examples for test BEFORE *)
Section examples_BEFORE.
  
  Example ex_matmap2_compat : forall A r c (f : A -> A -> A) 
    (ma1 ma2 mb1 mb2 : @mat A r c),
    ma1 == mb1 -> ma2 == mb2 -> matmap2 f ma1 ma2 == matmap2 f mb1 mb2.
  Proof. intros. Fail rewrite H. Abort.
  
End examples_BEFORE.

(** tell coq the morphism *)
Add Parametric Morphism {A r c f} : (matmap2 f)
  with signature (@mat_eq A r c) ==> (@mat_eq A r c) ==> (@mat_eq A r c)
  as matmap2_mor.
Proof.
  intros. unfold mat_eq in *. destruct x,y,x0,y0. simpl in *.
  unfold matmap2dl. simpl. subst. auto.
Qed.

(** Examples for test AFTER *)
Section examples_AFTER.
  
  Example ex_matmap2_compat : forall A r c (f : A -> A -> A) 
    (ma1 ma2 mb1 mb2 : @mat A r c),
    ma1 == mb1 -> ma2 == mb2 -> matmap2 f ma1 ma2 == matmap2 f mb1 mb2.
  Proof. intros. rewrite H,H0. reflexivity. Qed.

End examples_AFTER.


(** ** Matrix map2 with same base type *)
Section matmap2_sametype.

  Variable A : Type.
  Variable f : A -> A -> A.
  Variable f_comm : forall a b, f a b = f b a.
  Variable f_assoc : forall a b c, f (f a b) c = f a (f b c).

  Lemma matmap2_comm : forall {r c} (m1 m2 : @mat A r c),
    matmap2 f m1 m2 == matmap2 f m2 m1.
  Proof.
    intros. unfold mat_eq; simpl. unfold matmap2dl.
    apply dlmap2_comm; auto.
  Qed.
  
  Lemma matmap2_assoc : forall {r c} (m1 m2 m3 : @mat A r c),
    matmap2 f (matmap2 f m1 m2) m3 == matmap2 f m1 (matmap2 f m2 m3).
  Proof.
    intros. unfold mat_eq; simpl. unfold matmap2dl.
    apply dlmap2_assoc; auto.
  Qed.
  
End matmap2_sametype.

