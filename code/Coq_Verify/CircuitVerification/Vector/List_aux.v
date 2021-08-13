(*
  file:     list_aux.v
  purpose:  list auxilary
*)

Require Import Arith. (* ring *)
Require Import Lia.
Require Import Lra.

Require Export List.
Export ListNotations.

Require Export FunctionalExtensionality.


(** ** tactics that with a short name to do common jobs *)
Ltac gd k := generalize dependent k.


(** ** Extra properties *)
Section extra_props.
    
  (** map and repeat is communtative *)
  Lemma map_repeat {A} : forall (f : A -> A) (a : A) n, 
    map f (repeat a n) = repeat (f a) n.
  Proof. induction n; simpl; auto. f_equal; auto. Qed.
  
  (** decompose a list which length is 1 *)
  Lemma list_length_1 : forall {A} (l : list A),
    length l = 1 -> {x | l = [x]}.
  Proof. 
    destruct l; intros. inversion H. inversion H.
    apply length_zero_iff_nil in H1; subst. exists a. auto.
  Qed.
  
  (** decompose a list which length is S n *)
  Lemma list_length_Sn : forall {A} (l : list A) n,
    length l = S n -> {x & { t | l = x :: t}}.
  Proof. destruct l; intros. inversion H. exists a. exists l. auto. Qed.
  
  (** decompose a list which length is S (S n) *)
  Lemma list_length_SSn : forall {A} (l : list A) n,
    length l = S (S n) -> {x & { y & { t | l = x :: y :: t}}}.
  Proof.
    destruct l; intros. inversion H.
    exists a. destruct l. inversion H.
    exists a0. exists l. auto.
  Qed.

  (** a natural number must be odd or even *)
  Lemma nat_split : forall (n : nat), exists (x : nat),
    n = 2 * x \/ n = 2 * x + 1.
  Proof.
    induction n.
    - exists 0. auto.
    - destruct IHn. destruct H.
      + exists x. right. subst. ring.
      + exists (x+1). left. subst. ring.
  Qed.
  
  (** Two step induction principle for natural number *)
  Theorem nat_ind2 : forall (P : nat -> Prop),
    (P 0) -> (P 1) -> (forall n, P n -> P (S (S n))) -> (forall n, P n).
  Proof.
    intros. destruct (nat_split n). destruct H2; subst; induction x; auto.
    - replace (2 * S x) with (S (S (2 * x))); [apply H1; auto | ring].
    - replace (2 * S x + 1) with (S (S (2 * x + 1))); [apply H1; auto | ring].
  Qed.
  
  (** Connect induction principle between nat and list *)
  Lemma ind_nat_list {A} : forall (P : list A -> Prop) ,
    (forall n l, length l = n -> P l) -> (forall l, P l).
  Proof.
    intros. apply (H (length l)). auto.
  Qed.
  
  (** Two step induction principle for list *)
  Theorem list_ind2 : forall {A : Type} (P : list A -> Prop),
    (P []) -> (forall a, P [a]) -> (forall l a b, P l -> P (a :: b :: l)) ->
    (forall l, P l).
  Proof.
    intros A P H0 H1 H2. apply ind_nat_list. induction n using nat_ind2. 
    - intros. apply length_zero_iff_nil in H; subst; auto.
    - intros. apply list_length_1 in H. destruct H. subst; auto.
    - intros. apply list_length_SSn in H. destruct H. destruct s. destruct s.
      subst. apply H2.
      Abort.
  
  (** ** Heigth of a dlist *)
  Lemma dlist_h0_iff {A} : forall (dl : list (list A)), 
    length dl = 0 -> dl = nil.
  Proof. destruct dl; simpl; auto. intros H; easy. Qed.
  
End extra_props.


(** ** width of a dlist *)
Section dlist_width.

  Variable A : Type.
  
  Fixpoint width (dl : list (list A)) n :=
    match dl with
    | [] => True
    | x :: t => (length x = n) /\ width t n
    end.
  
  Lemma cons_width : forall l dl n, width (l :: dl) n ->
    length l = n /\ width dl n.
  Proof. intros. auto. Qed.
    
  Lemma In_length : forall l dl n, width dl n ->
    In l dl -> length l = n.
  Proof.
    intros. induction dl.
    - inversion H0.
    - apply cons_width in H; destruct H. apply in_inv in H0. destruct H0.
      + subst. auto.
      + apply IHdl; auto.
  Qed.
  
  Lemma app_width : forall dl1 dl2 n, 
    width (dl1 ++ dl2) n <-> width dl1 n /\ width dl2 n.
  Proof.
    induction dl1; simpl; intros; split; intros H; auto; destruct H; auto.
    - apply IHdl1 in H0. destruct H0. repeat split; auto.
    - destruct H. split; auto. apply IHdl1. split; auto.
  Qed.
  
  Lemma rev_width : forall dl n, width (rev dl) n -> width dl n.
  Proof.
    induction dl; simpl; intros; auto.
    apply app_width in H. simpl in H. destruct H. destruct H0. split; auto.
  Qed.
  
End dlist_width.

Arguments width {A}.


(** ** list repeat properties *)
Section list_repeat.

  Variable A : Type.
  Variable A0 : A.
  
  Lemma list_repeat_Sn : forall n, repeat A0 (S n) = A0 :: repeat A0 n.
  Proof. intros. auto. Qed.
  
  Lemma repeat_width : forall (l : list A) n k,
    length l = k -> width (repeat l n) k.
  Proof. induction n; intros; simpl; auto. Qed.
  
End list_repeat.


(** ** Zero list *)
Section lzero.

  Variable A : Type.
  Variable A0 : A.
  
  Definition lzero n := repeat A0 n.
  
  Lemma lzero_length : forall n, length (lzero n) = n.
  Proof. intros. apply repeat_length. Qed.
  
  Lemma lzero_app : forall n1 n2,
    lzero n1 ++ lzero n2 = lzero (n1 + n2).
  Proof. unfold lzero. intros. rewrite repeat_app. auto. Qed.
  
End lzero.

Arguments lzero {A}.

Compute lzero 99 3.


(** ** map one list to another one *)
Section lmap.

  Variable A B : Type.
  Variable f : A -> B.
  
(*   Check map. *)
  
  Lemma lmap_length : forall l, length (map f l) = length l.
  Proof. induction l; simpl; auto. Qed.
  
End lmap.

Compute map Nat.succ [1;2;3].


(** ** map two lists to a list *)
Section lmap2.

  Variable A B C : Type.
  Variable f : A -> B -> C.
  
  Fixpoint lmap2 (l1 : list A) (l2 : list B) : list C :=
    match l1, l2 with
    | x1 :: t1, x2 :: t2 => (f x1 x2) :: (lmap2 t1 t2)
    | _, _ => []
    end.
  
  Lemma lmap2_length : forall (l1 : list A) (l2 : list B) n,
    length l1 = n -> length l2 = n -> length (lmap2 l1 l2) = n.
  Proof. 
    induction l1,l2; simpl; auto. intros. destruct n; simpl; auto. easy.
  Qed.
  
  Lemma lmap2_app : forall (la1 la2 : list A) (lb1 lb2 : list B),
    length la1 = length lb1 ->
    length la2 = length lb2 ->
    lmap2 (la1 ++ la2) (lb1 ++ lb2) =
    (lmap2 la1 lb1) ++ (lmap2 la2 lb2).
  Proof.
    induction la1, lb1; intros; simpl; auto; simpl in H; try easy.
    f_equal. apply IHla1; auto.
  Qed.
  
  Lemma lmap2_nil_l : forall l, lmap2 [] l = [].
  Proof. destruct l; auto. Qed.

  Lemma lmap2_nil_r : forall l, lmap2 l [] = [].
  Proof. destruct l; auto. Qed.

End lmap2.

Arguments lmap2 {A B C}.

Compute lmap2 Nat.add [1;2;3] [4;5;6].


(** ** lmap2 properties needn't same base type *)
  
Section lmap2_anytype.

  Variable A B C : Type.
  Variable f : A -> B -> C.
  
  Lemma lmap2_tail : forall dl1 dl2,
    tl (lmap2 (lmap2 f) dl1 dl2) =
    lmap2 (lmap2 f) (tl dl1) (tl dl2).
  Proof. destruct dl1, dl2; simpl; auto. rewrite lmap2_nil_r. auto. Qed.

End lmap2_anytype.


(** ** lmap2 properties with same base type *)
Section lmap2_sametype.

  Variable A : Type.
  Variable f : A -> A -> A.
  Variable f_comm : forall a b, f a b = f b a.
  Variable f_assoc : forall a b c, f (f a b) c = f a (f b c).
  
  Lemma lmap2_comm : forall (l1 l2 : list A),
    lmap2 f l1 l2 = lmap2 f l2 l1.
  Proof. induction l1,l2; simpl; auto. rewrite IHl1. f_equal. auto. Qed.
  
  Lemma lmap2_assoc : forall (l1 l2 l3 : list A),
    lmap2 f (lmap2 f l1 l2) l3 = lmap2 f l1 (lmap2 f l2 l3).
  Proof. induction l1,l2,l3; simpl; auto. rewrite IHl1. f_equal. auto. Qed.
  
  (** lmap2 with map of two components *)
  Lemma lmap2_map_map : forall (f1 f2 g : A -> A) (h : A -> A -> A) 
    (H : forall x, g x = h (f1 x) (f2 x)) l,
    lmap2 h (map f1 l) (map f2 l) = map g l.
  Proof. induction l; simpl; auto. rewrite IHl. f_equal. auto. Qed.
  
  (** lmap2 over map is homorphism *)
  Lemma lmap2_map_hom : forall (f : A -> A) (g : A -> A -> A) 
    (H : forall x1 x2, f (g x1 x2) = g (f x1) (f x2)) l1 l2,
    lmap2 g (map f l1) (map f l2) = map f (lmap2 g l1 l2).
  Proof. induction l1,l2; auto. simpl. rewrite IHl1. f_equal. auto. Qed.

End lmap2_sametype.


(** ** lmap2 is considered as ladd *)
Section ladd.

  Variable A : Type.
  Variable A0 : A.
  Variable fadd : A -> A -> A.
  Variable fadd_comm : forall a b, fadd a b = fadd b a.
  Variable fadd_0_l : forall a, fadd A0 a = a.
  
  Definition ladd (l1 l2 : list A) : list A := lmap2 fadd l1 l2.
  
  (** l1 + l2 = l2 + l1 *)
  Lemma ladd_comm : forall l1 l2, ladd l1 l2 = ladd l2 l1.
  Proof. apply lmap2_comm; auto. Qed.
  
  (** [] + l = [] *)
  Lemma ladd_nil_l : forall l, ladd l [] = [].
  Proof. induction l; auto. Qed.
  
  (** l + [] = [] *)
  Lemma ladd_nil_r : forall l, ladd [] l = [].
  Proof. auto. Qed.
  
  (** 0 + l = l *)
  Lemma ladd_zero_l : forall l n, 
    length l = n -> ladd (lzero A0 n) l = l.
  Proof.
    induction l; simpl; intros. apply lmap2_nil_r.
    induction n ; simpl. inversion H. f_equal; auto.
  Qed.
  
  (** l + 0 = l *)
  Lemma ladd_zero_r : forall l n, 
    length l = n -> ladd l (lzero A0 n) = l.
  Proof.
    intros. unfold ladd. rewrite lmap2_comm; auto.
    apply ladd_zero_l; auto.
  Qed.
  
End ladd.

Arguments ladd {A}.

Compute ladd Nat.add [1;2] [3;4;5].


(** ** list sub,neg properties *)
Section listsub_neg.
  
  Variable A : Type.
  Variable A0 : A.
  Variable fadd : A -> A -> A.
  Variable fneg : A -> A.
  Variable fsub : A -> A -> A.
  Variable fsub_comm : forall a b, fsub a b = fneg (fsub b a).
  Variable fsub_assoc1 : forall a b c, fsub (fsub a b) c = fsub a (fsub c b).
  Variable fsub_assoc2 : forall a b c, fsub (fsub a b) c = fsub a (fadd b c).
  Variable fsub_0_l : forall a, fsub A0 a = fneg a.
  Variable fsub_0_r : forall a, fsub a A0 = a.
  Variable fsub_self : forall a, fsub a a = A0.
  
  Definition listsub (l1 l2 : list A) : list A := lmap2 fsub l1 l2.
  
  (** l1 - l2 = - (l2 - l1) *)
  Lemma listsub_comm : forall (l1 l2 : list A),
    listsub l1 l2 = map fneg (listsub l2 l1).
  Proof. induction l1,l2; simpl; auto. rewrite IHl1. f_equal. auto. Qed.
  
  (** (l1 - l2) - l3 = (l1 - l3) - l2 *)
  Lemma listsub_assoc1 : forall (l1 l2 l3 : list A),
    listsub (listsub l1 l2) l3 = listsub l1 (listsub l3 l2).
  Proof. induction l1,l2,l3; simpl; auto. rewrite IHl1. f_equal. auto. Qed.
  
  (** (l1 - l2) - l3 = l1 - (l2 + l3) *)
  Lemma listsub_assoc2 : forall (l1 l2 l3 : list A),
    listsub (listsub l1 l2) l3 = listsub l1 (lmap2 fadd l2 l3).
  Proof. induction l1,l2,l3; simpl; auto. rewrite IHl1. f_equal. auto. Qed.
  
  (** 0 - l = - l *)
  Lemma listsub_zero_l : forall l n, 
    length l = n -> listsub (lzero A0 n) l = map fneg l.
  Proof.
    induction l; simpl; intros. apply lmap2_nil_r.
    induction n ; simpl. inversion H. f_equal; auto.
  Qed.
  
  (** l - 0 = l *)
  Lemma listsub_zero_r : forall l n, 
    length l = n -> listsub l (lzero A0 n) = l.
  Proof.
    induction l; simpl; intros; auto. destruct n; simpl. inversion H.
    f_equal; auto.
  Qed.
  
  (** l - l = 0 *)
  Lemma listsub_self : forall l n, 
    length l = n -> listsub l l = (lzero A0 n).
  Proof.
    induction l; simpl; intros; subst; auto. simpl. f_equal; auto.
  Qed.
  
End listsub_neg.

Arguments listsub {A}.

Compute listsub Nat.sub [4;5;6] [1;2].


(** ** constant multiplication of list *)
Section lcmul_listmulc.

  Variable A : Type.
  Variable A0 : A.
  Variable fmul : A -> A -> A.
  Variable fmul_comm : forall a b, fmul a b = fmul b a.
  Variable fmul_0_l : forall a, fmul A0 a = A0.
  
  Definition lcmul (a : A) (l : list A) : list A :=
    map (fun x => fmul a x) l.
    
  Definition listmulc (l : list A) (a : A) : list A :=
    map (fun x => fmul x a) l.
  
  Lemma lcmul_length : forall a l n, length l = n -> 
    length (lcmul a l) = n.
  Proof. intros. unfold lcmul. rewrite map_length; auto. Qed.
  
  Lemma listmulc_lcmul : forall a l,
    listmulc l a = lcmul a l.
  Proof. induction l; auto. simpl. f_equal; auto. Qed.
  
  Lemma lcmul_nil : forall a, lcmul a [] = [].
  Proof. intros. auto. Qed.
  
  Lemma listmulc_nil : forall a, listmulc [] a = [].
  Proof. intros. auto. Qed.
  
End lcmul_listmulc.

Arguments lcmul {A}.
Arguments listmulc {A}.

Compute lcmul Nat.mul 3 [1;2;3].
Compute listmulc Nat.mul [1;2;3] 3.
Compute lcmul Nat.mul 3 [].


(** ** product of two lists *)
Section ldot.
  
  Variable A : Type.
  Variable A0 : A.
  Variable fadd fmul : A -> A -> A.
  Variable fadd_comm : forall a b, fadd a b = fadd b a.
  Variable fadd_assoc : forall a b c, fadd (fadd a b) c = fadd a (fadd b c).
  Variable fmul_assoc : forall a b c, fmul (fmul a b) c = fmul a (fmul b c).
  Variable fmul_comm : forall a b, fmul a b = fmul b a.
  Variable fmul_add_distr_l : forall a b1 b2,
    fmul a (fadd b1 b2) = fadd (fmul a b1) (fmul a b2).
  Variable fmul_add_distr_r : forall a1 a2 b,
    fmul (fadd a1 a2) b = fadd (fmul a1 b) (fmul a2 b).
  Variable fadd_0_l : forall a, fadd A0 a = a.
  Variable fmul_0_l : forall a, fmul A0 a = A0.
  
  Definition ldot (l1 l2 : list A) : A :=
    fold_right fadd A0 (lmap2 fmul l1 l2).
  
  Lemma ldot_comm : forall (l1 l2 : list A),
    ldot l1 l2 = ldot l2 l1.
  Proof. intros. unfold ldot. f_equal. apply lmap2_comm. auto. Qed.
  
  Lemma ldot_nil_l : forall (l : list A), ldot nil l = A0.
  Proof. intros. destruct l; simpl; auto. Qed.
  
  Lemma ldot_nil_r : forall (l : list A), ldot l nil = A0.
  Proof. intros. destruct l; simpl; auto. Qed.

  (** ldot cons *)
  Lemma ldot_cons : forall l1 l2 x1 x2,
    ldot (x1 :: l1) (x2 :: l2) = fadd (fmul x1 x2) (ldot l1 l2).
  Proof. induction l1,l2; simpl; intros; auto. Qed.
  
  Lemma ldot_zero_l : forall l n, ldot (lzero A0 n) l = A0.
  Proof.
    induction l,n; simpl; intros; auto. rewrite ldot_cons.
    rewrite IHl. rewrite fadd_comm, fadd_0_l, fmul_0_l. auto.
  Qed.
  
  Lemma ldot_zero_r : forall l n, ldot l (lzero A0 n) = A0.
  Proof. intros. rewrite ldot_comm. apply ldot_zero_l. Qed.
  
  (** ldot left distributive over ladd.
    l1 . (l2 + l3) = l1.l2 + l1.l3 *)
  Lemma ldot_ladd_distr_l : forall l1 l2 l3 r,
    length l1 = r -> length l2 = r -> length l3 = r ->
    ldot l1 (ladd fadd l2 l3) = fadd (ldot l1 l2) (ldot l1 l3).
  Proof.
    induction l1,l2,l3; simpl; intros; subst; auto; try discriminate.
    repeat rewrite ldot_cons. inversion H1. inversion H0.
    rewrite IHl1 with (r:=length l1); auto.
    (* IF we have ring ability, it is easy. *)
    rewrite fmul_add_distr_l.
    remember (fmul a a0). remember (fmul a a1).
    remember (ldot l1 l2). remember (ldot l1 l3).
    (* (a2 + a3) + (a4 + a5)  = (a2 + a4) + (a3 + a5) *)
    repeat rewrite fadd_assoc; f_equal. repeat rewrite <- fadd_assoc; f_equal.
    auto.
  Qed.
  
  (** ldot right distributive over ladd.
    (l1 + l2) . l3) = l1.l3 + l2.l3 *)
  Lemma ldot_ladd_distr_r : forall l1 l2 l3 r,
    length l1 = r -> length l2 = r -> length l3 = r ->
    ldot (ladd fadd l1 l2) l3 = fadd (ldot l1 l3) (ldot l2 l3).
  Proof.
    induction l1,l2,l3; simpl; intros; subst; auto; try discriminate.
    repeat rewrite ldot_cons. inversion H1. inversion H0.
    rewrite IHl1 with (r:=length l1); auto.
    (* IF we have ring ability, it is easy. *)
    remember (ldot l1 l3). remember (ldot l2 l3).
    rewrite fmul_add_distr_r. remember (fmul a a1). remember (fmul a0 a1).
    (* (a4 + a5) + (a2 + a3) = (a4 + a2) + (a5 + a3) *)
    repeat rewrite fadd_assoc; f_equal. repeat rewrite <- fadd_assoc; f_equal.
    auto.
  Qed.
  
  (* ldot right distributive over lcmul and fmul.
    (x * l1) . l2 = x * (l1 . l2) *)
  Lemma ldot_lcmul_distr_r : forall l1 l2 x,
    ldot (lcmul fmul x l1) l2 = fmul x (ldot l1 l2).
  Proof.
    induction l1,l2; simpl; intros; auto.
    - repeat rewrite ldot_nil_l; rewrite fmul_comm; auto.
    - repeat rewrite ldot_nil_l; rewrite fmul_comm; auto.
    - repeat rewrite ldot_nil_r; rewrite fmul_comm; auto.
    - repeat rewrite ldot_cons. rewrite IHl1.
      remember (ldot l1 l2). rewrite fmul_add_distr_l. f_equal.
      rewrite fmul_assoc. auto.
  Qed.
  
  (** ldot left distributve over lmap2.
    dot (map l1 l2) l3 = dot l1 l3 + dot l2 l3 *)
  Lemma ldot_lmap2_distr_l : forall l1 l2 l3 r,
    length l1 = r -> length l2 = r -> length l3 = r ->
    ldot (lmap2 fadd l1 l2) l3 = 
    fadd (ldot l1 l3) (ldot l2 l3).
  Proof.
    induction l1,l2,l3; simpl in *; intros; auto; subst; try discriminate.
    repeat rewrite ldot_cons.
    (* (r1 + p1) + (r2 + p2) => (r1 + r2) + (p1 + p2) *)
    remember (fmul a a1) as r1. remember (fmul a0 a1) as r2.
    remember (ldot l1 l3) as p1. remember (ldot l2 l3) as p2.
    rewrite <- fadd_assoc. rewrite (fadd_comm _ r2). rewrite <- fadd_assoc.
    rewrite (fadd_comm r2 r1). remember (fadd r1 r2) as r12.
    rewrite fadd_assoc. rewrite Heqr12,Heqp1,Heqp2,Heqr1,Heqr2. f_equal; auto.
    inversion H1. inversion H0.
    remember (length l1) as r0. apply IHl1 with (r:=r0); auto.
  Qed.
  
  (** ldot right distributve over lmap2.
    dot l1 (map l2 l3) = dot l1 l2 + dot l1 l3 *)
  Lemma ldot_lmap2_distr_r : forall l1 l2 l3 r,
    length l1 = r -> length l2 = r -> length l3 = r ->
    ldot l1 (lmap2 fadd l2 l3) = 
    fadd (ldot l1 l2) (ldot l1 l3).
  Proof.
    induction l1,l2,l3; simpl in *; intros; auto; subst; try discriminate.
    repeat rewrite ldot_cons.
    (* (r1 + p1) + (r2 + p2) => (r1 + r2) + (p1 + p2) *)
    remember (fmul a a0) as r1. remember (fmul a a1) as r2.
    remember (ldot l1 l2) as p1. remember (ldot l1 l3) as p2.
    rewrite <- fadd_assoc. rewrite (fadd_comm _ r2). rewrite <- fadd_assoc.
    rewrite (fadd_comm r2 r1). remember (fadd r1 r2) as r12.
    rewrite fadd_assoc. rewrite Heqr12,Heqp1,Heqp2,Heqr1,Heqr2. f_equal; auto.
    inversion H1. inversion H0.
    remember (length l1) as r0. apply IHl1 with (r:=r0); auto.
  Qed.

End ldot.

Arguments ldot {A}.
Arguments ldot_comm {A}.


Compute ldot 0 Nat.add Nat.mul [1;2;3] [4;5;6].


(** ** a dlist with same element nil *)
Section dnil.
  
  Variable A : Type.
  
  Fixpoint dnil n : list (list A) :=
    match n with
    | O => nil
    | S n' => nil :: (dnil n')
    end.

  Lemma dnil_height : forall n, length (dnil n) = n.
  Proof. induction n; simpl; auto. Qed.

  Lemma dnil_width : forall n, width (dnil n) 0.
  Proof. induction n; simpl; auto. Qed.
  
  Lemma dnil_app : forall n1 n2, 
    dnil (n1 + n2) = dnil n1 ++ dnil n2.
  Proof. induction n1,n2; simpl; auto; rewrite IHn1; auto. Qed.

  Lemma dlist_w0_eq_dnil : forall (dl : list (list A)), 
    width dl 0 -> dl = dnil (length dl).
  Proof.
    induction dl; simpl; auto. intros [H1 H2]. f_equal; auto.
    apply length_zero_iff_nil; auto.
  Qed.

  Lemma dnil_rev : forall n, rev (dnil n) = dnil n.
  Proof.
    induction n; simpl; auto. rewrite IHn. clear IHn. induction n; simpl; auto.
    rewrite IHn. auto.
  Qed.

End dnil.

Arguments dnil {A}.

Compute dnil 3.


(** ** lmap2 and dnil *)
Section lmap2_dnil.

  Variable A B C : Type.
  Variable f2 : A -> B -> C.

  Lemma lmap2_dnil_l : forall dl n, 
    length dl = n -> lmap2 (lmap2 f2) (dnil n) dl = dnil n.
  Proof.
    intros. gd dl. induction n; auto; intros.
    induction dl. inversion H. simpl. f_equal; auto.
  Qed.
  
  Lemma lmap2_dnil_r : forall dl n, 
    length dl = n -> lmap2 (lmap2 f2) dl (dnil n) = dnil n.
  Proof.
    intros. gd dl. induction n; simpl; intros.
    - induction dl; simpl; auto.
    - induction dl. inversion H. simpl. f_equal; auto. apply lmap2_nil_r.
  Qed.

End lmap2_dnil.


(** ** Convert between row and col. eg, [1;2;3] <-> [[1];[2];[3]] *)
Section convert_row_and_col.
  
  Variable A : Type.
  Variable A0 : A.
  
  Fixpoint cvt_row2col (l : list A) : list (list A) :=
    match l with
    | [] => []
    | x :: tl => [x] :: (cvt_row2col tl)
    end.
  
  Lemma cvt_row2col_height : forall l, length (cvt_row2col l) = length l.
  Proof. induction l; simpl; intros; auto. Qed.
  
  Lemma cvt_row2col_width : forall l, width (cvt_row2col l) 1.
  Proof. induction l; simpl; intros; auto. Qed.
  
  Fixpoint cvt_col2row (dl : list (list A)) : list A :=
    match dl with
    | [] => []
    | l :: tl => (hd A0 l) :: (cvt_col2row tl)
    end.
  
  Lemma cvt_row2col_col2row : forall (dl : list (list A)) r,
    length dl = r ->
    width dl 1 ->
    cvt_row2col (cvt_col2row dl) = dl.
  Proof.
    induction dl; simpl; auto; intros. inversion H. destruct H0. f_equal.
    - destruct a. inversion H0. inversion H0. apply length_zero_iff_nil in H4.
      subst. auto.
    - destruct r. inversion H. inversion H1. apply IHdl with (r:=r); auto.
  Qed.
  
  Lemma cvt_col2row_row2col : forall (l : list A), 
    cvt_col2row (cvt_row2col l) = l.
  Proof. induction l; simpl; auto; intros. f_equal; auto. Qed.
  
End convert_row_and_col.

Arguments cvt_row2col {A}.
Arguments cvt_col2row {A}.

Compute cvt_row2col [1;2;3].
Compute cvt_col2row 0 [].
Compute cvt_col2row 0 [[]].
Compute cvt_col2row 0 [[1];[];[3]].
Compute cvt_col2row 0 [[1];[2];[3]].
Compute cvt_row2col (cvt_col2row 0 []).
Compute cvt_row2col (cvt_col2row 0 [[1];[2];[3]]).
Compute cvt_col2row 0 (cvt_row2col []).
Compute cvt_col2row 0 (cvt_row2col [1;2;3]).


(** ** head column of a dlist *)
Section hdc.

  Variable A : Type.
  Variable A0 : A.
  
  Fixpoint hdc (dl : list (list A)) : list A :=
    match dl with
    | [] => []
    | l :: tl => (hd A0 l) :: (hdc tl)
    end.
  
  Lemma hdc_length : forall dl, length (hdc dl) = length dl.
  Proof. induction dl; simpl; auto. Qed.
  
End hdc.

Arguments hdc {A}.

Compute hdc 0 [].
Compute hdc 0 [[];[];[]].
Compute hdc 0 [[];[2];[]].
Compute hdc 0 [[1;2;3];[4;5;6]].


(** ** tail column of a dlist *)
Section tlc.

  Variable A : Type.
  Variable A0 : A.
  
  Fixpoint tlc (dl : list (list A)) : list (list A) :=
    match dl with
    | [] => []
    | l :: tl => (tail l) :: (tlc tl)
    end.
  
  Lemma tlc_height : forall dl, length (tlc dl) = length dl.
  Proof. induction dl; simpl; auto. Qed.
  
  Lemma tlc_width0 : forall dl, 
    width dl 0 -> width (tlc dl) 0.
  Proof.
    induction dl; simpl; auto. intros. destruct H. split; auto.
    apply length_zero_iff_nil in H. subst. auto. 
  Qed.
  
  Lemma tlc_widthS : forall dl c, 
    width dl (S c) -> width (tlc dl) c.
  Proof.
    induction dl; simpl; auto. intros. destruct H. split; auto.
    destruct a. inversion H. simpl in *. inversion H. auto.
  Qed.
  
End tlc.

Arguments tlc {A}.

Compute tlc [].
Compute tlc [[];[]].
Compute tlc [[2;3;4];[];[]].
Compute tlc [[1;2;3];[4;5;6]].


(** ** construct a dlist with a list and a dlist *)
Section consc.

  Variable A : Type.
  Variable A0 : A.
  
  Fixpoint consc (l : list A) (dl : list (list A)) : list (list A) :=
    match l, dl with
    | xl :: tl, xdl :: tdl => (xl :: xdl) :: (consc tl tdl)
    | _, _ => []
    end.
  
  Lemma consc_height : forall l dl r,
    length l = r -> length dl = r ->
    length (consc l dl) = r.
  Proof.
    induction l,dl; simpl; intros; auto. destruct r. inversion H. f_equal.
    inversion H. inversion H0. subst. apply IHl; auto.
  Qed.
  
  Lemma consc_width : forall l dl c,
    length l = length dl -> width dl c ->
    width (consc l dl) (S c).
  Proof.
    induction l,dl; simpl; intros; auto. inversion H. destruct H0. split; auto.
  Qed.
  
  Lemma consc_hdc_tlc_width0 : forall dl r, 
    length dl = r -> width dl 0 -> 
    consc (hdc A0 dl) (tlc dl) = cvt_row2col (repeat A0 r).
  Proof.
    induction dl; simpl; intros; subst; auto. destruct H0.
    rewrite length_zero_iff_nil in H. subst. simpl. f_equal. auto.
  Qed.
  
  Lemma consc_hdc_tlc_widthS : forall dl c, 
    width dl (S c) ->
    consc (hdc A0 dl) (tlc dl) = dl.
  Proof.
    induction dl; simpl; intros; auto. destruct H. f_equal; auto.
    - destruct a. inversion H. auto.
    - apply IHdl with (c:=c). auto.
  Qed.

  (** consc decompose.
    x1::l1 ++ l2::dl2 = (x::l2) :: (l1 ++ dl2)  *)
  Lemma consc_decompose : forall x1 l1 l2 dl2,
    consc (x1::l1) (l2::dl2) = (x1::l2) :: (consc l1 dl2).
  Proof. intros. simpl. auto. Qed.
  
  (** repeat (x :: l) decompose *)
  Lemma repeat_consr : forall l x n,
    repeat (x :: l) n = consc (repeat x n) (repeat l n).
  Proof. induction n; simpl; auto. rewrite IHn. auto. Qed.

End consc.

Arguments consc {A}.
Arguments consc_decompose {A}.
Arguments consc_hdc_tlc_widthS {A}.

Compute consc [] [].
Compute consc [1;2;3] [].
Compute consc [] [[1;2];[3;4]].
Compute consc [1;2] [[];[]].
Compute consc [1;2] [[];[];[]].
Compute consc [1;2;3] [[5;6];[7;8];[9;10]].
Compute consc [1;2;3] [[5;6];[7;8];[9;10];[11;12]].


(** ** Append two objects of dlist type to one object of dlist *)
Section dlist_app.
  
  Variable A : Type.
  
  (** dlist append by row *)
  Definition dlistappr := app.
  
  (** dlist apend by column *)
  Fixpoint dlistappc (dl1 dl2 : list (list A)) : list (list A) :=
    match dl1, dl2 with
    | l1 :: tl1, l2 :: tl2 => (app l1 l2) :: (dlistappc tl1 tl2)
    | _, _ => []
    end.

End dlist_app.

Arguments dlistappr {A}.
Arguments dlistappc {A}.

Notation "l @@ r" := (dlistappc l r) (at level 40) : list_scope.

Compute dlistappr [[1;2;3];[4;5;6]] [[7;8;9];[10;11;12]].
Compute dlistappc [[1;2;3];[4;5;6]] [[7;8;9];[10;11;12]].

Compute [[1;2;3];[4;5;6]] ++ [[7;8;9];[10;11;12]].
Compute [[1;2;3];[4;5;6]] @@ [[7;8;9];[10;11;12]].


(** ** Zero dlist *)
Section dlzero.

  Variable A : Type.
  Variable A0 : A.
  
  Definition dlzero r c := repeat (lzero A0 c) r.
  
  Lemma dlzero_dnil : forall c, dlzero c 0 = dnil c.
  Proof. induction c; simpl; auto. rewrite <- IHc. auto. Qed.
  
  Lemma dlzero_height : forall r c, length (dlzero r c) = r.
  Proof. intros. apply repeat_length. Qed.
  
  Lemma dlzero_width : forall r c, width (dlzero r c) c.
  Proof.
    induction r; intros. simpl. auto. simpl. split. apply lzero_length.
    unfold dlzero in IHr. auto.
  Qed.
  
  Lemma dlzero_w0_eq_dnil : forall r, (dlzero r 0) = dnil r.
  Proof. 
    induction r; auto. unfold dlzero in *. simpl in *. rewrite IHr. auto.
  Qed.
  
  Lemma dlzero_app_row : forall r1 r2 c,
    dlzero r1 c ++ dlzero r2 c = dlzero (r1 + r2) c.
  Proof. unfold dlzero. intros. rewrite repeat_app. auto. Qed.
  
  Lemma dlzero_app_col : forall r c1 c2,
    dlzero r c1 @@ dlzero r c2 = dlzero r (c1 + c2).
  Proof.
    induction r; intros; simpl; auto. unfold dlzero,lzero in *.
    rewrite IHr. simpl. f_equal. rewrite repeat_app. auto.
  Qed.

End dlzero.

Arguments dlzero {A}.
Arguments dlzero_height {A} A0 {r c}.
Arguments dlzero_width {A} A0 {r c}.

Compute dlzero 99 3 2.


(** ** dlist unit *)
Section dlunit.

  Variable A : Type.
  Variable A0 A1 : A.
  
  Fixpoint dlunit (n : nat) : list (list A) :=
    match n with
    | O => []
    | S n0 => (A1 :: (repeat A0 n0)) :: (consc (repeat A0 n0) (dlunit n0))
    end.
  
  Lemma dlunit_height : forall n, length (dlunit n) = n.
  Proof.
    induction n; simpl; auto. f_equal.
    rewrite consc_height with (r:=n); auto. apply repeat_length.
  Qed.
  
  Lemma dlunit_width : forall n, width (dlunit n) n.
  Proof.
    induction n; simpl; auto. split.
    - f_equal. apply repeat_length.
    - apply consc_width; auto. rewrite repeat_length, dlunit_height; auto.
  Qed.
  
End dlunit.

Arguments dlunit {A}.
Arguments dlunit_height {A} A0 A1 {n}.
Arguments dlunit_width {A} A0 A1 {n}.

Compute dlunit 0 1 0.
Compute dlunit 0 1 1.
Compute dlunit 0 1 2.
Compute dlunit 0 1 3.


(** ** transpose a dlist *)
Section dltrans.
  
  Variable A : Type.
  Variable A0 A1 : A.
  
  (** Idea: fetch row as column one bye one. 
      Generate a dlist with c rows if given c is <= column of input dlist *)
  (** Note that, we give c to support dlist_0_c situation.
    eg: 
      [] 3 => [[];[];[]]
      [[];[];[]] 0 => []
  *)
  Fixpoint dltrans (dl : list (list A)) (c : nat) : list (list A) :=
    match dl with
    | [] => @dnil A c
    | l :: tl => consc l (dltrans tl c)
    end.
  
  Lemma dltrans_height : forall dl c, 
    width dl c ->
    length (dltrans dl c) = c.
  Proof. induction dl; intros; simpl; auto.
    - rewrite dnil_height. auto.
    - inversion H. rewrite consc_height with (r:=c); auto.
  Qed.
 
  Lemma dltrans_width : forall dl r c, 
    length dl = r -> width dl c -> width (dltrans dl c) r.
  Proof.
    induction dl; intros; simpl in *; auto.
    - induction c; simpl in *; auto.
    - rewrite <- H. destruct H0. apply consc_width.
      2:{ apply IHdl; auto. }
      rewrite dltrans_height; auto.
  Qed.
  
  (** dltrans nil *)
  Lemma dltrans_nil : forall n, dltrans (dnil n) 0 = [].
  Proof. intros. destruct n; auto. Qed.
  
  (** dltrans and consr *)
  Lemma dltrans_consr : forall dl l c,
    dltrans (l :: dl) c = consc l (dltrans dl c).
  Proof. intros. simpl. auto. Qed.
  
  (** dltrans and consc *)
  Lemma dltrans_consc : forall dl l r c,
    length l = r -> length dl = r -> width dl c ->
    dltrans (consc l dl) (S c) = l :: (dltrans dl c).
  Proof.
    induction dl; simpl; intros; auto.
    - induction l; auto. subst. inversion H0.
    - destruct H1. induction l.
      + subst. inversion H0.
      + rewrite consc_decompose. rewrite <- (consc_decompose a0 a).
        rewrite <- IHdl with (r:=pred r); auto; subst; simpl; auto.
  Qed.
  
  (** dltrans twice return back *)
  Lemma dltrans_trans : forall dl r c,
    length dl = r -> width dl c ->
      dltrans (dltrans dl c) r = dl.
  Proof.
    induction dl; simpl; intros.
    - destruct c; simpl; auto. subst. auto.
    - destruct H0. rewrite <- H. rewrite dltrans_consc with (r:=c); auto.
      + f_equal. auto.
      + rewrite dltrans_height; auto.
      + apply dltrans_width; auto.
  Qed.
    
  (** dltrans with zero *)
  Lemma dltrans_zero : forall r c,
    dltrans (dlzero A0 r c) c = dlzero A0 c r.
  Proof.
    induction r; intros; simpl; auto. rewrite dlzero_dnil; auto.
    unfold dlzero in *; simpl in *. rewrite IHr.
    rewrite repeat_consr. auto.
  Qed.
    
  (** transpose dlunit keep unchanged *)
  Lemma dltrans_dlunit : forall n, 
    let u := dlunit A0 A1 n in
      dltrans u n = u.
  Proof.
    simpl. induction n; auto. simpl.
    rewrite dltrans_consc with (r:=n); auto; try apply repeat_length; 
    try apply dlunit_height; try apply dlunit_width; auto. rewrite IHn; auto.
  Qed.
  
End dltrans.

Arguments dltrans {A}.
Arguments dltrans_height {A}.
Arguments dltrans_width {A}.
Arguments dltrans_trans {A}.


Compute consc [1;2;3] [].
Compute (dltrans (consc [1;2;3] []) 3).
Compute [1;2;3] :: (dltrans [] 2).

Compute dltrans [] 2.
Compute dltrans [[];[]] 0.
Compute dltrans [[];[]] 2.  (* input error, colums must be <= 0 *)
Compute dltrans [[1;2;3];[4;5;6]] 2.
Compute dltrans [[1;2;3];[4;5;6]] 3.
Compute dltrans [[1;2;3];[4;5;6]] 4.  (* error, colums must be <= 3*)
Compute dltrans [[1;2;3];[]] 2.

Compute (dltrans (dltrans [] 2) 2).
Compute (dltrans (dltrans [[];[]] 0) 2).


(** ** map of dlist *)
Section dlmap.
  
  Variable A B : Type.
  Variable f : A -> B.
  
  Definition dlmap dl := map (map f) dl.

  Lemma dlmap_height : forall dl, length (dlmap dl) = length dl.
  Proof. induction dl; simpl; auto. Qed.
  
  Lemma dlmap_width : forall dl n, 
    width dl n <-> width (dlmap dl) n.
  Proof. 
    induction dl; simpl; auto; intros; try tauto. split.
    - intros [H1 H2]. split. rewrite lmap_length; auto. apply IHdl. auto.
    - intros [H1 H2]. rewrite lmap_length in H1. apply IHdl in H2. tauto.
  Qed.
  
  Lemma dlmap_cons : forall l dl, dlmap (l :: dl) = (map f l) :: (dlmap dl).
  Proof. intros. simpl. auto. Qed.
  
  Lemma dlmap_app : forall dl1 dl2,
    dlmap (dl1 ++ dl2) = (dlmap dl1) ++ (dlmap dl2).
  Proof. induction dl1,dl2; simpl; auto; rewrite IHdl1; auto. Qed.
  
  Lemma dlmap_dnil : forall n, 
    dlmap (dnil n) = dnil n.
  Proof. induction n; simpl; auto. rewrite IHn. auto. Qed.
  
End dlmap.

Arguments dlmap {A B}.

Compute dlmap Nat.succ [[1;2;3];[4;5;6]].


(** ** map2 of dlist *)
Section dlmap2.
  
  Variable A B C : Type.
  Variable f : A -> B -> C.
  
  Definition dlmap2 dl1 dl2 := lmap2 (lmap2 f) dl1 dl2.
  
  Lemma dlmap2_height : forall dl1 dl2,
    length dl1 = length dl2 -> length (dlmap2 dl1 dl2) = length dl1.
  Proof. induction dl1,dl2; simpl; auto. Qed.
  
  Lemma dlmap2_width : forall dl1 dl2 n,
    width dl1 n -> width dl2 n -> width (dlmap2 dl1 dl2) n.
  Proof. 
    induction dl1,dl2; simpl; auto. intros. destruct H,H0. split.
    - apply lmap2_length; auto.
    - apply IHdl1; auto.
  Qed.
  
  Lemma dlmap2_consr : forall dl1 dl2 l1 l2,
    dlmap2 (l1 :: dl1) (l2 :: dl2) = 
    (lmap2 f l1 l2) :: (dlmap2 dl1 dl2).
  Proof. intros. simpl. auto. Qed.
  
  Lemma dlmap2_consc : forall l1 dl1 l2 dl2 r c t,
    length l1 = r -> length dl1 = r -> width dl1 c ->
    length l2 = t -> length dl2 = t -> width dl2 c ->
    dlmap2 (consc l1 dl1) (consc l2 dl2) = 
    consc (lmap2 f l1 l2) (dlmap2 dl1 dl2).
  Proof.
    induction l1,dl1,l2,dl2; simpl; intros; auto. f_equal.
    destruct H1,H4. apply IHl1 with (r:=pred r) (c:=c) (t:=pred t); subst; auto.
  Qed.
  
  Lemma dlmap2_app : forall dla1 dla2 dlb1 dlb2,
    length dla1 = length dlb1 ->
    length dla2 = length dlb2 ->
    dlmap2 (dla1 ++ dla2) (dlb1 ++ dlb2) = 
    (dlmap2 dla1 dlb1) ++ (dlmap2 dla2 dlb2).
  Proof. intros. unfold dlmap2. apply lmap2_app; auto. Qed.
  
  Lemma dlmap2_dnil_l : forall dl n,
    length dl = n ->
    dlmap2 (dnil n) dl = dnil n.
  Proof. intros. unfold dlmap2. rewrite lmap2_dnil_l; auto. Qed.
  
  Lemma dlmap2_tail : forall dl1 dl2,
    length dl1 = length dl2 ->
    tl (dlmap2 dl1 dl2) = dlmap2 (tl dl1) (tl dl2).
  Proof. intros. unfold dlmap2. apply lmap2_tail. Qed.

  (** Relationship between dltrans and dlmap2 *)
  Lemma dltrans_dlmap2 : forall dl1 dl2 r c,
    length dl1 = r -> length dl2 = r -> width dl1 c -> width dl2 c ->
    dltrans (dlmap2 dl1 dl2) c = 
    dlmap2 (dltrans dl1 c) (dltrans dl2 c).
  Proof.
    induction dl1,dl2; simpl; intros; auto.
    - rewrite dlmap2_dnil_l; auto; apply dnil_height.
    - subst. inversion H0.
    - subst. inversion H0.
    - destruct H1, H2.
      rewrite IHdl1 with (r:=pred r) (c:=c); auto.
      + rewrite dlmap2_consc with (r:=c) (c:=pred r) (t:=c); auto;
        try apply dltrans_height; try apply dltrans_width; subst; auto.
      + subst; auto.
      + subst; auto.
  Qed.
  
End dlmap2.

Arguments dlmap2 {A B C}.

Compute dlmap2 Nat.add [[1;2];[3;4]] [[5;6];[7;8]].


(** ** dlmap2 with same base type *)
Section dlmap2_sametype.

  Variable A : Type.
  Variable f : A -> A -> A.
  Variable f_comm : forall a b, f a b = f b a.
  Variable f_assoc : forall a b c, f (f a b) c = f a (f b c).
  
  Lemma dlmap2_comm : forall (dl1 dl2 : list (list A)),
    dlmap2 f dl1 dl2 = dlmap2 f dl2 dl1.
  Proof.
    induction dl1,dl2; simpl; auto. f_equal; auto. apply lmap2_comm. auto. 
  Qed.
  
  Lemma dlmap2_assoc : forall (dl1 dl2 dl3 : list (list A)),
    dlmap2 f (dlmap2 f dl1 dl2) dl3 = 
    dlmap2 f dl1 (dlmap2 f dl2 dl3).
  Proof.
    induction dl1,dl2,dl3; simpl; auto. f_equal; auto. apply lmap2_assoc.
    auto. 
  Qed.
  
  (** dlmap2 with dlmap of two components *)
  Lemma dlmap2_dlmap_dlmap : forall (f1 f2 g : A -> A) (h : A -> A -> A) 
    (H : forall x, g x = h (f1 x) (f2 x)) l,
    dlmap2 h (dlmap f1 l) (dlmap f2 l) = dlmap g l.
  Proof.
    induction l; simpl; auto. rewrite IHl. f_equal. apply lmap2_map_map.
    auto.
  Qed.
  
  (** dlmap2 over dlmap is homorphism *)
  Lemma dlmap2_dlmap_hom : forall (f : A -> A) (g : A -> A -> A) 
    (H : forall x1 x2, f (g x1 x2) = g (f x1) (f x2)) d1 d2,
    dlmap2 g (dlmap f d1) (dlmap f d2) = dlmap f (dlmap2 g d1 d2).
  Proof.
    induction d1,d2; auto. simpl. rewrite IHd1. f_equal.
    rewrite lmap2_map_hom; auto.
  Qed.
  
End dlmap2_sametype.


(** ** Square Zero dlist *)
Section sdlzero.

  Variable A : Type.
  Variable A0 : A.
  
  Definition sdlzero n := repeat (repeat A0 n) n.
  
  Lemma sdlzero_eq_dlzero_r : forall r c,
    r = c -> sdlzero r = dlzero A0 r c.
  Proof. intros. subst. unfold sdlzero, dlzero. f_equal. Qed.
  
  Lemma sdlzero_eq_dlzero_c : forall r c,
    r = c -> sdlzero c = dlzero A0 r c.
  Proof. intros. subst. unfold sdlzero, dlzero. f_equal. Qed.
  
  Lemma sdlzero_height : forall n, length (sdlzero n) = n.
  Proof. intros. apply repeat_length. Qed.
  
  Lemma sdlzero_width : forall n, width (sdlzero n) n.
  Proof.
    intros. unfold sdlzero. induction n. simpl; auto.
    apply repeat_width. apply repeat_length.
  Qed.
  
End sdlzero.


(** ** dlmap2 is considered as dladd *)
Section dladd.

  Variable A : Type.
  Variable A0 : A.
  Variable fadd : A -> A -> A.
  Variable fadd_comm : forall a b, fadd a b = fadd b a.
  Variable fadd_0_l : forall a, fadd A0 a = a.
  
  Lemma dladd_zero_l : forall dl r c, 
    length dl = r -> width dl c ->
    dlmap2 fadd (dlzero A0 r c) dl = dl.
  Proof.
    induction dl; simpl; intros.
    - unfold dlmap2. apply lmap2_nil_r.
    - induction r. inversion H. inversion H. destruct H0. simpl.
      unfold dlzero in *. f_equal; auto.
      apply ladd_zero_l; auto.
  Qed.
  
  Lemma dladd_zero_r : forall dl r c, 
    length dl = r -> width dl c ->
    dlmap2 fadd dl (dlzero A0 r c) = dl.
  Proof.
    intros. rewrite dlmap2_comm; auto. apply dladd_zero_l; auto.
  Qed.

End dladd.


(** ** dlmap2 is considered as dlistsub *)
Section dlistsub.

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
  
  Lemma dlistsub_comm : forall dl1 dl2 c, 
    length dl1 = length dl2 ->
    width dl1 c -> width dl2 c ->
    dlmap2 fsub dl1 dl2 = dlmap fneg (dlmap2 fsub dl2 dl1).
  Proof.
    induction dl1,dl2; simpl; intros; auto. f_equal; auto.
    - apply listsub_comm; auto.
    - destruct H0,H1. apply IHdl1 with (c:=c); auto.
  Qed.
  
  Lemma dlistsub_assoc2 : forall dl1 dl2 dl3 r c, 
    length dl1 = r -> length dl2 = r -> length dl3 = r ->
    width dl1 c -> width dl2 c ->
    dlmap2 fsub (dlmap2 fsub dl1 dl2) dl3 = 
    dlmap2 fsub dl1 (dlmap2 fadd dl2 dl3).
  Proof.
    induction dl1,dl2,dl3; simpl; intros; auto. f_equal; auto.
    - apply listsub_assoc2; auto.
    - destruct H2,H3. destruct r; inversion H. 
      apply IHdl1 with (r:=r) (c:=c); auto.
  Qed.
  
  (** 0 - dl = - dl *)
  Lemma dlistsub_zero_l : forall dl r c, 
    length dl = r -> width dl c ->
    dlmap2 fsub (dlzero A0 r c) dl =
    dlmap fneg dl.
  Proof.
    induction dl; simpl; intros.
    - unfold dlmap2. apply lmap2_nil_r.
    - induction r. inversion H. inversion H. destruct H0. simpl.
      unfold dlzero in *. f_equal; auto.
      apply listsub_zero_l; auto.
  Qed.
  
  (** dl - 0 = dl *)
  Lemma dlistsub_zero_r : forall dl r c, 
    length dl = r -> width dl c ->
    dlmap2 fsub dl (dlzero A0 r c) = dl.
  Proof.
    induction dl; simpl; intros; auto. destruct r; simpl. inversion H.
    inversion H. destruct H0. f_equal; auto.
    apply listsub_zero_r; auto. apply IHdl; auto.
  Qed.
  
  (** dl - dl = 0 *)
  Lemma dlistsub_self : forall dl r c, 
    length dl = r -> width dl c ->
    dlmap2 fsub dl dl = (dlzero A0 r c).
  Proof.
    induction dl; simpl; intros; subst; auto. destruct H0.
    unfold dlzero in *. simpl. f_equal.
    apply listsub_self; auto. apply IHdl; auto.
  Qed.

End dlistsub.


(** list dot dlist *)
Section ldotdl.

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
  
  (* a convenient notation in this section *)
  Notation ldot := (ldot A0 fadd fmul).
  
  Fixpoint ldotdl (l : list A) (dl : list (list A)) : list A :=
    match dl with
    | h :: t => (ldot l h) :: (ldotdl l t)
    | [] => []
    end.
  
  Lemma ldotdl_length : forall l dl r c,
    length l = c -> length dl = r -> width dl c ->
    length (ldotdl l dl) = r.
  Proof.
    intros l dl. gd l. induction dl; simpl; intros; auto.
    destruct H1. rewrite IHdl with (r:=pred r) (c:=c); auto; subst; auto.
  Qed.
  
  (** ldotdl left distributve over lmap2 *)
  Lemma ldotdl_lmap2_distr_l : forall dl l1 l2 {r c},
    length l1 = r -> length l2 = r -> length dl = c -> width dl r ->
    ldotdl (lmap2 fadd l1 l2) dl = 
    lmap2 fadd (ldotdl l1 dl) (ldotdl l2 dl).
  Proof.
    induction dl; intros; simpl; auto. f_equal; simpl in *; destruct H2.
    - rewrite ldot_lmap2_distr_l with (r:=r); auto.
    - apply IHdl with (r:=r) (c:=pred c); auto. subst. auto.
  Qed.
  
  (** ldotdl right distributve over dlmap2 *)
  Lemma ldotdl_dlmap2_distr_r : forall l dl1 dl2 {r c},
    length l = c -> length dl1 = r -> length dl2 = r -> 
    width dl1 c -> width dl2 c ->
    ldotdl l (dlmap2 fadd dl1 dl2) = 
    lmap2 fadd (ldotdl l dl1) (ldotdl l dl2).
  Proof.
    induction dl1,dl2; simpl; intros; auto. destruct H2,H3. f_equal; simpl.
    - rewrite ldot_lmap2_distr_r with (r:=c); auto.
    - apply IHdl1 with (r:=pred r) (c:=c); subst; auto.
  Qed.
  
  (** ldotdl left with nil *)
  Lemma ldotdl_nil_l : forall dl r,
    length dl = r -> ldotdl [] dl = lzero A0 r.
  Proof.
    induction dl; simpl; intros; auto. subst; auto.
    rewrite ldot_nil_l. rewrite IHdl with (r:=pred r); subst; auto.
  Qed.
  
  (** ldotdl right with nil *)
  Lemma ldotdl_nil_r : forall r l, ldotdl l (dnil r) = lzero A0 r.
  Proof.
    induction r; simpl; intros; auto. rewrite IHr. f_equal.
    rewrite ldot_nil_r; auto.
  Qed.
  
  (** ldotdl left with zero *)
  Lemma ldotdl_zero_l : forall dl r c,
    length dl = r -> width dl c ->
    ldotdl (lzero A0 c) dl = lzero A0 r.
  Proof.
    induction dl; simpl; intros; auto.
    - subst; auto.
    - destruct H0. rewrite IHdl with (r:=pred r); subst; simpl; auto.
      rewrite ldot_zero_l; auto.
  Qed.
  
  (** ldotdl right with zero *)
  Lemma ldotdl_zero_r : forall l r c,
    length l = c ->
    ldotdl l (dlzero A0 r c) = lzero A0 r.
  Proof.
    induction r; simpl; intros; auto. f_equal; try apply IHr; auto.
    apply ldot_zero_r; auto.
  Qed.
  
  (** ldotdl of consr and consc *)
  Lemma ldotdl_consr_consc : forall l2 dl2 l1 x1 r c,
    length l2 = c -> length dl2 = c -> width dl2 r ->
    ldotdl (x1 :: l1) (consc l2 dl2) = 
    ladd fadd (lcmul fmul x1 l2) (ldotdl l1 dl2).
  Proof.
    induction l2, dl2; simpl; intros; auto. destruct H1.
    rewrite <- IHl2 with (r:=r) (c:=pred c); subst; auto.
  Qed.

  (** ldot and ldotdl could swap first two operands.
    l1 . (l2 . dl) = l2 . (l1 . dl^T) *)
  Lemma ldot_ldotdl_swap12 : forall dl l1 l2 r c,
    length l1 = r -> length l2 = c -> length dl = r -> width dl c ->
    ldot l1 (ldotdl l2 dl) = 
    ldot l2 (ldotdl l1 (dltrans dl c)).
  Proof.
    induction dl,l1; simpl; intros; auto.
    - rewrite ldotdl_nil_l with (r:=c); try apply dnil_height.
      rewrite ldot_zero_r; auto.
    - subst. inversion H1.
    - subst. inversion H1.
    - destruct H2. rewrite ldot_cons.
      rewrite IHdl with (r:=pred r) (c:=c); auto;
      [idtac | subst; auto | subst; auto].
      rewrite ldotdl_consr_consc with (r:=pred r) (c:=c); auto;
      [idtac | apply dltrans_height | apply dltrans_width; subst]; auto.
      rewrite ldot_ladd_distr_l with (r:=c); auto.
      + f_equal. apply eq_sym. rewrite ldot_comm; auto.
        rewrite ldot_lcmul_distr_r; auto. f_equal.
        apply ldot_comm; auto.
      + apply lcmul_length; auto.
      + apply ldotdl_length with (c:=pred r); auto;
        [idtac | apply dltrans_height | apply dltrans_width]; subst; auto.
  Qed.

  (** ldotdl with consr at right operend *)
  Lemma ldotdl_consr_r : forall l1 l2 dl2 r c,
    length l1 = r -> length l2 = r -> length dl2 = c -> width dl2 r ->
    ldotdl l1 (l2 :: dl2) = (ldot l1 l2) :: (ldotdl l1 dl2).
  Proof. induction l1,l2,dl2; simpl; intros; auto. Qed.
  
  (** ldotdl right distributive over ladd.
    (l1 + l2) . dl = l1 . dl + l2.dl *)
  Lemma ldotdl_ladd_distr_r : forall l1 l2 dl r c,
    length l1 = r -> length l2 = r -> length dl = c -> width dl r ->
    ldotdl (ladd fadd l1 l2) dl = 
    ladd fadd (ldotdl l1 dl) (ldotdl l2 dl).
  Proof.
    induction dl; simpl; intros; auto. destruct H2.
    rewrite IHdl with (r:=r) (c:=pred c); auto.
    - f_equal. rewrite ldot_ladd_distr_r with (r:=r); auto.
    - subst; auto.
  Qed.
  
  (** ldotdl with lcmul is assocociative.
    cmul a (dot l dl) = dot (cmul a l) dl *)
  Lemma ldotdl_lcmul_assoc : forall dl a l r c,
    length l = r -> length dl = c -> width dl r ->
    lcmul fmul a (ldotdl l dl) = ldotdl (lcmul fmul a l) dl.
  Proof.
    induction dl; simpl; intros; auto. destruct H1.
    rewrite IHdl with (r:=r) (c:=pred c); auto. f_equal.
    rewrite ldot_lcmul_distr_r; auto. subst; auto.
  Qed.
  
  Lemma lcmul_cons : forall a x l,
    lcmul fmul a (x :: l) = (fmul a x) :: (lcmul fmul a l).
  Proof. intros. auto. Qed.
  
  Lemma lcmul_zero_r : forall a n, lcmul fmul a (lzero A0 n) = lzero A0 n.
  Proof.
    intros. unfold lcmul. rewrite map_repeat. unfold lzero. f_equal; auto.
    rewrite fmul_comm, fmul_0_l; auto.
  Qed.
  
  (** l dotdl E = l *)
  Lemma ldotdl_dlunit : forall l {n},
    length l = n -> ldotdl l (dlunit A0 A1 n) = l.
  Proof.
    induction l; simpl; intros; auto.
    - subst. simpl. auto.
    - remember (length l) as m. rewrite <- H. simpl.
      rewrite ldotdl_consr_consc with (r:=m) (c:=m); auto;
      try apply repeat_length; try apply dlunit_height; try apply dlunit_width.
      rewrite IHl; auto. f_equal.
      + rewrite ldot_cons. rewrite ldot_zero_r; auto.
        rewrite fmul_comm, fmul_1_l, fadd_comm, fadd_0_l; auto.
      + rewrite lcmul_zero_r. rewrite ladd_zero_l; auto.
  Qed.
  
End ldotdl.

Arguments ldotdl {A}.

Compute ldotdl 0 Nat.add Nat.mul [1;2;3] [[1;2;3];[4;5;6]].
Compute ldotdl 0 Nat.add Nat.mul [1;2;3] (dnil 5).
Compute ldotdl 0 Nat.add Nat.mul [6;7;8;5;1;2;3] (dnil 5).

(** dlist dot dlist *)
Section dldotdl.

  Variable A : Type.
  Variable A0 A1 : A.
  Variable fcmul : A -> A.
  Variable fcmul_0 : fcmul A0 = A0.
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
  Variable fadd_0_r : forall a, fadd a A0 = a.
  Variable fmul_0_l : forall a, fmul A0 a = A0.
  Variable fmul_0_r : forall a, fmul a A0 = A0.
  Variable fmul_1_l : forall a, fmul A1 a = a.
  Variable fmul_1_r : forall a, fmul a A1 = a.
  
  (* a convenient notation in this section *)
  Notation ldot := (ldot A0 fadd fmul).
  Notation ldotdl := (ldotdl A0 fadd fmul).
  
  Fixpoint dldotdl (dl1 dl2 : list (list A)) : list (list A) :=
    match dl1 with
    | h1 :: t1 => (ldotdl h1 dl2) :: (dldotdl t1 dl2)
    | [] => []
    end.
  
  Lemma dldotdl_height : forall dl1 dl2 r1 r2 c,
    length dl1 = r1 -> length dl2 = r2 -> width dl1 c -> width dl2 c ->
    length (dldotdl dl1 dl2) = r1.
  Proof.
    induction dl1; intros; auto. simpl in *. inversion H1.
    rewrite IHdl1 with (r1:=pred r1) (r2:=r2) (c:=c); auto; subst; auto.
  Qed.
  
  Lemma dldotdl_width : forall dl1 dl2 r1 r2 c,
    length dl1 = r1 -> length dl2 = r2 -> width dl1 c -> width dl2 c ->
    width (dldotdl dl1 dl2) r2.
  Proof.
    induction dl1; intros; auto. simpl in *. destruct H1. split.
    - rewrite ldotdl_length with (r:=r2) (c:=c); auto.
    - apply IHdl1 with (r1:=pred r1) (r2:=r2) (c:=c); auto; subst; auto.
  Qed.
  
  (** dldotdl consr left *)
  Lemma dldotdl_consr_l : forall l1 dl1 dl2,
    dldotdl (l1 :: dl1) dl2 = (ldotdl l1 dl2) :: (dldotdl dl1 dl2). 
  Proof. simpl. auto. Qed.
  
  (** dldotdl consr right *)
  Lemma dldotdl_consr_r : forall dl1 l2 dl2 r c t,
    length dl1 = r -> width dl1 c ->
    length l2 = c ->
    length dl2 = t -> width dl2 c ->
    dldotdl dl1 (l2 :: dl2) = consc (ldotdl l2 dl1) (dldotdl dl1 dl2).
  Proof.
    induction dl1; simpl; intros; auto. destruct H0. f_equal.
    - f_equal. apply ldot_comm; auto.
    - apply IHdl1 with (r:=pred r) (c:=c) (t:=t); subst; auto.
  Qed.
  
  (** dldotdl left distributve over dlmap2 *)
  Lemma dldotdl_dlmap2_distr_l : forall dl1 dl2 dl3 {r c t},
    length dl1 = r -> length dl2 = r -> length dl3 = t -> 
    width dl1 c -> width dl2 c -> width dl3 c -> 
    dldotdl (dlmap2 fadd dl1 dl2) dl3 = 
    dlmap2 fadd (dldotdl dl1 dl3) (dldotdl dl2 dl3).
  Proof.
    induction dl1,dl2; simpl; intros; auto. f_equal;simpl in *;destruct H2,H3.
    - rewrite ldotdl_lmap2_distr_l with (r:=c) (c:=t); auto.
    - apply IHdl1 with (r:=pred r) (c:=c) (t:=t); subst; auto.
  Qed.
  
  (** dldotdl right distributve over dlmap2 *)
  Lemma dldotdl_dlmap2_distr_r : forall dl1 dl2 dl3 {r c t},
    length dl1 = r -> length dl2 = t -> length dl3 = t -> 
    width dl1 c -> width dl2 c -> width dl3 c -> 
    dldotdl dl1 (dlmap2 fadd dl2 dl3) = 
    dlmap2 fadd (dldotdl dl1 dl2) (dldotdl dl1 dl3).
  Proof.
    induction dl1; simpl; intros; auto. destruct H2. f_equal. 
    - apply ldotdl_dlmap2_distr_r with (r:=t) (c:=c); auto.
    - apply IHdl1 with (r:=pred r) (c:=c) (t:=t); subst; auto.
  Qed.
  
  (** dldotdl left with nil *)
  Lemma dldotdl_nil_r : forall dl r c, 
    length dl = r -> width dl c -> dldotdl dl [] = dnil r.
  Proof.
    induction dl; simpl; intros; simpl; auto. subst; auto.
    rewrite <- H. simpl. f_equal. destruct H0.
    rewrite IHdl with (r:=pred r) (c:=c); subst; auto.
  Qed.
  
  (** dldotdl left with zero dlist *)
  Lemma dldotdl_zero_l : forall r dl c t,
    length dl = t -> width dl c ->
    dldotdl (dlzero A0 r c) dl = dlzero A0 r t.
  Proof.
    induction r; simpl; intros; auto. unfold dlzero in *. simpl. 
    f_equal; auto. rewrite ldotdl_zero_l with (r:=t); auto.
  Qed.
  
  (** dldotdl right with zero dlist *)
  Lemma dldotdl_zero_r : forall dl r c t,
    length dl = r -> width dl c ->
    dldotdl dl (dlzero A0 t c) = dlzero A0 r t.
  Proof.
    induction dl; simpl; intros; auto.
    - subst; auto.
    - destruct H0. rewrite IHdl with (r:=pred r); auto.
      + rewrite ldotdl_zero_r; auto. unfold dlzero in *. subst. simpl.
        f_equal.
      + subst; auto.
  Qed.
  
  (** dltrans for dldotdl with right decomposition *)
  Lemma dltrans_dldotdl_right : forall d1 d2 l2 r c t,
    length d1 = r -> width d1 c ->
    length l2 = c ->
    length d2 = t -> width d2 c ->
    dltrans (dldotdl d1 (l2 :: d2)) (S t) =
    (ldotdl l2 d1) :: (dltrans (dldotdl d1 d2) t).
  Proof.
    induction d1,d2; simpl; intros; auto.
    - destruct H0. rewrite IHd1 with (r:=pred r) (c:=c); auto. 
      f_equal. f_equal. apply ldot_comm; auto. subst; auto.
    - destruct H0,H3. rewrite IHd1 with (r:=pred r) (c:=c); auto.
      f_equal. f_equal. apply ldot_comm; auto.
      subst; auto. simpl. split; auto.
  Qed. 
  
  (** dldotdl commutation *)
  Lemma dldotdl_comm : forall d1 d2 r c t,
    length d1 = r -> width d1 c ->
    length d2 = t -> width d2 c ->
    dldotdl d1 d2 = dltrans (dldotdl d2 d1) r.
  Proof.
    induction d1; simpl; intros.
    - rewrite dldotdl_nil_r with (r:=t) (c:=c); auto.
      rewrite <- H. rewrite dltrans_nil. auto.
    - destruct H0. rewrite IHd1 with (r:=pred r) (c:=c) (t:=t); auto.
      + rewrite <- H. 
        rewrite dltrans_dldotdl_right with (r:=t) (c:=c); auto.
      + subst; auto.
  Qed.
  
  (** HARD *)
  Lemma ldotdl_dldotdl_dltrans_assoc : forall d1 d2 l {r c t},
    length l = r ->
    length d1 = r -> width d1 c ->
    length d2 = t -> width d2 c ->
    ldotdl l (dltrans (dldotdl d1 d2) t) =
    ldotdl (ldotdl l (dltrans d1 c)) d2.
  Proof.
    induction d1,d2; intros; auto.
    - subst. auto.
    - simpl. destruct H3. repeat rewrite ldotdl_nil_r. 
      rewrite ldot_zero_l; auto.
      rewrite ldotdl_zero_l with (r:=pred t); subst; auto.
    - simpl dltrans at 2. simpl in H0,H1,H2,H3. destruct H1,H3. destruct l0.
      + rewrite ldotdl_nil_l with (r:=t).
        * rewrite ldotdl_nil_l with (r:=c).
          { rewrite ldotdl_zero_l with (r:=t); simpl; auto. }
          { rewrite consc_height with (r:=c); auto.
            apply dltrans_height; auto. }
        * apply dltrans_height.
          apply dldotdl_width with (r1:=r) (c:=c); simpl; auto.
      + simpl in H. rewrite ldotdl_consr_consc  with (r:=pred r) (c:=c); auto.
        (* (l1 + l2):dl = l1:dl + l2:dl *)
        rewrite ldotdl_ladd_distr_r with (r:=c) (c:=t); auto.
        { (* 1/6 *)
          rewrite <- IHd1 with (r:=pred r) (t:=t); auto.
          - rewrite dldotdl_consr_l.
            (* (l :: dl)^T = consc l (dl^T) *)
            replace (dltrans ((ldotdl a (l :: d2)) :: (dldotdl d1 (l :: d2))) t)
            with 
            (consc (ldotdl a (l::d2)) (dltrans (dldotdl d1 (l::d2)) t)); auto.
            rewrite ldotdl_consr_consc with (r:=pred r) (c:=t); auto.
            + f_equal. rewrite ldotdl_lcmul_assoc with (r:=c) (c:=t); auto.
              subst; simpl; auto.
            + rewrite ldotdl_length with (r:=t) (c:=c); simpl; auto.
            + apply dltrans_height.
              apply dldotdl_width with (r1:=pred r)(c:=c); simpl; subst; auto.
            + apply dltrans_width; auto.
              * rewrite dldotdl_height with (r1:=pred r)(r2:=t)(c:=c); 
                simpl; subst; auto.
              * apply dldotdl_width with (r1:=pred r)(c:=c); simpl; subst; auto.
          - subst; auto.
          - subst; auto.
          - simpl; auto. }
        { (* 2/6 *) apply lcmul_length; auto. }
        { (* 3/6 *) apply ldotdl_length with (c:=pred r); simpl; auto.
          - subst; auto.
          - apply dltrans_height; auto.
          - apply dltrans_width; subst; auto. }
        { (* 4/6 *) simpl; auto. }
        { (* 5/6 *) apply dltrans_height; auto. }
        { (* 6/6 *) apply dltrans_width; subst; auto. }
  Qed.
  
  (** dldotdl association *)
  Lemma dldotdl_assoc : forall d1 d2 d3 r c t s,
    length d1 = r -> width d1 c ->
    length d2 = c -> width d2 t ->
    length d3 = s -> width d3 t ->
    dldotdl (dldotdl d1 (dltrans d2 t)) d3 =
    dldotdl d1 (dltrans (dldotdl d2 d3) s).
  Proof.
    induction d1; simpl; intros; auto. destruct H0. f_equal; auto.
    rewrite ldotdl_dldotdl_dltrans_assoc with (r:=c) (c:=t); auto.
    apply IHd1 with (r:=pred r) (c:=c); subst; auto.
  Qed.
  
  (** dldotdl left with dlunit *)
  Lemma dldotdl_dlunit_l : forall (dl : list (list A)) {r c},
    length dl = r -> width dl c -> 
    dldotdl (dlunit A0 A1 c) dl = dltrans dl c.
  Proof.
    induction dl; simpl; intros; auto.
    - rewrite dldotdl_nil_r with (r:=c) (c:=c); auto.
      apply dlunit_height. apply dlunit_width.
    - destruct H0. 
      rewrite dldotdl_consr_r with (r:=c) (c:=c) (t:=pred r); auto;
      try apply dlunit_height; try apply dlunit_width.
      + rewrite IHdl with (r:=pred r); subst; auto.
        f_equal. rewrite ldotdl_dlunit; auto.
      + subst; auto.
  Qed.
  
  (** dldotdl right with dlunit *)
  Lemma dldotdl_dlunit_r : forall (dl : list (list A)) {r c},
    length dl = r -> width dl c -> 
    dldotdl dl (dlunit A0 A1 c) = dl.
  Proof.
    induction dl; simpl; intros; auto. destruct H0.
    rewrite IHdl with (r:=pred r); auto.
    - rewrite ldotdl_dlunit; auto.
    - subst; auto.
  Qed.
  
End dldotdl.

Arguments dldotdl {A}.

Compute dldotdl 0 Nat.add Nat.mul [[];[]] [[];[]].
Compute dldotdl 0 Nat.add Nat.mul [[1;2;3];[4;5;6]] [[7;8;9];[10;11;12]].
Compute dldotdl 0 Nat.add Nat.mul [[7;8;9];[10;11;12]] [[1;2;3];[4;5;6]].


(** ** OTHER properties *)
Section other_props.

  Variable A : Type.

  Lemma list_app_dlist : forall (l : list A) (dl : list (list A)), 
    [l] ++ dl = l :: dl.
  Proof. destruct l; auto. Qed.
  
End other_props.
