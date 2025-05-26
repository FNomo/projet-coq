Require Export Bool List Equalities Orders Setoid Morphisms.
Import ListNotations.

(** * Languages are sets of words over some type of letters *)

Module Lang (Letter : Typ).

Definition word := list Letter.t.
Definition t := word -> Prop.

Declare Scope lang_scope.
Bind Scope lang_scope with t.
Delimit Scope lang_scope with lang.
Local Open Scope lang_scope. 

Implicit Type a : Letter.t.
Implicit Type w x y z : word.
Implicit Type L : t.

Definition eq L L' := forall x, L x <-> L' x.

Definition void : t := fun _ => False.
Definition epsilon : t := fun w => w = [].
Definition singleton a : t := fun w => w = [a].

Definition cat L L' : t :=
  fun x => exists y z, x = y++z /\ L y /\ L' z.

Definition union L L' : t := fun w => L w \/ L' w.

Definition inter L L' : t := fun w => L w /\ L' w.

Fixpoint power L n : t :=
  match n with
  | 0 => epsilon
  | S n' => cat L (power L n')
  end.

(** Kleene's star *)

Definition star L : t := fun w => exists n, power L n w.

(** language complement *)

Definition comp L : t := fun w => ~(L w).

(** Languages : notations **)

Module Notations.
Infix "==" := Lang.eq (at level 70).
Notation "∅" := void : lang_scope. (* \emptyset *)
Notation "'ε'" := epsilon : lang_scope. (* \epsilon *)
Coercion singleton : Letter.t >-> Lang.t.
Infix "·" := cat (at level 35) : lang_scope. (* \cdot *)
Infix "∪" := union (at level 50) : lang_scope. (* \cup *)
Infix "∩" := inter (at level 40) : lang_scope. (* \cap *)
Infix "^" := power : lang_scope.
Notation "L ★" := (star L) (at level 30) : lang_scope. (* \bigstar *)
Notation "¬ L" := (comp L) (at level 65): lang_scope. (* \neg *)
End Notations.
Import Notations.

(** Technical stuff to be able to rewrite with respect to "==" *)

Global Instance : Equivalence eq.
Proof. firstorder. Qed.

Global Instance cat_eq : Proper (eq ==> eq ==> eq) cat.
Proof. firstorder. Qed.
Global Instance inter_eq : Proper (eq ==> eq ==> eq) inter.
Proof. firstorder. Qed.
Global Instance union_eq : Proper (eq ==> eq ==> eq) union.
Proof. firstorder. Qed.
Global Instance comp_eq : Proper (eq ==> eq) comp.
Proof. firstorder. Qed.
Global Instance power_eq : Proper (eq ==> Logic.eq ==> eq) power.
Proof.
 intros x x' Hx n n' <-. induction n; simpl; now rewrite ?IHn, ?Hx.
Qed.

Global Instance cat_eq' : Proper (eq ==> eq ==> Logic.eq ==> iff) cat.
Proof. intros x x' Hx y y' Hy w w' <-. now apply cat_eq. Qed.
Global Instance inter_eq' : Proper (eq ==> eq ==> Logic.eq ==> iff) inter.
Proof. intros x x' Hx y y' Hy w w' <-. now apply inter_eq. Qed.
Global Instance union_eq' : Proper (eq ==> eq ==> Logic.eq ==> iff) union.
Proof. intros x x' Hx y y' Hy w w' <-. now apply union_eq. Qed.
Global Instance comp_eq' : Proper (eq ==> Logic.eq ==> iff) comp.
Proof. intros x x' Hy w w' <-. now apply comp_eq. Qed.
Global Instance power_eq' : Proper (eq ==> Logic.eq ==> Logic.eq ==> iff) power.
Proof. intros x x' Hx n n' <- w w' <-. now apply power_eq. Qed.

Global Instance star_eq : Proper (eq ==> eq) star.
Proof.
 intros x x' Hx w. unfold star. now setoid_rewrite <- Hx.
Qed.

Global Instance star_eq' : Proper (eq ==> Logic.eq ==> iff) star.
Proof. intros x x' Hx w w' <-. now apply star_eq. Qed.

(** Languages : misc properties *)

Lemma cat_void_l L : ∅ · L == ∅.
Proof.
  split. 
  - intros; destruct H; intros; destruct H; intros; apply H.
  - intros; destruct H.
Qed.

Lemma cat_void_r L :  L · ∅ == ∅.
Proof.
  split.
  - intros; destruct H; intros; destruct H; intros; destruct H; intros; destruct H0;
    intros; assumption.
  - intros; destruct H.
Qed.

Lemma cat_eps_l L : ε · L == L.
Proof.
  split.
  - intros; destruct H; intros; destruct H; destruct H; destruct H0;
    rewrite H; rewrite H0; assumption.
  - exists []; exists x; split.
    + symmetry; apply app_nil_l.
    + split.
      * reflexivity.
      * assumption.
Qed.


Lemma cat_eps_r L : L · ε == L.
Proof. 
    split.
    - intro; destruct H; destruct H; destruct H; destruct H0;
      rewrite H1 in H; rewrite app_nil_r in H; rewrite H; assumption.
    - exists x; exists []; split.
      + symmetry; apply app_nil_r.
      + split.
        * assumption.
        * reflexivity.
Qed.

Lemma cat_assoc L1 L2 L3 : (L1 · L2) · L3 == L1 · (L2 · L3).
Proof.
  split.
    - intro; destruct H; destruct H; destruct H;
      destruct H0; destruct H0; destruct H0; destruct H0; destruct H2;
      exists x2; exists (x3 ++ x1); split.
      + rewrite H; rewrite H0; symmetry; apply app_assoc.
      + split.
        * assumption.
        * exists x3; exists x1; split.
          ** reflexivity.
          ** split.
            *** assumption.
            *** assumption.
    - intro. unfold cat in *. destruct H. destruct H; destruct H;
      destruct H0; destruct H1; destruct H1; destruct H1; destruct H2;
      exists (x0 ++ x2); exists x3; split.
      + rewrite H; rewrite H1; apply app_assoc.
      + split.
        * exists x0; exists x2; split.
          ** reflexivity.
          ** split.
            *** assumption.
            *** assumption.
        * assumption.
Qed.


Lemma star_eqn L : L★ == ε ∪ L · L ★.
Proof.
  split.
  - intro ; destruct H; induction x0.
    + left ;assumption.
    + destruct H; destruct H; destruct  H; destruct H0; right.
      exists x1 ;exists x2 ;split.
      * assumption.
      * split.
        ** assumption.
        ** exists x0; assumption.
  - intro; destruct H.
    + exists 0; assumption.
    + revert H; induction x.
      * intros; exists 0; reflexivity.
      * intros; destruct H; destruct H; destruct H; destruct H0; destruct H1.
        exists (S x2); exists x0; exists x1; split.
        ** assumption.
        ** split.
          *** assumption.
          *** assumption.
Qed.

Lemma star_void : ∅ ★ == ε.
Proof.
  split.
  - intro; destruct H; induction x0.
    + assumption.
    + destruct H; destruct H; destruct H; destruct H0; exfalso; assumption.
  - intro; exists 0; assumption.
Qed.

Lemma power_eps n : ε ^ n == ε.
Proof.
  split.
  - intro; induction n as [| n' IHn'].
    + assumption.
    + destruct H; destruct H; destruct H; destruct H0; apply IHn';
      rewrite H0 in H; rewrite H; simpl; assumption.
  - intro; induction n as [| n' IHn'].
    + assumption.
    + unfold power; unfold cat; exists []; exists x; split.
      * simpl; reflexivity.
      * split.
        ** reflexivity.
        ** assumption.
Qed.

Lemma star_eps : ε ★ == ε.
Proof.
  split.
  - intro; destruct H; induction x0.
    + assumption.
    + destruct H; destruct H; destruct H; destruct H0; apply IHx0;
      rewrite H0 in H; rewrite H; simpl; assumption.
  - intro; exists 0; assumption.
Qed.

Lemma plus_n_O : forall n:nat, n +0 = n.
Proof.
  intro; induction n.
  - reflexivity.
  - simpl; rewrite IHn; reflexivity.
Qed.

Lemma add_0_personal n: n + 0 = n.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma add_0_l_personal n: 0 + n = n.
Proof.
  auto.
Qed.

Lemma add_succ_r_personnal n m: n + S(m) = S (n + m).
Proof.
  auto.
Qed.

Lemma add_succ_l_personnal n m: S(n) + m = S (n + m).
Proof.
  auto.
Qed.

Lemma power_app n m y z L :
 (L^n) y -> (L^m) z -> (L^(n+m)) (y++z).
Proof.
  induction n.
  - intros. simpl in *. rewrite H. simpl. assumption.
  - intros. simpl in *. destruct H. destruct H.
    destruct H. destruct H1. induction m.
    + unfold cat.  exists x. exists x0. split.
      * rewrite H0.  rewrite app_nil_r. assumption.
      * split.
        ** assumption.
        ** rewrite add_0_personal. assumption.
    + destruct H0. destruct H0. destruct H0. destruct H3.
      unfold cat.
    
      
Admitted.

Lemma cat_star L : (L★)·(L★) == L★.
Proof.
  split.
  - intro; destruct H; destruct H; destruct H;
    destruct H0; rewrite H; destruct H0; destruct H1;
    exists (x2 + x3); apply power_app. all: assumption.
  - intro; exists x; exists []; split.
    + rewrite app_nil_r; reflexivity.
    + split.
      * assumption.
      * exists 0; reflexivity.
Qed.


Lemma star_star L : (L★)★ == L★.
Proof.
  split.
  - intro; destruct H as (n, H); revert x H;  induction n.
    + simpl in *; exists 0; assumption.
    + simpl in *; intros; destruct H. destruct H;
      destruct H; destruct H0; apply IHn in H1;
      simpl in *; rewrite H; destruct H0; destruct H1;
      exists (x2 + x3); apply power_app. all: assumption.
  - intro; exists 1; exists x; exists []; split.
    + rewrite app_nil_r; reflexivity.
    + split.
      * assumption.
      * reflexivity.
Qed.

(** ** Derivative of a language : definition **)

Definition derivative L w : t := fun x => L (w++x).

Global Instance derivative_eq : Proper (eq ==> Logic.eq ==> eq) derivative.
Proof. intros L L' HL w w' <-. unfold derivative. intro. apply HL. Qed.

(** ** Derivative of a language : properties **)

Lemma derivative_app L w w' :
  derivative L (w++w') == derivative (derivative L w) w'.
Proof.
  split.
  - intro; unfold derivative in *; rewrite app_assoc; assumption.
  - intro; unfold derivative in *; rewrite app_assoc in H; assumption.
Qed.

Lemma derivative_cat_null L L' a : L [] ->
  derivative (L · L') [a] == (derivative L [a] · L') ∪ derivative L' [a].
Proof.
  
  intros; split.
  
Admitted.

Lemma derivative_cat_nonnull L L' a : ~L [] ->
  derivative (L · L') [a] == derivative L [a] · L'.
Proof.
  intro. split.
  - induction x.
    + intro. simpl. unfold cat in *. unfold derivative in *.
  split.
  - intro. unfold derivative in *. unfold cat in *. induction x.
    + unfold derivative in *. destruct H0. destruct H0. destruct H0. destruct H1.

Admitted.

Lemma derivative_star L a :
  derivative (L★) [a] == (derivative L [a]) · (L★).
Proof.
  split.
  - intro. unfold cat. unfold derivative in *. unfold star in H. destruct H. induction x0.
    + exists x. exists []. split.
      * symmetry. apply app_nil_r.
      * admit.
    + destruct H. apply IHx0. admit.
Admitted.

End Lang.
