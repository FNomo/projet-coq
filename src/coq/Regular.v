Require Export Languages.
Import ListNotations.

(** * Regular expressions (regexps) on finite ordered letters *)

Module Type FiniteOrderedType.
 (* Ask for a type [t], an order [lt], a boolean test [eqb], etc *)
 Include UsualOrderedType' <+ HasEqBool.
 (* Moreover, [t] is finite. *)
 Parameter enumeration : list t.
 Parameter enumeration_spec : forall x:t, In x enumeration.
End FiniteOrderedType.

Module Regexps (Letter : FiniteOrderedType).

 (* For LetterB.eqb_spec, LetterB.eqb_neq, ... *)
 Module LetterB := BoolEqualityFacts(Letter).

 Definition word := list Letter.t.

 Implicit Types a : Letter.t.
 Implicit Types w : word.

 (** ** Regexps : definition *)

 Inductive re :=
  | Void : re
  | Epsilon : re
  | Letter : Letter.t -> re
  | Cat : re -> re -> re
  | Star : re -> re
  | Or : re -> re -> re
  | And : re -> re -> re
  | Not : re ->  re.

 (** ** Language of a regexp **)

Module Lang := Languages.Lang(Letter).
Import Lang.Notations.
Open Scope lang_scope.

Fixpoint lang r : Lang.t :=
match r with
| Void => ∅
| Epsilon => ε
| Letter a => a
| Cat r s => lang r · lang s
| Star r => (lang r)★
| Or r s => lang r ∪ lang s
| And r s => lang r ∩ lang s
| Not r =>  ¬lang r
end.

 (** ** Nullable regexp : definition **)

 Fixpoint is_nullable (r : re) : bool :=
  match r with
  | Epsilon | Star _ => true
  | Void | Letter _ => false
  | Cat r s | And r s => is_nullable r && is_nullable s
  | Or r s => is_nullable r || is_nullable s
  | Not r => negb (is_nullable r)
  end.

Theorem app_eq_nil_personnal (l l':word) :  l ++ l' = [] <-> l = [] /\ l' = [].
Proof.
  split.
  - intro. apply app_eq_nil. assumption.
  - intro. destruct H. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma nullable_ok r : is_nullable r = true <-> lang r [].
Proof.
  induction r.
  - simpl. split.
    + intro; discriminate.
    + intro; exfalso; assumption.
  - simpl. split.
    + intro. reflexivity.
    + intro. reflexivity.
  - simpl. split.
    + intro. discriminate.
    + intro. discriminate.
  - simpl in *. split.
    + intros. rewrite andb_true_iff in H.
      destruct H. repeat exists []. split.
      * reflexivity.
      * split.
        ** destruct IHr1. apply H1. assumption.
        ** destruct IHr2. apply H1. assumption.
    + intros. rewrite andb_true_iff. destruct H. destruct H. destruct H.
      destruct H0. symmetry in H. rewrite app_eq_nil_personnal in H. destruct H.
      split.
      * destruct IHr1. apply H4; rewrite H in H0. assumption.
      * destruct IHr2. apply H4; rewrite H2 in H1. assumption.
  - simpl. split.
    + intro. exists 0. simpl. reflexivity.
    + intro. reflexivity.
  - simpl in *. split.
    + intro. rewrite orb_true_iff in H. destruct H.
      * left. destruct IHr1. apply H0. assumption.
      * right. destruct IHr2. apply H0. assumption.
    + intro. rewrite orb_true_iff. destruct H.
      * left. destruct IHr1. apply H1. assumption.
      * right. destruct IHr2. apply H1. assumption.
  - simpl. split.
    + intro. rewrite andb_true_iff in H. destruct H. split.
      * destruct IHr1. apply H1. assumption.
      * destruct IHr2. apply H1. assumption.
    + intro. destruct H. rewrite andb_true_iff. split.
      * destruct IHr1. apply H2. assumption.
      * destruct IHr2. apply H2. assumption.
  - simpl. rewrite negb_true_iff. destruct IHr. split.
    + intros. intro. revert H1. apply eq_true_false_abs.
      apply H0. assumption.
    +  
Admitted.

Lemma nullable_spec r : reflect (lang r []) (is_nullable r).
Proof.
  induction r.
  - simpl; unfold Lang.void; apply iff_reflect; split.
    + intro; exfalso; assumption.
    + intro; discriminate.
  - simpl; unfold Lang.epsilon; apply iff_reflect; split.
    + intro; reflexivity.
    + intro; reflexivity.
  - simpl;  apply iff_reflect; split.
    + intro; discriminate.
    + intro; discriminate.
  - simpl; apply iff_reflect; split.
    + intro; destruct H; destruct H; destruct H; destruct H0.
      symmetry in H; rewrite app_eq_nil_personnal in H; destruct H.
      rewrite andb_true_iff; split.
      * apply reflect_iff in IHr1; destruct IHr1; apply H3; rewrite H in H0; assumption.
      * apply reflect_iff in IHr2; destruct IHr2; apply H3; rewrite H2 in H1; assumption.
    + intro; unfold Lang.cat; rewrite andb_true_iff in H; destruct H; exists []; exists []; split.
      * reflexivity.
      * split.
        ** apply reflect_iff in IHr1; destruct IHr1; apply H2; assumption.
        ** apply reflect_iff in IHr2; destruct IHr2; apply H2; assumption.
  - simpl; unfold Lang.star; apply iff_reflect; split.
    + intro; reflexivity.
    + intro; exists 0; reflexivity.
  - simpl; apply iff_reflect; split.
    + intro; apply orb_true_iff; unfold Lang.union in H; destruct IHr1.
      * left; reflexivity.
      * destruct IHr2.
        ** right; reflexivity.
        ** exfalso; destruct H.
          *** apply n; assumption.
          *** apply n0; assumption.
    + intro; rewrite orb_true_iff in H; destruct H.
      * unfold Lang.union; destruct IHr1.
        ** left; assumption.
        ** discriminate.
      * destruct IHr2.
        ** unfold Lang.union; right; assumption.
        ** discriminate.
  - simpl; apply iff_reflect; split.
    + intro; rewrite andb_true_iff; split.
      * destruct IHr1.
        ** reflexivity.
        ** destruct H; destruct IHr2.
          *** exfalso; apply n; assumption.
          *** exfalso; apply n; assumption.
      * destruct IHr2.
        ** reflexivity.
        ** destruct H; destruct IHr1.
          *** exfalso; apply n; assumption.
          *** exfalso; apply n; assumption.
    + intro; rewrite andb_true_iff in H; destruct H.
      unfold Lang.inter; split.
      * destruct IHr1.
        ** assumption.
        ** discriminate.
      * destruct IHr2.
        ** assumption.
        ** discriminate.
  - simpl in *; apply iff_reflect; split.
    + intro; unfold Lang.comp in *; destruct IHr.
      * exfalso; apply H; assumption.
      * apply negb_true_iff; reflexivity.
    + intro; unfold Lang.comp in *; destruct IHr.
      * apply negb_true_iff in H; discriminate.
      * intro; apply n; assumption.
Qed.


 (** ** Derivative of a regular expression **)
 
 Declare Scope re_scope.
 Bind Scope re_scope with re.
 Delimit Scope re_scope with re.
 Open Scope re_scope.

 (** deriv1 : derivative by a letter *)

 Fixpoint deriv1 r a :=
  match r with
  | Void => Void
  | Epsilon => Void
  | Letter a' => if Letter.eqb a a' then Epsilon else Void
  | Cat r s =>
    Or (Cat (deriv1 r a) s) (if is_nullable r then deriv1 s a else Void)
  | Star r => Cat (deriv1 r a) (Star r)
  | Or r s => Or (deriv1 r a) (deriv1 s a)
  | And r s => And (deriv1 r a) (deriv1 s a)
  | Not r => Not (deriv1 r a)
  end.

 Infix "/" := deriv1 : re_scope.

 (** deriv : derivative by a word, ie many letters *)

 Fixpoint deriv r w :=
  match w with
  | [] => r
  | a::w' => deriv (r/a) w'
  end.

 Infix "//" := deriv (at level 40) : re_scope.

Lemma deriv1_ok r a : lang (r/a) == Lang.derivative (lang r) [a].
Proof.
  induction r.
  - split.
    + simpl. intro. assumption.
    + intro. simpl in *. assumption.
  - split.
    + simpl. intro. exfalso. assumption.
    + simpl. intro. unfold Lang.derivative in *. simpl in *.

  (*split.
  - intro. unfold Lang.derivative. simpl in *. induction r.
    + assumption.
    + exfalso. assumption.
    + simpl in *. revert H. case LetterB.eqb_spec.
      * intro. simpl in *. intro. simpl.
    + simpl in *. destruct H.
      *)
Admitted.

Lemma deriv_ok r w : lang (r//w) == Lang.derivative (lang r) w.
Proof.
split.
- intro. induction r.
  + induction w.
    * assumption.
    * apply IHw. assumption.
  + induction w.
    * unfold Lang.derivative in *. simpl in *. assumption.
    * simpl in *. unfold Lang.derivative. simpl in *.
Admitted.

Lemma deriv1_ok' r a w : lang (r/a) w <-> lang r (a::w).
Proof.
  split.
  - intros. induction r.
    + simpl in *. assumption.
    + simpl in *. exfalso. assumption.
    + simpl in *. admit.
    + simpl in *. admit.
    + simpl in *.
Admitted.

Lemma deriv_ok' r w w' : lang (r//w) w' <-> lang r (w++w').
Proof.
  split.
  - induction r.
    + simpl. induction w.
Admitted.

(** ** Matching : is a word in the language of a regexp ? *)

 Definition matching r w := is_nullable (r//w).

 Lemma matching_ok r w : matching r w = true <-> lang r w.
 Proof.
 Admitted.

 (** We can now prove that being in [lang r] is decidable *)

 Lemma lang_dec r w : { lang r w } + { ~lang r w }.
 Proof.
 destruct (matching r w) eqn:E; [left|right];
  rewrite <- matching_ok; auto.
 intros E'. now rewrite E' in E.
 Qed.

 (** Derivative of a regexp : properties **)

Lemma deriv_void w : Void // w = Void.
Proof.
Admitted.

Lemma deriv_epsilon w : In (Epsilon // w) [Void; Epsilon].
Proof.
 induction w.
  - simpl. right. left. reflexivity.
  - simpl. destruct IHw.
    + simpl in *. left. rewrite H. simpl.
Admitted.

Lemma deriv_letter a w :
In (Letter a // w) [Void; Epsilon; Letter a].
Proof.
Admitted.

Lemma deriv_or r s w :
(Or r s) // w = Or (r//w) (s//w).
Proof.
Admitted.

Lemma deriv_and r s w :
(And r s) // w = And (r // w) (s // w).
Proof.
Admitted.

Lemma deriv_not r w :
(Not r) // w = Not (r // w).
Proof.
Admitted.

Lemma deriv_app r w w' :
r // (w++w') = r // w // w'.
Proof.
Admitted.

 (** ** Equivalence of regexps *)

 Definition equiv r s := lang r == lang s.

 Infix "===" := equiv (at level 70).

 (** A few technical declarations for being able to rewrite with === *)

 Global Instance : Equivalence equiv.
 Proof. firstorder. Qed.
 Global Instance : Proper (equiv ==> equiv ==> equiv) Or.
 Proof. firstorder. Qed.
 Global Instance : Proper (equiv ==> equiv ==> equiv) And.
 Proof. firstorder. Qed.
 Global Instance : Proper (equiv ==> equiv ==> equiv) Cat.
 Proof. firstorder. Qed.
 Global Instance : Proper (equiv ==> equiv) Not.
 Proof. firstorder. Qed.
 Global Instance : Proper (equiv ==> equiv) Star.
 Proof. intros r r' E. unfold "===" in *. simpl. now rewrite E. Qed.
 Global Instance : Proper (equiv ==> eq) is_nullable.
 Proof. intros r r' E. apply eq_true_iff_eq. rewrite !nullable_ok; auto. Qed.
 Global Instance : Proper (equiv ==> eq ==> equiv) deriv1.
 Proof. intros r r' E a a' <- w. rewrite !deriv1_ok'; auto. Qed.
 Global Instance : Proper (equiv ==> eq ==> equiv) deriv.
 Proof. intros r r' E w w' <- w2. rewrite !deriv_ok'; auto. Qed.
 Global Instance : Proper (equiv ==> eq ==> eq) matching.
 Proof. intros r r' E w w' <-. unfold matching. now rewrite E. Qed.

Lemma or_comm r s : Or r s === Or s r.
Proof.
  split.
  - intros; destruct H.
    + right; assumption.
    + left; assumption.
  - intros; destruct H.
    + right; assumption.
    + left; assumption.
Qed.

Lemma or_assoc r s t : Or (Or r s) t === Or r (Or s t).
Proof.
  split.
  - intro. destruct H.
    + destruct H.
      * left; assumption.
      * right; left; assumption.
    + repeat right; assumption.
  - intro. destruct H.
    + repeat left; assumption.
    + destruct H.
      * left; right; assumption.
      * right; assumption.
Qed.

Lemma or_idem r : Or r r === r.
Proof.
  split.
  - intro; destruct H. all: assumption.
  - intro; left; assumption.
Qed.

Lemma or_void_l r : Or Void r === r.
Proof.
  split.
  - intro; destruct H.
    + exfalso; assumption.
    + assumption.
  - intros; right; assumption.
Qed.

Lemma or_void_r r : Or r Void === r.
Proof.
  split.
  - intro; destruct H.
    + assumption.
    + exfalso; assumption.
  - intro; left; assumption.
Qed.

Lemma and_comm r s : And r s === And s r.
Proof.
  split.
  - intro; destruct H; split. all: assumption.
  - intro; destruct H; split. all: assumption.
Qed.

Lemma and_assoc r s t : And (And r s) t === And r (And s t).
Proof.
  split.
  - intro; destruct H; destruct H; split.
    + assumption.
    + split. all: assumption.
  - intros; destruct H; destruct H0; split.
    + split. all: assumption.
    + assumption.
Qed.

Lemma and_idem r : And r r === r.
Proof.
  split.
  - intro; destruct H; assumption.
  - intros; split. all: assumption.
Qed.

Lemma cat_void_l r : Cat Void r === Void.
Proof.
  split.
  - intro; destruct H; destruct H; destruct H; destruct H0; assumption.
  - intros; exfalso; assumption.
Qed.

Lemma cat_void_r r : Cat r Void === Void.
Proof.
  split.
  - intros; repeat destruct H. destruct H0. assumption.
  - intros; exfalso; assumption.
Qed.

Lemma cat_eps_l r : Cat Epsilon r === r.
Proof.
  split.
  - intros; destruct H; destruct H; destruct H; destruct H0; rewrite H0 in H;
    rewrite H; simpl ; assumption.
  - intros; simpl; unfold Lang.cat; exists []; exists x; split.
    + simpl; reflexivity.
    + split.
      * reflexivity.
      * assumption.
Qed.

Lemma cat_eps_r r : Cat r Epsilon === r.
Proof.
  split.
  - intros; destruct H; destruct H; destruct H; destruct H0;
    rewrite H1 in H; rewrite H; rewrite app_nil_r; assumption.
  - intros; exists x; exists []; split.
    + rewrite app_nil_r; reflexivity.
    + split.
      * assumption.
      * reflexivity.
Qed.

Lemma cat_assoc r s t : Cat (Cat r s ) t === Cat r (Cat s t).
Proof.
  split.
  - intro; destruct H; destruct H; destruct H; destruct H0;
    destruct H0; destruct H0; destruct H0; destruct H2;
    exists x2; exists (x3 ++ x1); split.
    + rewrite app_assoc; rewrite H0 in  H; assumption.
    + split.
      * assumption.
      * exists x3; exists x1; split.
        ** reflexivity.
        ** split. all: assumption.
  - intro; destruct H; destruct H; destruct H; destruct H0;
    destruct H1; destruct H1; destruct H1; destruct H2. simpl; unfold Lang.cat;
    exists (x0 ++ x2); exists x3; split.
    + rewrite H1 in H; rewrite app_assoc in H; assumption.
    + split.
      * exists x0; exists x2; split.
       ** reflexivity.
       ** split. all: assumption.
      * assumption.
Qed.

Lemma star_is_or r : Star r === Or Epsilon (Cat r (Star r)).
Proof.
  split.
  - intros; destruct H.
    unfold Lang.union; induction x0.
    + left; assumption.
    + destruct H; destruct H; destruct H; destruct H0;
      right; exists x1; exists x2; split.
      * assumption.
      * split.
        ** assumption.
        ** exists x0; assumption.
  - intros; destruct H.
    + exists 0; assumption.
    + destruct H; destruct H; destruct H; destruct H0; destruct H1; exists (S x2);
      exists x0; exists x1; split.
      * assumption.
      * split. all: assumption.
Qed.

Lemma star_void : Star Void === Epsilon.
Proof.
  split.
  - intro; destruct H; induction x0.
    +  assumption.
    + destruct H; destruct H;  destruct H; destruct H0; exfalso; assumption.
  - intro; exists 0; assumption.
Qed.

Lemma star_epsilon : Star Epsilon === Epsilon.
Proof.
  simpl in *. split.
  - intro; destruct H; induction x0.
    + assumption.
    + destruct H; destruct H; destruct H; destruct H0;
      apply IHx0; rewrite H0 in H; rewrite H; simpl; assumption.
  - exists 0; assumption.
Qed.

Lemma star_star r : Star (Star r) === Star r.
Proof.
  split.
  - intro. destruct H. induction x0.
    + simpl in *. exists 0. assumption.
      
Admitted.

Lemma cat_star r : Cat (Star r) (Star r) === Star r.
Proof.
  split.
  - intro. destruct H. destruct H. destruct H. destruct H0. destruct H0. destruct H1.
    exists 1. simpl. unfold Lang.cat. induction x.
Admitted.

End Regexps.
