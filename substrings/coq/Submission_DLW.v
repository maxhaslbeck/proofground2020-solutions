Require Import Defs Arith Lia Bool.

Check subseq.

Infix "<ss" := subseq (at level 70).

Fact ss_nil ys : [] <ss ys.
Proof.
  induction ys; constructor; auto.
Qed.

Fact ss_refl xs : xs <ss xs.
Proof. induction xs; constructor; auto. Qed.

Fact ss_nil_inv xs : xs <ss [] -> xs = nil.
Proof.
  inversion 1; auto.
Qed.

Fact ss_cons_inv_l x xs ys : 
   x::xs <ss ys -> exists y ys', ys = y::ys' /\ (   x = y /\ xs <ss ys'
                                                 \/  x::xs <ss ys').
Proof.
  inversion 1; subst.
  + exists x, ys0; auto.
  + exists x0, ys0; auto.
Qed. 

Fact ss_cons_inv_r y xs ys : 
   xs <ss y::ys -> xs <ss ys \/ exists xs', xs = y::xs' /\ xs' <ss ys.
         
Proof.
  inversion 1; subst; auto.
  right; exists xs0; auto.
Qed. 

Fact ss_trans xs ys zs : xs <ss ys -> ys <ss zs -> xs <ss zs.
Proof.
  intros H1 H2; revert H2 xs H1.
  induction 1 as 
    [ | ys zs y H IH | ys zs y H IH ]; auto; intros x Hx.
  + apply ss_cons_inv_r in Hx.
    destruct Hx as [ Hx | (xs' & -> & Hx) ].
    * constructor 3; auto.
    * constructor 2; auto.
  + constructor 3; auto.
Qed. 

Fact ss_app_l l xs ys : xs <ss ys -> l++xs <ss l++ys.
Proof.
  intros H; induction l; auto; constructor; auto.
Qed.

Fact ss_cons_inv x y xs ys : 
   x::xs <ss y::ys -> (x = y /\ xs <ss ys)
                   \/ ( x::xs <ss ys).
Proof.
  inversion 1; subst; auto.
Qed.

Hint Resolve ss_nil ss_refl : core.

Fact aux_spec xs ys : aux xs ys = true <-> xs <ss ys.
Proof.
  revert xs; induction ys as [ | y ys IHys ]; intros [ | x xs ]; simpl; split; auto; try discriminate.
  + intros H; now apply ss_nil_inv in H.
  + destruct (eq_nat_dec x y) as [ H | H ].
    * intros G; subst; constructor 2; apply IHys; auto.
    * rewrite IHys; constructor 3; auto.
  + intros G.
    apply  ss_cons_inv in G.
    destruct G as [ (-> & G) | G ].
    * destruct (eq_nat_dec y y) as [ H | [] ]; auto.
      apply IHys; auto.
    * destruct (eq_nat_dec x y) as [ H | H ]; auto.
      - apply IHys, ss_trans with (2 := G); constructor; auto.
      - apply IHys; auto.
Qed.

Infix "<pss" := proper_subseq (at level 70).

Fact aux2_spec xs acc ys : aux2 ys acc xs = true <-> forall l x r, xs = l++x::r -> acc++l++r <ss ys.
Proof.
  revert acc; induction xs as [ | x xs IHxs ]; intros acc; simpl; split; auto.
  + now intros _ [] x r.
  + rewrite andb_true_iff, aux_spec, IHxs.
    intros (H1 & H2)  [ | z l ] y r E.
    * inversion E; subst y r; auto.
    * inversion E; subst z xs.
      specialize (H2 l y r eq_refl).
      now rewrite app_ass in H2.
  + intros H; rewrite andb_true_iff, aux_spec, IHxs; split.
    * apply (H nil x); auto.
    * intros l y r E.
      rewrite app_ass; simpl.
      apply (H (x::l) y); subst; auto.
Qed.

Fact ss_length xs ys : xs <ss ys -> length xs <= length ys.
Proof.
  induction 1; simpl; lia.
Qed.

Fact proper_subseq_eq xs ys : xs <pss ys <-> exists l y r, xs <ss l++r /\ ys = l++y::r.
Proof.
  revert xs; induction ys as [ | y ys IH ]; intros xs; split.
  + intros (H1 & H2).
    apply ss_nil_inv in H2; now subst.
  + now intros ([] & y & r & H1 & H2).
  + intros (H1 & H2).
    apply ss_cons_inv_r in H2.
    destruct H2 as [ H2 | (xs' & -> & H2) ].
    * exists nil, y, ys; auto.
    * assert (xs' <> ys) as G.
      { contradict H1; subst; auto. }
      destruct (proj1 (IH _) (conj G H2)) as (l & x & r & G1 & G2); subst.
      exists (y::l), x, r; split; auto.
      constructor 2; auto.
  + intros ([ | z l] & x & r & H1 & H2).
    * inversion H2; subst x r.
      split.
      - intros E.
        apply ss_length in H1.
        revert H1; subst xs; simpl; lia.
      - constructor 3; auto.
    * inversion H2; subst z ys; split.
      - intros ->; apply ss_length in H1.
        revert H1; simpl; rewrite !app_length; simpl; lia.
      - apply ss_trans with (1 := H1); simpl. 
        constructor; apply ss_app_l; constructor; auto.
Qed.

(** * Task 1: completion of this gives full points*)
Lemma judge1_correct xs ys:
  (all_proper_subseq xs ys) <-> judge1 xs ys = true.
Proof.
  unfold judge1.
  rewrite aux2_spec.
  unfold all_proper_subseq.
  split.
  + intros H l x r E.
    apply H; subst; simpl.
    split.
    * intros E.
      apply f_equal with (f := @length _) in E.
      revert E; rewrite !app_length; simpl; lia.
    * apply ss_app_l; constructor; auto.
  + intros H xs'.
    rewrite  proper_subseq_eq.
    intros (l & y & r & H1 & H2).
    apply ss_trans with (1 := H1).
    apply (H l y r); auto.
Qed.

Definition judge2:= judge1.

Lemma judge2_correct xs ys:
  (all_proper_subseq xs ys) <-> judge2 xs ys = true.
Proof.
  apply judge1_correct.
Qed.



