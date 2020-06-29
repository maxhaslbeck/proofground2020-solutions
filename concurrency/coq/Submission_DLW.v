Require Import Defs Arith Relations Lia.

Hint Resolve Proc_0 : core.

Definition f i := if Nat.eq_dec (i + 1) N then 0 else i + 1.

(* The first move is to set one x to 1 *)

Theorem reachable_inv_1 st :
    reachable st -> forall i, Proc i -> st.(pc) i = assign_x \/ st.(x) i = 1. 
Proof.
  induction 1 as 
      [ ix iy 
      | st Hst IH i Hi H3 
      | st Hst IH i Hi H3
      ]; simpl; intros k Hk; auto.
  + destruct (eq_nat_dec i k); auto.
  + destruct (eq_nat_dec i k); auto; subst k.
    right.
    destruct IH with (1 := Hk); auto.
    now rewrite H3 in *.
Qed.

Theorem reachable_safe : forall st, reachable st -> safe st.
Proof.
  intros ? [ ix iy 
           | st Hst i Hi H3 
           | st Hst i Hi H3
           ] H4; auto.
  + now specialize (H4 _ Proc_0).
  + specialize (H4 _ Hi).
    simpl in H4; rewrite H3 in H4.
    now destruct (eq_nat_dec i i).
  + assert (H5 : Proc j).
    { unfold j, Proc in *; destruct (eq_nat_dec (i+1) N); lia. }
    destruct reachable_inv_1 with (1 := Hst) (i := j) as [ H6 | H6 ]; auto.
    * specialize (H4 _ H5); simpl in *.
      rewrite H6 in H4.
      destruct (eq_nat_dec i j) as [ E | E ]; try discriminate.
      now rewrite <- E, H3 in H6.
    * rewrite H6; exists i; split; auto.
      simpl.
      destruct (eq_nat_dec i i) as [ | [] ]; auto.
Qed.

