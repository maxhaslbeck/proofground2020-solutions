Require Import Defs Lia.

(* Inductive invariant. Adds to safe an invariant tracking the value
of x. *)
Definition indinv st :=
    safe st /\
    forall i, Proc i ->
        (st.(pc) i = assign_y \/ st.(pc) i = done) ->
        st.(x) i = 1.

Lemma Proc_mod :
    forall i, Proc i -> Proc (if Nat.eq_dec (i + 1) N then 0 else i + 1).
Proof.
    intros. destruct (Nat.eq_dec (i + 1) N).
    - apply Proc_0.
    - unfold Proc in *. lia.
Qed.

Lemma reachable_indinv :
    forall st, reachable st -> indinv st.
Proof.
    intros st Hreach. induction Hreach.
    - split; simpl.
        { intro. specialize (H 0 Proc_0). discriminate. }
        { intros. destruct H0; discriminate. }
    - split; simpl.
        { unfold safe. intros. specialize (H1 i H). simpl in H1.
          destruct (Nat.eq_dec i i); try discriminate; intuition. }
        { intros. destruct (Nat.eq_dec i i0); auto. unfold indinv in IHHreach.
          apply IHHreach; auto. }
    - split; simpl.
        { unfold indinv, safe in *. intros.
          exists i; split; auto.
          assert (Proc j) as HProcj by (unfold j; apply Proc_mod; auto).
          assert (x st j = 1).
          { destruct IHHreach as [_ IHHreach]. apply IHHreach; auto.
            specialize (H1 j HProcj). simpl in *.
            destruct (Nat.eq_dec i j); auto. rewrite <- e. auto. }
          simpl. destruct (Nat.eq_dec i i); intuition. }
        { intros. destruct IHHreach as [_ IHHreach]. apply IHHreach; auto.
          destruct (Nat.eq_dec i i0); auto. rewrite <- e. auto. }
Qed.

Theorem reachable_safe :
    forall st, reachable st -> safe st.
Proof.
    apply reachable_indinv.
Qed.

