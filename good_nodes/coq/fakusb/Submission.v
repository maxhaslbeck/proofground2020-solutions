Require Import Defs Lia Wf_nat PeanoNat.
Hint Unfold E : core.

(** * task 1*)
Lemma good_node_def i:
  good_node i <-> clos_refl_trans_1n _ E i 0.
Proof.
  split.
  -induction 1. all:eauto using clos_refl_trans_1n.
  -revert i. eapply rt1n_ind_right. all:eauto using good_node.
Qed.

(** * task 2*)

Lemma E_functional i j j':
  E i j -> E i j' -> j = j'.
Proof. unfold E;intuition congruence. Qed.

Hint Constructors clos_refl_trans_1n clos_trans_1n : core.

Lemma good_node_characterisation_1 i:
  good_node i
  -> i < n
  -> ~ exists j, clos_refl_trans_1n _ E i j
           /\ clos_trans_1n _ E j j.
Proof.
  rewrite good_node_def. 
  intros H _. pattern i. revert i H.
  apply rt1n_ind_right. 2:intros i j H_ij H_j_to_0 IH.
  +intros (j&H'&?).
   replace j with 0 in *.
   2:{ all:inversion H'. all:now unfold E in *. }
   destruct H. all:unfold E in *;try easy.
  +intros (?&?&?). destruct H as [ | j'].
   *apply IH.
    eexists j;split. 1:now unfold E in *.
    remember i as i' in H0 at 2.
    destruct H0 as [j'|j'];subst i.
    all:replace j' with j in * by now (eapply E_functional;eauto).
    now eauto.
    rewrite <- clos_trans_t1n_iff in *. econstructor 2. eassumption. now apply t_step.
   *replace j' with j in * by now (eapply E_functional;eauto).
    apply IH. eauto.
Qed.

(** * task 3*)

Fixpoint allN n :=
  match n with
    0 => [0]
  | S n => S n::allN n
  end.

Lemma In_alln_iff i n :
  In i (allN n) <-> i <= n.
Proof.
  induction n;cbn.
  1:{intuition lia. }
  rewrite IHn. lia.
Qed.

Lemma In_remove_iff X dec (d x:X) xs:
  In x (remove dec d xs) <-> x <> d /\ In x xs.
Proof.
  induction xs;cbn. easy.
  destruct dec. subst.
  all:cbn. all:rewrite IHxs. all:intuition subst. all:firstorder.
Qed.

Lemma length_remove X (x:X) xs dec:
  length (remove dec x xs) + length (filter (fun y => if dec x y then true else false) xs) = length xs.
Proof.
  induction xs;cbn -[Nat.sub]. easy. 
  destruct dec. subst.
  all:cbn - [Nat.sub]. all:rewrite <- IHxs. all:intuition subst. lia.
Qed.

(* Backwards-compatibility: This lemma is only in Coq starting on version 8.11, but the grader is not there yet, so I added this here. *)

Lemma nth_error_nth' {A} (l : list A) {n : nat} (d : A):
    n < length l -> nth_error l n = Some (nth n l d).
Proof.
  intros H.
  apply nth_split with (d:=d) in H. destruct H as [l1 [l2 [H H']]].
  subst. rewrite H. rewrite nth_error_app2; [|auto].
  rewrite app_nth2; [| auto]. repeat (rewrite PeanoNat.Nat.sub_diag). reflexivity.
Qed.


Lemma thm' maybeNoCircle i j:
  j < n
  -> clos_refl_trans_1n _ E i j
  -> (forall j', j' < n -> ~ In j' maybeNoCircle
           -> clos_trans_1n _ E j j'
           -> clos_trans_1n _ E j' j')
  -> clos_refl_trans_1n _ E i 0
    \/ (exists j, clos_refl_trans_1n _ E i j
            /\ clos_trans_1n _ E j j).
Proof.
  remember (length  maybeNoCircle) as n eqn:Hn.
  revert maybeNoCircle j Hn. 
  induction n as [n IH] using lt_wf_ind.
  intros maybeNoCircle j Hn wf_j H_partPath H_couldCycle;subst n.
  assert (j = 0 \/ exists j', E j j') as [ -> | [j' Hj']].
  { specialize (wellformed j) as wj_j. destruct j. now eauto. right. unfold E.
    erewrite nth_error_nth' with (d:=0) in *. 2-3:easy.
    eexists;repeat simple apply conj. 4:reflexivity. 1,3:lia. eauto.
  }
  {eauto. }
  destruct (in_dec Nat.eq_dec j' maybeNoCircle) as [H'|H'].
  2:{ right. eexists . split. 2: eapply H_couldCycle with (j':=j').
      2:now unfold E in *.
      2,3:cbn;now eauto.
      rewrite <- clos_rt_rt1n_iff in *. eauto using clos_refl_trans.
  }
  eapply IH with (maybeNoCircle := remove Nat.eq_dec j' maybeNoCircle) (j:=j'). (* as [ | (j__circ&?&?)]. *)
  2:now reflexivity.
  - erewrite <- length_remove with (xs:=maybeNoCircle) (dec:=Nat.eq_dec) (x:=j').
    clear - H'. induction maybeNoCircle. easy. destruct H' as [ | H'].
    2:apply IHmaybeNoCircle in H'. subst.
    all:cbn. all:destruct Nat.eq_dec;cbn;try lia.
  -hnf in Hj'. intuition eauto. 
  -rewrite <- clos_rt_rt1n_iff in *. eauto using clos_refl_trans.
  -intros j'' ? Hj'' HE''. rewrite  In_remove_iff in Hj''.
   assert (j'' = j' \/ j'' <> j') as [ | ] by decide equality.
   2:{ eapply H_couldCycle. all: eauto. }
   subst j''. clear Hj''. eauto.
Qed.    


Lemma good_node_characterisation_2 i:
  i < n
  -> (~ exists j, clos_refl_trans_1n _ E i j
            /\ clos_trans_1n _ E j j)
  -> good_node i.
Proof.
  intros ? ?. rewrite good_node_def.
  edestruct thm' with (maybeNoCircle:=allN n).
  1:now eassumption.
  3:{ eauto. }
  3:{ tauto. }
  now eauto.
  intros ? ? H'. rewrite In_alln_iff in H'. exfalso. lia.
Qed.


Lemma good_node_characterization i:
  i < n
  -> good_node i <-> ~ (exists j, clos_refl_trans_1n _ E i j
                          /\ clos_trans_1n _ E j j).
Proof.
  split;eauto using good_node_characterisation_1,good_node_characterisation_2.
Qed.
