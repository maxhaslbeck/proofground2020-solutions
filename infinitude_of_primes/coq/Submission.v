Require Import Defs.

Import Lia.
Lemma fS_2_le n: 2 <= fS n.
Proof. induction n;cbn. all:nia. Qed.

(** * Task 1*)
Lemma prime_pf_S_fS (n:nat):
  prime (pf (fS n + 1)).
Proof.
  edestruct pf_spec as [[H _] _]. 2:eassumption. specialize (fS_2_le n). lia.
Qed.

(** * Task2 *)
Lemma divisors_fS_succ {n k}:
  Nat.divide k (fS n+1) -> Nat.divide k (fS (1 + n)).
Proof. cbn. apply Nat.divide_mul_r.  Qed.


Lemma divisors_fS_mono {n n' k}:
  n <= n' -> Nat.divide k (fS n) -> Nat.divide k (fS n').
Proof.
  induction 1 using le_ind. easy.
  cbn in *. eauto using Nat.divide_mul_l.
Qed.

Lemma thm2' (n m k:nat) : pf (fS n + 1) = pf (fS m + 1) ->  n <= m.
Proof.
  intros Heq. apply Nat.nlt_ge. intros H.

  destruct (pf_spec (fS n + 1)) as ((Hp_k&H_k_div_n)&H_k_min).
  {specialize (fS_2_le n). nia. }

  specialize (pf_spec (fS m + 1)) as ((_&H_k_div_m)&H_k_m_min).
  {specialize (fS_2_le m). nia. }

  specialize (divisors_fS_succ H_k_div_m) as H'.
  apply (@divisors_fS_mono _ n) in H'. 2:now nia.

  rewrite <- Heq in H'.
  eapply (Nat.divide_sub_r _ _ _ H_k_div_n) in H'.

  replace (fS n + 1 - fS n) with 1 in H' by lia.
  apply Nat.divide_1_r in H'. hnf in Hp_k. lia.
Qed.


Lemma pf_fS_inj (n m:nat) :
  pf (fS n + 1) = pf (fS m + 1)
  -> n = m.
Proof.
    intros. apply Nat.le_antisymm. all:eauto using thm2'.
Qed.


(** * Final Conclusion *)
Require Import List Lia.


Lemma infinitely_many_primes':
  forall n, exists L, n <= length L
            /\ Forall prime L
            /\ NoDup L.
Proof.
  intros n. exists (map (fun i => pf(fS i + 1)) (seq 0 n)).
  repeat split.
  -now rewrite map_length,seq_length.
  -apply Forall_forall. intros ? (?&<-&?)%in_map_iff.
   eauto using prime_pf_S_fS.
  -erewrite NoDup_nth with (d:= pf(fS 0 + 1)).
   rewrite map_length,seq_length.
   setoid_rewrite  map_nth with (d:=0)(f:=(fun i0 : nat => pf (fS i0 + 1))). intros ? ? ? ? H'. setoid_rewrite seq_nth in H'. cbn in H'. 2-3:nia.
   now apply pf_fS_inj.
Qed.
