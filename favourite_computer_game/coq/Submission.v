Require Import Defs Lia.

Lemma takeWhile_forallb_true {X} (f: X -> bool) (xs:list X) :
  forallb f xs = true -> 
  takeWhile f xs = xs.
Proof.
  induction xs. all:cbn.
  -easy.
  -destruct (f a). all:cbn. intros ?%IHxs. all:intros;congruence.
Qed.

Lemma dropWhile_app {X} (f: X -> bool) (xs ys:list X) :
  dropWhile f (xs++ys) = if forallb f xs then dropWhile f ys else dropWhile f xs++ys.
Proof.
  induction xs. all:cbn.
  -easy.
  -destruct (f a). all:cbn.
   2:now easy.
   rewrite IHxs. now destruct forallb.
Qed.

Lemma dropWhile_forallb_true {X} (f: X -> bool) (xs:list X) :
  forallb f xs = true -> 
  dropWhile f xs = [].
Proof.
  induction xs. all:cbn.
  -easy.
  -destruct (f a). all:cbn. intros ?%IHxs. all:intros;congruence.
Qed.


Lemma hd_error_app  {X} {xs ys:list X} :
  hd_error (xs++ys) = match xs with [] => hd_error ys | _ => hd_error xs end.
Proof.
  destruct xs. all:cbn. all:easy.
Qed.

Lemma hd_error_rev {X} {xs:list X} :
  hd_error (rev xs) = last_error xs.
Proof.
  induction xs. all:cbn. easy.
  rewrite hd_error_app.
  destruct xs. easy.
  destruct (rev (x :: xs)) eqn:H. 2:congruence.
  exfalso. 
  apply (f_equal) with (f:=@length _) in H.
  cbn in H. rewrite app_length in H. cbn in H.  nia.
Qed.


Lemma last_error_rev {X} {xs:list X} :
  last_error (rev xs) = hd_error xs.
Proof.
  rewrite <- hd_error_rev. now rewrite rev_involutive.
Qed.


Lemma length_dropWhile_le {X} f (xs:list X) :
  length (dropWhile f xs) <= length xs.
Proof.
  induction xs;cbn. nia. destruct f. all:cbn;nia.
Qed.


Module ForTask1.
  
  Lemma takeWhile_app {X} (f: X -> bool) (xs ys:list X) :
    takeWhile f (xs++ys) = if forallb f xs then xs++takeWhile f ys else takeWhile f xs.
  Proof.
    induction xs. all:cbn.
    -easy.
    -destruct (f a). all:cbn.
     2:now easy.
     rewrite IHxs. now destruct forallb.
  Qed.

  Lemma forallb_e_repeat xs x:
    forallb (Nat.eqb x) xs = true -> xs = repeat x (length xs).
  Proof.
    induction xs;cbn. easy.
    intros [<-%EqNat.beq_nat_true ?%IHxs ]%andb_prop. congruence.
  Qed.


  Lemma last_error_repeat {X} (x:X) n:
    last_error (repeat x n) = match n with 0 => None | _ => Some x end.
  Proof.
    destruct n. now cbn. 
    induction n;cbn. easy. assumption.
  Qed.

  Lemma last_error_dropWhile {X} f (xs:list X) :
    last_error (dropWhile f xs) = if forallb f xs then None else last_error xs.
  Proof.
    induction xs. all:cbn. easy.
    destruct f eqn:?. all:cbn. 2:easy.
    rewrite IHxs. destruct forallb eqn:?. easy.
    destruct xs;cbn. easy. easy.
  Qed.

End ForTask1.

Section task1.
  Import ForTask1.

  (** The append lemma - gives 30% of the points.
   Note: While this lemma gives less points, it's actually harder to prove! *)
  Lemma rle_app (xs ys : list nat):
    (forall x, ~ (last_error xs = Some x
             /\ hd_error ys = Some x))
    -> rle (xs++ys) = rle xs ++ rle ys.
  Proof.
    intros H_gap.
    induction xs as [xs H_ind] using size_ind with (f:=(@length nat)).
    destruct xs;cbn.
    -reflexivity.
    -f_equal. f_equal.
     +rewrite takeWhile_app. destruct forallb eqn:H_fa. 2:reflexivity.
      rewrite takeWhile_forallb_true with (xs0:=xs). 2:easy.
      rewrite app_length.
      enough (length (takeWhile (Nat.eqb n) ys) = 0) as ->. now nia.
      destruct ys. easy. cbn.
      destruct (PeanoNat.Nat.eqb_spec n n0) as [<- |]. 2:easy.
      edestruct H_gap. split. 2:easy.
      replace (n::xs) with (repeat n (S (length xs))). now rewrite last_error_repeat.
      erewrite (forallb_e_repeat (n::xs)). reflexivity. cbn. rewrite H_fa. now rewrite PeanoNat.Nat.eqb_refl.
     +rewrite dropWhile_app. destruct forallb eqn:H_fa.
      2:{ rewrite H_ind.
          -easy.
          -eapply PeanoNat.Nat.le_lt_trans. now eapply length_dropWhile_le. cbn;lia.
          -intros ? []. eapply H_gap. split. 2:eassumption.
           rewrite last_error_dropWhile in H. rewrite H_fa in H.
           rewrite <- H. now destruct xs.
      }
      rewrite (dropWhile_forallb_true _ _ H_fa). cbn.
      f_equal.
      destruct ys. easy.
      cbn. destruct (PeanoNat.Nat.eqb_spec n n0). 2:easy.
      subst n0.
      edestruct H_gap. split. 2:easy.
      replace (n::xs) with (repeat n (S (length xs))). now rewrite last_error_repeat.
      erewrite (forallb_e_repeat (n::xs)). reflexivity. cbn. rewrite H_fa. now rewrite PeanoNat.Nat.eqb_refl.
  Qed.
End task1. 

Module ForTask2.
  Lemma take_drop_eq {X} (f:X -> bool) xs :
    takeWhile f xs ++ dropWhile f xs = xs.
  Proof.
    induction xs. all:cbn. easy.
    destruct f. 2:easy. cbn. congruence.
  Qed.

  Lemma hd_error_dropWhile_Some {X} f (xs:list X) x:
    hd_error (dropWhile f xs) = Some x -> f x = false.
  Proof.
    induction xs. easy. cbn. destruct (f a) eqn:?. all:cbn. easy. congruence. Qed.

  Lemma last_error_takeWhile_Some {X} f (xs:list X) x:
    last_error (takeWhile f xs) = Some x -> f x = true.
  Proof.
    induction xs. easy. cbn. destruct (f a) eqn:?. all:cbn. 2:easy.
    destruct takeWhile eqn:?. congruence. easy.
  Qed.

  Lemma takeWhile_eq n xs:
    takeWhile (Nat.eqb n) xs = repeat n (length (takeWhile (Nat.eqb n) xs)).
  Proof.
    induction xs. all:cbn. easy. destruct (Nat.eqb_spec n a). 2:easy.
    subst. cbn. congruence.
  Qed.

  Lemma rev_repeat {X} (x:X) n:
    rev (repeat x n) =  repeat x n.
  Proof.
    induction n;cbn. easy.
    rewrite IHn. clear. induction n. easy. cbn. now rewrite IHn.
  Qed. 

  Lemma forallb_eqb_repeat n k:
    forallb (Nat.eqb n) (repeat n k) = true.
  Proof.
    apply forallb_forall. intros ? ?%repeat_spec. subst. apply Nat.eqb_refl.
  Qed.
  
  Lemma rle_repeat x k :
    rle (repeat x k) = match k with 0 => [] | _ => [(x,k)] end.
  Proof.
    destruct k. all:cbn. easy.
    f_equal.
    -repeat f_equal. 
     rewrite takeWhile_forallb_true. 2:now apply forallb_eqb_repeat. now rewrite repeat_length.
    -rewrite dropWhile_forallb_true. easy. now apply forallb_eqb_repeat.
  Qed.

End ForTask2.

Import ForTask2.
  
(** Given the append lemma show the reverse lemma - gives 70% of the points.
    Note: While this lemma gives more points, it might actually be easier to prove *)
Lemma rle_rev_if_rle_app:
  (forall xs ys,
      (forall x, ~ (last_error xs = Some x
                /\ hd_error ys = Some x))
       -> rle (xs++ys) = rle xs ++ rle ys)
  -> forall xs, rev (rle xs) = rle (rev xs).
Proof.
  intros rle_app xs.
   induction xs as [xs H] using size_ind with (f:=(@length nat)).
    destruct xs;cbn. now easy.
    change ( (rev xs ++ [n])) with ( (rev (n::xs))).
    erewrite <- (take_drop_eq (Nat.eqb n) (n :: xs)).
    rewrite rev_app_distr.
    rewrite rle_app.
    2:{ rewrite last_error_rev, hd_error_rev.
        intros ? [?%hd_error_dropWhile_Some ?%last_error_takeWhile_Some]. congruence. }
    rewrite H.
    2:{ eapply PeanoNat.Nat.le_lt_trans. now eapply length_dropWhile_le. cbn;lia. }
    f_equal.
    {cbn. now rewrite Nat.eqb_refl. }
    rewrite (takeWhile_eq n (n::xs)). rewrite rev_repeat.
    rewrite rle_repeat.
    cbn. rewrite Nat.eqb_refl. cbn. easy.
Qed.
