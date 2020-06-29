Require Import Defs.

Hint Constructors subseq.

(** * Task 1: compleion of this gives full points*)

Hint Constructors subseq : core.

Lemma nil_subseq xs:
  subseq [] xs.
Proof. induction xs;eauto. Qed.
Hint Resolve nil_subseq.


Lemma subseq_of_nil xs:
  subseq xs [] -> xs = [].
Proof. inversion 1. easy. Qed.

Import Morphisms.
Instance subseq_PO: PreOrder subseq.
Proof.
  split;hnf.  
  -induction x;eauto.
  -intros x y z H H'. induction H' in H,x |-*;eauto 10. inversion H;subst;eauto.
Qed.


Lemma subseq_all_subseq_iff xs ys:
  subseq xs ys <-> (forall xs', subseq xs' xs -> subseq xs' ys).
Proof.
  split.
  -intros. now etransitivity;eauto.
  -intros H. now specialize (H _ (reflexivity _)).
Qed.

Lemma subseq_cons_l x xs ys :
  subseq (x::xs) ys <-> exists ys1 ys2, ys = ys1++x::ys2 /\ subseq xs ys2.
Proof.
  induction ys in x,xs|-*.
  -split. 2:now intros ([]&?&?&?).
   intros H. inversion H.
  -split.
   +intros H. inversion H;subst.
    {eexists [], _;cbn. split. all:easy. }
    eapply IHys in H2 as (?&?&->&?).
    eexists (_::_),_. split. reflexivity. easy.
   + intros (?&?&H'&?).
     destruct x0. all:inversion H';subst.
     *now eauto.
     *apply subseq_drop. apply IHys. eauto.
Qed.
    
Lemma subseq_diff_head x y xs ys:
  x<>y ->
  subseq (x :: xs) (y :: ys) <-> subseq (x::xs) ys.
Proof.
  rewrite ! subseq_cons_l. intros Hneq. split.
  -intros (?&?&?&?).
   destruct x0; cbn in H. all:inversion H;subst. easy.
   eauto.
  -intros (?&?&->&?). eexists (_::_),_. split. reflexivity. easy.
Qed. 

Lemma subseq_same_head x xs ys:
  subseq (x :: xs) (x :: ys) <-> subseq xs ys.
Proof.
  rewrite subseq_cons_l. split. 
  -intros (?&?&?&?).
   destruct x0; cbn in H. all:inversion H;subst. easy. etransitivity. eassumption.
   induction x0;cbn;eauto using (@reflexivity _ subseq _).
  -exists []. cbn;eauto.
Qed.

Lemma aux_spec xs ys:
 subseq xs ys  <-> aux xs ys = true.
Proof.
  induction ys in xs|-*.
  -split. now inversion 1. destruct xs;cbn. all:easy.
  -cbn. destruct xs;cbn.
   now split;eauto using subseq_of_nil.
   destruct Nat.eq_dec;subst.
   +now rewrite subseq_same_head.
   +now rewrite subseq_diff_head.
Qed.


Lemma proper_subseq_cons_l x xs ys :
  proper_subseq (x::xs) ys -> (exists ys1 ys2, ys1<>[] /\ ys = ys1++x::ys2 /\ subseq xs ys2) \/ exists ys', ys = x::ys' /\ proper_subseq xs ys'.
Proof.
  induction ys.
  -intros [? H]. easy.
  -intros [Hneq H]. inversion H;subst.
   {right. do 2 eexists. easy. split. congruence. easy. }
   eapply subseq_cons_l in H2 as (?&?&->&?).
   left. eexists (_::_),_;repeat simple apply conj. 2:reflexivity. all:easy.
Qed.


Lemma proper_subseq_if xs ys :
  proper_subseq xs ys -> exists ys1 y ys2, ys = ys1 ++ y::ys2 /\ subseq xs (ys1++ys2).
Proof.
  induction xs in ys|-*.
  {intros []. destruct ys. easy. eexists []. cbn. eauto 20. }
  intros [([]&?&?&->&?) | (?&->&?)]%proper_subseq_cons_l.
  -easy.
  -eexists [],_,_. split. cbn. reflexivity. cbn. clear - H0.  induction l;cbn; eauto 20.
  -eapply IHxs in H as (?&?&?&->&?). eexists (_::_). do 3 esplit. reflexivity. cbn. eauto.
Qed.

Require Import Lia. 
Lemma all_proper_subseq_iff xs ys :
  all_proper_subseq xs ys <-> (forall xs1 x xs2, xs = xs1++x::xs2 -> subseq (xs1++xs2) ys).
Proof.
  split.
  -intros H ? ? ? ->. eapply H. clear H. split.
   {intros H'%(f_equal (@length nat)). cbn in H';rewrite !app_length in H'. cbn in H'. lia. }
   induction xs1;cbn. now eauto using (@reflexivity _ subseq _).
   eauto.
  -intros H xs' (?&?&?&->&?)%proper_subseq_if. etransitivity. eassumption. eauto.
Qed. 


Lemma aux2_correct ys acc xs:
  aux2 ys acc xs = true <-> (forall xs1 x xs2, xs = xs1++x::xs2 -> subseq (acc++xs1++xs2) ys).
Proof.
  induction xs in ys,acc|-*. all:cbn.
  -split. 2:easy. now intros _ [].
  -split.
   +intros (Haux&Haux2)%andb_prop ? ? ? Heq.
    apply aux_spec in Haux.
    destruct xs1. all:inversion Heq;subst;cbn. easy.
    eapply IHxs in Haux2. 2:reflexivity.
    cbn in*. rewrite <- !app_assoc in *.  eauto.
   +intros H. eapply andb_true_intro. split.
    {specialize (H [] a xs eq_refl). now apply aux_spec. }
    apply IHxs. intros ? ? ? ->. rewrite <- ! app_assoc;cbn. eapply (H (_::_)). cbn. eauto.
Qed.

Lemma judge1_correct xs ys:
  all_proper_subseq xs ys <-> judge1 xs ys = true.
Proof.
  unfold judge1. rewrite aux2_correct,all_proper_subseq_iff. cbn. reflexivity.
Qed.


(** * Alternative Task *)
(** Show any implementation correct for half the points *)

(** Here is a Bruteforce-judge, we could just take judge1 from above, but as I tried it to see how hard it is, I wanted to give it here. *)

Fixpoint get_all_subseq {X} (xs:list X) : list (list X) :=
  match xs with
    [] => [[]]
  | x::xs => map (cons x) (get_all_subseq xs) ++ get_all_subseq xs
  end.


Definition get_all_proper_subseq  (xs:list nat) : list (list nat) :=
  filter (fun xs' => if list_eq_dec (Nat.eq_dec) xs' xs then false else true) (get_all_subseq xs).
         
Definition bruteforce_judge (xs ys : list nat) :=
  forallb
    (fun xs' =>
       existsb
         (fun ys' => if list_eq_dec (Nat.eq_dec) xs' ys'
                  then true else false)
         (get_all_subseq ys))
    (get_all_proper_subseq xs).


Lemma get_all_subseq_correct xs xs' :
  subseq xs' xs <-> In xs' (get_all_subseq xs).
Proof.
  induction xs in xs'|-*. all:cbn. 
  -split.
   +inversion 1. eauto.
   +intuition. subst. eauto.
  -rewrite in_app_iff,in_map_iff.
   setoid_rewrite <- IHxs.
   split.
   +inversion 1. all:subst. all:eauto.
   +intros [(?&<-&?) | ]. all:auto.
Qed.



Lemma get_all_proper_subseq_correct xs xs' :
  proper_subseq xs' xs <-> In xs' (get_all_proper_subseq xs).
Proof.
  unfold proper_subseq,get_all_proper_subseq.
  rewrite filter_In. rewrite and_comm.
  rewrite get_all_subseq_correct.
  destruct list_eq_dec. all:firstorder.
Qed. 

  
Lemma bruteforce_judge_correct xs ys :
  all_proper_subseq xs ys <-> bruteforce_judge xs ys = true.
Proof.
  unfold bruteforce_judge.
  unfold all_proper_subseq.
  setoid_rewrite forallb_forall.
  setoid_rewrite existsb_exists.
  assert (H : forall x y, (if list_eq_dec Nat.eq_dec x y then true else false) = true <-> x = y).
  { intros. destruct list_eq_dec. all:easy. }
  setoid_rewrite H.
  setoid_rewrite <- get_all_proper_subseq_correct. setoid_rewrite <- get_all_subseq_correct.
  split. 1:intuition;subst;eauto 10.
  intros H'. intuition.
  edestruct H' as (?&H''&->). all:easy.
Qed.

Definition judge2:= bruteforce_judge.

Lemma judge2_correct xs ys:
  (all_proper_subseq xs ys) <-> judge2 xs ys = true.
Proof.
  apply bruteforce_judge_correct.
Qed.

