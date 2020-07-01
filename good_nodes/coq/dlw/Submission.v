Require Import Defs Arith Lia Permutation.

Infix "~p" := (@Permutation _) (at level 70).

(** Small utility to be used in combination with the PHP 
    list_n n = [n-1;...;0] *)

Fixpoint list_n n :=
  match n with 
      0   => []
    | S n => n::list_n n
  end.

Fact list_n_spec n x : In x (list_n n) <-> x < n.
Proof. induction n as [ | n IHn ]; simpl; [ | rewrite IHn ]; lia. Qed.

Fact list_n_length n : length (list_n n) = n.
Proof. induction n; simpl; f_equal; auto. Qed.

(** One of the difficulties here it to see that
    we need to use the finite Pigeon Hole Principle *)

Section php.

  (* A short proof of the finite PHP *)

  Variable (X : Type).

  Implicit Type (l : list X).

  Fact in_Permutation x m : In x m -> exists l, x::l ~p m.
  Proof.
    intros H.
    apply in_split in H as (l & r & ->).
    exists (l++r); now apply Permutation_cons_app.
  Qed.

  Fact incl_cons_inv_l x l m : incl (x::l) m <-> In x m /\ incl l m.
  Proof.
    split.
    + intros H; split; [ | intros ? ? ]; apply H; simpl; auto.
    + intros (? & ?) z [ -> | ? ]; auto.
  Qed.

  Fact incl_cons_inv_r l x m : incl l (x::m) -> incl l m \/ In x l.
  Proof.
    induction l as [ | y l IHl ].
    + left; intros ? [].
    + rewrite incl_cons_inv_l.
      intros ([ -> | H1] & H2).
      * right; simpl; auto.
      * destruct (IHl H2).
        - rewrite incl_cons_inv_l; tauto.
        - right; simpl; auto.
  Qed.

  Definition has_dup l := exists x a b c, l = a++x::b++x::c.

  Fact has_dup_nil : has_dup nil <-> False.
  Proof. split; try tauto; now intros (? & [] & ? & ? & ?). Qed.

  Fact has_dup_cons x l : has_dup (x::l) <-> In x l \/ has_dup l.
  Proof.
    split.
    * intros (y & [ | z a ] & b & c & H); inversion H.
      + rewrite in_app_iff; simpl; auto.
      + right; now exists y, a, b, c.
    * intros [ H | (y & a & b & c & ->) ].
      + apply in_split in H as (a & b & ->).
        exists x, nil, a, b; auto.
      + exists y, (x::a), b, c; auto. 
  Qed.

  Fact perm_has_dup l m : l ~p m -> has_dup l -> has_dup m.
  Proof.
    induction 1 as [ | x l m H IH | | ]; auto; rewrite !has_dup_cons; simpl.
    + intros [ G | ]; auto; left; revert G; apply Permutation_in; auto.
    + generalize (@eq_sym _ x y); tauto.
  Qed.

  Fact incl_cons_inv_dup l x m : 
         incl l (x::m) 
      -> incl l m 
      \/ (exists l', x::l' ~p l /\ incl l' m) 
      \/ has_dup l.
  Proof.
    intros H.
    destruct incl_cons_inv_r with (1 := H) as [ H1 | H1 ]; auto.
    apply in_Permutation in H1 as (l' & H1).
    destruct (incl_cons_inv_r l' x m) as [ H2 | H2 ]; auto.
    + intros y Hy; apply H, Permutation_in with (1 := H1); right; auto.
    + firstorder.
    + apply in_split in H2 as (c & d & ->).
      do 2 right; apply perm_has_dup with (1 := H1).
      now exists x, nil, c, d.
  Qed.

  Theorem php l m : incl l m -> length m < length l -> has_dup l.
  Proof.
    revert l; induction m as [ | y m IHm ]; simpl; try lia; intros l;
      try (simpl; lia).
    + destruct l as [ | x l ]; simpl; try lia.
      intros H; destruct (H x); simpl; auto.
    + intros H1 H2.
      apply incl_cons_inv_dup in H1 as [ H1 | [ (l' & H1 & H3) | H1 ] ]; auto.
      * apply IHm; auto; lia.
      * apply perm_has_dup with (1 := H1), has_dup_cons; right.
        apply Permutation_length in H1; simpl in H1.
        apply IHm; auto; lia.
  Qed.

End php.

Reserved Notation "x '-{' l '}>' y" (at level 70, format "x  -{ l }>  y").
Reserved Notation "x '-[' n ']>' y" (at level 70, format "x  -[ n ]>  y").
Reserved Notation "x '->>' y" (at level 70).
Reserved Notation "x '-+>' y" (at level 70).

Section rels.

  Variables (X : Type) (R : X -> X -> Prop).

  Implicit Type (l m : list X).

  (* Enriched version of clos_refl_trans *)

  Fixpoint liter x l z :=
    match l with
      | nil  => x = z
      | y::l => R x y /\ y -{l}> z
    end
  where "x -{ l }> y" := (liter x l y).

  Fact liter_app x l m z : x -{l++m}> z <-> exists y, x -{l}> y /\ y -{m}> z.
  Proof.
    revert x z; induction l as [ | y l IHl ]; simpl; intros x z.
    + split; firstorder; subst; auto.
    + rewrite IHl; firstorder.
  Qed.

  Fixpoint riter n := 
    match n with 
      | 0   => eq
      | S n => fun x z => exists y, R x y /\ y -[n]> z
    end
  where "x -[ n ]> y" := (riter n x y).

  Fact riter_liter n x z : x -[n]> z <-> exists l, x -{l}> z /\ length l = n.
  Proof.
    split.
    * revert x z; induction n as [ | n IHn ]; intros x z; simpl.
      + intros ->; exists nil; simpl; auto.
      + intros (y & H1 & H2).
        destruct (IHn _ _ H2) as (l & H3 & H4).
        exists (y::l); simpl; auto.
    * intros (l & H & <-); revert x z H.
      induction l as [ | y l IHl ]; simpl; intros x z; auto.
      exists y; firstorder.
  Qed.

  Fact riter_plus a b x z : x -[a+b]> z <-> exists y, x -[a]> y /\ y -[b]> z.
  Proof.
    revert x z; induction a as [ | a IHa ]; intros x z; simpl.
    + split.
      * now exists x.
      * now intros (? & <- & ?).
    + split.
      * intros (y & H1 & H2); revert H2; rewrite IHa.
        intros (k & H3 & H4); exists k; split; auto; exists y; auto.
      * intros (y & (k & H1 & H2) & H3).
        exists k; rewrite IHa; split; auto.
        exists y; auto.
  Qed.

  Notation "x ->> y" := (exists n, x -[n]> y).
  Notation "x -+> y" := (exists n, x -[S n]> y).

  Fact riter_0 x y : x -[0]> y <-> x = y.
  Proof. simpl; tauto. Qed.

  Fact riter_1 x y : x -[1]> y <-> R x y.
  Proof. simpl; split; firstorder; subst; auto. Qed.

  Fact riter_S n x z : x -[S n]> z <-> exists y, x -[n]> y /\ R y z.
  Proof. 
    replace (S n) with (n+1) by lia.
    rewrite riter_plus.
    split; intros (y & H); exists y; revert H; rewrite riter_1; auto.
  Qed.

  (* Correspondance with clos_refl_trans and clos_trans *)

  Fact riter_rtc x z : clos_refl_trans_1n _ R x z <-> x ->> z.
  Proof.
    split.
    + induction 1 as [ | x y z H1 H2 (n & H3) ].
      * exists 0; simpl; auto.
      * exists (S n), y; auto.
    + intros (n & H); revert x z H; induction n as [ | n IHn ]; simpl; intros x z.
      * intros ->; constructor 1.
      * intros (y & ? & ?); constructor 2 with y; auto.
  Qed.

  Fact riter_tc x z : clos_trans_1n _ R x z <-> x -+> z.
  Proof.
    split.
    + induction 1 as [ | x y z H1 H2 (n & H3) ].
      * exists 0, y; simpl; auto.
      * exists (S n), y; auto.
    + intros (n & H); revert x z H; induction n as [ | n IHn ]; simpl; intros x z.
      * intros (y & H1 & ->); constructor 1; auto.
      * intros (y & ? & ?); constructor 2 with y; auto.
  Qed.

  (** If there is a chain of length k starting at x 
      and that chain is contained in a list of smaller length
      then x leads to a cycle, ie x ~>> y -+> y 

      This involves the finite Pigeon Hole Principle 
    *)

  Definition to_cycle x := exists y, x ->> y /\ y -+> y.

  Fact riter_php l k x y : 
       (forall x y, R x y -> In y l)
    -> length l < k 
    -> x -[k]> y -> to_cycle x.
  Proof.
    rewrite riter_liter. 
    intros H1 H2 (m & H3 & H4).
    assert (incl m l) as H5.
    { clear H2 H4; revert x y H3.
      induction m as [ | a m IHm ]; intros x y; simpl.
      + intros _ ? [].
      + intros (H2 & H3).
        apply incl_cons_inv_l; split.
        * apply (H1 _ _ H2).
        * revert H3; apply IHm. }
    destruct php with (1 := H5) as (z & a & b & c & ->); try lia.
    rewrite liter_app in H3; destruct H3 as (u & H3 & H6 & H7).
    rewrite liter_app in H7; destruct H7 as (v & H7 & H8 & H9).
    exists z; split. 
    + exists (length (a++[z])).
      apply riter_liter; exists (a++[z]); split; auto.
      rewrite liter_app; simpl; exists u; auto.
    + exists (length b).
      apply riter_liter; exists (b++[z]); rewrite liter_app; split.
      * exists v; simpl; auto.
      * rewrite app_length; simpl; lia.
  Qed.

  (** If R is deterministic this we have inversions wrt + and cycles *)

  Hypothesis R_det : forall x y z, R x y -> R x z -> y = z.

  Fact riter_det a x y z : x -[a]> y -> x -[a]> z -> y = z.
  Proof.
    revert x y z; induction a as [ | a IHa ]; intros x y z; simpl.
    + intros ->; auto.
    + intros (u & H1 & H2) (v & H3 & H4).
      rewrite (R_det _ _ _ H1 H3) in *.
      apply (IHa v); auto.
  Qed.

  Fact riter_plus_inv a b x y z : x -[a]> y ->  x-[a+b]> z -> y -[b]> z.
  Proof.
    rewrite riter_plus.
    intros H1 (k & H2 & H3).
    now rewrite (riter_det _ _ _ _ H1 H2).
  Qed.

  Fact riter_prefix_choose a b x y z : 
           x -[a]> y 
        -> x -[b]> z 
        -> y -[b-a]> z \/ z -[a-b]> y.
  Proof.
    intros H1 H2.
    destruct (le_lt_dec a b).
    + left; apply riter_plus_inv with (1 := H1).
      now replace (a+(b-a)) with b by lia.
    + right; apply riter_plus_inv with (1 := H2).
      now replace (b+(a-b)) with a by lia.
  Qed.

  Fact riter_choose x y z : x ->> y -> x ->> z -> y ->> z \/ z ->> y.
  Proof.
    intros (a & Ha) (b & Hb).
    destruct riter_prefix_choose with (1 := Ha) (2 := Hb).
    + left; now exists (b-a).
    + right; now exists (a-b).
  Qed.

  (** of x -+> .... ->> x is a cycle and x ->> y then also y ->> x 
      proof:
        a) x -[n]> y
        b) cycle arround until n is smaller than the length of the cycle
     *)

  Theorem riter_cycle x y : x -+> x -> x ->> y -> y ->> x.
  Proof.
    intros (b & Hb) (a & Ha).
    revert y Ha.
    induction a as [ a IHa ] using (well_founded_induction lt_wf); intros y.
    destruct (le_lt_dec (S b) a) as [ E | E ].
    + replace a with (S b+(a-S b)) by lia; intros H1.
      apply IHa with (2 := riter_plus_inv _ _ _ _ _ Hb H1); try lia.
    + intros H1.
      replace (S b) with (a + (S b-a)) in Hb by lia.
      exists (S b - a); revert Hb; apply riter_plus_inv; auto.
  Qed.

End rels.

(** The relation E is deterministic, total (except for 0) *)

Fact E_det i j1 j2 : E i j1 -> E i j2 -> j1 = j2.
Proof.
  intros (H1 & H2 & H3 & H4) (H5 & H6 & H7 & H8).
  rewrite H4 in H8; inversion H8; auto.
Qed.

Fact E_total i : 0 < i < n -> exists j, E i j.
Proof.
  unfold E.
  intros H.
  case_eq (nth_error G i).
  + intros j Hj; exists j; repeat split; auto; try lia.
    apply wellformed with i; auto.
  + rewrite nth_error_None; intros; unfold n in *; lia.
Qed.

Fact E_0_no_image i : ~ E 0 i.
Proof. intros (H1 & H2 & H3 & H4); lia. Qed.

Notation "x -[ n ]> y" := (riter _ E n x y).
Notation "x ->> y" := (exists n, x -[n]> y).
Notation "x -+> y" := (exists n, x -[S n]> y).

(** * task 1*)

Lemma good_node_riter i : good_node i <-> i ->> 0.
Proof.
  split.
  + induction 1 as [ | j i H (k & Hk) G ].
    * exists 0; simpl; auto.
    * exists (S k); exists i; auto.
  + intros (k & Hk); revert i Hk.
    induction k as [ | k IHk ]; simpl; intros i.
    * intros ->; constructor.
    * intros (j & H1 & H2).
      constructor 2 with j; auto.
Qed.

Lemma good_node_def i:
  good_node i <-> clos_refl_trans_1n _ E i 0.
Proof. rewrite riter_rtc, good_node_riter; tauto. Qed.

Fact riter_E_from_0 n i : 0 -[n]> i -> n = 0 /\ i = 0.
Proof.
  destruct n; simpl.
  + intros <-; auto.
  + intros (y & Hy & _).
    contradict Hy; apply E_0_no_image.
Qed.

Fact rtc_E_from_0 i : 0 ->> i -> i = 0.
Proof. intros (n & Hn); now apply riter_E_from_0 in Hn. Qed.

Fact tc_E_from_0 i : 0 -+> i -> False.
Proof. intros (n & Hn); now apply riter_E_from_0 in Hn. Qed.

Hint Resolve E_0_no_image E_det : core.

(** * task 2*)

(** good_node i <-> i ->> 0
    (exists j ...) <-> to_cycle i

    we show that 0 belongs to the cycle i ->> j -+> j 
    because i ->> 0 is a maximal computation
    hence we have also 0 ->> j which implies j = 0 
    and a contradiction *)
  
Lemma good_node_characterisation_1 i:
  good_node i
  -> i < n
  -> ~ exists j, clos_refl_trans_1n _ E i j
           /\ clos_trans_1n _ E j j.
Proof.
  intros H1 H2 (j & H3 & H4); revert H1 H3 H4.
  rewrite good_node_riter, riter_rtc, riter_tc; intros H1 H3 H4.
  destruct riter_choose 
    with (1 := E_det) (2 := H1) (3 := H3)
    as [ C | C ].
  + apply rtc_E_from_0 in C as ->.
    apply tc_E_from_0 in H4 as [].
  + apply riter_cycle with (1 := E_det) (2 := H4),
          rtc_E_from_0 in C as ->.
    apply tc_E_from_0 in H4 as [].
Qed.

(* Unless i ->> stops at 0, path from i can be arbitarily long *)

Lemma path_stops_at_0_or_as_long_as_wished i p : 
    i < n -> i ->> 0 \/ exists z, z < n /\ i -[p]> z.
Proof.
  intros Hi.
  induction p as [ | p [ H | (z & H1 & H2) ] ]; auto.
  + right; exists i; simpl; auto.
  + destruct (eq_nat_dec z 0) as [ -> | C ].
    * left; exists p; auto.
    * right.
      destruct E_total with z as (j & H3); try lia.
      exists j; split; auto.
      - apply H3.
      - rewrite riter_S; exists z; auto.
Qed.

(** Now with the PHP, we get a cycle out of a long enough path *)

Lemma stops_at_0_or_to_cycle i : 
   i < n -> i ->> 0 \/ to_cycle _ E i.
Proof.
  intros Hi.
  destruct (path_stops_at_0_or_as_long_as_wished i (S n))
    as [ H | (z & H1 & H2) ]; auto; right.
  apply riter_php with (l := list_n n) (3 := H2).
  + intros ? ? []; rewrite list_n_spec; lia.
  + rewrite list_n_length; lia.
Qed.

(** * task 3*)
Lemma good_node_characterisation_2 i:
  i < n
  -> (~ exists j, clos_refl_trans_1n _ E i j
            /\ clos_trans_1n _ E j j)
  -> good_node i.
Proof.
  intros H1 H2.
  destruct (stops_at_0_or_to_cycle _ H1) as [ H | H ].
  + apply good_node_riter; auto.
  + destruct H2.
    destruct H as (j & (a & H2) & b & H3).
    exists j; split.
    * rewrite riter_rtc; exists a; auto.
    * apply riter_tc; exists b; auto.
Qed.

Lemma good_node_characterization i:
  i < n
  -> good_node i <-> ~ (exists j, clos_refl_trans_1n _ E i j
                          /\ clos_trans_1n _ E j j).
Proof.
  split;eauto using good_node_characterisation_1,good_node_characterisation_2.
Qed.
