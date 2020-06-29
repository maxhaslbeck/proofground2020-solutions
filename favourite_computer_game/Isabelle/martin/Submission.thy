theory Submission
imports Defs
begin

(* The append lemma - gives 30% of the points.
   Note: While this lemma gives less points, it's actually harder to prove! *)

lemma rle_aux:
  assumes "x \<noteq> y"
  shows "rle (xs @ replicate (Suc n) x @ y # ys) = rle (xs @ replicate (Suc n) x) @ rle (y # ys)"
  using assms
proof (induction xs arbitrary: n x y ys rule: rev_induct)
  case Nil
  then show ?case
    by (induction n) auto
next
  case (snoc z zs)
  then show ?case
  proof (cases "z = x")
    case False
    have "rle (zs @ replicate (Suc 0) z @ x # replicate n x @ y # ys) =
      rle (zs @ replicate (Suc 0) z @ x # replicate n x) @ rle (y # ys)"
      unfolding snoc(1)[OF False, of 0 "replicate n x @ y # ys"]
        snoc(1)[OF False, of 0 "replicate n x"]
      using snoc(2)
      by (induction n) auto
    then show ?thesis
      by auto
  qed (metis append.assoc append.simps(1) append.simps(2) replicate_Suc)
qed

lemma rle_append: "xs = [] \<or> ys = [] \<or> last xs \<noteq> hd ys \<Longrightarrow> rle (xs @ ys) = rle xs @ rle ys"
  apply (cases xs rule: rev_cases; cases ys)
     apply auto[3]
  subgoal for zs z w ws
    using rle_aux[of z w zs 0 ws]
    by auto
  done

lemma rle_repl: "rle (replicate (Suc n) z) = [(z, Suc n)]"
  by (induction n) auto

(* Given the append lemma show the reverse lemma - gives 70% of the points.
   Note: While this lemma gives more points, it might actually be easier to prove *)
lemma rle_rev_if_rle_aux:
  fixes xs :: "'a list"
  shows "rle (rev xs) = rev (rle xs)"
proof (induction "length xs" arbitrary: xs rule: nat_less_induct)
  case 1
  have IH: "\<And>ys :: 'a list. length ys < length xs \<Longrightarrow> rle (rev ys) = rev (rle ys)"
    using 1
    by auto
  show ?case
  proof (cases xs)
    case (Cons z zs)
    note xs_Cons = Cons
    define ys where "ys = z # takeWhile (\<lambda>y. y = z) zs"
    define ys' where "ys' = dropWhile (\<lambda>y. y = z) zs"
    define n where "n = length (takeWhile (\<lambda>y. y = z) zs)"
    have ys_repl: "ys = replicate (Suc n) z"
      unfolding ys_def
      by (auto simp: n_def) (meson replicate_eqI set_takeWhileD)
    have xs_app: "xs = ys @ ys'"
      by (auto simp: xs_Cons ys_def ys'_def)
    have ys_Nil: "ys \<noteq> []"
      by (auto simp: ys_def)
    show ?thesis
    proof (cases ys')
      case Nil
      show ?thesis
        unfolding xs_app Nil ys_repl append_Nil2 rev_replicate rle_repl
        by auto
    next
      case (Cons w ws)
      have z_neq_w: "z \<noteq> w"
        using ys'_def
        unfolding Cons
        by (metis (mono_tags) hd_dropWhile list.distinct(1) list.sel(1))
      have aux1: "rev (rle xs) = rev (rle (w # ws)) @ [(z, Suc n)]"
        using rle_aux[OF z_neq_w, of "[]" n ws]
        unfolding append_Nil rle_repl xs_app ys_repl Cons
        by auto
      have aux2: "rle (rev xs) = rle (rev ws @ [w]) @ [(z, Suc n)]"
        using rle_aux[OF z_neq_w[symmetric], of "rev ws" 0 "replicate n z"]
        unfolding replicate.simps
        unfolding replicate.simps[symmetric] rle_repl
        unfolding xs_app ys_repl Cons
        by (auto simp: replicate_append_same)
      have prem: "length (w # ws) < length xs"
        by (auto simp: xs_app Cons ys_def)
      show ?thesis
        unfolding aux1 aux2 IH[OF prem, symmetric]
        by auto
    qed
  qed auto
qed

lemma rle_rev_if_rle_append: "(xs = [] \<or> ys = [] \<or> last xs \<noteq> hd ys \<Longrightarrow>
  rle (xs @ ys) = rle xs @ rle ys) \<Longrightarrow> rle (rev xs) = rev (rle xs)"
  by (rule rle_rev_if_rle_aux)

end