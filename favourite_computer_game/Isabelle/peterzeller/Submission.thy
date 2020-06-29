theory Submission
  imports Defs
begin    

lemma disjE':
  assumes major: "P \<or> Q"
    and minorP: "P \<Longrightarrow> R"
    and minorQ: "Q \<Longrightarrow> \<not>P \<Longrightarrow> R"
  shows R
  using assms by auto

(* The append lemma - gives 30% of the points.
   Note: While this lemma gives less points, it's actually harder to prove! *)

lemma takeWhile_other:
  assumes "hd ys \<noteq> a" 
  shows "takeWhile (\<lambda>y. y = a) ys = []"
  by (metis (mono_tags, lifting) assms hd_Cons_tl takeWhile.simps(1) takeWhile.simps(2))


lemma rle_append: "xs = [] \<or> ys = [] \<or> last xs \<noteq> hd ys \<Longrightarrow> rle (xs @ ys) = rle xs @ rle ys"
proof (induct xs)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a as)
  from `a # as = [] \<or> ys = [] \<or> last (a # as) \<noteq> hd ys`
  show ?case
  proof (elim disjE')
    assume "a # as = []"
    thus ?thesis by simp
  next
    assume "ys = []"
    thus ?thesis
      by simp
  next 
    assume "last (a # as) \<noteq> hd ys"
      and "ys \<noteq> []"

    show "rle ((a # as) @ ys) = rle (a # as) @ rle ys"
    proof (cases "as")
      case Nil
      then show ?thesis 
        by auto
         (metis \<open>last (a # as) \<noteq> hd ys\<close> last_ConsL takeWhile_other,
           metis (full_types) \<open>last (a # as) \<noteq> hd ys\<close> \<open>ys \<noteq> []\<close> dropWhile.simps(2) hd_Cons_tl last_ConsL)
    next
      case (Cons b bs)


      have "rle ((a # as) @ ys) = (case rle (as@ys) of
                (r,n)#rs \<Rightarrow> if r=a then (r,n+1)#rs else (a,1)#(r,n)#rs)"
        by (auto simp add: local.Cons split: list.splits)
      also have "... = (case rle as @ rle ys of
                (r,n)#rs \<Rightarrow> if r=a then (r,n+1)#rs else (a,1)#(r,n)#rs)"
        using Cons.hyps \<open>last (a # as) \<noteq> hd ys\<close> by fastforce
      also have "... = rle (a # as) @ rle ys"
        by (auto simp add: local.Cons split: list.splits)

      finally show ?thesis
        by blast
    qed
  qed
qed

text \<open>Note: Proofs for the second part were finished after the deadline.\<close>

lemma split_replicate:
  assumes "xs = a #as"
  shows "\<exists>n. xs = replicate n a @ drop n xs \<and> 0 < n \<and> n \<le> length xs \<and> (n = length xs \<or> a \<noteq> xs ! n)"
  using assms proof (induct xs arbitrary: a as)
  case Nil
  then show ?case 
    by simp
next
  case (Cons b bs)
  show ?case
  proof (cases bs)
    case Nil
    then show ?thesis
      using Cons.prems by (auto intro!: exI[where x=1])
  next
    case (Cons c cs)
    show ?thesis 
    proof (cases "b = c")
      case True

      from `\<And>a as. bs = a # as \<Longrightarrow> \<exists>n. bs = replicate n a @ drop n bs \<and> 0 < n \<and> n \<le> length bs \<and> (n = length bs \<or> a \<noteq> bs ! n)`[OF `bs = c # cs`]

      obtain n where "bs = replicate n c @ drop n bs"
        and "0 < n" and "n \<le> length bs"
        and "n = length bs \<or> c \<noteq> bs ! n"
        by blast
      then show ?thesis
        using Cons.prems True by (auto simp add: intro!: exI[where x="n+1"])
    next
      case False
      then show ?thesis
        using Cons.prems local.Cons by (auto intro!: exI[where x=1])
    qed
  qed
qed

lemma append_diff_induct:
  assumes "P []"
    and "\<And>n x xs. P xs \<Longrightarrow> xs = [] \<or> x \<noteq> hd xs  \<Longrightarrow> P (replicate n x @ xs)"
  shows "P xs"
proof (induct "length xs" arbitrary: xs rule: less_induct)
  case less

  show ?case 
  proof (cases xs)
    case Nil
    then show ?thesis
      by (simp add: assms(1))
  next
    case (Cons a list)

    obtain n where "xs = replicate n a @ drop n xs" and "n > 0" and "n\<le>length xs" and "n = length xs \<or> a \<noteq> xs!n"
      using split_replicate
      by (metis local.Cons)

    have "P (replicate n a @ drop n xs)"
    proof (rule assms(2))

      show "P (drop n xs)"
      proof (rule less.hyps)
        show "length (drop n xs) < length xs"
          by (simp add: \<open>0 < n\<close> local.Cons)
      qed
      show "drop n xs = [] \<or> a \<noteq> hd (drop n xs)"
        using \<open>n = length xs \<or> a \<noteq> xs ! n\<close> \<open>n \<le> length xs\<close> drop_eq_Nil hd_drop_conv_nth le_neq_implies_less by blast
    qed
    then show ?thesis
      using \<open>xs = replicate n a @ drop n xs\<close> by auto
  qed
qed

lemma dropWhile_replicate: 
  "dropWhile (\<lambda>y. y = x) (replicate n x) = []"
  by (induct n) auto

lemma rle_replicate: "rle (replicate n x) = (if n = 0 then []else [(x,n)])"
  by (induct n) 
    (auto simp add: dropWhile_replicate split: if_splits,
      metis (mono_tags, lifting) le_neq_implies_less length_replicate length_takeWhile_le nth_length_takeWhile nth_replicate)


(* Given the append lemma show the reverse lemma - gives 70% of the points.
   Note: While this lemma gives more points, it might actually be easier to prove *)
lemma rle_rev_if_rle_append1: " rle (rev xs) = rev (rle xs)"
proof (induct xs rule: append_diff_induct)
  case 1
  then show ?case
    by simp
next
  case (2 n x xs)


  show ?case
  proof (subst rev_append)
    show "rle (rev xs @ rev (replicate n x)) = rev (rle (replicate n x @ xs))"
    proof (subst rle_append)
      show "rev xs = [] \<or> rev (replicate n x) = [] \<or> last (rev xs) \<noteq> hd (rev (replicate n x))"
        using "2.hyps"(2) last_rev by force
      show "rle (rev xs) @ rle (rev (replicate n x)) = rev (rle (replicate n x @ xs))"
      proof (subst rle_append)
        show "replicate n x = [] \<or> xs = [] \<or> last (replicate n x) \<noteq> hd xs"
          using "2.hyps"(2) by auto
        show "rle (rev xs) @ rle (rev (replicate n x)) = rev (rle (replicate n x) @ rle xs)"
          by (subst rev_append)  (auto simp add: "2.hyps"(1) rle_replicate)
      qed
    qed
  qed
qed

lemma rle_rev_if_rle_append:
"(xs = [] \<or> ys = [] \<or> last xs \<noteq> hd ys \<Longrightarrow> rle (xs @ ys) = rle xs @ rle ys)
       \<Longrightarrow> rle (rev xs) = rev (rle xs)"
  by (rule rle_rev_if_rle_append1)

end