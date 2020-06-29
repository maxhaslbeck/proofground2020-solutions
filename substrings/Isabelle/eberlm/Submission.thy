theory Submission
  imports Defs
begin

lemma subseq_append2 [intro]: "subseq xs ys \<Longrightarrow> subseq xs (zs @ ys)"
  by (induct zs) auto

lemma subseq_prefix [intro]:
  assumes "subseq xs ys" shows "subseq xs (ys @ zs)"
  using assms
  by (induct arbitrary: zs) auto

lemma subseq_ConsD:
  assumes "subseq (x#xs) ys"
  shows "\<exists>us vs. ys = us @ x # vs \<and> subseq xs vs"
using assms
proof (induct x \<equiv> "x # xs" ys arbitrary: x xs)
  case 3
  then show ?case by (metis append_Cons)
next
  case 2
  thus ?case by blast
qed

lemma subseq_Nil_iff [simp]: "xs \<sqsubseteq> [] \<longleftrightarrow> xs = []"
  by (auto elim: subseq.cases)

lemma Cons_subseqD [dest]:
  assumes "x # xs \<sqsubseteq> ys"
  shows   "xs \<sqsubseteq> ys"
  using assms
  by (induction "x # xs" ys rule: subseq.induct) auto

lemma subseq_Cons_same_iff [simp]: "(x # xs) \<sqsubseteq> (x # ys) \<longleftrightarrow> xs \<sqsubseteq> ys"
proof
  assume "x # xs \<sqsubseteq> x # ys"
  thus "xs \<sqsubseteq> ys"
    by (cases rule: subseq.cases) auto
qed auto

lemma subseq_Cons_different_iff [simp]:
  assumes "x \<noteq> y"
  shows   "(x # xs) \<sqsubseteq> (y # ys) \<longleftrightarrow> x # xs \<sqsubseteq> ys"
proof
  assume "x # xs \<sqsubseteq> y # ys"
  thus "x # xs \<sqsubseteq> ys"
    using assms
    by (induction "x # xs" "y # ys" rule: subseq.induct) auto
qed auto

lemma subseq_Cons_iff: "(x # xs) \<sqsubseteq> (y # ys) \<longleftrightarrow> (if x = y then xs \<sqsubseteq> ys else x # xs \<sqsubseteq> ys)"
  by auto

lemma subseq_trans [trans]: "xs \<sqsubseteq> ys \<Longrightarrow> ys \<sqsubseteq> zs \<Longrightarrow> xs \<sqsubseteq> zs"
proof -
  assume "xs \<sqsubseteq> ys" and "ys \<sqsubseteq> zs"
  then show "xs \<sqsubseteq> zs"
  proof (induction arbitrary: zs)
    case 1 show ?case by blast
  next
    case (3 xs ys y)
    from subseq_ConsD [OF \<open>(y#ys) \<sqsubseteq> zs\<close>] obtain us v vs
      where zs: "zs = us @ v # vs" and "ys \<sqsubseteq> vs" by blast
    then have "ys \<sqsubseteq> (v#vs)" by blast
    then have "ys \<sqsubseteq> zs" unfolding zs by (rule subseq_append2)
    from "3.IH" [OF this] show ?case by auto
  next
    case (2 xs ys y)
    from subseq_ConsD[OF 2(3)] obtain us vs where zs: "zs = us @ y # vs \<and> ys \<sqsubseteq> vs"
      by auto
    hence "y # ys \<sqsubseteq> us @ y # vs"
      using 2(2)[of vs] 2(1,3) by auto
    thus ?case using 2 zs
      by auto
  qed
qed

lemma not_proper_subseq_Nil [simp]: "\<not>zs \<sqsubset> []"
  by (auto simp: proper_subseq_def)

lemma subseq_imp_length_le:
  assumes "xs \<sqsubseteq> ys"
  shows   "length xs \<le> length ys"
  using assms by induction auto

lemma not_Cons_suseq_self [simp]: "\<not>x # xs \<sqsubseteq> xs"
  using subseq_imp_length_le[of "x # xs" xs] by auto

lemma subseq_refl [simp]: "xs \<sqsubseteq> xs"
  by (induction xs) auto

lemma subseq_append_left_cancel [simp]: "xs @ ys \<sqsubseteq> xs @ zs \<longleftrightarrow> ys \<sqsubseteq> zs"
  by (induction xs) auto


lemma aux_correct [simp]: "aux xs ys \<longleftrightarrow> xs \<sqsubseteq> ys"
  by (induction xs ys rule: aux.induct) auto

lemma aux2_correct: "aux2 ys acc xs \<longleftrightarrow> (\<forall>zs. zs \<sqsubset> xs \<longrightarrow> acc @ zs \<sqsubseteq> ys)"
proof (induction ys acc xs rule: aux2.induct)
  case (2 ys acc x xs)
  text \<open>
    Idea: we split the proper subsequences of \<^term>\<open>x # xs\<close> into two cases:
      1. the (not necessarily proper) subsequences of \<^term>\<open>xs\<close>
      2. the proper subsequences of \<^term>\<open>xs\<close> with \<^term>\<open>x\<close> slapped in front of each of them
  \<close>
  define ZS where "ZS = {zs. zs \<sqsubset> x # xs}"
  define ZS1 and ZS2 where "ZS1 = {zs. zs \<sqsubseteq> xs}" and "ZS2 = (\<lambda>zs. x # zs) ` {zs. zs \<sqsubset> xs}"

  have "(\<forall>zs. zs \<sqsubset> x # xs \<longrightarrow> acc @ zs \<sqsubseteq> ys) \<longleftrightarrow> (\<forall>zs\<in>ZS. acc @ zs \<sqsubseteq> ys)"
    by (auto simp: ZS_def)
  also have "ZS = ZS1 \<union> ZS2"
  proof (intro equalityI subsetI) (* can be sledgehammered in one line *)
    fix zs assume "zs \<in> ZS1 \<union> ZS2"
    thus "zs \<in> ZS"
      by (auto simp: ZS_def ZS1_def ZS2_def proper_subseq_def)
  next
    fix zs assume "zs \<in> ZS"
    thus "zs \<in> ZS1 \<union> ZS2"
      by (cases zs) (auto simp: ZS_def ZS1_def ZS2_def proper_subseq_def subseq_Cons_iff
                          split: if_splits)
  qed
  also have "(\<forall>zs\<in>ZS1\<union>ZS2. acc @ zs \<sqsubseteq> ys) \<longleftrightarrow> (\<forall>zs\<in>ZS1. acc @ zs \<sqsubseteq> ys) \<and> (\<forall>zs\<in>ZS2. acc @ zs \<sqsubseteq> ys)"
    by blast

  text \<open>
    Due to transitivity, we don't have to check all of \<^term>\<open>ZS1\<close>; it is enough to
    check for the biggest list in it, which is \<^term>\<open>xs\<close> itself.
  \<close>
  also have "(\<forall>zs\<in>ZS1. acc @ zs \<sqsubseteq> ys) \<longleftrightarrow> acc @ xs \<sqsubseteq> ys"
  proof safe
    fix zs assume "zs \<in> ZS1" and *: "acc @ xs \<sqsubseteq> ys"
    have "acc @ zs \<sqsubseteq> acc @ xs"
      using \<open>zs \<in> _\<close> unfolding ZS1_def by auto
    also note \<open>acc @ xs \<sqsubseteq> ys\<close>
    finally show "acc @ zs \<sqsubseteq> ys" .
  qed (auto simp: ZS1_def)
  also have "(\<forall>zs\<in>ZS2. acc @ zs \<sqsubseteq> ys) \<longleftrightarrow> aux2 ys (acc @ [x]) xs"
    using 2 by (auto simp: ZS2_def)
  finally show ?case by simp
qed auto

definition
  "judge2 xs ys \<longleftrightarrow> judge1 xs ys"

theorem judge1_correct: "judge1 xs ys \<longleftrightarrow> all_proper_subseq xs ys"
  by (auto simp: judge1_def all_proper_subseq_def aux2_correct)

theorem judge2_correct:
  "judge2 xs ys \<longleftrightarrow> all_proper_subseq xs ys"
  unfolding judge2_def by (rule judge1_correct)

theorem judge2_is_executable:
  "judge2 ''ab'' ''ab'' \<longleftrightarrow> True"
  "judge2 ''ba'' ''ab'' \<longleftrightarrow> True"
  "judge2 ''abcd'' ''cdabc'' \<longleftrightarrow> False"
  by eval+

end