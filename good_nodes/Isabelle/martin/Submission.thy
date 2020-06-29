theory Submission
  imports Defs
begin

lemma good_only_if: "good_node i \<Longrightarrow> E\<^sup>*\<^sup>* i 0"
  by (induction i rule: good_node.induct) auto

lemma good_if: "E\<^sup>*\<^sup>* i j \<Longrightarrow> good_node j \<Longrightarrow> good_node i"
  by (induction i j rule: rtranclp.induct) (auto intro: good_node.intros)

theorem good_node_def:
  "good_node i \<longleftrightarrow> E\<^sup>*\<^sup>* i 0"
  using good_only_if good_if[OF _ good_node.intros(1)]
  by auto

lemma good_node_1:
  assumes "good_node i" "i < n" "i > 0" "E\<^sup>*\<^sup>* i j" "E\<^sup>+\<^sup>+ j j"
  shows False
  using assms
proof (induction i rule: good_node.induct)
  case (2 k i)
  have good_i: "good_node i"
    using 2(1,2)
    by (auto intro: good_node.intros)
  have k_0: "0 < k"
    using 2(2,6,7)
    by (metis E_def converse_rtranclpE tranclpD)
  have k_n: "k < n"
    using 2(2)
    by (auto simp: E_def)
  have E_k_j: "E\<^sup>*\<^sup>* k j"
    using 2(2,6)
    by (metis E_def assms(5) rtranclp_tranclp_tranclp tranclpD)
  show ?case
    by (rule 2(3)[OF k_n k_0 E_k_j 2(7)])
qed auto

theorem good_node_characterization_1:
  assumes "i < n" "i > 0" "good_node i"
  shows "\<not> (\<exists>j. E\<^sup>*\<^sup>* i j \<and> E\<^sup>+\<^sup>+ j j)"
  using good_node_1 assms
  by auto

lemma term_aux:
  assumes "i < n" "i \<notin> set ns"
  shows "card (set ns \<inter> {..<n}) < n"
  using assms
  by (metis card_lessThan card_seteq finite_lessThan inf_commute inf_le1 lessThan_iff
      not_le subsetD)

function sucs :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "sucs i ns = (if i < n then (if i \<in> set ns \<or> i = 0 then [i] else
    i # sucs (graph ! i) (ns @ [i])) else [])"
  by pat_completeness auto
termination
  using term_aux diff_less_mono2
  by (relation "measure (\<lambda>(i, ns). n - (card (set ns \<inter> {..<n})))") auto

lemma sucs_sound:
  assumes "i < n" "set ns \<subseteq> {..<n}" "\<And>k. k \<in> set ns \<Longrightarrow> E\<^sup>+\<^sup>+ k i" "j = last (sucs i ns)"
  shows "E\<^sup>*\<^sup>* i j \<and> (j = 0 \<or> E\<^sup>+\<^sup>+ j j)"
  using assms
proof (induction i ns rule: sucs.induct)
  case (1 i ns)
  show ?case
    using 1(2,4,5)
  proof (cases "i \<in> set ns \<or> i = 0")
    case False
    have wf: "graph ! i < n"
      using 1(2) wellformed
      by (auto simp: n_def)
    have set: "set (ns @ [i]) \<subseteq> {..<n}"
      using 1(2,3)
      by auto
    have hd: "hd (sucs i ns) = i" "hd (sucs (graph ! i) (ns @ [i])) = graph ! i"
      using 1(2) wf
      by auto
    have "E i (graph ! i)"
      using 1(2) wf False
      by (auto simp: E_def)
    then have prem: "\<And>k. k \<in> set (ns @ [i]) \<Longrightarrow> E\<^sup>+\<^sup>+ k (graph ! i)"
      using 1(4)
      by force
    have E_star: "E\<^sup>*\<^sup>* (graph ! i) j \<and> (j = 0 \<or> E\<^sup>+\<^sup>+ j j)"
      using 1(1)[OF 1(2) False wf set prem] 1(2,5) False wf
      by (metis last_ConsR list.distinct(1) sucs.elims)
    moreover have "E i (graph ! i)"
      using 1(2) wf False
      by (auto simp: E_def)
    ultimately show ?thesis
      unfolding hd(2)
      by auto
  qed auto
qed

theorem good_node_characterization_2:
  assumes "i < n" "i > 0" "\<not> (\<exists>j. E\<^sup>*\<^sup>* i j \<and> E\<^sup>+\<^sup>+ j j)"
  shows "good_node i"
proof -
  define j where "j = last (sucs i [])"
  have "E\<^sup>*\<^sup>* i j" "j = 0 \<or> E\<^sup>+\<^sup>+ j j"
    using sucs_sound[OF assms(1), of "[]", folded j_def] assms(1,2)
    by auto
  then show ?thesis
    using assms(2,3)
    unfolding good_node_def
    by auto
qed

corollary good_node_characterization:
  assumes "i < n" "i > 0"
  shows "good_node i \<longleftrightarrow> \<not> (\<exists>j. E\<^sup>*\<^sup>* i j \<and> E\<^sup>+\<^sup>+ j j)"
  using good_node_characterization_1 good_node_characterization_2 assms by blast

end