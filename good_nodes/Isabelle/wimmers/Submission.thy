theory Submission
  imports Defs
begin

theorem good_node_def:
  "good_node i \<longleftrightarrow> E\<^sup>*\<^sup>* i 0"
  apply safe
  subgoal premises prems
    using prems by induction auto
  subgoal premises prems
    using prems by (induction rule: converse_rtranclp_induct) (auto intro: good_node.intros)
  done

lemma E_determ:
  assumes "E a b" "E a c"
  shows "b = c"
  using assms unfolding E_def by auto

lemma reaches_bound:
  assumes "E\<^sup>*\<^sup>* i j" "i < n"
  shows "j < n"
  using assms by cases (auto simp: E_def)

lemma reaches1_0:
  "E\<^sup>+\<^sup>+ 0 j \<longleftrightarrow> False"
  by (meson E_def tranclpD zero_less_iff_neq_zero)

lemma cycle_never_reaches_0:
  assumes "E\<^sup>+\<^sup>+ j 0" "E\<^sup>+\<^sup>+ j j"
  shows False
  using assms
  apply (induction j rule: converse_tranclp_induct)
   apply (metis E_def converse_tranclpE less_numeral_extra(3))
  by (metis E_determ rtranclpD tranclp.trancl_into_trancl tranclpD)

lemma reaches_determ:
  assumes "E\<^sup>*\<^sup>* a b" "E\<^sup>*\<^sup>* a c"
  obtains "E\<^sup>*\<^sup>* c b" | "E\<^sup>*\<^sup>* b c"
  apply atomize_elim
  using assms
  apply induction
   apply auto
  by (metis E_determ converse_rtranclpE r_into_rtranclp)

\<comment> \<open>This definition and the theorem are copied from the timed automata graph library
(cf.\ \<^url>\<open>https://github.com/wimmers/munta/blob/13a3a83270f9613b164af58a8ece6373c92fb7c8/library/Graphs.thy#L436\<close>)\<close>
definition sink where
  "sink a \<equiv> \<nexists>b. E a b"

lemma sink_or_cycle:
  assumes "finite {b. E\<^sup>*\<^sup>* a b}"
  obtains b where "E\<^sup>*\<^sup>* a b" "sink b" | b where "E\<^sup>*\<^sup>* a b" "E\<^sup>+\<^sup>+ b b"
proof -
  let ?S = "{b. E\<^sup>+\<^sup>+ a b}"
  have "?S \<subseteq> {b. E\<^sup>*\<^sup>* a b}"
    by auto
  then have "finite ?S"
    using assms by (rule finite_subset)
  then show ?thesis
    using that
  proof (induction ?S arbitrary: a rule: finite_psubset_induct)
    case psubset
    consider (empty) "Collect (E\<^sup>+\<^sup>+ a) = {}" | b where "E\<^sup>+\<^sup>+ a b"
      by auto
    then show ?case
    proof cases
      case empty
      then have "sink a"
        unfolding sink_def by auto
      with psubset.prems show ?thesis
        by auto
    next
      case 2
      show ?thesis
      proof (cases "E\<^sup>*\<^sup>* b a")
        case True
        with \<open>E\<^sup>+\<^sup>+ a b\<close> have "E\<^sup>+\<^sup>+ a a"
          by auto
        with psubset.prems show ?thesis
          by auto
      next
        case False
        show ?thesis
        proof (cases "E\<^sup>+\<^sup>+ b b")
          case True
          with \<open>E\<^sup>+\<^sup>+ a b\<close> psubset.prems show ?thesis
            by (auto intro: tranclp_into_rtranclp)
        next
          case False
          with \<open>\<not> E\<^sup>*\<^sup>* b a\<close> \<open>E\<^sup>+\<^sup>+ a b\<close> have "Collect (E\<^sup>+\<^sup>+ b) \<subset> Collect (E\<^sup>+\<^sup>+ a)"
            by (intro psubsetI) auto
          then show ?thesis
            using \<open>E\<^sup>+\<^sup>+ a b\<close> psubset.prems
            by - (erule psubset.hyps; meson tranclp_into_rtranclp tranclp_rtranclp_tranclp)
        qed
      qed
    qed
  qed
qed


theorem good_node_characterization_1:
  assumes "i < n" "i > 0" "good_node i"
  shows "\<not> (\<exists>j. E\<^sup>*\<^sup>* i j \<and> E\<^sup>+\<^sup>+ j j)" (* this is right *)
  using assms(3) unfolding good_node_def
proof safe
  \<comment> \<open>paths are determinstic & nothing can leave from \<open>0\<close>\<close>
  fix j :: nat
  assume prems: "E\<^sup>*\<^sup>* i 0" and "E\<^sup>*\<^sup>* i j" and "E\<^sup>+\<^sup>+ j j"
  from \<open>E\<^sup>*\<^sup>* i 0\<close> \<open>E\<^sup>*\<^sup>* i j\<close> consider "j = 0" | "E\<^sup>+\<^sup>+ 0 j" | "E\<^sup>+\<^sup>+ j 0"
    by (metis reaches_determ rtranclpD)
  then show False
  proof cases
    case 1
    with \<open>E\<^sup>+\<^sup>+ j j\<close> show ?thesis
      by (simp add: reaches1_0)
  next
    case 2
    then show ?thesis
      by (simp add: reaches1_0)
  next
    case 3
    with \<open>E\<^sup>+\<^sup>+ j j\<close> show ?thesis
      using cycle_never_reaches_0 by auto
  qed
qed


theorem good_node_characterization_2:
  assumes "i < n" "i > 0" "\<not> (\<exists>j. E\<^sup>*\<^sup>* i j \<and> E\<^sup>+\<^sup>+ j j)"
  shows "good_node i" (* this is right *)
  unfolding good_node_def
proof -
  \<comment> \<open>if a node cannot reach a cycle, then it has to reach a sink\<close>
  let ?S = "{j. E\<^sup>*\<^sup>* i j}"
  have "sink 0"
    unfolding sink_def E_def by auto
  have "?S \<subseteq> {0..<n}"
    using \<open>i < n\<close> by (auto intro: reaches_bound)
  then have "finite ?S"
    by (rule finite_subset) rule
  with assms(3) obtain j where j: "E\<^sup>*\<^sup>* i j" "sink j"
    by (auto elim: sink_or_cycle)
  with \<open>i < n\<close> have "j < n"
    by (auto intro: reaches_bound)
  with \<open>sink j\<close> have "j = 0"
    unfolding sink_def E_def n_def using wellformed by auto
  with \<open>E\<^sup>*\<^sup>* i j\<close> show "E\<^sup>*\<^sup>* i 0"
    by simp
qed

corollary good_node_characterization:
  assumes "i < n" "i > 0"
  shows "good_node i \<longleftrightarrow> \<not> (\<exists>j. E\<^sup>*\<^sup>* i j \<and> E\<^sup>+\<^sup>+ j j)" (* this is right *)
  using good_node_characterization_1 good_node_characterization_2 assms by blast

end