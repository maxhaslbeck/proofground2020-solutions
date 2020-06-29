theory Submission
  imports Defs
begin

lemmas [intro] = good_node.intros(1)

theorem good_node_def:
  "good_node i \<longleftrightarrow> E\<^sup>*\<^sup>* i 0"
proof
  assume "good_node i"
  thus "E\<^sup>*\<^sup>* i 0"
    by induction auto
next
  assume "E\<^sup>*\<^sup>* i 0"
  thus "good_node i"
    by (induction rule: converse_rtranclp_induct) (auto intro: good_node.intros(2))
qed

theorem good_node_characterization_1:
  assumes "i < n" "i > 0" "good_node i"
  shows "\<not> (\<exists>j. E\<^sup>*\<^sup>* i j \<and> E\<^sup>+\<^sup>+ j j)"
proof safe
  fix j assume "E\<^sup>*\<^sup>* i j" "E\<^sup>+\<^sup>+ j j"
  from assms(3,1,2) this show False
  proof (induction rule: good_node.induct)
    case (2 a b)
    thus False
      by (metis E_def rtranclp_tranclp_tranclp tranclpD)
  qed auto
qed

definition step :: "nat \<Rightarrow> nat" where
  "step i = graph ! i"

lemma step_less: "i < n \<Longrightarrow> step i < n"
  using wellformed by (auto simp: n_def step_def)

theorem good_node_characterization_2:
  assumes "i < n" "i > 0" "\<not> (\<exists>j. E\<^sup>*\<^sup>* i j \<and> E\<^sup>+\<^sup>+ j j)"
  shows "good_node i"
proof (rule ccontr)
  assume "\<not>good_node i"

  text \<open>
    We define a step function and consider the sequence of steps starting from \<^term>\<open>i\<close>:
  \<close>
  have step: "E k (step k)" if "k > 0" "k < n" for k
    using that wellformed by (auto simp: E_def step_def n_def)
  have steps_less: "(step ^^ k) i < n" for k
    using assms(1) by (induction k) (auto intro: step_less)

  text \<open>
    Because \<^term>\<open>i\<close> is not good, we will never hit 0:
  \<close>
  have steps_nonzero: "(step ^^ k) i \<noteq> 0" for k
  proof
    assume "(step ^^ k) i = 0"
    from this and \<open>i < n\<close> have "good_node i"
    proof (induction k arbitrary: i)
      case (Suc k i)
      show ?case
      proof (cases "i = 0")
        case False
        have "E i (step i)"
          using step[of i] Suc False by auto
        moreover have "good_node (step i)"
          using Suc.IH[of "step i"] Suc.prems False step_less[of i]
          by (intro Suc) (auto simp: funpow_Suc_right simp del: funpow.simps)
        ultimately show ?thesis by (auto intro: good_node.intros(2))
      qed auto
    qed auto
    with \<open>\<not>good_node i\<close> show False by blast
  qed

  text \<open>
    We can reach the \<open>k + x\<close>-th step from the \<open>k\<close>-th step in \<open>x\<close> steps:
  \<close>
  have reach_aux: "(E ^^ x) ((step ^^ k) i) ((step ^^ (k + x)) i)" for k x
  proof (induction x)
    case (Suc x)
    have "(E ^^ x) ((step ^^ k) i) ((step ^^ (k + x)) i)" by fact
    thus ?case
      using local.step steps_less steps_nonzero by auto
  qed auto

  have reach: "(E ^^ k) i ((step ^^ k) i)" for k
    using reach_aux[of k 0] by simp

  text \<open>
    By the pigeonhole principle, there we hit some node \<open>j\<close> twice. Let \<open>k\<^sub>1 < k\<^sub>2\<close> be the indices
    of these two steps.
  \<close>
  obtain k1 k2 where k12: "k1 < k2" "(step ^^ k1) i = (step ^^ k2) i"
  proof -
    have "\<not>inj (\<lambda>k. (step ^^ k) i)"
    proof
      assume "inj (\<lambda>k. (step ^^ k) i)"
      hence "infinite (range (\<lambda>k. (step ^^ k) i))"
        using finite_image_iff by blast
      moreover have "range (\<lambda>k. (step ^^ k) i) \<subseteq> {..<n}"
        using steps_less by auto
      hence "finite (range (\<lambda>k. (step ^^ k) i))"
        using infinite_super by auto
      ultimately show False by auto
    qed
    have "\<exists>k1 k2. k1 < k2 \<and> (step ^^ k1) i = (step ^^ k2) i"
    proof -
      from \<open>\<not>inj (\<lambda>k. (step ^^ k) i)\<close>
        obtain k1 k2 where "k1 \<noteq> k2" "(step ^^ k1) i = (step ^^ k2) i"
        by (auto simp: inj_def)
      thus ?thesis
        by (cases k1 k2 rule: linorder_cases; force)
    qed
    thus ?thesis using that by blast
  qed
  define j where "j = (step ^^ k1) i"
  have [simp]: "(step ^^ k1) i = j" "(step ^^ k2) i = j"
    using k12 by (simp_all add: j_def)

  text \<open>
    We then note that \<open>j\<close> is reachable from \<open>i\<close>, and it is also reachable from itself
    in more than one step (i.e.\ it lies on a circle).
  \<close>
  have "E\<^sup>*\<^sup>* i j"
    using reach unfolding j_def by (meson relpowp_imp_rtranclp)
  moreover have "E\<^sup>+\<^sup>+ j j"
  proof -
    have "(E ^^ (k2 - k1)) ((step ^^ k1) i) ((step ^^ k2) i)"
      using reach_aux[of "k2 - k1" k1] k12 by simp
    hence "E\<^sup>+\<^sup>+ ((step ^^ k1) i) ((step ^^ k2) i)"
      by (meson k12 tranclp_power zero_less_diff)
    thus "E\<^sup>+\<^sup>+ j j"
      by simp    
  qed
  ultimately show False using assms k12 by auto
qed

corollary good_node_characterization:
  assumes "i < n" "i > 0"
  shows "good_node i \<longleftrightarrow> \<not>(\<exists>j. E\<^sup>*\<^sup>* i j \<and> E\<^sup>+\<^sup>+ j j)"
  using good_node_characterization_1 good_node_characterization_2 assms by blast

end