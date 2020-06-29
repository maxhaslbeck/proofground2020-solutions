theory Submission
  imports Defs
begin

lemma record_updates [simp]:
  "pc (update_pc st i l) = (pc st) (i := l)"
  "pc (update_x st i v) = pc st"
  "pc (update_y st i v) = pc st"
  "x (update_pc st i l) = x st"
  "x (update_x st i v) = (x st) (i := v)"
  "y (update_y st i v) = (y st) (i := v)"
  "y (update_pc st i l) = y st"
  "x (update_y st i v) = x st"
  "y (update_x st i v) = y st"
  by (simp_all add: update_pc_def update_x_def update_y_def)

lemma x_assigned:
  assumes "reachable st"
  shows   "\<forall>i. Proc i \<longrightarrow> pc st j \<noteq> assign_x \<longrightarrow> x st j = 1"
  using assms by induction auto

lemma N_gt_0: "N > 0"
  using Proc_def proc_0 by auto

theorem reachable_safe: "reachable st \<Longrightarrow> safe st"
proof (induction rule: reachable.induct)
  case (y_step st i)
  show ?case
  proof (cases "Proc i")
    case True
    show ?thesis
    proof (cases "\<exists>j. Proc j \<and> j \<noteq> i \<and> pc st j \<noteq> finished")
      case True
      thus ?thesis
        by (auto simp: safe_def)
    next
      case False
      have "x st ((i + 1) mod N) = 1"
      proof -
        from y_step have "Proc ((i + 1) mod N)"
          using N_gt_0 by (simp add: Proc_def)
        moreover from this have "pc st ((i + 1) mod N) \<noteq> assign_x"
          using False y_step by auto
        ultimately show "x st ((i + 1) mod N) = 1"
          using x_assigned y_step by auto
      qed
      thus ?thesis
        using \<open>Proc i\<close> by (auto simp: safe_def)
    qed
  qed (use y_step in \<open>auto simp: safe_def\<close>)
qed (use proc_0 in \<open>auto simp: safe_def\<close>)

end