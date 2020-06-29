theory Submission
  imports Defs
begin

lemma N_pos: "\<exists>m. N = Suc m"
  using proc_0
  by (cases N) (auto simp: Proc_def)

lemma reach_aux: "reachable st \<Longrightarrow> (\<forall>i. Proc i \<longrightarrow> pc st i \<noteq> assign_x \<longrightarrow> x st i = 1)"
  by (induction st rule: reachable.induct)
     (auto simp: update_x_def update_pc_def update_y_def)

theorem reachable_safe: "reachable st \<Longrightarrow> safe st"
proof (induction st rule: reachable.induct)
  case (init init_x init_y)
  then show ?case
    using proc_0
    by (auto simp: safe_def)
next
  case (x_step st i)
  then show ?case
    by (auto simp: safe_def update_x_def update_pc_def)
next
  case (y_step st i)
  show ?case
  proof (cases "Proc i")
    case True
    define j where "j = (i + 1) mod N"
    show ?thesis
      unfolding safe_def j_def[symmetric]
    proof (rule impI)
      assume assm: "\<forall>k. Proc k \<longrightarrow> pc (update_y (update_pc st i finished) i (x st j)) k = finished"
      obtain m where m_def: "N = Suc m"
        using N_pos
        by auto
      have proc_j: "Proc j"
        by (auto simp: j_def m_def Proc_def)
      have pc_j: "pc st j \<noteq> assign_x"
        using assm proc_j y_step(2)
        by (auto simp: update_y_def update_pc_def split: if_splits)
      have x_j: "x st j = 1"
        using reach_aux[OF y_step(1)] proc_j pc_j
        by auto
      show "\<exists>k. Proc k \<and> y (update_y (update_pc st i finished) i (x st j)) k = 1"
        using x_j True
        unfolding update_y_def update_pc_def
        by (auto simp: j_def)
    qed
  next
    case False
    then show ?thesis
      using y_step
      by (auto simp: safe_def update_y_def update_pc_def)
  qed
qed

end