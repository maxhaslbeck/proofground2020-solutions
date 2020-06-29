theory Submission
  imports Defs
begin

record p_state =
  p_pc :: "pc_label"
  p_x  :: "nat"
  p_y  :: "nat"


definition get_p_state where
  "get_p_state s p \<equiv> \<lparr>
  p_pc = pc s p, p_x = x s p, p_y = y s p\<rparr>" 

lemma n_pos: "N \<ge> 1"
  using proc_0
  by (auto simp add: Proc_def)

lemma possible_states:
  assumes "reachable st"
    and "N > 1"
  shows "(\<forall>p. let ps = get_p_state st p in
     (\<exists>x y. ps = \<lparr>p_pc = assign_x, p_x = x, p_y = y\<rparr>)
  \<or> (\<exists>y. ps = \<lparr>p_pc = assign_y, p_x = 1, p_y = y\<rparr>)
  \<or> (\<exists>y. ps = \<lparr>p_pc = finished, p_x = 1, p_y = y\<rparr>))
      \<and> safe st"
  using \<open>reachable st\<close>
proof induct
  case (init init_x init_y)
  then show ?case
    using proc_0 by (auto simp add: Let_def get_p_state_def safe_def)
next
  case (x_step st i)
  then show ?case
    using proc_0 by (auto simp add: Let_def get_p_state_def safe_def update_x_def update_pc_def)
next
  case (y_step st i)
  show ?case 
  proof (cases "\<forall>p. Proc p \<longrightarrow> p\<noteq>i \<longrightarrow> pc st p = finished")
    case True
      \<comment> \<open>If all others are finished, then we must have a 1 for y.\<close>
    hence "pc st (Suc i mod N) = finished" 
      using `N > 1`
      by (metis Proc_def less_le_trans mod_Suc mod_less_divisor mod_mod_trivial mod_self n_not_Suc_n n_pos nat_neq_iff zero_less_one)

    hence h1: "x st (Suc i mod N) = 1" 
      using y_step.hyps proc_0  
      by (auto simp add: Let_def get_p_state_def safe_def update_x_def update_pc_def update_y_def)
        force+





    from `pc st i = assign_y`
    have "x st i = Suc 0"
      using y_step.hyps
      by (auto simp add: Let_def get_p_state_def)
        force

    show ?thesis
    proof (intro conjI allI)
      show "safe (update_y (update_pc st i finished) i (x st ((i + 1) mod N)))"
        by (auto simp add: safe_def update_y_def update_pc_def)
          (metis One_nat_def h1 safe_def y_step.hyps(2))

      show "let ps = get_p_state (update_y (update_pc st i finished) i (x st ((i + 1) mod N))) p
        in (\<exists>x y. ps = \<lparr>p_pc = assign_x, p_x = x, p_y = y\<rparr>) \<or>
           (\<exists>y. ps = \<lparr>p_pc = assign_y, p_x = 1, p_y = y\<rparr>) \<or> (\<exists>y. ps = \<lparr>p_pc = finished, p_x = 1, p_y = y\<rparr>)" for p
      proof (cases "p = i")
        case True
        then show ?thesis 
          using n_pos True h1 by (auto simp add:  \<open>x st i = Suc 0\<close> Let_def get_p_state_def safe_def update_x_def update_pc_def update_y_def)
      next
        case False
        then show ?thesis 
          using y_step.hyps
          by (auto simp add: get_p_state_def update_y_def update_pc_def)
      qed
    qed
  next
    case False
    from this obtain pu
      where "pc st pu \<noteq> finished" and "pu \<noteq> i" and "Proc pu"
      by blast


    show ?thesis 
    proof (intro conjI allI)
      show "safe (update_y (update_pc st i finished) i (x st ((i + 1) mod N)))"
        using Proc_def \<open>Proc pu\<close> \<open>pc st pu \<noteq> finished\<close> \<open>pu \<noteq> i\<close>
        by (auto simp add: safe_def update_y_def update_pc_def Proc_def)

      show "let ps = get_p_state (update_y (update_pc st i finished) i (x st ((i + 1) mod N))) p
         in (\<exists>x y. ps = \<lparr>p_pc = assign_x, p_x = x, p_y = y\<rparr>) \<or>
            (\<exists>y. ps = \<lparr>p_pc = assign_y, p_x = 1, p_y = y\<rparr>) \<or> (\<exists>y. ps = \<lparr>p_pc = finished, p_x = 1, p_y = y\<rparr>)"
        for p
        using y_step.hyps False
        by (auto simp add: get_p_state_def update_y_def update_pc_def safe_def Proc_def)
          force+
    qed
  qed
qed

lemma possible_states_n1:
  assumes "reachable st"
    and "N = 1"
  shows "(let ps = get_p_state st 0 in
     (\<exists>x y. ps = \<lparr>p_pc = assign_x, p_x = x, p_y = y\<rparr>)
  \<or> (\<exists>y. ps = \<lparr>p_pc = assign_y, p_x = 1, p_y = y\<rparr>)
  \<or> (\<exists>y. ps = \<lparr>p_pc = finished, p_x = 1, p_y = y\<rparr>))
      \<and> safe st"
  using \<open>reachable st\<close>
proof induct
  case (init init_x init_y)
  then show ?case using proc_0 by (auto simp add: Let_def get_p_state_def safe_def)
next
  case (x_step st i)
  then show ?case using proc_0 by (auto simp add: Let_def get_p_state_def safe_def update_x_def update_pc_def)
next
  case (y_step st i)



  show ?case 
  proof (cases "i=0")
    case True

    have "x st 0 = 1"
      by (metis One_nat_def True get_p_state_def p_state.iffs pc_label.distinct(1) y_step.hyps(2) y_step.hyps(3))


    show ?thesis 
      using proc_0
      by (auto simp add: `N = 1` `i=0` `x st 0 = 1` Let_def get_p_state_def safe_def update_x_def update_pc_def update_y_def)
  next
    case False
    then show ?thesis
      using proc_0 y_step.hyps(2)
      by (auto simp add: `N = 1`   Let_def get_p_state_def safe_def update_x_def update_pc_def update_y_def)
  qed
qed

theorem reachable_safe :
  "safe st" if "reachable st"
proof (cases "N = 1")
  case True
  then show ?thesis
    by (simp add: possible_states_n1 that)
next
  case False
  then show ?thesis
    using n_pos possible_states that by auto
qed

end