theory Submission
  imports Defs
begin

definition indinv where
  "indinv st \<equiv> safe st \<and> (\<forall>i. Proc i \<longrightarrow> (pc st i = assign_y \<or> pc st i = finished) \<longrightarrow> x st i = 1)"

lemma Proc_mod :
  "\<forall> i. Proc i \<longrightarrow> Proc ((i + 1) mod N)"
  unfolding Proc_def by auto

lemma reachable_indinv :
  "indinv st" if "reachable st"
  using that
proof induction
  case (init init_x init_y)
  then show ?case
    using proc_0 by (auto simp: indinv_def safe_def)
next
  case (x_step st i)
  then show ?case
    by (auto simp: indinv_def safe_def update_x_def update_pc_def)
next
  case (y_step st i)
  then show ?case
    apply (auto simp: indinv_def safe_def update_y_def update_pc_def)
     apply (metis Proc_mod Suc_eq_plus1)+
    done
qed

theorem reachable_safe :
  "safe st" if "reachable st"
  using reachable_indinv[OF that] unfolding indinv_def ..

end