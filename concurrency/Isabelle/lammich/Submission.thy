theory Submission
  imports Defs
begin

definition "init st \<equiv> pc st = (\<lambda>_. assign_x)"

inductive step where
  xx_step: "step st (update_x (update_pc st i assign_y) i 1)" if "pc st i = assign_x"
| yy_step: "step st (update_y (update_pc st i finished) i (x st ((i + 1) mod N)))" if "pc st i = assign_y"


lemma 1: assumes "reachable st" shows "\<exists>st0. init st0 \<and> step\<^sup>*\<^sup>* st0 st"
  using assms apply induction
  apply (auto simp: init_def)
  subgoal
    by (meson rtranclp.rtrancl_refl select_convs(1))
  subgoal
    using xx_step by force
  subgoal 
    using yy_step by fastforce
  done  
  
lemma 2:
  assumes "step\<^sup>*\<^sup>* st0 st"  
  assumes "init st0"
  shows "reachable st"
  using assms  
  apply (induction rule: rtranclp_induct)
  subgoal
    unfolding init_def
    apply (cases st0)
    apply simp
    apply (rule init)
    done
  subgoal for y z
    by (metis step.cases x_step y_step)
  done  

lemma I1: 
  assumes "reachable st"
  shows "\<forall>i<N. (pc st i = finished \<or> pc st i = assign_y) \<longrightarrow> x st i = 1"
  using assms
  apply induction
  apply auto []
  subgoal for st
    apply (cases st)
    apply (auto simp: update_x_def update_y_def update_pc_def)
    done
    
  subgoal for st
    apply (cases st)
    apply (auto simp: update_x_def update_y_def update_pc_def)
    done
  done
  

theorem reachable_safe :
  "safe st" if R: "reachable st"
proof -
  from R obtain st0 where I: "init st0" and S: "step\<^sup>*\<^sup>* st0 st"
    using 1 by auto

  from S show ?thesis proof (induction)
    case base
    then show ?case using I
      by (auto simp: init_def safe_def intro: proc_0)
    
  next
    case (step b c)
    then show ?case unfolding safe_def
      apply (cases b; cases c)
      apply (auto simp: step.simps)
      apply (auto simp: update_x_def update_y_def update_pc_def split: if_split)
      apply (auto split: if_splits)
      apply (metis "2" I I1 One_nat_def Proc_def mod_less_divisor proc_0 simps(1) simps(2))
      by (metis "2" I I1 One_nat_def Proc_def mod_less_divisor proc_0 simps(1) simps(2))
  qed
qed  
  

end
