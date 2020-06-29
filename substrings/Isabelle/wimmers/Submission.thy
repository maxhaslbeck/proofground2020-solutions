\<^marker>\<open>creator "Simon Wimmer"\<close>
theory Submission
  imports "HOL-Library.Sublist" Defs
begin

definition all_subseq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "all_subseq xs ys \<longleftrightarrow> (\<forall>xs'. xs' \<sqsubseteq> xs \<longrightarrow> xs' \<sqsubseteq> ys)"

lemma subseq_id:
  "subseq = Sublist.subseq"
  apply (intro ext)
  apply safe
  subgoal premises prems
    using prems by induction auto
  subgoal premises prems
    using prems by induction auto
    done

lemma proper_subseq_id:
  "proper_subseq = strict_subseq"
  unfolding proper_subseq_def strict_subseq_def subseq_id ..

lemmas subseq_ids = subseq_id proper_subseq_id

lemmas [termination_simp] = length_dropWhile_le

lemma subseq_empty_iff:
  "xs \<sqsubseteq> [] \<longleftrightarrow> xs = []"
  unfolding subseq_ids by auto

lemma [simp]:
  "all_subseq [] ys \<longleftrightarrow> True"
  "all_subseq (x # xs) [] \<longleftrightarrow> False"
  unfolding all_subseq_def by (auto simp: subseq_empty_iff)

lemma [simp]:
  "all_subseq (x # xs) (y # ys) \<longleftrightarrow> all_subseq (x # xs) ys" if "x \<noteq> y"
  using that by (auto simp: all_subseq_def subseq_ids)

lemma [simp]:
  "all_subseq (x # xs) (x # ys) \<longleftrightarrow> all_subseq xs ys"
  apply (auto simp: all_subseq_def subseq_ids)
  by (meson subseq_Cons2 subseq_order.dual_order.trans subseq_order.order_refl)

lemma aux_correct:
  "aux xs ys \<longleftrightarrow> all_subseq xs ys"
  by (induction rule: aux.induct; simp)

lemma strict_subseq_ConsE:
  assumes "a # as \<sqsubset> bs"
  obtains xs ys where "bs = xs @ a # ys" "xs \<noteq> []" "as \<sqsubseteq> ys" | ys where "bs = a # ys" "as \<sqsubset> ys"
  by (metis (full_types) assms list_emb_ConsD self_append_conv2 subseq_order.antisym_conv2
        subseq_order.dual_order.strict_implies_order subseq_ids)

lemma strict_subseqE:
  assumes "xs \<sqsubset> ys"
  obtains as x bs where "ys = as @ x # bs" and "xs \<sqsubseteq> as @ bs"
  using assms unfolding subseq_ids
  apply (induction xs arbitrary: ys)
  subgoal for ys
    apply (cases ys; force)
    done
  apply (erule strict_subseq_ConsE[unfolded subseq_ids])
   apply (metis append_Cons append_Nil list.exhaust list_emb_append2 subseq_Cons2_iff)
  by (metis append.simps(2) subseq_Cons2)

lemma all_proper_subseq_subdivide:
  "all_proper_subseq xs ys \<longleftrightarrow> (\<forall>as x bs. xs = as @ x # bs \<longrightarrow> all_subseq (as @ bs) ys)"
unfolding all_proper_subseq_def all_subseq_def subseq_ids
  apply auto
  apply (meson list_emb_Cons not_Cons_self2 same_append_eq subseq_append_iff
          subseq_order.dual_order.order_iff_strict subseq_order.le_less_trans)
  subgoal
    by (erule strict_subseqE[unfolded subseq_ids]) auto
  done

lemma aux2_iff:
  "aux2 ys acc xs \<longleftrightarrow> (\<forall>as x bs. xs = as @ x # bs \<longrightarrow> aux (acc @ as @ bs) ys)"
  apply (induction xs arbitrary: acc)
   apply auto
  subgoal
    by (smt Nil_is_append_conv append_eq_append_conv2 hd_Cons_tl hd_append2 list.sel(1) list.sel(3)
          tl_append2)
  apply force
  by (metis append_Cons)

lemma aux2_correct:
  "aux2 ys [] xs \<longleftrightarrow> all_proper_subseq xs ys"
  unfolding aux2_iff all_proper_subseq_subdivide aux_correct by simp

theorem judge1_correct: "judge1 xs ys \<longleftrightarrow> all_proper_subseq xs ys"
  unfolding judge1_def aux2_correct by auto


definition
  "judge2 xs ys \<longleftrightarrow> judge1 xs ys"

theorem judge2_correct:
  "judge2 xs ys \<longleftrightarrow> all_proper_subseq xs ys"
  unfolding judge2_def by (rule judge1_correct)

theorem judge2_is_executable:
  "judge2 ''ab'' ''ab'' \<longleftrightarrow> True"
  "judge2 ''ba'' ''ab'' \<longleftrightarrow> True"
  "judge2 ''abcd'' ''cdabc'' \<longleftrightarrow> False"
  by eval+

end