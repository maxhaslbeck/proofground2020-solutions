theory Submission
  imports Defs "HOL-Library.Sublist"
begin

lemma subseq_only_if: "xs \<sqsubseteq> ys \<Longrightarrow> Sublist.subseq xs ys"
  by (induction xs ys rule: subseq.induct) auto

lemma subseq_if: "Sublist.subseq xs ys \<Longrightarrow> xs \<sqsubseteq> ys"
  by (induction xs ys rule: list_emb.induct) auto

lemma subseq_eq: "xs \<sqsubseteq> ys \<longleftrightarrow> Sublist.subseq xs ys"
  using subseq_only_if subseq_if
  by auto

lemma strict_subseq_eq: "xs \<sqsubset> ys \<longleftrightarrow> Sublist.strict_subseq xs ys"
  unfolding proper_subseq_def subseq_eq
  by auto

lemma aux_def: "aux xs ys \<longleftrightarrow> Sublist.subseq xs ys"
  by (induction xs ys rule: aux.induct) auto

lemma aux2_def: "aux2 ys zs xs \<longleftrightarrow> (\<forall>i < length xs. aux (zs @ take i xs @ drop (Suc i) xs) ys)"
proof (induction ys zs xs rule: aux2.induct)
  case (2 ys acc x xs)
  show ?case
    apply (auto simp: 2)
    subgoal for i
      by (cases i) auto
    done
qed auto

lemma strict_subseq_only_if: "Sublist.subseq xs ys \<Longrightarrow> xs \<noteq> ys \<Longrightarrow>
  \<exists>i < length ys. Sublist.subseq xs (take i ys @ drop (Suc i) ys)"
  by (induction xs ys rule: list_emb.induct) auto

lemma strict_subseq_if: "i < length ys \<Longrightarrow> Sublist.subseq xs (take i ys @ drop (Suc i) ys) \<Longrightarrow>
  Sublist.strict_subseq xs ys"
  by (auto simp: strict_subseq_def)
     (metis append_Nil append_take_drop_id drop_drop list_emb_Nil plus_1_eq_Suc subseq_append
      subseq_append' subseq_order.dual_order.trans)

lemma strict_subseq_iff: "Sublist.strict_subseq xs ys \<longleftrightarrow>
  (\<exists>i < length ys. Sublist.subseq xs (take i ys @ drop (Suc i) ys))"
  using strict_subseq_only_if strict_subseq_if
  unfolding strict_subseq_def
  by blast

theorem judge1_correct: "judge1 xs ys \<longleftrightarrow> all_proper_subseq xs ys"
  by (auto simp: judge1_def aux2_def aux_def all_proper_subseq_def subseq_eq strict_subseq_eq
      strict_subseq_iff)

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