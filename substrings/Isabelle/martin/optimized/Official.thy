theory Official
  imports Defs
begin

(* Definitions *)

fun aux where
  "aux [] _ = True"
| "aux _ [] = False"
| "aux (x#xs) (y#ys) = (if x = y then aux xs ys else aux (x # xs) ys)"

fun aux2 where
  "aux2 ys acc [] = True"
| "aux2 ys acc (x # xs) \<longleftrightarrow> aux (acc @ xs) ys \<and> aux2 ys (acc @ [x]) xs"

definition
  "judge xs ys \<longleftrightarrow> aux2 ys [] xs"

(* Task *)

theorem judge_correct: "judge xs ys \<longleftrightarrow> all_proper_subseq xs ys"
  oops

(* Solution *)

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

theorem judge_correct: "judge xs ys \<longleftrightarrow> all_proper_subseq xs ys"
  by (auto simp: judge_def aux2_def aux_def all_proper_subseq_def strict_subseq_iff)

definition judge_string :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "judge_string = judge"

export_code judge_string String.explode in OCaml module_name Judge file_prefix official

end
