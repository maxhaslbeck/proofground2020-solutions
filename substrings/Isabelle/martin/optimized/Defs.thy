theory Defs
  imports "HOL-Library.Sublist"
begin

(* Definitions *)

notation subseq (infixr "\<sqsubseteq>" 50)

notation strict_subseq (infixr "\<sqsubset>" 50)

definition all_proper_subseq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "all_proper_subseq xs ys \<longleftrightarrow> (\<forall>xs'. xs' \<sqsubset> xs \<longrightarrow> xs' \<sqsubseteq> ys)"

end
