theory Optimized
  imports Defs
begin

(* Definitions *)

definition checker_suf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "checker_suf x x' xs y y' ys \<longleftrightarrow> (x = x' \<and> x = y' \<and> set xs \<subseteq> {x} \<and> set ys \<subseteq> {x}) \<or>
    (x \<noteq> x' \<and> x = y' \<and> y = x' \<and> set xs \<subseteq> {y} \<and> set ys \<subseteq> {y})"

lemma [code_unfold]: "set xs \<subseteq> {y} \<longleftrightarrow> list_all (\<lambda>x. x = y) xs"
  by (induction xs) auto

fun checker_go :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "checker_go _ [] [] = False"
| "checker_go z [x] [y] = (z = x)"
| "checker_go z (x # x' # xs) (y # y' # ys) = (if x \<noteq> z then False
    else if x = y then checker_go z (x' # xs) (y' # ys)
    else checker_suf x x' xs y y' ys)"
| "checker_go _ _ _ = False"

fun checker :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "checker [] [] = True"
| "checker (x # xs) (y # ys) = checker_go x (x # xs) (y # ys)"
| "checker _ _ = False"

definition judge :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "judge xs ys \<longleftrightarrow> xs \<noteq> ys \<and> length xs = length ys \<and> checker xs ys"

(* Task *)

theorem judge_correct: "judge xs ys \<longleftrightarrow> xs \<noteq> ys \<and> length xs = length ys \<and> all_proper_subseq xs ys"
  oops

(* Solution *)

lemma subseq_empty_iff[simp]:
  "xs \<sqsubseteq> [] \<longleftrightarrow> xs = []"
  by auto

lemma set_subseq: "xs \<sqsubseteq> ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<in> set ys"
  using notin_set_nthsI subseq_conv_nths
  by force

lemma repl_subseq:
  assumes "set ys \<subseteq> {y}"
  shows "xs \<sqsubseteq> ys \<longleftrightarrow> length xs \<le> length ys \<and> set xs \<subseteq> {y}"
proof (rule iffI)
  show "xs \<sqsubseteq> ys \<Longrightarrow> length xs \<le> length ys \<and> set xs \<subseteq> {y}"
    using assms list_emb_length set_subseq
    by (induction ys arbitrary: xs) force+
next
  show "length xs \<le> length ys \<and> set xs \<subseteq> {y} \<Longrightarrow> xs \<sqsubseteq> ys"
    using assms
  proof (induction xs arbitrary: ys)
    case (Cons x xs)
    then show ?case
      by (cases ys) auto
  qed auto
qed

lemma all_proper_subseq_singleI:
  assumes "set xs \<subseteq> {x}" "set ys \<subseteq> {x}" "length xs \<le> Suc (length ys)"
  shows "all_proper_subseq xs ys"
  unfolding all_proper_subseq_def strict_subseq_def
  by (meson Suc_leI assms leI le_antisym order.trans repl_subseq subseq_same_length)

lemma all_proper_subseqI: "(\<And>x xs'. x # xs' \<sqsubset> xs \<Longrightarrow> x # xs' \<sqsubseteq> ys) \<Longrightarrow> all_proper_subseq xs ys"
  by (auto simp: all_proper_subseq_def) (metis list.exhaust list_emb_Nil)

lemma all_proper_subseq_set:
  assumes "x \<noteq> y" "all_proper_subseq (x # ps) (y # ps)"
  shows "set ps \<subseteq> {x}"
  using assms
proof (induction ps)
  case (Cons p ps')
  have "x # ps' \<sqsubset> x # (p # ps')"
    by (auto simp: strict_subseq_def)
  then have p_def: "p = x"
    using Cons(2,3) list.sel(1)
    by (fastforce simp: all_proper_subseq_def)
  have "all_proper_subseq (x # ps') (y # ps')"
  proof (rule all_proper_subseqI)
    fix z zs
    assume sub: "z # zs \<sqsubset> x # ps'"
    then show "z # zs \<sqsubseteq> y # ps'"
    proof (cases "z = x")
      case True
      have "x # z # zs \<sqsubset> x # p # ps'"
        using sub
        by (auto simp: p_def strict_subseq_def)
      then have "x # z # zs \<sqsubseteq> y # x # ps'"
        using Cons(3) all_proper_subseq_def p_def
        by blast
      then show ?thesis
        by (auto simp: True)
    qed (meson list_emb_Cons strict_subseq_def subseq_Cons2_neq)
  qed
  then show ?case
    using p_def Cons
    by auto
qed auto

lemma all_proper_subseq_set':
  assumes "length xs = length ys" "x \<noteq> y" "all_proper_subseq (xs @ x # ps) (ys @ y # ps)"
  shows "set ps \<subseteq> {x}"
  using assms
proof (induction xs ys rule: list_induct2)
  case Nil
  then show ?case
    using all_proper_subseq_set
    by fastforce
next
  case (Cons z zs w ws)
  have "all_proper_subseq (zs @ x # ps) (ws @ y # ps)"
  proof (rule all_proper_subseqI)
    fix t ts
    assume "t # ts \<sqsubset> zs @ x # ps"
    then have "z # t # ts \<sqsubseteq> (w # ws) @ y # ps"
      using Cons(4)
      by (auto simp: all_proper_subseq_def strict_subseq_def)
    then show "t # ts \<sqsubseteq> ws @ y # ps"
      by (auto simp add: subseq_Cons' split: if_splits)
  qed
  then show ?case
    using Cons
    by auto
qed

lemma all_proper_subseq_Cons_eq:
  assumes "length xs = length ys" "x \<noteq> y" "all_proper_subseq (x # x' # xs) (y # y' # ys)"
  shows "y' # ys = x # xs"
proof -
  have "x # xs \<sqsubset> x # x' # xs"
    by (auto simp: strict_subseq_def)
  then have "x # xs \<sqsubseteq> y # y' # ys"
    using assms(2,3) subseq_Cons2_neq
    by (fastforce simp: all_proper_subseq_def)
  then show "y' # ys = x # xs"
    using assms(1,2) subseq_Cons2_neq subseq_same_length
    by fastforce
qed

lemma all_proper_subseq_eqD:
  assumes "x \<noteq> y" "all_proper_subseq (x # x # xs) (y # x # xs)"
  shows "set xs \<subseteq> {x}"
  using all_proper_subseq_set assms
  by fastforce

lemma all_proper_subseq_eq:
  assumes "length xs = length ys" "x \<noteq> y" "all_proper_subseq (x # x # xs) (y # y' # ys)"
  shows "x = y' \<and> set xs \<subseteq> {x} \<and> set ys \<subseteq> {x}"
proof -
  note y'_ys_def = all_proper_subseq_Cons_eq[OF assms]
  show ?thesis
    using all_proper_subseq_eqD[OF assms(2) assms(3)[unfolded y'_ys_def]] y'_ys_def
    by auto
qed

lemma checker_suf_eqD:
  assumes "length xs = length ys" "x \<noteq> y" "x = y'" "set xs \<subseteq> {x}" "set ys \<subseteq> {x}"
  shows "all_proper_subseq (x # x # xs) (y # y' # ys)"
proof -
  have ys_def: "ys = xs"
    using assms(1,4,5)
    by (induction xs ys rule: list_induct2) auto
  have "all_proper_subseq (x # x # xs) (y' # ys)"
    apply (rule all_proper_subseq_singleI)
    using assms(4)
    by (auto simp: assms(3) ys_def all_proper_subseq_def)
  then show ?thesis
    by (auto simp: all_proper_subseq_def)
qed

lemma all_proper_subseq_neqD:
  assumes "x \<noteq> y" "all_proper_subseq (x # x' # xs) (y # x # xs)" "x \<noteq> x'"
  shows "set xs \<subseteq> {x'}"
  using all_proper_subseq_set'[OF _ assms(3)[symmetric], of "[x]" "[y]" xs] assms
  by auto

lemma all_proper_subseq_neq:
  assumes "length xs = length ys" "x \<noteq> y" "all_proper_subseq (x # x' # xs) (y # y' # ys)" "x \<noteq> x'"
  shows "x = y' \<and> y = x' \<and> set xs \<subseteq> {y} \<and> set ys \<subseteq> {y}"
proof -
  note y'_ys_def = all_proper_subseq_Cons_eq[OF assms(1,2,3)]
  then have y'_def: "y' = x"
    by auto
  have "x' # xs \<sqsubset> x # x' # xs"
    by (auto simp: strict_subseq_def)
  then have y_def: "y = x'"
    using assms(3,4) subseq_Cons2_neq
    by (fastforce simp: y'_ys_def all_proper_subseq_def)
  have ys_def: "ys = xs"
    using y'_ys_def
    by auto
  show ?thesis
    using all_proper_subseq_neqD[OF assms(2) assms(3)[unfolded y'_ys_def] assms(4)]
    by (auto simp: y'_def y_def ys_def)
qed

lemma all_proper_subseq_singleI':
  assumes "set xs \<subseteq> {x'}"
  shows "all_proper_subseq (x # x' # xs) (x' # x # xs)"
proof (rule all_proper_subseqI)
  fix z zs
  assume sub: "z # zs \<sqsubset> x # x' # xs"
  show "z # zs \<sqsubseteq> x' # x # xs"
  proof (cases "z = x")
    case True
    have "zs \<sqsubseteq> xs"
      using sub repl_subseq[of "x' # xs"] assms
      by (auto simp: True strict_subseq_def repl_subseq[OF assms])
         (metis le_SucE length_Cons subseq_same_length)
    then show ?thesis
      by (auto simp: True)
  next
    case False
    then have "z # zs \<sqsubseteq> x' # xs"
      using sub
      by (auto simp: strict_subseq_def)
    then show ?thesis
      by (metis list_emb_Cons subseq_Cons2 subseq_Cons2' subseq_Cons2_neq)
  qed
qed

lemma checker_suf_neqD:
  assumes "length xs = length ys" "x \<noteq> y" "x \<noteq> x'" "set xs \<subseteq> {x'}" "set ys \<subseteq> {x'}"
  shows "all_proper_subseq (x # x' # xs) (x' # x # ys)"
proof -
  have ys_def: "ys = xs"
    using assms(1,4,5)
    by (induction xs ys rule: list_induct2) auto
  show "all_proper_subseq (x # x' # xs) (x' # x # ys)"
    unfolding ys_def
    by (rule all_proper_subseq_singleI'[OF assms(4)])
qed

lemma all_proper_subseq_ext:
  assumes "all_proper_subseq (x # xs') (y # ys')" "set ps \<subseteq> {x}"
  shows "all_proper_subseq (ps @ x # xs') (ps @ y # ys')"
proof -
  {
    fix zs
    assume sub: "zs \<sqsubset> ps @ x # xs'"
    then obtain ws ws' where split: "zs = ws @ ws'" "ws \<sqsubseteq> ps" "ws' \<sqsubseteq> x # xs'"
      using subseq_appendE[of zs ps "x # xs'"]
      by (auto simp: strict_subseq_def)
    then have "zs \<sqsubseteq> ps @ y # ys'"
      using assms(1)
    proof (cases "ws' = x # xs'")
      case True
      have "xs' \<sqsubseteq> y # ys'"
        using assms(1)
        by (auto simp: all_proper_subseq_def strict_subseq_def list_emb_Cons)
      moreover have "ws @ [x] \<sqsubseteq> ps"
        using sub
        by (auto simp: split(1) True strict_subseq_def repl_subseq[OF assms(2)])
           (meson assms(2) eq_iff not_less_eq_eq repl_subseq subseq_same_length)
      ultimately show ?thesis
        by (auto simp: split(1) True)
           (metis append.assoc append_Cons append_Nil list_emb_append_mono)
    qed (auto simp: split(1) all_proper_subseq_def strict_subseq_def list_emb_append_mono)
  }
  then show ?thesis
    by (auto simp: all_proper_subseq_def)
qed

lemma all_proper_subseq_cut:
  "all_proper_subseq (ps @ xs) (ps @ ys) \<Longrightarrow> all_proper_subseq xs ys"
  using subseq_append'
  by (auto simp: all_proper_subseq_def strict_subseq_def)

lemma subseq_rev: "xs \<sqsubseteq> ys \<Longrightarrow> rev xs \<sqsubseteq> rev ys"
  by (induction xs ys rule: list_emb.induct) auto

lemma all_proper_subseq_rev: "all_proper_subseq xs ys \<Longrightarrow> all_proper_subseq (rev xs) (rev ys)"
  by (auto simp: all_proper_subseq_def strict_subseq_def) (metis rev_swap subseq_rev)

lemma judge_correct_aux:
  assumes "xs \<noteq> ys" "length xs = length ys"
  shows "judge xs ys \<longleftrightarrow> all_proper_subseq xs ys"
proof -
  obtain ps x y xs' ys' where ps_def: "xs = ps @ x # xs'" "ys = ps @ y # ys'" "x \<noteq> y"
    using same_length_different[OF assms]
    by auto
  have len_xs'_ys': "length xs' = length ys'"
    using assms(2)
    by (auto simp: ps_def(1,2))
  show ?thesis
  proof (rule iffI)
    assume j: "judge xs ys"
    then have checker: "set ps \<subseteq> {x} \<and> checker_go x (x # xs') (y # ys')"
    proof (cases ps)
      case (Cons p ps')
      have checker: "checker_go p (ps @ x # xs') (ps @ y # ys')"
        using j
        by (auto simp: judge_def ps_def(1,2) Cons)
      have "checker_go p (x # xs') (y # ys') \<Longrightarrow> p = x"
        by (cases xs'; cases ys') (auto split: if_splits)
      then have "p = x"
        using checker
        by (induction ps rule: induct_list012) (auto split: if_splits)
      then show ?thesis
        using checker ps_def(3)
        by (induction ps rule: induct_list012) (auto split: if_splits)
    qed (auto simp: Nil judge_def ps_def(1,2))
    show "all_proper_subseq xs ys"
    proof (cases xs')
      case Nil
      have ys'_def: "ys' = []"
        using assms(2)
        by (auto simp: ps_def(1,2) Nil)
      have "all_proper_subseq (ps @ [x]) ps"
        apply (rule all_proper_subseq_singleI)
        using checker
        by auto
      then show ?thesis
        by (auto simp: ps_def(1,2) Nil ys'_def all_proper_subseq_def)
    next
      case (Cons x' xs'')
      obtain y' ys'' where ys'_def: "ys' = y' # ys''"
        using assms(2)
        by (cases ys') (auto simp: ps_def(1,2) Cons)
      have lens: "length xs'' = length ys''"
        using assms(2)
        by (auto simp: ps_def(1,2) Cons ys'_def)
      have "checker_suf x x' xs'' y y' ys''"
        using checker ps_def(3)
        by (auto simp: Cons ys'_def)
      then have "all_proper_subseq (x # x' # xs'') (y # y' # ys'')"
        using checker_suf_eqD[OF lens ps_def(3)] checker_suf_neqD[OF lens ps_def(3)]
        by (auto simp: checker_suf_def)
      then show ?thesis
        using all_proper_subseq_ext[OF _ conjunct1[OF checker]]
        by (auto simp: ps_def(1,2) Cons ys'_def)
    qed
  next
    assume all: "all_proper_subseq xs ys"
    have checker_go: "checker_go x (x # xs') (y # ys')"
      using assms(2)
    proof (cases xs')
      case (Cons x' xs'')
      obtain y' ys'' where ys'_def: "ys' = y' # ys''"
        using assms(2)
        by (cases ys') (auto simp: ps_def(1,2) Cons)
      have lens: "length xs'' = length ys''"
        using assms(2)
        by (auto simp: ps_def(1,2) Cons ys'_def)
      have all': "all_proper_subseq (x # x' # xs'') (y # y' # ys'')"
        using all_proper_subseq_cut all
        by (auto simp: ps_def(1,2) Cons ys'_def)
      have "checker_suf x x' xs'' y y' ys''"
        using all_proper_subseq_eq[OF lens ps_def(3)] all_proper_subseq_neq[OF lens ps_def(3)] all'
        by (cases "x = x'") (auto simp: checker_suf_def)
      then show ?thesis
        using ps_def(3)
        by (auto simp: Cons ys'_def)
    qed (auto simp: ps_def(1,2) Nil)
    have set_ps: "set ps \<subseteq> {x}"
      using all_proper_subseq_set'[OF _ ps_def(3), of "rev xs'" "rev ys'" "rev ps"]
        all_proper_subseq_rev len_xs'_ys' all
      by (fastforce simp: ps_def(1,2))
    have "checker xs ys"
      using checker_go
    proof (cases ps)
      case (Cons p ps')
      have p_def: "p = x"
        using set_ps
        by (auto simp: Cons)
      have "checker_go p xs ys"
        using checker_go set_ps
        unfolding ps_def(1,2) p_def
        by (induction ps rule: induct_list012) auto
      then show ?thesis
        by (auto simp: ps_def(1,2) Cons)
    qed (auto simp: ps_def(1,2))
    then show "judge xs ys"
      using assms
      by (auto simp: judge_def)
  qed
qed

theorem judge_correct: "judge xs ys \<longleftrightarrow> xs \<noteq> ys \<and> length xs = length ys \<and> all_proper_subseq xs ys"
  using judge_correct_aux
  by (auto simp: judge_def)

definition judge_string :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "judge_string = judge"

export_code judge_string String.explode in OCaml module_name Judge file_prefix optimized

end
