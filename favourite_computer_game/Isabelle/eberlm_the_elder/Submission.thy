theory Submission
imports Defs "HOL-Library.Sublist"
begin


subsection \<open>Some lemmas about \<^const>\<open>takeWhile\<close> and \<^const>\<open>dropWhile\<close>\<close>

(* TODO Move all of this *)
lemma takeWhile_eq_Nil [simp]: "xs = [] \<or> \<not>P (hd xs) \<Longrightarrow> takeWhile P xs = []"
  by (cases xs) auto

lemma dropWhile_eq_self [simp]: "xs = [] \<or> \<not>P (hd xs) \<Longrightarrow> dropWhile P xs = xs"
  by (cases xs) auto

lemma takeWhile_append3: "ys = [] \<or> \<not>P (hd ys) \<Longrightarrow> takeWhile P (xs @ ys) = takeWhile P xs"
  by (induction xs) auto

lemma takeWhile_append:
  "takeWhile P (xs @ ys) = (if \<forall>x\<in>set xs. P x then xs @ takeWhile P ys else takeWhile P xs)"
  using takeWhile_append1[of _ xs P ys] takeWhile_append2[of xs P ys] by auto

lemma takeWhile_replicate: "takeWhile P (replicate n x) = (if P x then replicate n x else [])"
  and dropWhile_replicate: "dropWhile P (replicate n x) = (if P x then [] else replicate n x)"
  by (induction n; simp)+

lemma takeWhile_replicate_True [simp]: "P x \<Longrightarrow> takeWhile P (replicate n x) = replicate n x"
  and takeWhile_replicate_False [simp]: "\<not>P x \<Longrightarrow> takeWhile P (replicate n x) = []"
  and dropWhile_replicate_True [simp]: "P x \<Longrightarrow> dropWhile P (replicate n x) = []"
  and dropWhile_replicate_False [simp]: "\<not>P x \<Longrightarrow> dropWhile P (replicate n x) = replicate n x"
  by (simp_all add: takeWhile_replicate dropWhile_replicate)

lemma takeWhile_replicate_append_True [simp]:
        "P x \<Longrightarrow> takeWhile P (replicate n x @ xs) = replicate n x @ takeWhile P xs"
  and takeWhile_replicate_append_False [simp]:
        "\<not>P x \<Longrightarrow> n > 0 \<Longrightarrow> takeWhile P (replicate n x @ xs) = []"
  and dropWhile_replicate_append_True [simp]:
        "P x \<Longrightarrow> dropWhile P (replicate n x @ xs) = dropWhile P xs"
  and dropWhile_replicate_append_False [simp]:
        "\<not>P x \<Longrightarrow> n > 0 \<Longrightarrow> dropWhile P (replicate n x @ xs) = replicate n x @ xs"
     by (induction n; simp; fail)+


subsection \<open>Applying a relation to successive elements in a list\<close>

inductive successively :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" for P where
  "successively P []"
| "successively P [x]"
| "P x y \<Longrightarrow> successively P (y # xs) \<Longrightarrow> successively P (x # y # xs)"

lemmas [simp, intro] = successively.intros(1,2)

lemma successively_Cons_Cons [simp]:
  "successively P (x # y # xs) \<longleftrightarrow> P x y \<and> successively P (y # xs)"
  by (subst successively.simps) auto

lemma successively_Cons:
  "successively P (x # xs) \<longleftrightarrow> xs = [] \<or> P x (hd xs) \<and> successively P xs"
  by (cases xs) auto

lemma successively_ConsI [intro]:
  "P x (hd xs) \<Longrightarrow> successively P xs \<Longrightarrow> successively P (x # xs)"
  by (auto simp: successively_Cons)

lemma successively_ConsD [dest]:
  "successively P (x # xs) \<Longrightarrow> successively P xs"
  by (auto simp: successively_Cons)

lemma successively_append_iff:
  "successively P (xs @ ys) \<longleftrightarrow>
     successively P xs \<and> successively P ys \<and> 
     (xs = [] \<or> ys = [] \<or> P (last xs) (hd ys))"
  by (induction xs) (auto simp: successively_Cons)

lemma
  assumes "successively P (xs @ ys)"
  shows   successively_appendD1 [dest]: "successively P xs"
    and   successively_appendD2 [dest]: "successively P ys"
  using assms by (auto simp: successively_append_iff)

lemma successively_appendI [intro?]:
  assumes "successively P xs" "successively P ys" "xs = [] \<or> ys = [] \<or> P (last xs) (hd ys)"
  shows   "successively P (xs @ ys)"
  using assms by (auto simp: successively_append_iff)

lemma successively_sublist:
  assumes "successively P ys" "sublist xs ys"
  shows   "successively P xs"
  using assms by (auto simp: sublist_def)

lemma sorted_wrt_imp_successively: "sorted_wrt P xs \<Longrightarrow> successively P xs"
  by (induction xs rule: induct_list012) auto

lemma successively_conv_sorted_wrt:
  assumes "\<And>x y z. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> z \<in> set xs \<Longrightarrow>
                   P x y \<Longrightarrow> P y z \<Longrightarrow> P x z"
  shows   "successively P xs \<longleftrightarrow> sorted_wrt P xs"
proof
  assume "successively P xs"
  from this and assms show "sorted_wrt P xs"
  proof (induction rule: successively.induct)
    case (3 x y xs)
    have IH: "sorted_wrt P (y # xs)"
      using "3.prems" unfolding set_simps(2)[of _ "y # xs"] by (intro "3.IH") blast
    have "P x z" if "z \<in> set xs" for z
    proof -
      from "3.hyps" have "P x y"
        by auto
      moreover from IH and that have "P y z"
        by auto
      ultimately show "P x z"
        using "3.prems" that by auto
    qed
    with IH and \<open>P x y\<close> show ?case by auto
  qed auto
qed (use sorted_wrt_imp_successively in blast)

lemma successively_conv_sorted_wrt':
  assumes "transp P"
  shows   "successively P xs \<longleftrightarrow> sorted_wrt P xs"
  using assms unfolding transp_def
  by (intro successively_conv_sorted_wrt) blast


subsection \<open>Lists without repeated adjacent elements\<close>

definition adj_distinct where
  "adj_distinct = successively (\<noteq>)"

lemmas adj_distinct_induct = successively.induct[of "(\<noteq>)", folded adj_distinct_def, consumes 1]

lemma adj_distinct_Nil [simp]: "adj_distinct []"
  and adj_distinct_singleton [simp]: "adj_distinct [x]"
  by (auto simp: adj_distinct_def)

lemma adj_distinct_Cons_Cons [simp]: "adj_distinct (x # y # xs) \<longleftrightarrow> x \<noteq> y \<and> adj_distinct (y # xs)"
  by (auto simp: adj_distinct_def)

lemma adj_distinct_Cons: "adj_distinct (x # xs) \<longleftrightarrow> xs = [] \<or> x \<noteq> hd xs \<and> adj_distinct xs"
  by (cases xs) auto

lemma adj_distinct_ConsI [intro?]: "x \<noteq> hd xs \<and> adj_distinct xs \<Longrightarrow> adj_distinct (x # xs)"
  by (cases xs) auto

lemma adj_distinct_ConsD1 [dest]: "adj_distinct (x # xs) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> x \<noteq> hd xs"
  by (cases xs) auto

lemma adj_distinct_ConsD2 [dest]: "adj_distinct (x # xs) \<Longrightarrow> adj_distinct xs"
  by (cases xs) auto

lemma adj_distinct_remdups_adj [intro]: "adj_distinct (remdups_adj xs)"
  by (induction xs rule: remdups_adj.induct) (auto simp: adj_distinct_Cons)

lemma adj_distinct_altdef: "adj_distinct xs \<longleftrightarrow> remdups_adj xs = xs"
proof
  assume eq: "remdups_adj xs = xs"
  have "adj_distinct (remdups_adj xs)"
    by blast
  with eq show "adj_distinct xs"
    by simp
next
  assume "adj_distinct xs"
  thus "remdups_adj xs = xs"
    by (induction rule: adj_distinct_induct) auto
qed

lemma adj_distinct_rev [simp]: "adj_distinct (rev xs) \<longleftrightarrow> adj_distinct xs"
  by (simp add: adj_distinct_altdef)

lemma adj_distinct_append_iff:
  "adj_distinct (xs @ ys) \<longleftrightarrow>
     adj_distinct xs \<and> adj_distinct ys \<and> (xs = [] \<or> ys = [] \<or> last xs \<noteq> hd ys)"
  by (auto simp: adj_distinct_def successively_append_iff)

lemma adj_distinct_appendD1 [dest]: "adj_distinct (xs @ ys) \<Longrightarrow> adj_distinct xs"
  and adj_distinct_appendD2 [dest]: "adj_distinct (xs @ ys) \<Longrightarrow> adj_distinct ys"
  by (auto simp: adj_distinct_append_iff)

lemma adj_distinct_sublist:
  assumes "adj_distinct ys" "sublist xs ys"
  shows   "adj_distinct xs"
  using assms by (auto simp: sublist_def)


subsection \<open>Run-length encoding\<close>

lemmas [termination_simp] = length_dropWhile_le

text \<open>
  The following function performs run-length encoding of a list, converting each run of \<open>n > 0\<close>
  successive equal elements \<open>x\<close> into a single element \<open>(x, n)\<close>.
\<close>

lemma length_rle: "length (rle xs) \<le> length xs"
  by (induction xs rule: rle.induct) (auto intro: order.trans[OF _ length_dropWhile_le])

lemma rle_eq_Nil_iff [simp]: "rle xs = [] \<longleftrightarrow> xs = []"
  by (cases xs) auto

lemma Nil_eq_rle_iff [simp]: "[] = rle xs \<longleftrightarrow> xs = []"
  by (cases xs) auto

lemma rle_replicate: "rle (replicate n x) = (if n = 0 then [] else [(x, n)])"
  by (cases n) auto

lemma rle_replicate' [simp]: "n > 0 \<Longrightarrow> rle (replicate n x) = [(x, n)]"
  by (subst rle_replicate) auto

lemma fst_hd_rle [simp]: "xs \<noteq> [] \<Longrightarrow> fst (hd (rle xs)) = hd xs"
  by (cases xs) auto

lemma map_fst_run_le [simp]: "map fst (rle xs) = remdups_adj xs"
  by (induction xs rule: remdups_adj.induct) auto

lemma fst_set_rle [simp]: "fst ` set (rle xs) = set xs"
proof -
  have "fst ` set (rle xs) = set (map fst (rle xs))"
    by (rule set_map [symmetric])
  also have "map fst (rle xs) = remdups_adj xs"
    by simp
  finally show ?thesis
    by simp
qed

lemma snd_rle_pos: "n \<in> snd ` set (rle xs) \<Longrightarrow> n > 0"
  by (induction xs rule: rle.induct) auto


text \<open>
  A valid run-length encoding contains no zero-length runs, and two adjacent runs always
  have a different element.
\<close>
definition valid_rle :: "('a \<times> nat) list \<Rightarrow> bool" where
  "valid_rle xs \<longleftrightarrow> 0 \<notin> snd ` set xs \<and> adj_distinct (map fst xs)"

lemma valid_rle_append_iff [intro]:
  "valid_rle (xs @ ys) \<longleftrightarrow>
     valid_rle xs \<and> valid_rle ys \<and> (xs = [] \<or> ys = [] \<or> fst (last xs) \<noteq> fst (hd ys))"
  by (auto simp: valid_rle_def adj_distinct_append_iff last_map hd_map)

lemma 
  assumes "valid_rle (xs @ ys)"
  shows valid_rle_appendD1 [dest]: "valid_rle xs"
    and valid_rle_appendD2 [dest]: "valid_rle ys"
  using assms by (auto simp: valid_rle_append_iff)

lemma valid_rle_ConsD [dest]: "valid_rle (x # xs) \<Longrightarrow> valid_rle xs"
  by (auto simp: valid_rle_def)

lemma valid_rle_rle [intro]: "valid_rle (rle xs)"
  using snd_rle_pos[of _ xs] by (auto simp: valid_rle_def)

lemma valid_rle_rev [simp]: "valid_rle (rev xs) \<longleftrightarrow> valid_rle xs"
  by (auto simp: valid_rle_def simp flip: rev_map)



text \<open>
  The inverse of the run-length encoding function:
\<close>
definition unrle
  where "unrle = concat \<circ> map (\<lambda>(x, n). replicate n x)"

lemma unrle_Nil [simp]: "unrle [] = []"
  and unrle_Cons [simp]: "unrle (x # xs) = replicate (snd x) (fst x) @ unrle xs"
  and unrle_append [simp]: "unrle (xs @ ys) = unrle xs @ unrle ys"
  and unrle_rev [simp]: "unrle (rev xs) = rev (unrle xs)"
  by (auto simp: unrle_def case_prod_unfold rev_concat rev_map o_def)

lemma unrle_eq_Nil_iff [simp]: "unrle xs = [] \<longleftrightarrow> snd ` set xs \<subseteq> {0}"
  by (induction xs) auto

lemma unrle_Nil_eq_iff [simp]: "Nil = unrle xs \<longleftrightarrow> snd ` set xs \<subseteq> {0}"
  by (induction xs) auto

lemma hd_unrle [simp]: "xs \<noteq> [] \<Longrightarrow> snd (hd xs) > 0 \<Longrightarrow> hd (unrle xs) = fst (hd xs)"
  by (cases xs) (auto simp: unrle_def)

lemma unrle_map_1 [simp]: "unrle (map (\<lambda>x. (x, Suc 0)) xs) = xs"
  by (induction xs) (auto simp: unrle_def o_def)


lemma unrle_rle [simp]: "unrle (rle xs) = xs"
proof (induction xs rule: rle.induct) 
  case (2 x xs)
  have "replicate (length (takeWhile (\<lambda>y. y = x) xs)) x = takeWhile (\<lambda>y. y = x) xs"
    by (induction xs) auto
  thus ?case
    using 2 by simp
qed auto

lemma rle_unrle [simp]:
  assumes "valid_rle xs"
  shows   "rle (unrle xs) = xs"
  using assms
proof (induction xs)
  case (Cons x' xs)
  obtain x n where [simp]: "x' = (x, n)"
    by (cases x')
  have [simp]: "n > 0" "n \<noteq> 0"
    using Cons.prems by (auto simp: valid_rle_def)
  show ?case
  proof (cases "xs = []")
    case [simp]: False
    have [simp]: "snd (hd xs) > 0" "x \<noteq> fst (hd xs)"
      using Cons.prems by (auto simp: valid_rle_def adj_distinct_Cons hd_map)
    have "takeWhile (\<lambda>y. y = x) (unrle xs) = []"
         "dropWhile (\<lambda>y. y = x) (unrle xs) = unrle xs"
      by (subst takeWhile_eq_Nil dropWhile_eq_self; force; fail)+
    hence "rle (replicate n x @ unrle xs) = (x, n) # rle (unrle xs)"
      by (cases n) auto
    thus ?thesis
      using Cons by (auto simp: valid_rle_def adj_distinct_Cons hd_unrle)
  qed auto
qed auto

text \<open>
  The \<^const>\<open>unrle\<close> function is injective on all valid run-length encodings
\<close>
lemma unrle_eqD [simp]:
  assumes "valid_rle xs" "valid_rle ys"
  assumes "unrle xs = unrle ys"
  shows   "xs = ys"
proof -
  have "rle (unrle xs) = rle (unrle ys)"
    by (simp add: assms(3))
  with assms(1,2) show ?thesis
    by (subst (asm) (1 2) rle_unrle) auto
qed

text \<open>
  The injectivity of \<^const>\<open>unrle\<close> allows us to show several properties of \<^const>\<open>rle\<close> more
  easily using the following lemma:
\<close>
lemma rle_eqI:
  assumes "valid_rle ys" "unrle ys = xs"
  shows "rle xs = ys"
  by (rule unrle_eqD) (use assms in auto)

lemma rle_rev [simp]: "rle (rev xs) = rev (rle xs)"
  by (rule rle_eqI) auto

lemma fst_last_rle [simp]: "xs \<noteq> [] \<Longrightarrow> fst (last (rle xs)) = last xs"
  by (simp flip: hd_rev rle_rev)

lemma rle_append:
  assumes "xs = [] \<or> ys = [] \<or> last xs \<noteq> hd ys"
  shows   "rle (xs @ ys) = rle xs @ rle ys"
  by (rule rle_eqI) (use assms in \<open>auto simp: valid_rle_append_iff\<close>)

lemma rle_of_adj_distinct: "adj_distinct xs \<Longrightarrow> rle xs = map (\<lambda>x. (x, 1)) xs"
  by (rule rle_eqI) (auto simp: valid_rle_def o_def)


lemma rle_rev_if_rle_append: "(xs = [] \<or> ys = [] \<or> last xs \<noteq> hd ys \<Longrightarrow> rle (xs @ ys) = rle xs @ rle ys)
       \<Longrightarrow>rle (rev xs) = rev (rle xs)"
  by (rule rle_eqI) auto


end