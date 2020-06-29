theory Submission
imports Defs
begin

subsection \<open>Some auxiliary lemmas on lists\<close>

lemma takeWhile_replicate_append:
  "takeWhile P (replicate n x @ ys) = (if P x \<or> n = 0 then replicate n x @ takeWhile P ys else [])"
  by (induction n) auto

lemma dropWhile_replicate_append:
  "dropWhile P (replicate n x @ ys) = (if P x \<or> n = 0 then dropWhile P ys else replicate n x @ ys)"
  by (induction n) auto

lemma takeWhile_NilI:
  assumes "xs = [] \<or> \<not>P (hd xs)"
  shows   "takeWhile P xs = []"
  using assms by (cases xs) auto

lemma dropWhile_selfI:
  assumes "xs = [] \<or> \<not>P (hd xs)"
  shows   "dropWhile P xs = xs"
  using assms by (cases xs) auto


subsection \<open>Lists with distinct adjoint elements\<close>

fun distinct_adj
  where "distinct_adj [] = True" |
        "distinct_adj [_] = True" |
        "distinct_adj (x # y # xs) \<longleftrightarrow> x \<noteq> y \<and> distinct_adj (y # xs)"

lemma distinct_adj_ConsI:
  assumes "xs = [] \<or> x \<noteq> hd xs" "distinct_adj xs"
  shows   "distinct_adj (x # xs)"
  using assms by (cases xs) auto

lemma distinct_adj_Cons: "distinct_adj (x # xs) \<longleftrightarrow> xs = [] \<or> x \<noteq> hd xs \<and> distinct_adj xs"
  by (cases xs) auto

lemma distinct_adj_append:
  assumes "xs = [] \<or> ys = [] \<or> last xs \<noteq> hd ys" "distinct_adj xs" "distinct_adj ys"
  shows   "distinct_adj (xs @ ys)"
  using assms
  by (induction xs rule: distinct_adj.induct)
     (auto split: if_splits intro!: distinct_adj_ConsI)

lemma distinct_adj_rev: "distinct_adj xs \<Longrightarrow> distinct_adj (rev xs)"
proof (induction xs)
  case (Cons x xs)
  show ?case using Cons
    by (cases "xs = []") (auto intro!: distinct_adj_append simp: last_rev distinct_adj_Cons)
qed auto


subsection \<open>Reversing run-length encoding\<close>

definition unrle where "unrle = concat \<circ> map (\<lambda>(x, n). replicate n x)"

lemma unrle_Nil [simp]: "unrle (xs @ ys) = unrle xs @ unrle ys"
  by (simp add: unrle_def)

lemma unrle_append [simp]: "unrle [] = []"
  by (simp add: unrle_def)

lemma unrle_Cons [simp]: "unrle ((x, n) # xs) = replicate n x @ unrle xs"
  by (simp add: unrle_def)

lemma unrle_rev [simp]: "unrle (rev xs) = rev (unrle xs)"
  by (induction xs) auto


subsection \<open>Valid RLE encodings\<close>

definition valid
  where "valid xs \<longleftrightarrow> distinct_adj (map fst xs) \<and> 0 \<notin> snd ` set xs"

lemma valid_append:
  assumes "xs = [] \<or> ys = [] \<or> fst (last xs) \<noteq> fst (hd ys)" "valid xs" "valid ys"
  shows   "valid (xs @ ys)"
  using assms unfolding valid_def
  by (auto intro!: distinct_adj_append simp: hd_map last_map)

lemma valid_rev: "valid xs \<Longrightarrow> valid (rev xs)"
  using distinct_adj_rev[of "map fst xs"]
  by (auto simp: valid_def rev_map)


subsection \<open>Correctness of \<^const>\<open>unrle\<close>\<close>

lemma hd_rle: "xs \<noteq> [] \<Longrightarrow> hd (rle xs) = (hd xs, length (takeWhile (\<lambda>y. y = hd xs) xs))"
  by (cases xs) auto

lemma rle_eq_Nil_iff [simp]: "rle xs = [] \<longleftrightarrow> xs = []"
  by (cases xs) auto

lemma distinct_adj_rle: "distinct_adj (map fst (rle xs))"
  by (induction xs rule: rle.induct)
     (use hd_dropWhile in \<open>force intro!: distinct_adj_ConsI simp: hd_map hd_rle\<close>)+

lemma fst_hd_rle [simp]: "xs \<noteq> [] \<Longrightarrow> fst (hd (rle xs)) = hd xs"
  by (cases xs) auto

lemma fst_last_rle [simp]: "xs \<noteq> [] \<Longrightarrow> fst (last (rle xs)) = last xs"
  by (induction xs rule: rle.induct) (use last_in_set in \<open>force simp: dropWhile_last\<close>)+

lemma snd_rle_pos: "0 \<notin> snd ` set (rle xs)"
  by (induction xs rule: rle.induct) auto

lemma valid_rle [intro]: "valid (rle xs)"
  unfolding valid_def using distinct_adj_rle[of xs] snd_rle_pos[of xs]
  by auto

lemma hd_unrle:
  assumes "xs \<noteq> []" "valid xs"
  shows   "hd (unrle xs) = fst (hd xs)"
  using assms by (cases xs) (auto simp: valid_def unrle_def distinct_adj_Cons)

lemma unrle_eq_Nil_iff [simp]:
  assumes "valid xs"
  shows   "unrle xs = [] \<longleftrightarrow> xs = []"
proof (cases xs) 
  case (Cons xn xs')
  obtain x n where [simp]: "xn = (x, n)"
    by (cases xn) auto
  from assms have "n > 0"
    by (auto simp: valid_def Cons)
  thus ?thesis
    by (auto simp: Cons)
qed auto

lemma unrle_rle [simp]: "unrle (rle xs) = xs"
proof (induction xs rule: rle.induct)
  case (2 x xs)
  have "unrle (rle (x # xs)) =
          x # replicate (length (takeWhile (\<lambda>y. y = x) xs)) x @ dropWhile (\<lambda>y. y = x) xs"
    using 2 by simp
  also have "replicate (length (takeWhile (\<lambda>y. y = x) xs)) x = takeWhile (\<lambda>y. y = x) xs"
    by (induction xs) auto
  also have "\<dots> @ dropWhile (\<lambda>y. y = x) xs = xs"
    by simp
  finally show ?case .
qed auto

lemma rle_unrle: "rle (unrle xs) = xs" if "valid xs"
  using that
proof (induction xs)
  case (Cons xn xs)
  obtain x n where [simp]: "xn = (x, n)" by (cases xn) auto
  have "valid xs"
    using Cons(2) by (auto simp: valid_def distinct_adj_Cons)
  from Cons have "n > 0"
    by (auto simp: valid_def)
  have "rle (unrle (xn # xs)) = rle (replicate n x @ unrle xs)"
    by simp
  also have "replicate n x = x # replicate (n - 1) x"
    using \<open>n > 0\<close> by (cases n) auto
  also have "rle (\<dots> @ unrle xs) =
               (x, Suc (length (takeWhile (\<lambda>y. y = x) (replicate (n - Suc 0) x @ unrle xs)))) #
               rle (dropWhile (\<lambda>y. y = x) (replicate (n - Suc 0) x @ unrle xs))"
    by simp
  also have "takeWhile (\<lambda>y. y = x) (replicate (n - Suc 0) x @ unrle xs) =
             replicate (n - Suc 0) x @ takeWhile (\<lambda>y. y = x) (unrle xs)"
    by (simp add: takeWhile_replicate_append)
  also have "dropWhile (\<lambda>y. y = x) (replicate (n - Suc 0) x @ unrle xs) = dropWhile (\<lambda>y. y = x) (unrle xs)"
    by (simp add: dropWhile_replicate_append)
  also have *: "x \<noteq> fst (hd xs)" if "xs \<noteq> []"
    using Cons that by (auto simp: valid_def distinct_adj_Cons hd_map)
  hence "takeWhile (\<lambda>y. y = x) (unrle xs) = []"
    using \<open>valid xs\<close>
    by (intro takeWhile_NilI) (auto simp: hd_unrle)
  also have "Suc (length (replicate (n - Suc 0) x @ [])) = n"
    using \<open>n > 0\<close> by simp
  also have "dropWhile (\<lambda>y. y = x) (unrle xs) = unrle xs"
    using \<open>valid xs\<close> * by (intro dropWhile_selfI) (auto simp: hd_unrle)
  also have "rle (unrle xs) = xs"
    by (intro Cons.IH) fact
  finally show ?case by simp
qed auto

lemma rle_unique:
  assumes "unrle ys = xs" and "valid ys"
  shows   "rle xs = ys"
  using rle_unrle assms by blast    


subsection \<open>Main proofs\<close>

lemma rle_append: "xs = [] \<or> ys = [] \<or> last xs \<noteq> hd ys \<Longrightarrow> rle (xs @ ys) = rle xs @ rle ys"
  by (rule rle_unique) (auto intro!: valid_append)

lemma rle_rev [simp]: "rle (rev xs) = rev (rle xs)"
  by (rule rle_unique) (auto intro: valid_rev)

(* Given the append lemma show the reverse lemma - gives 70% of the points.
   Note: While this lemma gives more points, it might actually be easier to prove *)
lemma rle_rev_if_rle_append: "(xs = [] \<or> ys = [] \<or> last xs \<noteq> hd ys \<Longrightarrow> rle (xs @ ys) = rle xs @ rle ys)
       \<Longrightarrow> rle (rev xs) = rev (rle xs)"
  by simp

end