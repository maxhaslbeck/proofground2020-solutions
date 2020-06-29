theory Submission
  imports Defs
begin

text \<open>Illustration:
\<open>n\<close>:        0 | 1 | 2  | 3
\<open>S(n)\<close>:     2 | 6 | 42 | 1806 = 42 * 43
\<open>pf(S(n)+1)\<close>: 3 | 7 | 43 | 13 (13 * 139 = 1807)
\<close>

lemma S_gt_1: "S n > 1"
  by (induction n) auto

lemma pf_is_factor:
  assumes "n > (1::nat)"
  shows   "pf n \<in> prime_factors n"
proof -
  have "prime_factors n \<noteq> {}"
    using assms by (auto simp: prime_factorization_empty_iff)
  from Min_in[OF _ this, folded pf_def] have "pf n \<in> prime_factors n"
    by auto
  thus ?thesis by auto
qed

theorem prime_pf_Suc_S: "prime (pf (S n + 1))"
  using pf_is_factor[of "S n + 1"] S_gt_1[of n] by auto

lemma S_dvd:
  assumes "m < n"
  shows   "(S m + 1) dvd S n"
  using assms
proof (induction n)
  case (Suc n)
  show ?case
  proof (cases "m = n")
    case True
    thus ?thesis
      by (metis S.simps(2) dvd_triv_right)
  qed (use Suc.prems Suc.IH in auto)
qed (use assms in auto)
  
lemma coprime_S:
  assumes "m \<noteq> n"
  shows   "coprime (S m + 1) (S n + 1)"
  using assms
proof (induction m n rule: linorder_wlog)
  case (le m n)
  hence "(S m + 1) dvd S n"
    by (intro S_dvd) auto
  thus "coprime (S m + 1) (S n + 1)"
    by (metis coprime_add_one_right coprime_mult_left_iff dvd_def)
qed (auto simp: coprime_commute)

theorem pf_S_inj:
  assumes "pf (S n + 1) = pf (S m + 1)"
  shows "n = m"
proof (rule ccontr)
  assume "n \<noteq> m"
  define p where "p = pf (S n + 1)"
  have p1: "p \<in> prime_factors (S n + 1)"
    unfolding p_def using S_gt_1[of n] by (intro pf_is_factor) auto
  have p2: "p \<in> prime_factors (S m + 1)"
    unfolding p_def assms using S_gt_1[of m] by (intro pf_is_factor) auto
  hence "prime p" by auto

  from \<open>n \<noteq> m\<close> have "coprime (S m + 1) (S n + 1)"
    using coprime_S[of m n] by auto
  with p1 and p2 have "is_unit p"
    using not_coprimeI by blast
  with \<open>prime p\<close> show False
    using not_prime_unit by blast
qed

theorem infinitely_many_primes:
  "infinite {p :: nat. prime p}"
proof -
  let ?S = "(\<lambda>n. pf(S(n)+1)) ` UNIV" let ?P = "{p :: nat. prime p}"
  have "?S \<subseteq> ?P"
    using prime_pf_Suc_S by auto
  moreover have "infinite ?S"
    by (intro range_inj_infinite inj_onI, rule pf_S_inj)
  ultimately show ?thesis
    by (rule infinite_super)
qed

end