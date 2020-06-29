theory Submission
  imports Defs
begin

lemma S_ge_2:
  "S n \<ge> 2"
  by (induction n) auto

lemma prime_factors_nonempty:
  "prime_factors n \<noteq> {}" if "n > 1" for n :: nat
  by (metis less_trans neq_iff prime_factorization_1 prod_mset_prime_factorization_nat
        set_mset_eq_empty_iff that zero_less_one)

lemma pf_in_prime_factors[intro]:
  "pf n \<in> prime_factors n" if "n > 1" for n :: nat
  unfolding pf_def using prime_factors_nonempty[OF \<open>n > 1\<close>] by (intro Min_in) auto

lemma pf_S_in_prime_factors[simp, intro]:
  "pf (S n) \<in> prime_factors (S n)"
  using S_ge_2[of n] by auto


theorem prime_pf_Suc_S:
  "prime(pf(S(n)+1))"
  using S_ge_2[of n] by force


lemma prime_factors_subs:
  "prime_factors m \<subseteq> prime_factors (m * k)" if "0 < m" "0 < k" for m k :: nat
  using that by (intro dvd_prime_factors) auto

lemma prime_factors_S_Suc:
  "prime_factors (S m + 1) \<subseteq> prime_factors (S (m + 1))"
  using prime_factors_subs[of "S m + 1" "S m"] S_ge_2[of m] by simp

lemma prime_factors_S_le_subs:
  "prime_factors (S m + 1) \<subseteq> prime_factors (S n)" if "m < n"
  using that
  apply (induction n)
  apply simp
  subgoal for n
    apply (cases "m = n")
    using prime_factors_S_Suc
     apply simp
    apply simp
    apply (erule subset_trans)
    using prime_factors_subs[of "S n" "S n + 1"] S_ge_2[of n]
    apply simp
    done
  done

lemma prime_factors_int_Suc:
  "prime_factors n \<inter> prime_factors (n + 1) = {}" if "n > 0" for n :: nat
  by (metis add_eq_0_iff_both_eq_0 gcd_add2 inf_bot_right not_gr_zero prime_factorization_1
      prime_factors_gcd set_mset_empty that zero_neq_one)

lemma prime_factors_S_neq:
  "prime_factors (S m + 1) \<inter> prime_factors (S n + 1) = {}" if "m < n"
  using prime_factors_int_Suc[of "S n"] S_ge_2[of n] prime_factors_S_le_subs[OF \<open>m < n\<close>] by auto

lemma pf_S_inj_aux:
  assumes "pf(S(n)+1) = pf(S(m)+1)" "m < n"
  shows False
proof -
  have "pf(S(n)+1) \<in> prime_factors (S n + 1)" "pf(S(m)+1) \<in> prime_factors (S m + 1)"
    using S_ge_2[of n] S_ge_2[of m] by auto
  with prime_factors_S_neq[OF \<open>m < n\<close>] assms(1) show ?thesis
    by auto
qed


theorem pf_S_inj:
  assumes "pf(S(n)+1) = pf(S(m)+1)"
  shows "n = m"
  using pf_S_inj_aux assms by (metis less_linear)

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
