import .defs

namespace concurrency

def indinv (st : state) :=
safe st ∧
(∀ i, (st.pc i = pc_label.assign_y ∨ st.pc i = pc_label.finished) → st.x i = 1)

lemma reachable_indinv (st : state) :
  reachable st → indinv st :=
begin
  intro h,
  induction h; dsimp [indinv,safe] at *,
  { split,
    { intros h, cases (h 0) },
    intros, casesm* [_ ∨ _, _ = _] },
  { cases h_ih, split,
    { intros, specialize a h_i, simp [update] at a, contradiction, },
    { intros, simp [update], split_ifs; simp [update,h] at a ⊢,
      solve_by_elim } },
  { cases h_ih, split,
    { intros, clear h_ih_left,
      simp [update], use h_i, simp,
      specialize (a (h_i + 1)), simp [update] at a,
      apply h_ih_right, split_ifs at a,
      { rw [← h,h_a_1],
        left, refl },
      { rw a, right, refl } },
    { intros, apply h_ih_right,
      simp [update] at a, split_ifs at a,
      { subst h, tauto! },
      { exact a } } },
end

theorem reachable_safe (st : state) (h : reachable st) : safe st :=
(reachable_indinv st h).1

-- theorem reachable_safe : ∀ (st : state) (h : reachable st), safe st :=
-- sorry

end concurrency
