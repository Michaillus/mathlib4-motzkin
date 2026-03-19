import Mathlib

namespace MvPolynomial

theorem totalDegree_pow_eq {R : Type u} {σ : Type u_1} [CommSemiring R] [IsReduced R]
    (f : MvPolynomial σ R) (n : ℕ) : (f ^ n).totalDegree = n * f.totalDegree := by
  sorry

end MvPolynomial

open MvPolynomial

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

notation "⟨x" n "y" m "⟩" => (Finsupp.single 0 n + Finsupp.single 1 m)

noncomputable def motzkin : MvPolynomial (Fin 2) K :=
  (monomial ⟨x 4 y 2⟩ 1) + (monomial ⟨x 2 y 4⟩ 1) - (monomial ⟨x 2 y 2⟩ 3) + (monomial 0 1)

lemma motzkin_ne_sos {ι : Type*} (s : Finset ι) (g : ι → MvPolynomial (Fin 2) K) :
    motzkin ≠ ∑ i ∈ s, g i ^ 2 := by
  by_contra! h1

  have h2 {i : ι} (hi : i ∈ s) (m : _) (hm : (g i).coeff m ≠ 0) : m 0 + m 1 ≤ 3 := by
    rw [← mem_support_iff] at hm
    revert m
    rw [← Finset.sup_le_iff]
    revert i
    rw [← Finset.sup_le_iff]
    sorry
    
/-
    suffices h2 : (g i).totalDegree ≤ 3 by
      apply le_trans _ h2
      conv =>
        right; rw [totalDegree]; right; intro s
        simp [Finsupp.sum_of_support_subset s (Finset.subset_univ s.support)]
      apply Finset.le_sup (mem_support_iff.mpr hm)

    -- MvPolynomial.coeff_eq_zero_of_totalDegree_lt
    /- rw [← degreeOf_monomial_eq m 0 (by decide : 1 ≠ 0)] -/
    /- rw [← degreeOf_monomial_eq m 1 (by decide : 1 ≠ 0)] -/

    


    /- rw [← Nat.mul_le_mul_left_iff zero_lt_two, ← totalDegree_pow_eq] -/
    clear m hm
    revert i
    rw [← Finset.sup_le_iff]
    unfold totalDegree
    conv =>
      left; right; intro i; right; intro s
      simp [Finsupp.sum_of_support_subset s (Finset.subset_univ s.support)]
  -/


    /- simp only [totalDegree, Nat.reduceMul, Finset.sup_le_iff, mem_support_iff, ne_eq] -/
    /- intro i hi m hm -/
    /- push_neg at hm -/
    /- simp [Finsupp.sum_of_support_subset m (Finset.subset_univ m.support)] -/
    /- contrapose! hm -/

    /- have h2 : s.Nonempty := sorry -/
    /- obtain ⟨j, h3, h4⟩ := s.exists_mem_eq_sup h2 fun i ↦ (g i).totalDegree -/
    /- rw [h4] -/

  have h3 {i : ι} (hi : i ∈ s) (m : _) (hm : (g i).coeff m ≠ 0) : 0 < m 0 ↔ 0 < m 1 := by
    sorry

  let t : Set (Fin 2 →₀ ℕ) := {⟨x 2 y 1⟩, ⟨x 1 y 2⟩, ⟨x 1 y 1⟩, 0}
  have h4 : t = {m | m 0 + m 1 ≤ 3 ∧ (0 < m 0 ↔ 0 < m 1)} := by
    ext m
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, t]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      <;> simp 
    · rintro ⟨h4, h5⟩
      suffices (m 0 = 2 ∧ m 1 = 1) ∨ (m 0 = 1 ∧ m 1 = 2) ∨
          (m 0 = 1 ∧ m 1 = 1) ∨ (m 0 = 0 ∧ m 1 = 0) by
        simpa [Finsupp.ext_iff]
      have : m 0 ≤ 3 := by omega
      have : m 1 ≤ 3 - m 0 := by omega
      interval_cases (m 0)
      <;> interval_cases (m 1)
      <;> (first | contradiction | decide)

  have h5 : ∀ i ∈ s, ∃ a b c d, g i = (monomial ⟨x 2 y 1⟩ a) + (monomial ⟨x 1 y 2⟩ b) +
      (monomial ⟨x 1 y 1⟩ c) + (monomial 0 d) := by
    intro i hi
    refine ⟨(g i).coeff ⟨x 2 y 1⟩, (g i).coeff ⟨x 1 y 2⟩, (g i).coeff ⟨x 1 y 1⟩, (g i).coeff 0, ?_⟩
    rw [MvPolynomial.ext_iff]
    intro m
    by_cases! h5 : m ∈ t
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, t] at h5 
      rcases h5 with rfl | rfl | rfl | rfl
      <;> simp [Finsupp.ext_iff] 
    · have h6 : (g i).coeff m = 0 := by
        simp only [h4, Set.mem_setOf_eq] at h5
        contrapose! h5
        refine ⟨h2 hi m h5, h3 hi m h5⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, t] at h5
      simp [h6, h5, eq_comm]
  
  have h6 : ∀ i ∈ s, (g i ^ 2).coeff ⟨x 2 y 2⟩ = (g i).coeff ⟨x 1 y 1⟩ ^ 2 := by
    intro i hi
    obtain ⟨a, b, c, d, h6⟩ := h5 i hi
    simp only [h6, pow_two, mul_add, add_mul, monomial_mul, coeff_add, coeff_monomial]
    simp [Finsupp.ext_iff]

  replace h1 := congr(($h1).coeff ⟨x 2 y 2⟩)
  rw [coeff_sum, Finset.sum_congr rfl h6] at h1
  have : 0 ≤ motzkin (K := K).coeff ⟨x 2 y 2⟩ := by simp [h1, Finset.sum_nonneg, sq_nonneg]
  have : 0 > motzkin (K := K).coeff ⟨x 2 y 2⟩ := by simp [motzkin, coeff_one, Finsupp.ext_iff]
  order
