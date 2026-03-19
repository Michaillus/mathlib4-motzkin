/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan, Heather Macbeth
-/
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib

/-!
# The Motzkin polynomial

The Motzkin polynomial is a well-known counterexample: it is nonnegative everywhere, but not
expressible as a polynomial sum of squares.

This file contains a proof of the first property (nonnegativity).

TODO: prove the second property.
-/

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The **Motzkin polynomial** is nonnegative.
This bivariate polynomial cannot be written as a sum of squares. -/
lemma motzkin_polynomial_nonneg (x y : K) :
    0 ≤ x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h : 0 < (x ^ 2 + y ^ 2) ^ 2 := by positivity
  refine nonneg_of_mul_nonneg_left ?_ h
  have H : 0 ≤ (x ^ 3 * y + x * y ^ 3 - 2 * x * y) ^ 2 * (1 + x ^ 2 + y ^ 2)
    + (x ^ 2 - y ^ 2) ^ 2 := by positivity
  linear_combination H



open MvPolynomial
/- noncomputable def motzkin : MvPolynomial (Fin 2) K := -/
/-   let x := X 0 -/
/-   let y := X 1 -/
/-   x ^ 4 * y ^ 2 + x ^ 2 + y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1 -/

noncomputable def motzkin : MvPolynomial (Fin 2) K :=
  (monomial (Finsupp.single 0 4 + Finsupp.single 1 2) 1) + 
  (monomial (Finsupp.single 0 2 + Finsupp.single 1 4) 1) + 
  (monomial (Finsupp.single 0 2 + Finsupp.single 1 2) (-3)) + 
  (monomial (Finsupp.single 0 0) 1)

lemma motzkin_polynomial_ne_sos (s : Finset (MvPolynomial (Fin 2) K)) :
    motzkin ≠ ∑ g ∈ s, g ^ 2 := by
  intro h

  /- have h_nox (n : ℕ) (hn : n > 0) : (coeff (Finsupp.single (0: Fin 2) n) g) = 0 := by -/
  /- have h_nox : ∀ n : ℕ, n > 0 → ∀ g ∈ s, (coeff (Finsupp.single (0: Fin 2) n) g) = 0 := by -/
  /-   intro n hn g hg -/
  /-   sorry -/

     

  let m : Fin 2 →₀ ℕ := Finsupp.single 0 2 + Finsupp.single 1 2
  let c : K := coeff m motzkin
  have : c = -3 := by
    unfold c m motzkin
    simp [Finsupp.ext_iff, MvPolynomial.coeff_one]

  have s_nonempty : s.Nonempty := by
    by_contra! hs
    have h1 := hs ▸ h
    rw [Finset.sum_empty, MvPolynomial.ext_iff] at h1
    specialize h1 0
    simp [motzkin] at h1
  
  have motzkin_xk_zero : ∀ n > 0, motzkin.coeff (Finsupp.single 0 n) = (0 : K) := by
    intro n hn
    simp [motzkin, Finsupp.ext_iff, MvPolynomial.coeff_one]
    omega

  have g_xk_zero : ∀ g ∈ s, ∀ k : ℕ, k > 0 →
      g.coeff (Finsupp.single 0 k) = 0 := by

    let k_sup := s.sup' s_nonempty (MvPolynomial.degreeOf 0)
    have h1 := MvPolynomial.ext_iff.mp h
    specialize h1 (Finsupp.single 0 (2 * k_sup))
    suffices k_sup = 0 by
      intro g hg k hk_pos
      by_contra! hk
      have : k_sup ≥ k := by
        simp [k_sup]
        use g
        refine ⟨hg, ?_⟩
        unfold degreeOf
        rw [MvPolynomial.degrees_def]

        sorry
        




      sorry


    by_contra! hsup
    rw [motzkin_xk_zero (2 * k_sup) (by positivity)] at h1



    sorry
  
  have coeff_yk_zero : ∀ g ∈ s, ∀ k : ℕ, k > 0 →
      g.coeff (Finsupp.single (1 : Fin 2) k) = 0 := by
    sorry
  
  have coeff_geq3_zero : ∀ g ∈ s, ∀ a : ℕ, a ≥ 0 → ∀ b : ℕ,
      g.coeff (Finsupp.single 0 a + Finsupp.single 1 a) = 0 := by
    sorry



  sorry



