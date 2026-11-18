import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace PeraVerification

private lemma pair_bound {x y z : ℝ} (hxy : x * y ≤ 0) :
    (x + y + z) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (z - x - y)]

theorem weighted_three_sum_bound
    {u₀ u₁ u₂ v₀ v₁ v₂ : ℝ}
    (hu₀ : 0 ≤ u₀) (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂)
    (hu : 0 < u₀ + u₁ + u₂)
    (horth : u₀ * v₀ + u₁ * v₁ + u₂ * v₂ = 0) :
    (v₀ + v₁ + v₂) ^ 2 ≤ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2) := by
  by_contra hnot
  push_neg at hnot
  have hp01 : 0 < v₀ * v₁ := by
    by_contra h
    exact (not_lt_of_ge (pair_bound (x := v₀) (y := v₁) (z := v₂) (le_of_not_gt h))) hnot
  have hp02 : 0 < v₀ * v₂ := by
    by_contra h
    have hb := pair_bound (x := v₀) (y := v₂) (z := v₁) (le_of_not_gt h)
    nlinarith [hb]
  have hp12 : 0 < v₁ * v₂ := by
    by_contra h
    have hb := pair_bound (x := v₁) (y := v₂) (z := v₀) (le_of_not_gt h)
    nlinarith [hb]
  have hsame : (0 < v₀ ∧ 0 < v₁ ∧ 0 < v₂) ∨
      (v₀ < 0 ∧ v₁ < 0 ∧ v₂ < 0) := by
    by_cases hv₀ : 0 < v₀
    · left
      have hv₁ : 0 < v₁ := by nlinarith
      have hv₂ : 0 < v₂ := by nlinarith
      exact ⟨hv₀, hv₁, hv₂⟩
    · right
      have hv₀le : v₀ ≤ 0 := le_of_not_gt hv₀
      have hv₀' : v₀ < 0 := by
        rcases (mul_pos_iff.mp hp01) with h | h
        · linarith [h.1]
        · exact h.1
      have hv₁ : v₁ < 0 := by
        rcases (mul_pos_iff.mp hp01) with h | h
        · linarith [hv₀le, h.1]
        · exact h.2
      have hv₂ : v₂ < 0 := by
        rcases (mul_pos_iff.mp hp02) with h | h
        · linarith [hv₀le, h.1]
        · exact h.2
      exact ⟨hv₀', hv₁, hv₂⟩
  rcases hsame with ⟨hv₀, hv₁, hv₂⟩ | ⟨hv₀, hv₁, hv₂⟩
  · by_cases hu₀' : 0 < u₀
    · have h0 : 0 < u₀ * v₀ := mul_pos hu₀' hv₀
      have h1 : 0 ≤ u₁ * v₁ := mul_nonneg hu₁ (le_of_lt hv₁)
      have h2 : 0 ≤ u₂ * v₂ := mul_nonneg hu₂ (le_of_lt hv₂)
      nlinarith
    · by_cases hu₁' : 0 < u₁
      · have h0 : 0 ≤ u₀ * v₀ := mul_nonneg hu₀ (le_of_lt hv₀)
        have h1 : 0 < u₁ * v₁ := mul_pos hu₁' hv₁
        have h2 : 0 ≤ u₂ * v₂ := mul_nonneg hu₂ (le_of_lt hv₂)
        nlinarith
      · have hu₂' : 0 < u₂ := by nlinarith
        have h0 : 0 ≤ u₀ * v₀ := mul_nonneg hu₀ (le_of_lt hv₀)
        have h1 : 0 ≤ u₁ * v₁ := mul_nonneg hu₁ (le_of_lt hv₁)
        have h2 : 0 < u₂ * v₂ := mul_pos hu₂' hv₂
        nlinarith
  · by_cases hu₀' : 0 < u₀
    · have h0 : u₀ * v₀ < 0 := mul_neg_of_pos_of_neg hu₀' hv₀
      have h1 : u₁ * v₁ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu₁ (le_of_lt hv₁)
      have h2 : u₂ * v₂ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu₂ (le_of_lt hv₂)
      nlinarith
    · by_cases hu₁' : 0 < u₁
      · have h0 : u₀ * v₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu₀ (le_of_lt hv₀)
        have h1 : u₁ * v₁ < 0 := mul_neg_of_pos_of_neg hu₁' hv₁
        have h2 : u₂ * v₂ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu₂ (le_of_lt hv₂)
        nlinarith
      · have hu₂' : 0 < u₂ := by nlinarith
        have h0 : u₀ * v₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu₀ (le_of_lt hv₀)
        have h1 : u₁ * v₁ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu₁ (le_of_lt hv₁)
        have h2 : u₂ * v₂ < 0 := mul_neg_of_pos_of_neg hu₂' hv₂
        nlinarith

end PeraVerification
