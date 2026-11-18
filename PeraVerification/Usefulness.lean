import Mathlib.Tactic
import Mathlib.Analysis.CStarAlgebra.Matrix
import PeraVerification.TargetProperties

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix WithLp

namespace PeraVerification

noncomputable section

def fixedPera : Matrix (Fin 3) (Fin 3) ℝ :=
  pera ![1, -1, 0] ![(1 / 2 : ℝ), -1 / 2, 0] 2

private lemma fixedPera_apply (v : V3) :
    fixedPera *ᵥ v = ![v 0, v 1, 0] := by
  funext i
  fin_cases i <;> simp [fixedPera, pera, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

private lemma fixed_error_sq_bound (v : V3) :
    sqNorm ((target - fixedPera) *ᵥ v) ≤ (2 / 3 : ℝ) * sqNorm v := by
  have hpair : (v 0 + v 1) ^ 2 ≤ 2 * (v 0 ^ 2 + v 1 ^ 2) := by
    nlinarith [sq_nonneg (v 0 - v 1)]
  have ht : target *ᵥ v =
      ![v 0 - coordSum v / 3, v 1 - coordSum v / 3,
        v 2 - coordSum v / 3] := by
    funext i
    fin_cases i <;> simp [target_apply]
  rw [Matrix.sub_mulVec, ht, fixedPera_apply]
  simp only [sqNorm]
  dsimp [coordSum]
  ring_nf
  nlinarith

theorem fixed_pera_operator_norm_le :
    ‖target - fixedPera‖ ≤ Real.sqrt (2 / 3 : ℝ) := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro x
  let v : V3 := ofLp x
  have hs := fixed_error_sq_bound v
  have hx : ‖x‖ ^ 2 = sqNorm v := by
    simpa [v] using euclidean_norm_sq v
  have hnorm :
      ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (target - fixedPera) x‖ ^ 2 =
        sqNorm ((target - fixedPera) *ᵥ v) := by
    rw [← euclidean_norm_sq ((target - fixedPera) *ᵥ v)]
    rfl
  have hsqrt : 0 ≤ Real.sqrt (2 / 3 : ℝ) := Real.sqrt_nonneg _
  have hsqrt2 : (Real.sqrt (2 / 3 : ℝ)) ^ 2 = 2 / 3 := by
    rw [Real.sq_sqrt]
    norm_num
  have hsq :
      ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (target - fixedPera) x‖ ^ 2 ≤
        (Real.sqrt (2 / 3 : ℝ) * ‖x‖) ^ 2 := by
    rw [hnorm, mul_pow, hsqrt2, hx]
    exact hs
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hsqrt (norm_nonneg _))).mp hsq

theorem fixed_pera_operator_norm_lt_one :
    ‖target - fixedPera‖ < 1 := by
  have h := fixed_pera_operator_norm_le
  have hs : Real.sqrt (2 / 3 : ℝ) < 1 := by
    have hnonneg : 0 ≤ Real.sqrt (2 / 3 : ℝ) := Real.sqrt_nonneg _
    have hsquare : (Real.sqrt (2 / 3 : ℝ)) ^ 2 = 2 / 3 := by
      rw [Real.sq_sqrt]
      norm_num
    nlinarith
  exact lt_of_le_of_lt h hs

/-- A concrete witness also bounds the best achievable error from above. -/
theorem optimal_error_upper_bound : sInf errorSet ≤ Real.sqrt (2 / 3 : ℝ) := by
  have hb : BddBelow errorSet := by
    refine ⟨0, ?_⟩
    rintro e ⟨a, b, h, rfl⟩
    exact norm_nonneg _
  have hm : ‖target - fixedPera‖ ∈ errorSet := by
    exact ⟨![1,-1,0], ![(1/2:ℝ),-1/2,0], 2, rfl⟩
  exact le_trans (csInf_le hb hm) fixed_pera_operator_norm_le

theorem certified_error_interval :
    1 / Real.sqrt 3 ≤ sInf errorSet ∧ sInf errorSet ≤ Real.sqrt (2 / 3 : ℝ) :=
  ⟨optimal_error_lower_bound, optimal_error_upper_bound⟩

end
end PeraVerification
