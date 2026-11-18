import Mathlib.Tactic
import Mathlib.Analysis.CStarAlgebra.Matrix
import PeraVerification.Usefulness

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix WithLp

namespace PeraVerification

noncomputable section

private lemma lora_kills (a b v : V3) (ha : dotProduct a v = 0) :
    pera a b 0 *ᵥ v = 0 := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pera] at ha ⊢
  linear_combination b i * ha

private lemma target_fixes_zero_sum (v : V3) (hsum : coordSum v = 0) :
    target *ᵥ v = v := by
  funext i
  rw [target_apply]
  simp [hsum]

private lemma operator_lower_bound_of_witness
    (M : Matrix (Fin 3) (Fin 3) ℝ) (v : V3) (hv : v ≠ 0)
    (hM : M *ᵥ v = v) : 1 ≤ ‖M‖ := by
  have hop := Matrix.l2_opNorm_mulVec M
    (toLp 2 v : EuclideanSpace ℝ (Fin 3))
  have hop' : ‖(toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ ≤
      ‖M‖ * ‖(toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ := by
    change ‖(toLp 2 (M *ᵥ v) : EuclideanSpace ℝ (Fin 3))‖ ≤
      ‖M‖ * ‖(toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ at hop
    rw [hM] at hop
    exact hop
  have hp := sqNorm_pos hv
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hop'
  simp only [mul_pow, euclidean_norm_sq] at hs
  have hn : 0 < ‖(toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ ^ 2 := by
    rw [euclidean_norm_sq]
    exact hp
  have hnorm : 0 ≤ ‖M‖ := norm_nonneg _
  by_contra hbad
  have hlt : ‖M‖ < 1 := lt_of_not_ge hbad
  have hsquare : ‖M‖ ^ 2 < 1 := by nlinarith [sq_nonneg (‖M‖ - 1)]
  nlinarith

/- Every rank-one LoRA update has spectral error at least one on this target. -/
theorem lora_rank_one_error_lower_bound (a b : V3) :
    1 ≤ ‖target - pera a b 0‖ := by
  by_cases ha : a = 0
  · have hM : target - pera a b 0 = target := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [ha, pera, target]
    rw [hM]
    apply operator_lower_bound_of_witness target ![1, -1, 0]
    · intro hv
      have h0 := congrFun hv 0
      norm_num at h0
    · have hsum : coordSum (![1, -1, 0] : V3) = 0 := by
        dsimp [coordSum]
        norm_num
      exact target_fixes_zero_sum _ hsum
  · obtain ⟨v, hv, hav, huv⟩ :=
      exists_common_orthogonal a (fun _ : Fin 3 => (1 : ℝ)) ha
    have hsum : coordSum v = 0 := by
      simpa [dot3, dotProduct, Fin.sum_univ_succ, coordSum, add_assoc] using huv
    have hkill : pera a b 0 *ᵥ v = 0 := lora_kills a b v hav
    have hfix : target *ᵥ v = v := target_fixes_zero_sum v hsum
    have happ : (target - pera a b 0) *ᵥ v = v := by
      rw [Matrix.sub_mulVec, hfix, hkill, sub_zero]
    exact operator_lower_bound_of_witness _ v hv happ

theorem fixed_pera_beats_rank_one_lora :
    ‖target - fixedPera‖ < 1 ∧
      ∀ a b : V3, 1 ≤ ‖target - pera a b 0‖ := by
  exact ⟨fixed_pera_operator_norm_lt_one, lora_rank_one_error_lower_bound⟩

end
end PeraVerification
