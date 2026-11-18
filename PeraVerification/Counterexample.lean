import Mathlib.Analysis.CStarAlgebra.Matrix
import PeraVerification.ScalarBound
import PeraVerification.KernelWitness

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix WithLp

noncomputable section

namespace PeraVerification

abbrev V3 := Fin 3 → ℝ

def pera (a b : V3) (h : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => b i * a j + h * (b i)^2 * (a j)^2

def target : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (if i = j then 1 else 0) - 1/3

def sqNorm (v : V3) : ℝ := v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2

def coordSum (v : V3) : ℝ := v 0 + v 1 + v 2

lemma sqNorm_pos {v : V3} (hv : v ≠ 0) : 0 < sqNorm v := by
  have h0 := sq_nonneg (v 0)
  have h1 := sq_nonneg (v 1)
  have h2 := sq_nonneg (v 2)
  by_contra hn
  have hn' : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 ≤ 0 := le_of_not_gt hn
  have hz0 : v 0 = 0 := sq_eq_zero_iff.mp (by linarith : v 0 ^ 2 = 0)
  have hz1 : v 1 = 0 := sq_eq_zero_iff.mp (by linarith : v 1 ^ 2 = 0)
  have hz2 : v 2 = 0 := sq_eq_zero_iff.mp (by linarith : v 2 ^ 2 = 0)
  apply hv
  funext i
  fin_cases i <;> simpa using (by assumption : _)

lemma euclidean_norm_sq (v : V3) :
    ‖(toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ ^ 2 = sqNorm v := by
  simp [EuclideanSpace.norm_sq_eq, sqNorm, Fin.sum_univ_succ, Real.norm_eq_abs, add_assoc]

lemma target_apply (v : V3) (i : Fin 3) :
    (target *ᵥ v) i = v i - coordSum v / 3 := by
  fin_cases i <;> simp [target, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, coordSum] <;> ring

lemma target_sqNorm (v : V3) :
    sqNorm (target *ᵥ v) = sqNorm v - (coordSum v)^2 / 3 := by
  simp only [sqNorm, target_apply]
  dsimp [coordSum]
  ring

lemma pera_kills (a b v : V3) (h : ℝ)
    (ha : dotProduct a v = 0) (hu : dotProduct (fun i => (a i)^2) v = 0) :
    pera a b h *ᵥ v = 0 := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pera] at ha hu ⊢
  linear_combination b i * ha + (h * b i ^ 2) * hu

lemma exists_error_witness (a b : V3) (h : ℝ) :
    ∃ v : V3, v ≠ 0 ∧ pera a b h *ᵥ v = 0 ∧
      (coordSum v)^2 ≤ 2 * sqNorm v := by
  by_cases ha : a = 0
  · refine ⟨![1,-1,0], ?_, ?_, ?_⟩
    · intro he
      have := congrFun he 0
      norm_num at this
    · have hz : pera (0 : V3) b h = 0 := by
        ext i j
        simp [pera]
      rw [ha, hz]
      simp
    · have h0 : (![1,-1,0] : V3) 0 = 1 := rfl
      have h1 : (![1,-1,0] : V3) 1 = -1 := rfl
      have h2 : (![1,-1,0] : V3) 2 = 0 := rfl
      simp only [coordSum, sqNorm, h0, h1, h2]
      norm_num
  · obtain ⟨v, hv, hav, huv⟩ := exists_common_orthogonal a (fun i => (a i)^2) ha
    refine ⟨v, hv, pera_kills a b v h hav huv, ?_⟩
    have hp : 0 < a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 := sqNorm_pos ha
    have ho : a 0 ^ 2 * v 0 + a 1 ^ 2 * v 1 + a 2 ^ 2 * v 2 = 0 := by
      simpa [dot3, dotProduct, Fin.sum_univ_succ, add_assoc] using huv
    exact weighted_three_sum_bound (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) hp ho

/-- Main quantitative statement. The norm is mathlib's Euclidean operator norm. -/
theorem pera_error_sq_lower_bound (a b : V3) (h : ℝ) :
    1 ≤ 3 * ‖target - pera a b h‖ ^ 2 := by
  obtain ⟨v, hv, hkill, hsum⟩ := exists_error_witness a b h
  have hp := sqNorm_pos hv
  have happ : (target - pera a b h) *ᵥ v = target *ᵥ v := by
    rw [Matrix.sub_mulVec, hkill, sub_zero]
  have hop := Matrix.l2_opNorm_mulVec (target - pera a b h)
    (toLp 2 v : EuclideanSpace ℝ (Fin 3))
  have hop' : ‖(toLp 2 (target *ᵥ v) : EuclideanSpace ℝ (Fin 3))‖ ≤
      ‖target - pera a b h‖ * ‖(toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ := by
    change ‖(toLp 2 ((target - pera a b h) *ᵥ v) : EuclideanSpace ℝ (Fin 3))‖ ≤
      ‖target - pera a b h‖ * ‖(toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ at hop
    rw [happ] at hop
    exact hop
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hop'
  simp only [mul_pow, euclidean_norm_sq, target_sqNorm] at hs
  by_contra hn
  have hn' : 3 * ‖target - pera a b h‖ ^ 2 < 1 := lt_of_not_ge hn
  have hm := mul_pos (sub_pos.mpr hn') hp
  nlinarith

 theorem pera_error_lower_bound (a b : V3) (h : ℝ) :
    1 / Real.sqrt 3 ≤ ‖target - pera a b h‖ := by
  have hs := pera_error_sq_lower_bound a b h
  have hr : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hr2 : (Real.sqrt (3 : ℝ))^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn := norm_nonneg (target - pera a b h)
  apply (div_le_iff₀ hr).2
  have he : (‖target - pera a b h‖ * Real.sqrt 3)^2 = 3 * ‖target - pera a b h‖^2 := by
    rw [mul_pow, hr2]
    ring
  have hsquare : (1 : ℝ)^2 ≤ (‖target - pera a b h‖ * Real.sqrt 3)^2 := by nlinarith
  exact (sq_le_sq₀ (by norm_num) (mul_nonneg hn hr.le)).mp hsquare

/-- All spectral approximation errors in the tied real rank-one-base family. -/
def errorSet : Set ℝ := {e | ∃ a b : V3, ∃ h : ℝ, e = ‖target - pera a b h‖}

theorem errorSet_nonempty : errorSet.Nonempty := by
  exact ⟨‖target - pera 0 0 0‖, 0, 0, 0, rfl⟩

/-- The bound holds for the infimum, without assuming an optimizer exists. -/
theorem optimal_error_lower_bound : 1 / Real.sqrt 3 ≤ sInf errorSet := by
  apply le_csInf errorSet_nonempty
  rintro e ⟨a, b, h, rfl⟩
  exact pera_error_lower_bound a b h

theorem optimal_error_positive : 0 < sInf errorSet := by
  have hp : 0 < (1 : ℝ) / Real.sqrt 3 := by positivity
  exact lt_of_lt_of_le hp optimal_error_lower_bound

theorem not_zero_optimal_error : ¬ sInf errorSet ≤ 0 :=
  not_le_of_gt optimal_error_positive

theorem target_not_representable (a b : V3) (h : ℝ) : pera a b h ≠ target := by
  intro he
  have hb := pera_error_lower_bound a b h
  rw [he, sub_self, norm_zero] at hb
  have hp : 0 < (1 : ℝ) / Real.sqrt 3 := by positivity
  linarith

end PeraVerification
