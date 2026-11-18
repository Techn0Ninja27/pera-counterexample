import Mathlib.LinearAlgebra.Matrix.Rank
import PeraVerification.Counterexample

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace PeraVerification

noncomputable section

private def rowSelect : Fin 2 → Fin 3 := ![0, 1]

private def rankWitness : Matrix (Fin 2) (Fin 3) ℝ :=
  target.submatrix rowSelect (Equiv.refl (Fin 3))

private def factorLeft : Matrix (Fin 3) (Fin 2) ℝ :=
  !![1, 0; 0, 1; -1, -1]

private def factorRight : Matrix (Fin 2) (Fin 3) ℝ :=
  !![(2 / 3 : ℝ), -1 / 3, -1 / 3; -1 / 3, 2 / 3, -1 / 3]

lemma target_transpose : targetᵀ = target := by
  ext i j
  simp [target, eq_comm]

lemma target_mul_self : target * target = target := by
  have ht : target = !![(2 / 3 : ℝ), -1 / 3, -1 / 3;
      -1 / 3, 2 / 3, -1 / 3; -1 / 3, -1 / 3, 2 / 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [target]
  rw [ht]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

private lemma target_factorization : factorLeft * factorRight = target := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [factorLeft, factorRight, target, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma rank_target_le_two : target.rank ≤ 2 := by
  rw [← target_factorization]
  exact (Matrix.rank_mul_le_left factorLeft factorRight).trans
    (Matrix.rank_le_card_width factorLeft)

private lemma rank_witness_eq_two : rankWitness.rank = 2 := by
  apply LinearIndependent.rank_matrix
  rw [linearIndependent_fin2]
  constructor
  · intro hz
    have h := congrFun hz 0
    norm_num [rankWitness, target, rowSelect] at h
  · intro c heq
    have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    norm_num [rankWitness, target, rowSelect] at h0 h1
    nlinarith

private lemma rank_target_ge_two : 2 ≤ target.rank := by
  have hsub : rankWitness.rank ≤ target.rank := by
    exact Matrix.rank_submatrix_le rowSelect (Equiv.refl (Fin 3)) target
  rw [rank_witness_eq_two] at hsub
  exact hsub

theorem target_rank : target.rank = 2 := by
  exact Nat.le_antisymm rank_target_le_two rank_target_ge_two

theorem explicit_pera_witness :
    pera ![1, -1, 0] ![(1 / 2 : ℝ), -1 / 2, 0] 2 =
      !![1, 0, 0; 0, 1, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pera]

end

/-- A rank-two target has strictly positive best error in this PERA family. -/
theorem rank_two_counterexample : target.rank = 2 ∧ 0 < sInf errorSet :=
  ⟨target_rank, optimal_error_positive⟩

/-- Rank at most two does not imply arbitrary approximation by nominal-rank-one PERA. -/
theorem rank_two_approximation_claim_false :
    ¬ (∀ E : Matrix (Fin 3) (Fin 3) ℝ, E.rank ≤ 2 →
      ∀ ε : ℝ, 0 < ε → ∃ a b : V3, ∃ h : ℝ, ‖E - pera a b h‖ < ε) := by
  intro hall
  have hp : 0 < (1 : ℝ) / Real.sqrt 3 := by positivity
  obtain ⟨a, b, h, he⟩ := hall target (le_of_eq target_rank) (1 / Real.sqrt 3) hp
  exact (not_lt_of_ge (pera_error_lower_bound a b h)) he

end PeraVerification
