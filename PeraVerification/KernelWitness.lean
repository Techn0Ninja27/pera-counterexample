import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation

namespace PeraVerification

open scoped BigOperators

abbrev Vec3 := Fin 3 → ℝ

def cross3 (x y : Vec3) : Vec3 := ![
  x 1 * y 2 - x 2 * y 1,
  x 2 * y 0 - x 0 * y 2,
  x 0 * y 1 - x 1 * y 0]

def dot3 (x y : Vec3) : ℝ := ∑ i, x i * y i

lemma cross3_dot_left (x y : Vec3) : dot3 x (cross3 x y) = 0 := by
  simp [dot3, cross3, Fin.sum_univ_succ]
  ring

lemma cross3_dot_right (x y : Vec3) : dot3 y (cross3 x y) = 0 := by
  simp [dot3, cross3, Fin.sum_univ_succ]
  ring

lemma cross3_kernel_witness {x y : Vec3}
    (hcross : cross3 x y ≠ 0) :
    ∃ v : Vec3, v ≠ 0 ∧ dot3 x v = 0 ∧ dot3 y v = 0 := by
  refine ⟨cross3 x y, hcross, cross3_dot_left x y, ?_⟩
  exact cross3_dot_right x y

/- A completely explicit three-dimensional kernel witness.  The cross product
   handles the independent case.  If it vanishes, one of the coordinate
   witnesses below is orthogonal to both vectors; this avoids importing any
   rank-nullity theorem into the main counterexample. -/
theorem exists_common_orthogonal (x y : Vec3) (hx : x ≠ 0) :
    ∃ v : Vec3, v ≠ 0 ∧ dot3 x v = 0 ∧ dot3 y v = 0 := by
  by_cases hcross : cross3 x y ≠ 0
  · exact cross3_kernel_witness hcross
  · by_cases hx0 : x 0 ≠ 0
    · let v : Vec3 := ![x 1, -x 0, 0]
      refine ⟨v, ?_, ?_, ?_⟩
      · intro hv
        have h1 := congrFun hv 1
        simp [v] at h1
        exact hx0 (by linarith)
      · simp [v, dot3, Fin.sum_univ_succ]
        ring
      · have hc := congrFun (show cross3 x y = 0 from Classical.byContradiction (fun hn => hcross hn)) 2
        simp [cross3] at hc
        simp [v, dot3, Fin.sum_univ_succ]
        linarith
    · by_cases hx1 : x 1 ≠ 0
      · let v : Vec3 := ![0, x 2, -x 1]
        refine ⟨v, ?_, ?_, ?_⟩
        · intro hv
          have h2 := congrFun hv 2
          simp [v] at h2
          exact hx1 (by linarith)
        · simp [v, dot3, Fin.sum_univ_succ]
          ring
        · have hc := congrFun (show cross3 x y = 0 from Classical.byContradiction (fun hn => hcross hn)) 0
          simp [cross3] at hc
          simp [v, dot3, Fin.sum_univ_succ]
          linarith
      · by_cases hx2 : x 2 ≠ 0
        · let v : Vec3 := ![1, 0, 0]
          have hx0' : x 0 = 0 := not_ne_iff.mp hx0
          have hx1' : x 1 = 0 := not_ne_iff.mp hx1
          refine ⟨v, ?_, ?_, ?_⟩
          · intro hv
            have h0 := congrFun hv 0
            simp [v] at h0
          · simp [v, dot3, Fin.sum_univ_succ, hx0', hx1']
          · have hc := congrFun (show cross3 x y = 0 from Classical.byContradiction (fun hn => hcross hn)) 1
            simp [cross3, hx0'] at hc
            have hy0 : y 0 = 0 := by
              exact (mul_eq_zero.mp (by simpa [hx0'] using hc)).resolve_left hx2
            simp [v, dot3, Fin.sum_univ_succ]
            exact hy0
        · let v : Vec3 := ![1, -1, 0]
          have hx0' : x 0 = 0 := not_ne_iff.mp hx0
          have hx1' : x 1 = 0 := not_ne_iff.mp hx1
          have hx2' : x 2 = 0 := not_ne_iff.mp hx2
          exfalso
          apply hx
          funext i
          fin_cases i <;> simp [hx0', hx1', hx2']


end PeraVerification
