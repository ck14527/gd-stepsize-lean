import GD.Kernel
namespace GD
noncomputable section

def objectiveCoefficient (U : ℝ) : ℝ := 1/(2*U-1)

/-- The affine-reciprocal identity (7). -/
theorem objective_reciprocal {U : ℝ} (hU : 1 ≤ U) :
    (1/U)/(2-1/U) = objectiveCoefficient U := by
  have h0 : U ≠ 0 := by linarith
  have h1 : 2*U-1 ≠ 0 := by linarith
  unfold objectiveCoefficient; field_simp

/-- The exact remainder used in Theorem 5.8. -/
theorem objective_remainder {U : ℝ} (hU : 1 ≤ U) :
    objectiveCoefficient U-1/(2*U) = 1/((2*U-1)*(2*U)) := by
  have h0 : U ≠ 0 := by linarith
  have h1 : 2*U-1 ≠ 0 := by linarith
  unfold objectiveCoefficient; field_simp

theorem objective_remainder_bound {U : ℝ} (hU : 1 ≤ U) :
    0 < objectiveCoefficient U-1/(2*U) ∧
    objectiveCoefficient U-1/(2*U) ≤ 1/(2*U^2) := by
  rw [objective_remainder hU]
  have hu : 0 < U := by linarith
  have hd : 0 < (2*U-1)*(2*U) := mul_pos (by linarith) (by linarith)
  constructor
  · positivity
  · apply one_div_le_one_div_of_le (by positivity : (0:ℝ) < 2*U^2)
    nlinarith [sq_nonneg (U-1)]

/-- A formal correction to the text after (3) and (29): the standard
quadratic's coefficient eta^2 is strictly below the pure objective bound. -/
theorem quadratic_not_objective_extremizer {eta : ℝ} (h0 : 0 < eta) (h1 : eta < 1) :
    eta^2 < eta/(2-eta) := by
  apply (lt_div_iff₀ (show 0 < 2-eta by linarith)).mpr
  have hs : 0 < (1-eta)^2 := sq_pos_of_pos (by linarith)
  nlinarith [mul_pos h0 hs]

/-- Eq. (30), with its correct domain. -/
theorem objective_rate_correction {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 1) :
    s/(2-s)-s/2 = s^2/(2*(2-s)) ∧ 0 < s^2/(2*(2-s)) := by
  have hd : 2-s ≠ 0 := by linarith
  constructor
  · field_simp; ring
  · apply div_pos (sq_pos_of_pos h0); nlinarith

end
end GD
