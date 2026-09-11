import GD.BinaryProducts

namespace GD
noncomputable section
open Set Filter
open scoped Topology

theorem levelError_lt_half (k : ℕ) : levelError k < 1/2 := by
  have hrho := rho_gt_two
  have hp : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
  unfold levelError
  apply (div_lt_iff₀ (by positivity : (0:ℝ) < 4*rho*(2:ℝ)^k)).mpr
  nlinarith

theorem abs_log_le_twice (w : ℝ) (hw : 1/2 ≤ w) : |Real.log w| ≤ 2*|w-1| := by
  have hw0 : 0 < w := by linarith
  rcases le_total 1 w with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h),abs_of_nonneg (sub_nonneg.mpr h)]
    have hh := Real.log_le_sub_one_of_pos hw0
    linarith
  · rw [abs_of_nonpos (Real.log_nonpos hw0.le h),abs_of_nonpos (sub_nonpos.mpr h)]
    have hh := Real.one_sub_inv_le_log_of_pos hw0
    have hratio : w⁻¹-1 ≤ 2*(1-w) := by
      have he : w⁻¹-1=(1-w)/w := by field_simp
      rw [he]
      apply (div_le_iff₀ hw0).mpr
      nlinarith [mul_nonneg (show 0 ≤ 2*w-1 by linarith) (show 0 ≤ 1-w by linarith)]
    linarith

theorem binary_log_bound (ε : ℕ → Bool) (k : ℕ) :
    |Real.log (binaryWeight ε k)| ≤ 2*levelError k := by
  have hw := (binaryWeight_bounds ε k).2
  have hl := (abs_le.mp hw).1
  have hh : 1/2 ≤ binaryWeight ε k := by linarith [levelError_lt_half k]
  exact (abs_log_le_twice _ hh).trans (mul_le_mul_of_nonneg_left hw (by norm_num))

theorem binary_log_tail (ε : ℕ → Bool) (k : ℕ) :
    Summable (fun i : ℕ => |Real.log (binaryWeight ε (k+i))|) ∧
    (∑' i : ℕ, |Real.log (binaryWeight ε (k+i))|) ≤ 1/(rho*(2:ℝ)^k) := by
  have hrho := rho_pos
  have hgeom : Summable (fun i : ℕ => (1/2:ℝ)^i) := summable_geometric_of_norm_lt_one (by norm_num)
  have he : (fun i : ℕ => 2*levelError (k+i))=(fun i => (2*levelError k)*(1/2:ℝ)^i) := by
    funext i
    unfold levelError
    rw [pow_add,div_pow,one_pow]
    field_simp
    <;> ring
  have hsum : Summable (fun i : ℕ => 2*levelError (k+i)) := by rw [he]; exact hgeom.mul_left _
  have hlogs : Summable (fun i : ℕ => |Real.log (binaryWeight ε (k+i))|) :=
    Summable.of_nonneg_of_le (fun i => abs_nonneg _) (fun i => binary_log_bound ε (k+i)) hsum
  refine ⟨hlogs,?_⟩
  have h := hlogs.tsum_le_tsum (fun i => binary_log_bound ε (k+i)) hsum
  have htotal : (∑' i : ℕ, 2*levelError (k+i))=1/(rho*(2:ℝ)^k) := by
    rw [he,tsum_mul_left,tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)]
    unfold levelError
    norm_num
    ring
  rwa [htotal] at h

end
end GD
