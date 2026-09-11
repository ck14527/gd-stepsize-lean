import GD.DerivativeIntegral
import GD.BinaryPaths
import Mathlib.Analysis.SpecialFunctions.Log.Summable

namespace GD
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

theorem pathLower_binary_sum (ε : ℕ → Bool) (k : ℕ) :
    pathLower ε k=1+∑ i ∈ Finset.range k, (if ε i then (1:ℝ) else 0)/(2:ℝ)^(i+1) := by
  induction k with
  | zero => simp [pathLower,binaryIndex]
  | succ k ih =>
    have hstep : pathLower ε (k+1)=pathLower ε k+(if ε k then (1:ℝ) else 0)/(2:ℝ)^(k+1) := by
      unfold pathLower
      rw [binaryIndex,pow_succ]
      cases hb : ε k <;> simp only [hb,Bool.false_eq_true,↓reduceIte,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero]
      all_goals field_simp <;> ring
    rw [hstep,ih,Finset.sum_range_succ]
    ring

theorem binaryProduct_tprod (ε : ℕ → Bool) :
    Multipliable (binaryWeight ε) ∧ binaryProductLimit ε=(rho-1)*∏' i, binaryWeight ε i := by
  have hnorm : Summable (fun i => ‖Real.log (binaryWeight ε i)‖) := by
    simpa only [zero_add,Real.norm_eq_abs] using (binary_log_tail ε 0).1
  have hs : Summable (fun i => Real.log (binaryWeight ε i)) := Summable.of_norm hnorm
  have hm := Real.multipliable_of_summable_log (fun i => (binaryWeight_bounds ε i).1) hs
  refine ⟨hm,?_⟩
  have h := hm.hasProd.tendsto_prod_nat.const_mul (rho-1)
  exact tendsto_nhds_unique (binaryProduct_tendsto ε) h

namespace Targets
/-- Full analytical content of C.1. Binary expansions are represented by the
recursively defined digit indices, their finite binary sums and unique limiting
point. Terminating and recurring-one expansions are stated explicitly. -/
def theorem_C_1 : Prop :=
  theorem_C_1_regularity_part ∧
  (∀ x ∈ Icc (1:ℝ) 2, F x=1+∫ u in (1:ℝ)..x, derivativeProfile u) ∧
  TendstoUniformlyOn slopeGrid derivativeProfile atTop (Icc (1:ℝ) 2) ∧
  TendstoUniformly binaryProduct binaryProductLimit atTop ∧
  (∀ ε, Multipliable (binaryWeight ε) ∧ binaryProductLimit ε=(rho-1)*∏' i, binaryWeight ε i) ∧
  (∀ ε k, Summable (fun i : ℕ => |Real.log (binaryWeight ε (k+i))|) ∧
    (∑' i : ℕ, |Real.log (binaryWeight ε (k+i))|) ≤ 1/(rho*(2:ℝ)^k)) ∧
  (∀ ε k, pathLower ε k=1+∑ i ∈ Finset.range k, (if ε i then (1:ℝ) else 0)/(2:ℝ)^(i+1)) ∧
  (∀ ε, Tendsto (pathLower ε) atTop (𝓝 (binaryPoint ε)) ∧ FollowsPath ε (binaryPoint ε) ∧
    ∀ x, FollowsPath ε x → x=binaryPoint ε) ∧
  (∀ ε x, x ∈ Ioo (1:ℝ) 2 → ¬IsDyadic x → FollowsPath ε x →
    binaryProductLimit ε=derivativeProfile x ∧ HasDerivAt F (binaryProductLimit ε) x) ∧
  (∀ ε K, (∀ l, ε (K+l)=false) → binaryPoint ε ∈ Ioo (1:ℝ) 2 →
    HasDerivWithinAt F (binaryProductLimit ε) (Ici (binaryPoint ε)) (binaryPoint ε)) ∧
  (∀ ε K, (∀ l, ε (K+l)=true) → binaryPoint ε ∈ Ioo (1:ℝ) 2 →
    HasDerivWithinAt F (binaryProductLimit ε) (Iic (binaryPoint ε)) (binaryPoint ε))
end Targets

theorem theorem_C_1 : Targets.theorem_C_1 := by
  refine ⟨theorem_C_1_regularity_part,F_integral_derivativeProfile,slopeGrid_uniform,binaryProduct_uniform,
    binaryProduct_tprod,binary_log_tail,pathLower_binary_sum,?_,?_,binaryProduct_zero_tail_derivative,binaryProduct_one_tail_derivative⟩
  · exact fun ε => ⟨pathLower_tendsto ε,binaryPoint_follows ε,binaryPoint_unique ε⟩
  · intro ε x hx hnd hp
    have he := binaryProduct_nondyadic ε x hx hnd hp
    exact ⟨he,he.symm ▸ F_hasDeriv_nondyadic x hx hnd⟩

end
end GD
