import GD.DyadicInterpolation
import GD.Targets

namespace GD
noncomputable section
open Filter
open scoped Topology

theorem C_ray_identity (m k : ℕ) (hm : 1 ≤ m) :
    C (m*2^k)=(m:ℝ)^p/(W (m*2^k)/rho^k) := by
  have hrho := rho_pos
  have hn : 1 ≤ m*2^k := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by positivity))
  have hw := W_pos (m*2^k) hn
  rw [C,etaF,nat_dyadic_rpow]
  field_simp

/-- Proposition 6.2 including the fixed-ray limits and their phase bounds. -/
theorem proposition_6_2 : Targets.proposition_6_2 := by
  refine ⟨W_sandwich,?_⟩
  intro m hm
  obtain ⟨d,hd0,hdup,hdlim⟩ := W_ray_limit_exists m hm
  have hdlo := W_ray_limit_lower m hm d hdlim
  have hmp : 0 < (m:ℝ)^p := Real.rpow_pos_of_pos (by exact_mod_cast hm) p
  have hph : 0 < Phi (phase m) := by
    rw [Phi_seed m hm]
    exact div_pos (U_pos hm) hmp
  have heq := U_phase_exact m hm
  refine ⟨(m:ℝ)^p/d,?_,?_,?_⟩
  · have hc := (tendsto_const_nhds (x:=(m:ℝ)^p)).div hdlim hd0.ne'
    exact hc.congr' (Filter.Eventually.of_forall (fun k => (C_ray_identity m k hm).symm))
  · apply (div_le_div_iff₀ (mul_pos rho_pos hph) hd0).mpr
    calc 1*d=d := by ring
         _ ≤ rho*U m := hdup
         _ = (m:ℝ)^p*(rho*Phi (phase m)) := by rw [heq]; ring
  · apply (div_le_div_iff₀ hd0 (mul_pos (by norm_num) hph)).mpr
    nlinarith

end
end GD
