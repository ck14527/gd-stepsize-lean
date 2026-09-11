import GD.InterpolationRegularity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace GD
noncomputable section
open Set

theorem rho_lt_four : rho < 4 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg 2
  unfold rho
  nlinarith

theorem p_bounds : 1 < p ∧ p < 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · apply (lt_div_iff₀ hl2).mpr
    simpa using Real.log_lt_log (by norm_num : (0:ℝ) < 2) rho_gt_two
  · apply (div_lt_iff₀ hl2).mpr
    have h := Real.log_lt_log rho_pos rho_lt_four
    have he : Real.log (4:ℝ)=2*Real.log 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
      norm_num
    rwa [he] at h

theorem q_bounds : 1/2 < q ∧ q < 1 := by
  rw [q]
  constructor
  · apply (lt_div_iff₀ p_pos).mpr
    nlinarith [p_bounds.2]
  · apply (div_lt_iff₀ p_pos).mpr
    nlinarith [p_bounds.1]

def supportG (a x : ℝ) : ℝ := x^a*(2-x)
def turningPoint (a : ℝ) : ℝ := 2*a/(a+1)

theorem turningPoint_bounds (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    0 < turningPoint a ∧ turningPoint a < 1 := by
  unfold turningPoint
  constructor
  · positivity
  · apply (div_lt_one (by linarith)).mpr
    linarith

theorem supportG_continuous (a : ℝ) (ha : 0 < a) : Continuous (supportG a) := by
  unfold supportG
  exact (Real.continuous_rpow_const ha.le).mul (continuous_const.sub continuous_id)

theorem supportG_derivative (a x : ℝ) (hx : 0 < x) :
    HasDerivAt (supportG a) (x^(a-1)*(2*a-(a+1)*x)) x := by
  have h := (Real.hasDerivAt_rpow_const (p:=a) (Or.inl hx.ne')).mul
    ((hasDerivAt_const x 2).sub (hasDerivAt_id x))
  have he : x^a=x^(a-1)*x := by
    calc x^a=x^((a-1)+1) := by congr 1; ring
         _=x^(a-1)*x := by rw [Real.rpow_add hx,Real.rpow_one]
  convert h using 1
  rw [he]
  simp only [id_eq]
  ring

theorem supportG_inc (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    StrictMonoOn (supportG a) (Icc 0 (turningPoint a)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (supportG_continuous a ha).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(supportG_derivative a x hx.1).deriv]
  have hc : x*(a+1) < 2*a := (lt_div_iff₀ (by linarith)).mp hx.2
  exact mul_pos (Real.rpow_pos_of_pos hx.1 _) (by nlinarith)

theorem supportG_dec (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    StrictAntiOn (supportG a) (Icc (turningPoint a) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (supportG_continuous a ha).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  have hx0 : 0 < x := (turningPoint_bounds a ha ha1).1.trans hx.1
  rw [(supportG_derivative a x hx0).deriv]
  have hc : 2*a < x*(a+1) := (div_lt_iff₀ (by linarith)).mp hx.1
  exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hx0 _) (by nlinarith)

theorem supportG_root (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ z : ℝ, 0 < z ∧ z < turningPoint a ∧ supportG a z=1 ∧
      (∀ x : ℝ, 0 < x → x < z → supportG a x < 1) ∧
      (∀ x : ℝ, z < x → x < 1 → 1 < supportG a x) := by
  obtain ⟨hb0,hb1⟩ := turningPoint_bounds a ha ha1
  have hg0 : supportG a 0=0 := by simp [supportG,Real.zero_rpow ha.ne']
  have hg1 : supportG a 1=1 := by norm_num [supportG]
  have hgb : 1 < supportG a (turningPoint a) := by
    have h := supportG_dec a ha ha1 (show turningPoint a ∈ Icc (turningPoint a) 1 from ⟨le_rfl,hb1.le⟩)
      (show (1:ℝ) ∈ Icc (turningPoint a) 1 from ⟨hb1.le,le_rfl⟩) hb1
    simpa [hg1] using h
  have hv := intermediate_value_Icc hb0.le (supportG_continuous a ha).continuousOn
  have ht : (1:ℝ) ∈ Icc (supportG a 0) (supportG a (turningPoint a)) := by rw [hg0]; exact ⟨by norm_num,hgb.le⟩
  obtain ⟨z,hz,hgz⟩ := hv ht
  have hz0 : 0 < z := by
    rcases eq_or_lt_of_le hz.1 with h | h
    · subst z; rw [hg0] at hgz; norm_num at hgz
    · exact h
  have hzb : z < turningPoint a := by
    rcases eq_or_lt_of_le hz.2 with h | h
    · rw [h] at hgz; linarith
    · exact h
  refine ⟨z,hz0,hzb,hgz,?_,?_⟩
  · intro x hx0 hxz
    have h := supportG_inc a ha ha1 ⟨hx0.le,(hxz.trans hzb).le⟩ hz hxz
    rwa [hgz] at h
  · intro x hzx hx1
    by_cases hxb : x ≤ turningPoint a
    · have h := supportG_inc a ha ha1 hz ⟨(hz0.trans hzx).le,hxb⟩ hzx
      rwa [hgz] at h
    · have hbx : turningPoint a ≤ x := le_of_not_ge hxb
      have h := supportG_dec a ha ha1 ⟨hbx,hx1.le⟩ ⟨hb1.le,le_rfl⟩ hx1
      rwa [hg1] at h

/-- The infimum in the actual definition of xi selects the unique interior root. -/
theorem xi_root_and_signs :
    xi ∈ Ioo (0:ℝ) 1 ∧ xi^(2*q-1)*(2-xi)=1 ∧
    (∀ x : ℝ, x ∈ Ioo (0:ℝ) 1 → x^(2*q-1)*(2-x)=1 → x=xi) ∧
    (∀ x : ℝ, 0 < x → x < xi → x^(2*q-1)*(2-x) < 1) ∧
    (∀ x : ℝ, xi < x → x < 1 → 1 < x^(2*q-1)*(2-x)) := by
  have ha : 0 < 2*q-1 := by linarith [q_bounds.1]
  have ha1 : 2*q-1 < 1 := by linarith [q_bounds.2]
  obtain ⟨z,hz0,hzb,hgz,hleft,hright⟩ := supportG_root (2*q-1) ha ha1
  have hz1 := hzb.trans (turningPoint_bounds (2*q-1) ha ha1).2
  have huniq : ∀ x : ℝ, x ∈ Ioo (0:ℝ) 1 → x^(2*q-1)*(2-x)=1 → x=z := by
    intro x hx he
    rcases lt_trichotomy x z with hl | heq | hr
    · have h := hleft x hx.1 hl
      change x^(2*q-1)*(2-x) < 1 at h
      linarith
    · exact heq
    · have h := hright x hr hx.2
      change 1 < x^(2*q-1)*(2-x) at h
      linarith
  have hset : {x : ℝ | x ∈ Ioo 0 1 ∧ x^(2*q-1)*(2-x)=1}={z} := by
    ext x
    simp only [Set.mem_setOf_eq,Set.mem_singleton_iff]
    exact ⟨fun h => huniq x h.1 h.2,by rintro rfl; exact ⟨⟨hz0,hz1⟩,hgz⟩⟩
  have hxi : xi=z := by rw [xi,hset,csInf_singleton]
  rw [hxi]
  exact ⟨⟨hz0,hz1⟩,hgz,huniq,hleft,hright⟩

end
end GD
