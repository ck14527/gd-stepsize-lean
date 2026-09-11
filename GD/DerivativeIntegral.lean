import GD.DyadicDerivatives
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace GD
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

theorem slopeGrid_measurable (k : ℕ) : Measurable (slopeGrid k) := by
  have hcell : Measurable (cellIndex k) :=
    (Nat.measurable_floor.comp (measurable_id.mul_const ((2:ℝ)^k))).min measurable_const
  exact (measurable_of_countable (slope k)).comp hcell

theorem derivativeProfile_integrable : IntegrableOn derivativeProfile (Icc (1:ℝ) 2) := by
  have hm : AEMeasurable derivativeProfile (volume.restrict (Icc (1:ℝ) 2)) := by
    apply aemeasurable_of_tendsto_metrizable_ae' (fun k => (slopeGrid_measurable k).aemeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact slopeGrid_tendsto x hx
  apply (integrable_const cplus).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have h := derivativeProfile_bounds x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (cminus_pos.le.trans h.1)]
  exact h.2

theorem F_integral_derivativeProfile (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    F x=1+∫ u in (1:ℝ)..x, derivativeProfile u := by
  have hcont := F_continuousOn.mono (Icc_subset_Icc le_rfl hx.2)
  have hint : IntervalIntegrable derivativeProfile volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx.1).mpr
      (derivativeProfile_integrable.mono_set (Icc_subset_Icc le_rfl hx.2))
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx.1 hcont
    (fun y hy => F_hasDeriv_right y ⟨hy.1,hy.2.trans_le hx.2⟩) hint
  rw [F_one] at h
  linarith

end
end GD
