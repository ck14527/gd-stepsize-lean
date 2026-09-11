import GD.LocalSlopes
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace GD
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 1200000

theorem cell_right_open (k : ℕ) (x : ℝ) (hx : x ∈ Ico (1:ℝ) 2) :
    x ∈ Ico ((cellIndex k x:ℝ)/(2:ℝ)^k) (((cellIndex k x+1:ℕ):ℝ)/(2:ℝ)^k) := by
  have hp : 0 < (2:ℝ)^k := by positivity
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hf : Nat.floor (x*(2:ℝ)^k) < 2^(k+1) := by
    have hh := (Nat.floor_le (mul_nonneg hx0 hp.le)).trans_lt (mul_lt_mul_of_pos_right hx.2 hp)
    have he : (2:ℝ)*(2:ℝ)^k=(2:ℝ)^(k+1) := by ring
    rw [he] at hh
    exact_mod_cast hh
  have hi : cellIndex k x=Nat.floor (x*(2:ℝ)^k) := by unfold cellIndex; rw [min_eq_left (by omega)]
  refine ⟨(cell_bounds k x ⟨hx.1,hx.2.le⟩).2.2.1,?_⟩
  rw [hi]
  apply (lt_div_iff₀ hp).mpr
  simpa only [Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (x*(2:ℝ)^k)

theorem nondyadic_cell_interior (k : ℕ) (x : ℝ) (hx : x ∈ Ioo (1:ℝ) 2) (hnd : ¬IsDyadic x) :
    x ∈ Ioo ((cellIndex k x:ℝ)/(2:ℝ)^k) (((cellIndex k x+1:ℕ):ℝ)/(2:ℝ)^k) := by
  have h := cell_right_open k x ⟨hx.1.le,hx.2⟩
  refine ⟨lt_of_le_of_ne h.1 ?_,h.2⟩
  intro he
  exact hnd ⟨k,cellIndex k x,he.symm⟩

theorem secant_derivativeProfile_error (k : ℕ) (x y : ℝ) (hx : x ∈ Icc (1:ℝ) 2)
    (hy : y ∈ Icc ((cellIndex k x:ℝ)/(2:ℝ)^k) (((cellIndex k x+1:ℕ):ℝ)/(2:ℝ)^k)) (hne : y ≠ x) :
    |(F y-F x)/(y-x)-derivativeProfile x| ≤ 2*slopeTail k := by
  have hj := cell_bounds k x hx
  have hs := F_local_secant k (cellIndex k x) hj.1 (by omega) x y hj.2.2 hy hne
  have hd := slopeGrid_error k x hx
  have ht := abs_sub_le ((F y-F x)/(y-x)) (slopeGrid k x) (derivativeProfile x)
  change |(F y-F x)/(y-x)-slopeGrid k x| ≤ slopeTail k at hs
  linarith

theorem F_hasDeriv_right (x : ℝ) (hx : x ∈ Ioo (1:ℝ) 2) :
    HasDerivWithinAt F (derivativeProfile x) (Ioi x) x := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp : x ∉ Ioi x)]
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have htail := slopeTail_tendsto.const_mul 2
  simp only [mul_zero] at htail
  obtain ⟨k,hk⟩ := (htail.eventually (gt_mem_nhds heps)).exists
  have hcell := cell_right_open k x ⟨hx.1.le,hx.2⟩
  have hupper : ∀ᶠ y in 𝓝[Ioi x] x, y < ((cellIndex k x+1:ℕ):ℝ)/(2:ℝ)^k :=
    nhdsWithin_le_nhds (Iio_mem_nhds hcell.2)
  filter_upwards [hupper,self_mem_nhdsWithin] with y hy hyx
  rw [Real.dist_eq,slope_def_field]
  exact (secant_derivativeProfile_error k x y ⟨hx.1.le,hx.2.le⟩ ⟨hcell.1.trans hyx.le,hy.le⟩ hyx.ne').trans_lt hk

theorem F_hasDeriv_nondyadic (x : ℝ) (hx : x ∈ Ioo (1:ℝ) 2) (hnd : ¬IsDyadic x) :
    HasDerivAt F (derivativeProfile x) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have htail := slopeTail_tendsto.const_mul 2
  simp only [mul_zero] at htail
  obtain ⟨k,hk⟩ := (htail.eventually (gt_mem_nhds heps)).exists
  have hc := nondyadic_cell_interior k x hx hnd
  have hevent : ∀ᶠ y in 𝓝[≠] x, y ∈ Ioo ((cellIndex k x:ℝ)/(2:ℝ)^k) (((cellIndex k x+1:ℕ):ℝ)/(2:ℝ)^k) :=
    nhdsWithin_le_nhds (Ioo_mem_nhds hc.1 hc.2)
  filter_upwards [hevent,self_mem_nhdsWithin] with y hy hne
  rw [Real.dist_eq,slope_def_field]
  exact (secant_derivativeProfile_error k x y ⟨hx.1.le,hx.2.le⟩ ⟨hy.1.le,hy.2.le⟩ hne).trans_lt hk

theorem derivativeProfile_continuousAt_nondyadic (x : ℝ) (hx : x ∈ Ioo (1:ℝ) 2) (hnd : ¬IsDyadic x) :
    ContinuousAt derivativeProfile x := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have htail := slopeTail_tendsto.const_mul 2
  simp only [mul_zero] at htail
  obtain ⟨k,hk⟩ := (htail.eventually (gt_mem_nhds heps)).exists
  have hc := nondyadic_cell_interior k x hx hnd
  have hj := cell_bounds k x ⟨hx.1.le,hx.2.le⟩
  filter_upwards [Ioo_mem_nhds hc.1 hc.2] with y hy
  have hyg := cell_interval_subset k (cellIndex k x) hj.1 (by omega) ⟨hy.1.le,hy.2.le⟩
  have he := cellIndex_eq_of_mem k (cellIndex k x) hj.1 (by omega) y ⟨hy.1.le,hy.2⟩
  have hdx := slopeGrid_error k x ⟨hx.1.le,hx.2.le⟩
  have hdy := slopeGrid_error k y hyg
  have hsame : slopeGrid k y=slopeGrid k x := by unfold slopeGrid; rw [he]
  rw [hsame] at hdy
  have ht := abs_sub_le (derivativeProfile y) (slopeGrid k x) (derivativeProfile x)
  have hdy' : |derivativeProfile y-slopeGrid k x| ≤ slopeTail k := by simpa only [abs_sub_comm] using hdy
  rw [Real.dist_eq]
  linarith

end
end GD
