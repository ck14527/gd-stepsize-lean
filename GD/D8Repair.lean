import GD.DyadicInterpolation

/-! Verified components of the corrected D.8 proof.
These elementary components are used by the complete proof in ContactPhase.lean.
The small-pivot estimate and finite-spine concentration are proved independently
in SmallPivots.lean, PivotSpine.lean and DeficitConcentration.lean. -/
namespace GD
noncomputable section
open Filter
open scoped Topology

namespace D8

/-- The discarded mass and the actual remainder, with every analytic
prerequisite exposed. This applies to the real casts of the integer spine sizes. -/
theorem actual_remainder_limits
    (N b m E Er : ℕ → ℝ) (c a : ℝ)
    (hN : ∀ k, 0 < N k) (hc : 0 < c) (ha : a < 1)
    (hb0 : ∀ k, 0 ≤ b k) (hbN : ∀ k, b k < N k)
    (hbE : ∀ k, b k ≤ E k/c)
    (hEr0 : ∀ k, 0 ≤ Er k) (hErE : ∀ k, Er k ≤ E k)
    (hE : Tendsto (fun k => E k/N k) atTop (𝓝 0))
    (hm : Tendsto (fun k => m k/(N k-b k)) atTop (𝓝 a)) :
    Tendsto (fun k => b k/N k) atTop (𝓝 0) ∧
    Tendsto (fun k => (N k-b k)/N k) atTop (𝓝 1) ∧
    Tendsto (fun k => m k/N k) atTop (𝓝 a) ∧
    Tendsto (fun k => (N k-b k-m k)/N k) atTop (𝓝 (1-a)) ∧
    Tendsto (fun k => Er k/(N k-b k-m k)) atTop (𝓝 0) := by
  have hblim : Tendsto (fun k => b k/N k) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => div_nonneg (hb0 k) (hN k).le)
      (g:=fun k => (E k/N k)/c)
    · intro k
      have hh := div_le_div_of_nonneg_right (hbE k) (hN k).le
      calc b k/N k ≤ (E k/c)/N k := hh
           _ = (E k/N k)/c := by ring
    · simpa using hE.div_const c
  have hslim : Tendsto (fun k => (N k-b k)/N k) atTop (𝓝 1) := by
    have hl := (tendsto_const_nhds (x:=(1:ℝ))).sub hblim
    have he : (fun k => (N k-b k)/N k)=(fun k => 1-b k/N k) := by
      funext k
      rw [sub_div,div_self (hN k).ne']
    rw [he]
    simpa using hl
  have hmlim : Tendsto (fun k => m k/N k) atTop (𝓝 a) := by
    have hl : Tendsto (fun k => m k/(N k-b k)*((N k-b k)/N k)) atTop (𝓝 (a*1)) := hm.mul hslim
    have he : (fun k => m k/(N k-b k)*((N k-b k)/N k))=(fun k => m k/N k) := by
      funext k
      have hs : N k-b k ≠ 0 := (sub_pos.mpr (hbN k)).ne'
      field_simp
    rw [he] at hl
    simpa using hl
  have hrlim : Tendsto (fun k => (N k-b k-m k)/N k) atTop (𝓝 (1-a)) := by
    simpa only [← sub_div] using hslim.sub hmlim
  have herlim : Tendsto (fun k => Er k/N k) atTop (𝓝 0) := by
    exact squeeze_zero (fun k => div_nonneg (hEr0 k) (hN k).le)
      (fun k => div_le_div_of_nonneg_right (hErE k) (hN k).le) hE
  refine ⟨hblim,hslim,hmlim,hrlim,?_⟩
  have hl : Tendsto (fun k => (Er k/N k)/((N k-b k-m k)/N k)) atTop (𝓝 (0/(1-a))) :=
    herlim.div hrlim (sub_pos.mpr ha).ne'
  have he : (fun k => (Er k/N k)/((N k-b k-m k)/N k))=
      (fun k => Er k/(N k-b k-m k)) := by
    funext k
    exact div_div_div_cancel_right₀ (hN k).ne' _ _
  rw [he] at hl
  simpa using hl

theorem logarithmic_remainder_bounds (a : ℝ)
    (ha0 : 1/4 < 1-a) (ha1 : 1-a < 1/2) :
    -2 < Real.logb 2 (1-a) ∧ Real.logb 2 (1-a) < -1 := by
  have hp : 0 < 1-a := by linarith
  constructor
  · apply (Real.lt_logb_iff_rpow_lt (by norm_num : (1:ℝ) < 2) hp).mpr
    norm_num [Real.rpow_neg,Real.rpow_two]
    exact ha0
  · apply (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ) < 2) hp).mpr
    norm_num
    exact ha1

/-- Two contacts require an integral dyadic logarithm of the continuation
fraction. The strict interval from D.5 excludes that possibility. -/
theorem two_contact_contradiction (a t0 t1 : ℝ)
    (ha0 : 1/4 < 1-a) (ha1 : 1-a < 1/2)
    (h0 : ∃ i : ℤ, t0+Real.logb 2 a=(i:ℝ))
    (h1 : ∃ j : ℤ, t1+Real.logb 2 a=(j:ℝ))
    (hstep : ∃ l : ℤ, t1=t0+Real.logb 2 (1-a)-(l:ℝ)) : False := by
  obtain ⟨i,hi⟩ := h0
  obtain ⟨j,hj⟩ := h1
  obtain ⟨l,hl⟩ := hstep
  obtain ⟨hlo,hhi⟩ := logarithmic_remainder_bounds a ha0 ha1
  have he : Real.logb 2 (1-a)=((j-i+l:ℤ):ℝ) := by
    push_cast
    linarith
  rw [he] at hlo hhi
  have hli : (-2:ℤ) < j-i+l := by exact_mod_cast hlo
  have hhi' : j-i+l < (-1:ℤ) := by exact_mod_cast hhi
  omega

end D8
end
end GD
