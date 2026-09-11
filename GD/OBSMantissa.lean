import GD.OBSDiscrete
import Mathlib.Topology.MetricSpace.Pseudo.Basic

namespace GD
noncomputable section
open Set Filter
open scoped Topology

def obsMantissa (x : ℝ) : ℝ := limUnder atTop (fun k : ℕ => obsGrid k x)

theorem dyadic_mesh_tendsto : Tendsto (fun k : ℕ => 1/(2:ℝ)^k) atTop (𝓝 0) := by
  simpa only [one_div] using tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2))

theorem obsGrid_tendsto (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    Tendsto (fun k : ℕ => obsGrid k x) atTop (𝓝 (obsMantissa x)) := by
  let f := fun k : ℕ => obsGrid k x+obsLip/(2:ℝ)^k
  have ha : Antitone f := by
    apply antitone_nat_of_succ_le
    intro k
    have h := obsGrid_step x hx k
    have he : obsLip/(2:ℝ)^(k+1)+obsLip/(2:ℝ)^(k+1)=obsLip/(2:ℝ)^k := by rw [pow_succ]; ring
    change obsGrid (k+1) x+obsLip/(2:ℝ)^(k+1) ≤ obsGrid k x+obsLip/(2:ℝ)^k
    linarith
  have hlower : ∀ k, cstar ≤ f k := by
    intro k
    have hn := (gridHorizon_bounds x hx k).1
    have hn1 := (Nat.one_le_pow k 2 (by norm_num)).trans hn
    have h := C_ge_cstar _ hn1
    have he : 0 ≤ obsLip/(2:ℝ)^k := div_nonneg obsLip_pos.le (by positivity)
    change cstar ≤ C (gridHorizon x k)+obsLip/(2:ℝ)^k
    linarith
  have hb : BddBelow (range f) := ⟨cstar,by rintro y ⟨k,rfl⟩; exact hlower k⟩
  have hf := tendsto_atTop_ciInf ha hb
  have herr : Tendsto (fun k : ℕ => obsLip/(2:ℝ)^k) atTop (𝓝 0) := by
    simpa using dyadic_mesh_tendsto.const_mul obsLip
  have hlim := hf.sub herr
  apply tendsto_nhds_limUnder
  refine ⟨⨅ k, f k,?_⟩
  simpa [f] using hlim

theorem obsMantissa_lipschitz (x y : ℝ) (hx : x ∈ Icc (1:ℝ) 2) (hy : y ∈ Icc (1:ℝ) 2) :
    |obsMantissa x-obsMantissa y| ≤ obsLip*|x-y| := by
  have hl := ((obsGrid_tendsto x hx).sub (obsGrid_tendsto y hy)).abs
  have hr := (tendsto_const_nhds (x:=|x-y|) |>.add dyadic_mesh_tendsto).const_mul obsLip
  simp only [add_zero] at hr
  exact le_of_tendsto_of_tendsto' hl hr (fun k => obsGrid_modulus k x y hx hy)

theorem obsMantissa_continuousOn : ContinuousOn obsMantissa (Icc (1:ℝ) 2) := by
  have hl : LipschitzOnWith ⟨obsLip,obsLip_pos.le⟩ obsMantissa (Icc (1:ℝ) 2) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Real.dist_eq] using obsMantissa_lipschitz x y hx hy
  exact hl.continuousOn

theorem obsMantissa_bounds (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    cstar ≤ obsMantissa x ∧ obsMantissa x ≤ 1/phiMin := by
  have hn : ∀ k, 1 ≤ gridHorizon x k := fun k =>
    (Nat.one_le_pow k 2 (by norm_num)).trans (gridHorizon_bounds x hx k).1
  have hlim := obsGrid_tendsto x hx
  constructor
  · exact ge_of_tendsto' hlim (fun k => C_ge_cstar _ (hn k))
  · apply le_of_tendsto' hlim
    intro k
    have h := (normalizedW_bounds _ (hn k)).1
    rw [obsGrid,C_eq_inverse_normalizedW]
    exact one_div_le_one_div_of_le phiMin_bounds.1 h

theorem obsMantissa_endpoints : obsMantissa 2=obsMantissa 1 := by
  have h2 := obsGrid_tendsto 2 (by norm_num)
  have h1 := (obsGrid_tendsto 1 (by norm_num)).comp (tendsto_add_atTop_nat 1)
  have he : ∀ k : ℕ, obsGrid k 2=obsGrid (k+1) 1 := by
    intro k
    unfold obsGrid gridHorizon
    simp only [one_mul,pow_succ]
    rw [mul_comm (2:ℝ)]
  exact tendsto_nhds_unique (h2.congr' (Eventually.of_forall he)) h1

theorem gridHorizon_point_mem (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) (k : ℕ) :
    (gridHorizon x k:ℝ)/(2:ℝ)^k ∈ Icc (1:ℝ) 2 ∧
    |x-(gridHorizon x k:ℝ)/(2:ℝ)^k| ≤ 1/(2:ℝ)^k := by
  have h := gridHorizon_bounds x hx k
  have hx0 : 0 < x := by linarith [hx.1]
  have hp : 0 < (2:ℝ)^k := by positivity
  have hlo : (gridHorizon x k:ℝ)/(2:ℝ)^k ≤ x := (div_le_iff₀ hp).mpr (Nat.floor_le (by positivity))
  refine ⟨⟨?_,hlo.trans hx.2⟩,?_⟩
  · apply (le_div_iff₀ hp).mpr
    have hc : (2:ℝ)^k ≤ (gridHorizon x k:ℝ) := by exact_mod_cast h.1
    simpa using hc
  · rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    have hh := div_le_div_of_nonneg_right (Nat.lt_floor_add_one (x*(2:ℝ)^k)).le hp.le
    rw [mul_div_cancel_right₀ x hp.ne',add_div] at hh
    exact (by dsimp only [gridHorizon]; linarith)

theorem obsGrid_uniform : TendstoUniformlyOn obsGrid obsMantissa atTop (Icc (1:ℝ) 2) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  have hmesh := dyadic_mesh_tendsto.const_mul (3*obsLip)
  simp only [mul_zero] at hmesh
  obtain ⟨l,hl⟩ := (hmesh.eventually (gt_mem_nhds (show (0:ℝ) < eps/2 by linarith))).exists
  have hsmall : 3*obsLip*(1/(2:ℝ)^l) < eps/2 := hl
  have hfinite : ∀ j : ℕ, j ∈ Finset.Icc (2^l) (2^(l+1)) →
      ∀ᶠ k in atTop, |obsGrid k ((j:ℝ)/(2:ℝ)^l)-obsMantissa ((j:ℝ)/(2:ℝ)^l)| < eps/2 := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have hx : (j:ℝ)/(2:ℝ)^l ∈ Icc (1:ℝ) 2 := by
      have hp : 0 < (2:ℝ)^l := by positivity
      constructor
      · apply (le_div_iff₀ hp).mpr
        have hc : (2:ℝ)^l ≤ (j:ℝ) := by exact_mod_cast hj'.1
        simpa using hc
      · apply (div_le_iff₀ hp).mpr
        have hc : (j:ℝ) ≤ (2:ℝ)^(l+1) := by exact_mod_cast hj'.2
        simpa [pow_succ,mul_comm] using hc
    have hh := (obsGrid_tendsto _ hx).sub_const (obsMantissa ((j:ℝ)/(2:ℝ)^l)) |>.abs
    simp only [sub_self,abs_zero] at hh
    exact hh.eventually (gt_mem_nhds (show (0:ℝ) < eps/2 by linarith))
  have hall := (eventually_all_finset (Finset.Icc ((2:ℕ)^l) (2^(l+1)))).mpr hfinite
  filter_upwards [hall,eventually_ge_atTop l] with k hk hkl
  intro x hx
  let j := gridHorizon x l
  let y : ℝ := (j:ℝ)/(2:ℝ)^l
  have hj := gridHorizon_bounds x hx l
  have hy := gridHorizon_point_mem x hx l
  have hmid := hk j (Finset.mem_Icc.mpr hj)
  have hg := obsGrid_modulus k x y hx hy.1
  have hh := obsMantissa_lipschitz x y hx hy.1
  have hdyad : 1/(2:ℝ)^k ≤ 1/(2:ℝ)^l :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hkl)
  have hdist : |x-y| ≤ 1/(2:ℝ)^l := hy.2
  have htri := abs_sub_le (obsGrid k x) (obsGrid k y) (obsMantissa x)
  have htri' := abs_sub_le (obsGrid k y) (obsMantissa y) (obsMantissa x)
  rw [abs_sub_comm (obsMantissa y)] at htri'
  have hmul := mul_le_mul_of_nonneg_left hdist obsLip_pos.le
  have hmul' := mul_le_mul_of_nonneg_left hdyad obsLip_pos.le
  rw [Real.dist_eq,abs_sub_comm]
  nlinarith

end
end GD
