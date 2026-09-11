import GD.ClusterPhase
import GD.Objective
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace GD
noncomputable section
open Set Filter
open scoped Topology

theorem B_phase_exact (N : ℕ) (hN : 1 ≤ N) : B N=1/(2*(N:ℝ)^p*Phi (phase N)-1) := by
  rw [B,U_phase_exact N hN]
  congr 2
  ring

theorem B_main_term (N : ℕ) (hN : 1 ≤ N) :
    (N:ℝ)^(-p)/(2*Phi (phase N))=1/(2*U N) := by
  have hn0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnp := Real.rpow_pos_of_pos hn0 p
  have hphi := Phi_pos (phase N)
  rw [U_phase_exact N hN,Real.rpow_neg hn0.le]
  field_simp
  <;> ring

theorem B_remainder_bound (N : ℕ) (hN : 1 ≤ N) :
    0 < B N-(N:ℝ)^(-p)/(2*Phi (phase N)) ∧
    B N-(N:ℝ)^(-p)/(2*Phi (phase N)) ≤ (N:ℝ)^(-2*p)/(2*phiMin^2) := by
  have hb := objective_remainder_bound (U_ge_one N hN)
  change 0 < B N-1/(2*U N) ∧ B N-1/(2*U N) ≤ 1/(2*(U N)^2) at hb
  rw [B_main_term N hN]
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hn0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := Real.rpow_pos_of_pos hn0 p
  have hmin := phiMin_bounds.1
  have hU : (N:ℝ)^p*phiMin ≤ U N := by
    rw [U_phase_exact N hN]
    exact mul_le_mul_of_nonneg_left (phiMin_attained.choose_spec.2.2 _) hp.le
  have hs := (sq_le_sq₀ (mul_pos hp hmin).le (U_nonneg N)).mpr hU
  have hi := one_div_le_one_div_of_le (by positivity : (0:ℝ) < 2*((N:ℝ)^p*phiMin)^2)
    (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 2))
  apply hi.trans_eq
  have he : (N:ℝ)^(-2*p)=((N:ℝ)^p)^(-2:ℝ) := by
    rw [← Real.rpow_mul hn0.le]
    congr 1
    ring
  rw [he,Real.rpow_neg hp.le,Real.rpow_two]
  field_simp
  <;> ring

theorem Clust_scale_iff {a : ℕ → ℝ} {c y : ℝ} (hc : c ≠ 0) :
    y ∈ Clust (fun N => c*a N) ↔ y/c ∈ Clust a := by
  constructor
  · rintro ⟨ns,hns,hl⟩
    refine ⟨ns,hns,?_⟩
    have h := hl.div_const c
    simpa only [mul_div_cancel_left₀ _ hc] using h
  · rintro ⟨ns,hns,hl⟩
    refine ⟨ns,hns,?_⟩
    have h := hl.const_mul c
    simpa only [mul_div_cancel₀ y hc] using h

theorem Clust_eq_of_sub_tendsto_zero {a b : ℕ → ℝ}
    (h : Tendsto (fun N => b N-a N) atTop (𝓝 0)) : Clust b=Clust a := by
  ext l
  constructor
  · rintro ⟨ns,hns,hl⟩
    refine ⟨ns,hns,?_⟩
    have hh := hl.sub (h.comp hns.tendsto_atTop)
    simpa using hh
  · rintro ⟨ns,hns,hl⟩
    refine ⟨ns,hns,?_⟩
    have hh := hl.add (h.comp hns.tendsto_atTop)
    simpa using hh

theorem nat_neg_power_tendsto : Tendsto (fun N : ℕ => (N:ℝ)^(-p)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop p_pos).comp tendsto_natCast_atTop_atTop

theorem B_scaled_remainder_tendsto :
    Tendsto (fun N : ℕ => (N:ℝ)^p*B N-(1/2)*((N:ℝ)^p*s N)) atTop (𝓝 0) := by
  have hup := nat_neg_power_tendsto.div_const (2*phiMin^2)
  simp only [zero_div] at hup
  apply squeeze_zero' (g:=fun N : ℕ => (N:ℝ)^(-p)/(2*phiMin^2)) _ _ hup
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hp : 0 ≤ (N:ℝ)^p := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hb := (B_remainder_bound N hN).1.le
    rw [B_main_term N hN] at hb
    have hh := mul_nonneg hp hb
    have he : (N:ℝ)^p*(B N-1/(2*U N))=(N:ℝ)^p*B N-(1/2)*((N:ℝ)^p*s N) := by
      unfold s
      ring
    rwa [he] at hh
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hn0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hp := Real.rpow_pos_of_pos hn0 p
    have hb := (B_remainder_bound N hN).2
    rw [B_main_term N hN] at hb
    have hh := mul_le_mul_of_nonneg_left hb hp.le
    have he : (N:ℝ)^p*((N:ℝ)^(-2*p)/(2*phiMin^2))=(N:ℝ)^(-p)/(2*phiMin^2) := by
      rw [← mul_div_assoc,← Real.rpow_add hn0]
      congr 2
      ring
    rw [he] at hh
    have he' : (N:ℝ)^p*(B N-1/(2*U N))=(N:ℝ)^p*B N-(1/2)*((N:ℝ)^p*s N) := by
      unfold s
      ring
    rwa [he'] at hh

theorem B_scaled_Clust : Clust (fun N : ℕ => (N:ℝ)^p*B N)=Icc (1/2) (1/(2*phiMin)) := by
  rw [Clust_eq_of_sub_tendsto_zero B_scaled_remainder_tendsto]
  ext y
  rw [Clust_scale_iff (by norm_num : (1/2:ℝ) ≠ 0),normalized_s_Clust]
  simp only [mem_Icc,div_div,div_one]
  have hmin := phiMin_bounds.1
  constructor
  · intro h
    constructor
    · linarith [h.1]
    · apply (le_div_iff₀ (by positivity : (0:ℝ) < 2*phiMin)).mpr
      have hh := (le_div_iff₀ hmin).mp h.2
      nlinarith
  · intro h
    constructor
    · linarith [h.1]
    · apply (le_div_iff₀ hmin).mpr
      have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 2*phiMin)).mp h.2
      nlinarith

/-- All scalar assertions of Theorem 5.8, including the uniform remainder and cluster interval.
The separate smooth-convex certificate interface is documented in the coverage report. -/
theorem theorem_5_8_scalar : Targets.theorem_5_8_scalar :=
  ⟨B_phase_exact,B_remainder_bound,B_scaled_Clust⟩

end
end GD
