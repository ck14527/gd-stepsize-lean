import GD.OBSProfile

namespace GD
noncomputable section
open Set Filter
open scoped Topology

theorem periodicLipschitz_continuous (g : ℝ → ℝ) (h : PeriodicLipschitzPositive g) : Continuous g := by
  obtain ⟨L,hL,hg⟩ := h.2.2
  have hl : LipschitzWith ⟨L,hL⟩ g := by
    apply LipschitzWith.of_dist_le_mul
    simpa only [Real.dist_eq] using hg
  exact hl.continuous

theorem OBSPhase_error (g : ℝ → ℝ) (hg : OBSPhase g) :
    Tendsto (fun N : ℕ => C N-g (phase N)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨k0,hk0⟩ := hg.2 eps heps
  refine ⟨2^k0,?_⟩
  intro N hN
  have hn0 : N ≠ 0 := by
    have hp : 0 < (2:ℕ)^k0 := by positivity
    omega
  have hk : k0 ≤ N.log2 := (Nat.le_log2 hn0).mpr hN
  have h := hk0 N.log2 hk N (Nat.log2_self_le hn0) Nat.lt_log2_self.le
  simpa only [Real.dist_eq,sub_zero] using h

theorem phase_dyadic (m k : ℕ) (hm : 1 ≤ m) : phase (m*2^k)=phase m := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  change Int.fract (Real.logb 2 ((m*2^k:ℕ):ℝ))=Int.fract (Real.logb 2 (m:ℝ))
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Real.logb_mul hm0.ne' (by positivity),
    Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2),mul_one,Int.fract_add_natCast]

theorem OBSPhase_ray (g : ℝ → ℝ) (hg : OBSPhase g) (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun k : ℕ => C (m*2^k)) atTop (𝓝 (g (phase m))) := by
  have hns : StrictMono (fun k : ℕ => m*2^k) := by
    apply strictMono_nat_of_lt_succ
    intro k
    have hp : 0 < m*2^k := mul_pos (by omega) (by positivity)
    rw [pow_succ]
    nlinarith
  have h := (OBSPhase_error g hg).comp hns.tendsto_atTop
  have he : (fun k : ℕ => C (m*2^k)-g (phase (m*2^k)))=(fun k : ℕ => C (m*2^k)-g (phase m)) := by
    funext k
    rw [phase_dyadic m k hm]
  change Tendsto (fun k : ℕ => C (m*2^k)-g (phase (m*2^k))) atTop (𝓝 0) at h
  rw [he] at h
  simpa using h.add_const (g (phase m))

theorem Psi_unique (g : ℝ → ℝ) (hg : OBSPhase g) : g=Psi := by
  have hc := periodicLipschitz_continuous g hg.1
  have hseed : ∀ m : ℕ, 1 ≤ m → g (phase m)=Psi (phase m) := by
    intro m hm
    exact tendsto_nhds_unique (OBSPhase_ray g hg m hm) (OBSPhase_ray Psi Psi_OBSPhase m hm)
  let h := fun t : ℝ => g t-Psi t+Phi t
  have hh : h=Phi := by
    apply Phi_unique h ((hc.sub Psi_continuous).add Phi_continuous)
    · intro t
      dsimp only [h]
      rw [hg.1.2.1 t,Psi_periodic,Phi_periodic]
    · intro N hN
      dsimp only [h]
      rw [hseed N hN,sub_self,zero_add]
      exact U_phase_exact N hN
  funext t
  have he := congrFun hh t
  change g t-Psi t+Phi t=Phi t at he
  linarith

theorem Psi_extrema :
    ∃ a ∈ Icc (0:ℝ) 1, ∃ b ∈ Icc (0:ℝ) 1,
      Psi a=sInf (Psi '' Icc (0:ℝ) 1) ∧ Psi b=sSup (Psi '' Icc (0:ℝ) 1) ∧
      ∀ t : ℝ, Psi a ≤ Psi t ∧ Psi t ≤ Psi b := by
  have hne : (Icc (0:ℝ) 1).Nonempty := ⟨0,by norm_num⟩
  obtain ⟨a,ha,hamin⟩ := isCompact_Icc.exists_isMinOn hne Psi_continuous.continuousOn
  obtain ⟨b,hb,hbmax⟩ := isCompact_Icc.exists_isMaxOn hne Psi_continuous.continuousOn
  have hlo : IsLeast (Psi '' Icc (0:ℝ) 1) (Psi a) := by
    refine ⟨⟨a,ha,rfl⟩,?_⟩
    rintro y ⟨t,ht,rfl⟩
    exact hamin ht
  have hhi : IsGreatest (Psi '' Icc (0:ℝ) 1) (Psi b) := by
    refine ⟨⟨b,hb,rfl⟩,?_⟩
    rintro y ⟨t,ht,rfl⟩
    exact hbmax ht
  refine ⟨a,ha,b,hb,hlo.csInf_eq.symm,hhi.csSup_eq.symm,?_⟩
  intro t
  rw [← periodic_fract Psi Psi_periodic t]
  exact ⟨hamin ⟨Int.fract_nonneg t,(Int.fract_lt_one t).le⟩,
    hbmax ⟨Int.fract_nonneg t,(Int.fract_lt_one t).le⟩⟩

theorem Psi_range : Psi '' Icc (0:ℝ) 1=Icc (sInf (Psi '' Icc (0:ℝ) 1)) (sSup (Psi '' Icc (0:ℝ) 1)) := by
  obtain ⟨a,ha,b,hb,hea,heb,hbound⟩ := Psi_extrema
  rw [← hea,← heb]
  apply le_antisymm
  · rintro y ⟨t,ht,rfl⟩
    exact hbound t
  · exact isPreconnected_Icc.intermediate_value ha hb Psi_continuous.continuousOn

theorem Psi_mem_Clust (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : Psi t ∈ Clust C := by
  have hx := two_rpow_mem t ht
  refine ⟨gridHorizon ((2:ℝ)^t),gridHorizon_strictMono _ hx,?_⟩
  rw [Psi_on_unit t ht]
  exact obsGrid_tendsto _ hx

theorem C_Clust : Clust C=Icc (sInf (Psi '' Icc (0:ℝ) 1)) (sSup (Psi '' Icc (0:ℝ) 1)) := by
  obtain ⟨a,ha,b,hb,hea,heb,hbound⟩ := Psi_extrema
  apply le_antisymm
  · have he := Clust_eq_of_sub_tendsto_zero (OBSPhase_error Psi Psi_OBSPhase)
    rw [he]
    apply Clust_bounds
    intro N _
    rw [← hea,← heb]
    exact hbound (phase N)
  · intro l hl
    rw [← Psi_range] at hl
    obtain ⟨t,ht,rfl⟩ := hl
    exact Psi_mem_Clust t ht

/-- Block-uniform convergence, uniqueness, and cluster assertions of Theorem 6.3.
The explicit phase interpolant clauses are separate obligations. -/
theorem theorem_6_3_block_version : Targets.theorem_6_3_block_version := ⟨Psi_OBSPhase,Psi_unique,C_Clust⟩

end
end GD
