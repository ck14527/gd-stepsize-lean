import GD.PhaseTheorem

namespace GD
noncomputable section
open Set Filter
open scoped Topology

def gridHorizon (x : ℝ) (k : ℕ) : ℕ := Nat.floor (x*(2:ℝ)^k)

theorem gridHorizon_bounds (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) (k : ℕ) :
    2^k ≤ gridHorizon x k ∧ gridHorizon x k ≤ 2^(k+1) := by
  have hp : 0 < (2:ℝ)^k := by positivity
  have hx0 : 0 < x := by linarith [hx.1]
  constructor
  · apply (Nat.le_floor_iff (mul_pos hx0 hp).le).mpr
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    nlinarith [hx.1]
  · have hle := Nat.floor_le (mul_pos hx0 hp).le
    have hu : (gridHorizon x k:ℝ) ≤ (2:ℝ)^(k+1) := by
      rw [pow_succ]
      change (Nat.floor (x*(2:ℝ)^k):ℝ) ≤ (2:ℝ)^k*2
      nlinarith [hx.2]
    exact_mod_cast hu

theorem gridHorizon_strictMono (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) : StrictMono (gridHorizon x) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hx0 : 0 < x := by linarith [hx.1]
  have hp : 0 < (2:ℝ)^k := by positivity
  have hy : 1 ≤ x*(2:ℝ)^k := by
    have hpow : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
    nlinarith [hx.1]
  have hfloor := Nat.floor_le (mul_pos hx0 hp).le
  have hn : gridHorizon x k+1 ≤ gridHorizon x (k+1) := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ x*(2:ℝ)^(k+1))).mpr
    simp only [Nat.cast_add,Nat.cast_one,pow_succ,gridHorizon]
    nlinarith
  omega

theorem gridHorizon_tendsto (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    Tendsto (fun k => (gridHorizon x k:ℝ)/(2:ℝ)^k) atTop (𝓝[Icc (1:ℝ) 2] x) := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hinv : Tendsto (fun k : ℕ => ((2:ℝ)^k)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2))
  have hlo : ∀ k, (gridHorizon x k:ℝ)/(2:ℝ)^k ≤ x := by
    intro k
    exact (div_le_iff₀ (by positivity)).mpr (Nat.floor_le (by positivity))
  have hgap : ∀ k, x-(gridHorizon x k:ℝ)/(2:ℝ)^k ≤ ((2:ℝ)^k)⁻¹ := by
    intro k
    have h := Nat.lt_floor_add_one (x*(2:ℝ)^k)
    have he := (div_le_div_of_nonneg_right h.le (by positivity : 0 ≤ (2:ℝ)^k))
    dsimp only [gridHorizon]
    have hp : (2:ℝ)^k ≠ 0 := by positivity
    rw [mul_div_cancel_right₀ x hp,add_div] at he
    rw [← one_div]
    linarith
  have hlim := squeeze_zero (fun k => sub_nonneg.mpr (hlo k)) hgap hinv
  have hl := tendsto_const_nhds (x:=x) |>.sub hlim
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨by simpa using hl,Eventually.of_forall ?_⟩
  intro k
  have hb := gridHorizon_bounds x hx k
  constructor
  · apply (le_div_iff₀ (by positivity)).mpr
    have hc : (2:ℝ)^k ≤ (gridHorizon x k:ℝ) := by exact_mod_cast hb.1
    simpa using hc
  · exact (hlo k).trans hx.2

theorem normalized_grid_limit (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    Tendsto (fun k => U (gridHorizon x k)/(gridHorizon x k:ℝ)^p) atTop (𝓝 (F x/x^p)) := by
  have ht := gridHorizon_tendsto x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hf := (F_continuousOn x hx).tendsto.comp ht
  have hp := (tendsto_nhds_of_tendsto_nhdsWithin ht).rpow_const (p:=p) (Or.inl hx0.ne')
  have hr := hf.div hp (Real.rpow_pos_of_pos hx0 p).ne'
  apply hr.congr'
  apply Eventually.of_forall
  intro k
  have hb := gridHorizon_bounds x hx k
  have hn0 : 0 < (gridHorizon x k:ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < (2:ℕ)^k) hb.1)
  dsimp only [Pi.div_apply,Function.comp_apply]
  rw [F_grid k _ hb.1 hb.2,Real.div_rpow hn0.le (by positivity),
    ← Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2),two_rpow_p]
  have hrho := rho_pos
  field_simp

theorem Phi_mem_Clust (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    Phi t ∈ Clust (fun N : ℕ => U N/(N:ℝ)^p) := by
  have hx := two_rpow_mem t ht
  refine ⟨gridHorizon ((2:ℝ)^t),gridHorizon_strictMono _ hx,?_⟩
  have h := normalized_grid_limit _ hx
  have hp : ((2:ℝ)^t)^p=rho^t := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),mul_comm t p,
      Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),two_rpow_p]
  have he : F ((2:ℝ)^t)/((2:ℝ)^t)^p=Phi t := by
    rw [Phi_eq_profile t ht,phaseProfile,hp,Real.rpow_neg rho_pos.le]
    ring
  rwa [he] at h

theorem Clust_bounds {a : ℕ → ℝ} {lo hi : ℝ}
    (hb : ∀ N : ℕ, 1 ≤ N → lo ≤ a N ∧ a N ≤ hi) : Clust a ⊆ Icc lo hi := by
  rintro l ⟨ns,hns,hl⟩
  have hn : ∀ᶠ k in atTop, 1 ≤ ns k := hns.tendsto_atTop.eventually (eventually_ge_atTop 1)
  exact ⟨ge_of_tendsto hl (hn.mono (fun k hk => (hb _ hk).1)),
    le_of_tendsto hl (hn.mono (fun k hk => (hb _ hk).2))⟩

theorem normalized_U_bounds (N : ℕ) (hN : 1 ≤ N) :
    phiMin ≤ U N/(N:ℝ)^p ∧ U N/(N:ℝ)^p ≤ 1 := by
  rw [← Phi_seed N hN]
  exact ⟨phiMin_attained.choose_spec.2.2 _,Phi_le_one _⟩

theorem normalized_U_Clust : Clust (fun N : ℕ => U N/(N:ℝ)^p)=Icc phiMin 1 := by
  apply le_antisymm
  · exact Clust_bounds normalized_U_bounds
  · intro l hl
    rw [← Phi_range] at hl
    obtain ⟨t,ht,rfl⟩ := hl
    exact Phi_mem_Clust t ht

theorem normalized_s_inverse (N : ℕ) (hN : 1 ≤ N) : (N:ℝ)^p*s N=1/(U N/(N:ℝ)^p) := by
  have hn0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := Real.rpow_pos_of_pos hn0 p
  have hu := U_pos (show 0 < N by omega)
  unfold s
  field_simp

theorem normalized_s_Clust : Clust (fun N : ℕ => (N:ℝ)^p*s N)=Icc 1 (1/phiMin) := by
  have hmin := phiMin_bounds.1
  apply le_antisymm
  · apply Clust_bounds
    intro N hN
    have hb := normalized_U_bounds N hN
    have ha0 : 0 < U N/(N:ℝ)^p := hmin.trans_le hb.1
    rw [normalized_s_inverse N hN]
    constructor
    · exact (le_div_iff₀ ha0).mpr (by simpa using hb.2)
    · exact one_div_le_one_div_of_le hmin hb.1
  · intro l hl
    have hl0 : 0 < l := by linarith [hl.1]
    have hr : 1/l ∈ Icc phiMin 1 := by
      constructor
      · apply (le_div_iff₀ hl0).mpr
        have h := (le_div_iff₀ hmin).mp hl.2
        nlinarith
      · exact (div_le_one hl0).mpr hl.1
    rw [← normalized_U_Clust] at hr
    obtain ⟨ns,hns,hn⟩ := hr
    refine ⟨ns,hns,?_⟩
    have hinv := (tendsto_const_nhds (x:=(1:ℝ))).div hn (one_div_pos.mpr hl0).ne'
    simp only [one_div_one_div] at hinv
    apply hinv.congr'
    have hs : ∀ᶠ k in atTop, 1 ≤ ns k := hns.tendsto_atTop.eventually (eventually_ge_atTop 1)
    exact hs.mono (fun k hk => (normalized_s_inverse _ hk).symm)

theorem no_limit_of_two_clusters {a : ℕ → ℝ} {x y : ℝ} (hx : x ∈ Clust a) (hy : y ∈ Clust a)
    (hne : x ≠ y) : ¬∃ l, Tendsto a atTop (𝓝 l) := by
  rintro ⟨l,hl⟩
  obtain ⟨ns,hns,hxlim⟩ := hx
  obtain ⟨ms,hms,hylim⟩ := hy
  have hx' := tendsto_nhds_unique hxlim (hl.comp hns.tendsto_atTop)
  have hy' := tendsto_nhds_unique hylim (hl.comp hms.tendsto_atTop)
  exact hne (hx'.trans hy'.symm)

/-- Corollary 5.7 with actual strictly increasing integer subsequences. -/
theorem corollary_5_7 : Targets.corollary_5_7 := by
  refine ⟨normalized_U_Clust,normalized_s_Clust,?_,?_⟩
  · apply no_limit_of_two_clusters (x:=phiMin) (y:=1)
    · rw [normalized_U_Clust]; exact ⟨le_rfl,phiMin_bounds.2.le⟩
    · rw [normalized_U_Clust]; exact ⟨phiMin_bounds.2.le,le_rfl⟩
    · exact phiMin_bounds.2.ne
  · have hlt : 1 < 1/phiMin := (lt_div_iff₀ phiMin_bounds.1).mpr (by simpa using phiMin_bounds.2)
    apply no_limit_of_two_clusters (x:=1) (y:=1/phiMin)
    · rw [normalized_s_Clust]; exact ⟨le_rfl,hlt.le⟩
    · rw [normalized_s_Clust]; exact ⟨hlt.le,le_rfl⟩
    · exact hlt.ne

end
end GD
