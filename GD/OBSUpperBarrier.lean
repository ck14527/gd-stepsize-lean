import GD.OBSConstant

namespace GD
noncomputable section
open Set Filter
open scoped Topology

theorem floor_ratio_tendsto (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun k => (Nat.floor (a*(n k:ℝ)):ℝ)/(n k:ℝ)) atTop (𝓝 a) := by
  have hinv : Tendsto (fun k => 1/(n k:ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hn)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g:=fun k => a-1/(n k:ℝ)) (h:=fun _ => a)
  · simpa using tendsto_const_nhds.sub hinv
  · exact tendsto_const_nhds
  · filter_upwards [hn.eventually (eventually_ge_atTop 1)] with k hk
    have hn0 : 0 < (n k:ℝ) := by exact_mod_cast (show 0 < n k by omega)
    have hh := div_le_div_of_nonneg_right (Nat.lt_floor_add_one (a*(n k:ℝ))).le hn0.le
    rw [mul_div_cancel_right₀ _ hn0.ne',add_div] at hh
    linarith
  · filter_upwards [hn.eventually (eventually_ge_atTop 1)] with k hk
    have hn0 : 0 < (n k:ℝ) := by exact_mod_cast (show 0 < n k by omega)
    exact (div_le_iff₀ hn0).mpr (Nat.floor_le (mul_nonneg ha hn0.le))

theorem nat_atTop_of_ratio (m n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (a : ℝ) (ha : 0 < a)
    (h : Tendsto (fun k => (m k:ℝ)/(n k:ℝ)) atTop (𝓝 a)) : Tendsto m atTop atTop := by
  apply tendsto_atTop.mpr
  intro j
  have hr := h.eventually (lt_mem_nhds (show a/2 < a by linarith))
  have hnc : Tendsto (fun k => (n k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  filter_upwards [hr,hn.eventually (eventually_ge_atTop 1),hnc.eventually (eventually_ge_atTop ((j:ℝ)/(a/2)))] with k hk hkn hj
  have hn0 : 0 < (n k:ℝ) := by exact_mod_cast (show 0 < n k by omega)
  have hm := (lt_div_iff₀ hn0).mp hk
  have hh := (div_le_iff₀ (show 0 < a/2 by linarith)).mp hj
  exact_mod_cast (show (j:ℝ) ≤ m k by nlinarith)

theorem floor_split_limits (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (a : ℝ) (ha : a ∈ Ioo (0:ℝ) 1) :
    let m := fun k => Nat.floor (a*(n k:ℝ))
    let r := fun k => n k-m k
    Tendsto m atTop atTop ∧ Tendsto r atTop atTop ∧
    Tendsto (fun k => (m k:ℝ)/(n k:ℝ)) atTop (𝓝 a) ∧
    Tendsto (fun k => (r k:ℝ)/(n k:ℝ)) atTop (𝓝 (1-a)) ∧
    ∀ᶠ k in atTop, 1 ≤ m k ∧ m k < n k := by
  let m := fun k => Nat.floor (a*(n k:ℝ))
  let r := fun k => n k-m k
  have hml := floor_ratio_tendsto n hn a ha.1.le
  have hm := nat_atTop_of_ratio m n hn a ha.1 hml
  have hmn : ∀ k, m k ≤ n k := by
    intro k
    have hh := Nat.floor_mono (mul_le_of_le_one_left (Nat.cast_nonneg (n k)) ha.2.le)
    simpa only [Nat.floor_natCast] using hh
  have hrl : Tendsto (fun k => (r k:ℝ)/(n k:ℝ)) atTop (𝓝 (1-a)) := by
    have h := (tendsto_const_nhds (x:=(1:ℝ))).sub hml
    apply h.congr'
    filter_upwards [hn.eventually (eventually_ge_atTop 1)] with k hk
    have hn0 : (n k:ℝ) ≠ 0 := by exact_mod_cast (show n k ≠ 0 by omega)
    dsimp only [r]
    rw [Nat.cast_sub (hmn k),sub_div,div_self hn0]
  have hr := nat_atTop_of_ratio r n hn (1-a) (sub_pos.mpr ha.2) hrl
  refine ⟨hm,hr,hml,hrl,?_⟩
  filter_upwards [hm.eventually (eventually_ge_atTop 1),hr.eventually (eventually_ge_atTop 1)] with k hk hk'
  change 1 ≤ m k at hk
  change 1 ≤ r k at hk'
  change 1 ≤ m k ∧ m k < n k
  exact ⟨hk,by change 1 ≤ n k-m k at hk'; omega⟩

theorem C_eventually_le_max_add (M δ : ℝ) (hM : ∀ t, Psi t ≤ M) (hδ : 0 < δ) :
    ∀ᶠ N in atTop, C N ≤ M+δ := by
  filter_upwards [(OBSPhase_error Psi Psi_OBSPhase).eventually (gt_mem_nhds hδ)] with N hN
  have hh := hM (phase N)
  linarith

theorem normalized_pivot_lower (N m : ℕ) (hm : 1 ≤ m) (hmN : m < N) :
    A (U m/(N:ℝ)^p) (W (N-m)/(N:ℝ)^p) ≤ normalizedW N := by
  have hn0 : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp : 0 < (N:ℝ)^p := Real.rpow_pos_of_pos hn0 p
  have h := W_pivot_lower N m hm hmN
  have he := A_hom (inv_nonneg.mpr hp.le) (U_nonneg m) (W_pos (N-m) (by omega)).le
  simp only [← div_eq_inv_mul] at he
  rw [he,normalizedW,div_eq_inv_mul]
  simpa only [div_eq_inv_mul] using mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hp.le)

/-- Bellman test at a cluster attaining the global phase maximum; every
continuation estimate follows from the already proved uniform phase law. -/
theorem max_phase_Bellman_delta (M a δ : ℝ) (hM0 : 0 < M) (hM : ∀ t, Psi t ≤ M)
    (hcl : M ∈ Clust C) (ha : a ∈ Ioo (0:ℝ) 1) (hδ : 0 < δ) :
    A (phiMin*a^p) ((1/(M+δ))*(1-a)^p) ≤ 1/M := by
  obtain ⟨n,hn,hCn⟩ := hcl
  have hnt := hn.tendsto_atTop
  let m := fun k => Nat.floor (a*(n k:ℝ))
  let r := fun k => n k-m k
  have hs := floor_split_limits n hnt a ha
  have hD : Tendsto (fun k => normalizedW (n k)) atTop (𝓝 (1/M)) := by
    have h := (tendsto_const_nhds (x:=(1:ℝ))).div hCn hM0.ne'
    change Tendsto (fun k => 1/C (n k)) atTop (𝓝 (1/M)) at h
    simpa only [← normalizedW_eq_inverse_C] using h
  have hmp := (Real.continuousAt_rpow_const a p (Or.inl ha.1.ne')).tendsto.comp hs.2.2.1
  have hrp := (Real.continuousAt_rpow_const (1-a) p (Or.inl (sub_pos.mpr ha.2).ne')).tendsto.comp hs.2.2.2.1
  have hA : Tendsto (fun k => A (phiMin*((m k:ℝ)/(n k:ℝ))^p)
      ((1/(M+δ))*((r k:ℝ)/(n k:ℝ))^p)) atTop
      (𝓝 (A (phiMin*a^p) ((1/(M+δ))*(1-a)^p))) :=
    A_continuous.continuousAt.tendsto.comp ((hmp.const_mul phiMin).prodMk_nhds (hrp.const_mul (1/(M+δ))))
  apply le_of_tendsto_of_tendsto hA hD
  filter_upwards [hs.2.2.2.2,hs.2.1.eventually (C_eventually_le_max_add M δ hM hδ)] with k hk hCr
  have hm : 1 ≤ m k := hk.1
  have hmn : m k < n k := hk.2
  have hr : 1 ≤ r k := by dsimp only [r]; omega
  have hn0 : 0 < (n k:ℝ) := by exact_mod_cast (show 0 < n k by omega)
  have hm0 : 0 < (m k:ℝ) := by exact_mod_cast (show 0 < m k by omega)
  have hr0 : 0 < (r k:ℝ) := by exact_mod_cast (show 0 < r k by omega)
  have hden : 0 < M+δ := by linarith
  have hCpos : 0 < C (r k) := cstar_pos.trans_le (C_ge_cstar _ hr)
  have hw : 1/(M+δ) ≤ normalizedW (r k) := by
    rw [normalizedW_eq_inverse_C]
    exact one_div_le_one_div_of_le hCpos hCr
  have hu := (normalized_U_bounds (m k) hm).1
  have hu' : phiMin*((m k:ℝ)/(n k:ℝ))^p ≤ U (m k)/(n k:ℝ)^p := by
    rw [Real.div_rpow hm0.le hn0.le]
    have hh := mul_le_mul_of_nonneg_right hu (Real.rpow_nonneg hm0.le p)
    rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hm0 p).ne'] at hh
    exact (by simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hh (Real.rpow_nonneg hn0.le p))
  have hw' : (1/(M+δ))*((r k:ℝ)/(n k:ℝ))^p ≤ W (r k)/(n k:ℝ)^p := by
    rw [Real.div_rpow hr0.le hn0.le]
    have hh := mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hr0.le p)
    rw [normalizedW,div_mul_cancel₀ _ (Real.rpow_pos_of_pos hr0 p).ne'] at hh
    exact (by simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hh (Real.rpow_nonneg hn0.le p))
  exact (A_mono (mul_nonneg phiMin_bounds.1.le (Real.rpow_nonneg (by positivity) _))
    (mul_nonneg (one_div_pos.mpr hden).le (Real.rpow_nonneg (by positivity) _)) hu' hw').trans
    (normalized_pivot_lower (n k) (m k) hm hmn)

theorem max_phase_Bellman (M a : ℝ) (hM0 : 0 < M) (hM : ∀ t, Psi t ≤ M)
    (hcl : M ∈ Clust C) (ha : a ∈ Ioo (0:ℝ) 1) :
    A (phiMin*a^p) ((1/M)*(1-a)^p) ≤ 1/M := by
  have hinv : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 (0:ℝ)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have h := (tendsto_const_nhds (x:=(1:ℝ))).div (hinv.const_add M) (by simpa using hM0.ne')
  simp only [add_zero] at h
  have hA : Tendsto (fun k : ℕ => A (phiMin*a^p) ((1/(M+1/((k:ℝ)+1)))*(1-a)^p)) atTop
      (𝓝 (A (phiMin*a^p) ((1/M)*(1-a)^p))) :=
    A_continuous.continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds (h.mul_const ((1-a)^p)))
  exact le_of_tendsto' hA (fun k => max_phase_Bellman_delta M a _ hM0 hM hcl ha (by positivity))

theorem support_barrier_of_tests (e d : ℝ) (he : 0 < e) (hd : 0 < d)
    (htest : ∀ b : ℝ, 0 < b → A e (d*b^p) ≤ d*(1+b)^p) : Bsup^p*e ≤ d := by
  have htau := tau_positive
  let b := (e/(d*tau))^q
  have hb : 0 < b := Real.rpow_pos_of_pos (by positivity) _
  have hbp : b^p=e/(d*tau) := by
    dsimp only [b]
    rw [← Real.rpow_mul (by positivity : 0 ≤ e/(d*tau)),mul_comm q p,p_mul_q,Real.rpow_one]
  have hratio : e/(d*b^p)=tau := by rw [hbp]; field_simp [hd.ne',he.ne',htau.ne'] <;> ring
  have hcontact := (support_positive e (d*b^p) he (mul_pos hd (Real.rpow_pos_of_pos hb _))).2.mpr hratio
  have hpow := Real.rpow_le_rpow (A_nonneg he.le (by positivity)) (htest b hb) q_pos.le
  rw [hcontact] at hpow
  simp only [Real.mul_rpow hd.le (Real.rpow_nonneg hb.le p),
    Real.mul_rpow hd.le (Real.rpow_nonneg (show 0 ≤ 1+b by linarith) p),
    ← Real.rpow_mul hb.le,← Real.rpow_mul (show 0 ≤ 1+b by linarith),p_mul_q,Real.rpow_one] at hpow
  have hs : Bsup*e^q ≤ d^q := by nlinarith
  have hh := Real.rpow_le_rpow (mul_nonneg Bsup_pos.le (Real.rpow_nonneg he.le _)) hs p_pos.le
  rw [Real.mul_rpow Bsup_pos.le (Real.rpow_nonneg he.le _),← Real.rpow_mul he.le,
    ← Real.rpow_mul hd.le,mul_comm q p,p_mul_q,Real.rpow_one,Real.rpow_one] at hh
  exact hh

theorem max_phase_support_bound (M : ℝ) (hM0 : 0 < M) (hM : ∀ t, Psi t ≤ M)
    (hcl : M ∈ Clust C) : Bsup^p*phiMin ≤ 1/M := by
  apply support_barrier_of_tests phiMin (1/M) phiMin_bounds.1 (one_div_pos.mpr hM0)
  intro b hb
  have hden : 0 < 1+b := by linarith
  let a := 1/(1+b)
  have ha : a ∈ Ioo (0:ℝ) 1 := ⟨one_div_pos.mpr hden,(div_lt_one hden).mpr (by linarith)⟩
  have ha' : 1-a=b/(1+b) := by dsimp only [a]; field_simp <;> ring
  have h := max_phase_Bellman M a hM0 hM hcl ha
  have hp : 0 < (1+b)^p := Real.rpow_pos_of_pos hden p
  have hscale := A_hom hp.le
    (mul_nonneg phiMin_bounds.1.le (Real.rpow_nonneg ha.1.le p))
    (mul_nonneg (one_div_pos.mpr hM0).le (Real.rpow_nonneg (sub_pos.mpr ha.2).le p))
  have hu : (1+b)^p*(phiMin*a^p)=phiMin := by
    dsimp only [a]
    rw [Real.div_rpow (by norm_num) hden.le,Real.one_rpow]
    field_simp
  have hw : (1+b)^p*((1/M)*(1-a)^p)=(1/M)*b^p := by
    rw [ha',Real.div_rpow hb.le hden.le]
    field_simp <;> ring
  rw [hu,hw] at hscale
  have hm := mul_le_mul_of_nonneg_left h hp.le
  rw [← hscale] at hm
  simpa only [mul_comm ((1+b)^p) (1/M)] using hm

theorem proposition_D_9 : Targets.proposition_D_9 := by
  obtain ⟨a,ha,b,hb,hea,heb,hbound⟩ := Psi_extrema
  have hM := max_phase_support_bound (Psi b) (Psi_pos b) (fun t => (hbound t).2) (Psi_mem_Clust b hb)
  have hupper : Psi b ≤ cstar/phiMin := by
    have hbp := Real.rpow_pos_of_pos Bsup_pos p
    rw [cstar,Real.rpow_neg Bsup_pos.le,← one_div,div_div]
    apply (le_div_iff₀ (mul_pos hbp phiMin_bounds.1)).mpr
    have hh := (le_div_iff₀ (Psi_pos b)).mp hM
    nlinarith
  intro t
  exact (hbound t).2.trans hupper

end
end GD
