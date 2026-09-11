import GD.PivotSpine

namespace GD
noncomputable section
open Set Filter
open scoped Topology

theorem rpow_p_q (x : ℝ) (hx : 0 ≤ x) : (x^p)^q=x := by
  rw [← Real.rpow_mul hx,p_mul_q,Real.rpow_one]

theorem rpow_q_p (x : ℝ) (hx : 0 ≤ x) : (x^q)^p=x := by
  rw [← Real.rpow_mul hx,mul_comm q p,p_mul_q,Real.rpow_one]

theorem cstar_inverse : 1/cstar=Bsup^p := by
  rw [cstar,Real.rpow_neg Bsup_pos.le]
  simp

theorem normalizedW_power (N : ℕ) (hN : 1 ≤ N) :
    (normalizedW N)^q=(W N)^q/(N:ℝ) := by
  rw [normalizedW,Real.div_rpow (W_pos N hN).le (Real.rpow_nonneg (Nat.cast_nonneg _) _),rpow_p_q _ (Nat.cast_nonneg _)]

theorem deficit_normalized (N : ℕ) (hN : 1 ≤ N) :
    deficit N/(N:ℝ)=Bsup-(normalizedW N)^q := by
  rw [normalizedW_power N hN,deficit,sub_div,mul_div_cancel_right₀ _]
  exact_mod_cast (show N ≠ 0 by omega)

theorem deficit_tendsto_of_C (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hC : Tendsto (fun k => C (n k)) atTop (𝓝 cstar)) :
    Tendsto (fun k => deficit (n k)/(n k:ℝ)) atTop (𝓝 0) := by
  have hD := (tendsto_const_nhds (x:=(1:ℝ))).div hC cstar_pos.ne'
  change Tendsto (fun k => 1/C (n k)) atTop (𝓝 (1/cstar)) at hD
  simp only [← normalizedW_eq_inverse_C,cstar_inverse] at hD
  have hq := hD.rpow_const (Or.inr q_pos.le)
  rw [rpow_p_q Bsup Bsup_pos.le] at hq
  have hh := hq.const_sub Bsup
  rw [sub_self] at hh
  apply hh.congr'
  filter_upwards [hn.eventually (eventually_ge_atTop 1)] with k hk
  exact (deficit_normalized (n k) hk).symm

theorem C_tendsto_of_deficit (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hE : Tendsto (fun k => deficit (n k)/(n k:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun k => C (n k)) atTop (𝓝 cstar) := by
  have hq : Tendsto (fun k => (normalizedW (n k))^q) atTop (𝓝 Bsup) := by
    have h := hE.const_sub Bsup
    rw [sub_zero] at h
    apply h.congr'
    filter_upwards [hn.eventually (eventually_ge_atTop 1)] with k hk
    rw [deficit_normalized (n k) hk]
    ring
  have hD : Tendsto (fun k => normalizedW (n k)) atTop (𝓝 (Bsup^p)) := by
    apply (hq.rpow_const (Or.inr p_pos.le)).congr'
    filter_upwards [hn.eventually (eventually_ge_atTop 1)] with k hk
    exact rpow_q_p _ (phiMin_bounds.1.le.trans (normalizedW_bounds _ hk).1)
  have h := (tendsto_const_nhds (x:=(1:ℝ))).div hD (Real.rpow_pos_of_pos Bsup_pos p).ne'
  change Tendsto (fun k => 1/normalizedW (n k)) atTop (𝓝 (1/Bsup^p)) at h
  have he : 1/Bsup^p=cstar := by rw [← cstar_inverse]; simp
  simpa only [he,← C_eq_inverse_normalizedW] using h

theorem sigma_continuous : Continuous (fun z : ℝ × ℝ => sigma z.1 z.2) := by
  unfold sigma
  exact ((continuous_const.mul ((Real.continuous_rpow_const q_pos.le).comp continuous_fst)).add
    ((Real.continuous_rpow_const q_pos.le).comp continuous_snd)).sub
    ((Real.continuous_rpow_const q_pos.le).comp A_continuous)

theorem support_contact_fraction (a : ℝ) (ha : a ∈ Ioc (0:ℝ) 1)
    (hs : sigma (a^p) ((Bsup*(1-a))^p)=0) : a=alpha := by
  have hB := Bsup_pos
  by_cases h1 : a=1
  · subst a
    simp only [sub_self,mul_zero,Real.zero_rpow p_pos.ne',Real.one_rpow,sigma,A_zero_right,
      mul_one,Real.zero_rpow q_pos.ne',add_zero,sub_eq_zero] at hs
    exact (ne_of_lt Bsup_gt_two_rpow hs.symm).elim
  have har : 0 < 1-a := sub_pos.mpr (lt_of_le_of_ne ha.2 h1)
  have hu : 0 < a^p := Real.rpow_pos_of_pos ha.1 p
  have hw : 0 < (Bsup*(1-a))^p := Real.rpow_pos_of_pos (mul_pos hB har) p
  have hEq : (A (a^p) ((Bsup*(1-a))^p))^q=Bsup*(a^p)^q+((Bsup*(1-a))^p)^q := by
    unfold sigma at hs
    linarith
  have hr := (support_positive _ _ hu hw).2.mp hEq
  have hrq := congrArg (fun x : ℝ => x^q) hr
  change (a^p/((Bsup*(1-a))^p))^q=tau^q at hrq
  rw [Real.div_rpow hu.le hw.le,rpow_p_q a ha.1.le,rpow_p_q _ (mul_pos hB har).le] at hrq
  have hh := (div_eq_iff (mul_pos hB har).ne').mp hrq
  unfold alpha
  apply (eq_div_iff (show 1+Bsup*tau^q ≠ 0 by have := tau_positive; positivity)).mpr
  nlinarith

theorem power_scaled_tendsto (u n : ℕ → ℝ) (a : ℝ) (hu : ∀ k, 0 ≤ u k) (hn : ∀ k, 0 < n k)
    (h : Tendsto (fun k => (u k)^q/n k) atTop (𝓝 a)) :
    Tendsto (fun k => u k/(n k)^p) atTop (𝓝 (a^p)) := by
  apply (h.rpow_const (Or.inr p_pos.le)).congr'
  exact Eventually.of_forall (fun k => by change ((u k)^q/n k)^p=u k/(n k)^p; rw [Real.div_rpow (Real.rpow_nonneg (hu k) _) (hn k).le,rpow_q_p _ (hu k)])

end
end GD
