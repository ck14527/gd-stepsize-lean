import GD.OBSPhaseTheorem

namespace GD
noncomputable section
open Set Filter
open scoped Topology

theorem A_continuous : Continuous (fun z : ℝ × ℝ => A z.1 z.2) := by
  unfold A
  fun_prop

theorem tau_positive : 0 < tau := by
  unfold tau
  exact div_pos (sub_pos.mpr lemma_6_4.1.2) (mul_pos (by norm_num) (sq_pos_of_pos lemma_6_4.1.1))

theorem scaled_floor_limit (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun k : ℕ => (Nat.floor (x*(2:ℝ)^k):ℝ)/(2:ℝ)^k) atTop (𝓝 x) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g:=fun k : ℕ => x-1/(2:ℝ)^k) (h:=fun _ : ℕ => x)
  · simpa using tendsto_const_nhds.sub dyadic_mesh_tendsto
  · exact tendsto_const_nhds
  · intro k
    have h := (Nat.lt_floor_add_one (x*(2:ℝ)^k)).le
    have hh := (div_le_div_of_nonneg_right h (show 0 ≤ (2:ℝ)^k by positivity))
    rw [mul_div_cancel_right₀ _ (by positivity),add_div] at hh
    linarith
  · intro k
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^k)).mpr
    exact Nat.floor_le (mul_nonneg hx (by positivity))

theorem scaled_floor_atTop (x : ℝ) (hx : 0 < x) :
    Tendsto (fun k : ℕ => Nat.floor (x*(2:ℝ)^k)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  have h := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)).eventually
    (eventually_ge_atTop ((n:ℝ)/x))
  filter_upwards [h] with k hk
  apply (Nat.le_floor_iff (by positivity : 0 ≤ x*(2:ℝ)^k)).mpr
  have hh := (div_le_iff₀ hx).mp hk
  simpa [mul_comm] using hh

theorem normalizedW_eq_inverse_C (N : ℕ) : normalizedW N=1/C N := by
  rw [C_eq_inverse_normalizedW]
  simp

theorem normalizedW_limit_of_constant (c : ℝ) (hc : ∀ t, Psi t=c) :
    Tendsto normalizedW atTop (𝓝 (1/c)) := by
  have hc0 : 0 < c := hc 0 ▸ Psi_pos 0
  have h := OBSPhase_error Psi Psi_OBSPhase
  have he : (fun N : ℕ => C N-Psi (phase N))=(fun N : ℕ => C N-c) := by
    funext N
    rw [hc]
  rw [he] at h
  have hC : Tendsto C atTop (𝓝 c) := by simpa using h.add_const c
  have hi := (tendsto_const_nhds (x:=(1:ℝ))).div hC hc0.ne'
  change Tendsto (fun N => 1/C N) atTop (𝓝 (1/c)) at hi
  simpa only [← normalizedW_eq_inverse_C] using hi

theorem scaledW_limit (n : ℕ → ℕ) (x d : ℝ) (hx : 0 < x)
    (hn : Tendsto n atTop atTop)
    (hnx : Tendsto (fun k => (n k:ℝ)/(2:ℝ)^k) atTop (𝓝 x))
    (hW : Tendsto normalizedW atTop (𝓝 d)) :
    Tendsto (fun k => W (n k)/rho^k) atTop (𝓝 (d*x^p)) := by
  have hp := (Real.continuousAt_rpow_const x p (Or.inl hx.ne')).tendsto.comp hnx
  have hlim := (hW.comp hn).mul hp
  apply hlim.congr'
  filter_upwards [hn.eventually (eventually_ge_atTop 1)] with k hk
  have hn0 : 0 < (n k:ℝ) := by exact_mod_cast (show 0 < n k by omega)
  change (W (n k)/(n k:ℝ)^p)*((n k:ℝ)/(2:ℝ)^k)^p=W (n k)/rho^k
  rw [Real.div_rpow hn0.le (by positivity),← Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2),two_rpow_p]
  field_simp

theorem constant_Bellman (c b : ℝ) (hc : ∀ t, Psi t=c) (hb : 0 < b) :
    A 1 ((1/c)*b^p) ≤ (1/c)*(1+b)^p := by
  let r := fun k : ℕ => Nat.floor (b*(2:ℝ)^k)
  let n := fun k : ℕ => 2^k+r k
  have hr := scaled_floor_atTop b hb
  have hn : Tendsto n atTop atTop := by
    apply tendsto_atTop_mono (fun k => Nat.le_add_left (r k) (2^k)) hr
  have hnr : Tendsto (fun k => (n k:ℝ)/(2:ℝ)^k) atTop (𝓝 (1+b)) := by
    have h := (scaled_floor_limit b hb.le).const_add 1
    convert h using 1
    funext k
    simp only [n,r,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,add_div,div_self (by positivity : (2:ℝ)^k ≠ 0)]
  have hW := normalizedW_limit_of_constant c hc
  have hrl := scaledW_limit r b (1/c) hb hr (scaled_floor_limit b hb.le) hW
  have hnl := scaledW_limit n (1+b) (1/c) (by linarith) hn hnr hW
  have hAl : Tendsto (fun k => A 1 (W (r k)/rho^k)) atTop (𝓝 (A 1 ((1/c)*b^p))) :=
    A_continuous.continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds hrl)
  apply le_of_tendsto_of_tendsto hAl hnl
  filter_upwards [hr.eventually (eventually_ge_atTop 1)] with k hk
  change 1 ≤ r k at hk
  have hrho := rho_pos
  have hp : 1 ≤ (2:ℕ)^k := Nat.one_le_pow _ _ (by norm_num)
  have h := W_pivot_lower (n k) (2^k) hp (by dsimp only [n]; omega)
  have hs : n k-2^k=r k := by dsimp only [n]; omega
  have hU : U (2^k)=rho^k := by simpa using U_dyadic k 1
  rw [hs,hU] at h
  have ha := A_hom (show 0 ≤ rho^k by positivity) (show (0:ℝ) ≤ 1 by norm_num)
    (show 0 ≤ W (r k)/rho^k from div_nonneg (W_pos _ hk).le (by positivity))
  rw [mul_one,mul_div_cancel₀ _ (by positivity)] at ha
  apply (le_div_iff₀ (by positivity : (0:ℝ) < rho^k)).mpr
  nlinarith [ha]

/-- The exact contact test forces every constant asymptotic profile to the sharp
support value. No density or optimization statement is assumed. -/
theorem lemma_D_7 : Targets.lemma_D_7 := by
  intro c hc
  have hc0 : 0 < c := hc 0 ▸ Psi_pos 0
  let d := 1/c
  have hd : 0 < d := one_div_pos.mpr hc0
  have htau := tau_positive
  let b := (1/(d*tau))^q
  have hb : 0 < b := Real.rpow_pos_of_pos (by positivity) _
  have hbp : b^p=1/(d*tau) := by
    dsimp only [b]
    rw [← Real.rpow_mul (by positivity : 0 ≤ 1/(d*tau)),mul_comm q p,p_mul_q,Real.rpow_one]
  have hratio : 1/(d*b^p)=tau := by
    rw [hbp]
    field_simp [hd.ne',tau_positive.ne']
  have hcontact := (support_positive 1 (d*b^p) (by norm_num) (mul_pos hd (Real.rpow_pos_of_pos hb _))).2.mpr hratio
  have hineq := constant_Bellman c b hc hb
  change A 1 (d*b^p) ≤ d*(1+b)^p at hineq
  have hpow := Real.rpow_le_rpow (A_nonneg (by norm_num) (by positivity)) hineq q_pos.le
  rw [hcontact,Real.one_rpow,mul_one] at hpow
  simp only [Real.mul_rpow hd.le (Real.rpow_nonneg hb.le p),
    Real.mul_rpow hd.le (Real.rpow_nonneg (show 0 ≤ 1+b by linarith) p),
    ← Real.rpow_mul hb.le,← Real.rpow_mul (show 0 ≤ 1+b by linarith),p_mul_q,Real.rpow_one] at hpow
  have hsupport : Bsup ≤ d^q := by nlinarith
  have hdp := Real.rpow_le_rpow Bsup_pos.le hsupport p_pos.le
  rw [← Real.rpow_mul hd.le,mul_comm q p,p_mul_q,Real.rpow_one] at hdp
  have hc_le : c ≤ cstar := by
    rw [cstar,Real.rpow_neg Bsup_pos.le,← one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos Bsup_pos p)).mpr
    have hh := (le_div_iff₀ hc0).mp hdp
    simpa [mul_comm] using hh
  have hc_ge : cstar ≤ c := by
    rw [← hc 0,Psi_eq_mantissa]
    exact (obsMantissa_bounds _ (two_rpow_mem _ ⟨Int.fract_nonneg 0,(Int.fract_lt_one 0).le⟩)).1
  exact le_antisymm hc_le hc_ge

end
end GD
