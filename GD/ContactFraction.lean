import GD.SharpSupport

namespace GD
noncomputable section

theorem rho_rational_bounds : (241/100:ℝ) < rho ∧ rho < 483/200 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg 2
  unfold rho
  constructor <;> nlinarith

theorem q_log_ratio : q=Real.log 2/Real.log rho := by
  unfold q p
  simp only [one_div,inv_div]

/-- Exact rational bounds; only integer/rational arithmetic and log monotonicity. -/
theorem q_rational_bounds : (11/14:ℝ) < q ∧ q < 15/19 ∧ q < 4/5 := by
  have hl : 0 < Real.log rho := Real.log_pos (by linarith [rho_gt_two])
  have hr0 := rho_pos
  have h15 : (2:ℝ)^19 < rho^15 := by
    have h := pow_lt_pow_left₀ rho_rational_bounds.1 (by norm_num : (0:ℝ) ≤ 241/100) (by omega : 15 ≠ 0)
    have hc : (2:ℝ)^19 < (241/100:ℝ)^15 := by norm_num
    exact hc.trans h
  have h11 : rho^11 < (2:ℝ)^14 := by
    have h := pow_lt_pow_left₀ rho_rational_bounds.2 rho_pos.le (by omega : 11 ≠ 0)
    have hc : (483/200:ℝ)^11 < (2:ℝ)^14 := by norm_num
    exact h.trans hc
  have h4 : (2:ℝ)^5 < rho^4 := by
    have h := pow_lt_pow_left₀ (show (12/5:ℝ) < rho by linarith [rho_rational_bounds.1])
      (by norm_num : (0:ℝ) ≤ 12/5) (by omega : 4 ≠ 0)
    have hc : (2:ℝ)^5 < (12/5:ℝ)^4 := by norm_num
    exact hc.trans h
  have l15 := Real.log_lt_log (by positivity : (0:ℝ) < 2^19) h15
  have l11 := Real.log_lt_log (by positivity : (0:ℝ) < rho^11) h11
  have l4 := Real.log_lt_log (by positivity : (0:ℝ) < 2^5) h4
  simp only [Real.log_pow,Nat.cast_ofNat] at l15 l11 l4
  rw [q_log_ratio]
  refine ⟨(lt_div_iff₀ hl).mpr ?_,(div_lt_iff₀ hl).mpr ?_,(div_lt_iff₀ hl).mpr ?_⟩ <;> linarith

theorem rational_rpow_lt (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (a b : ℕ) (hb : b ≠ 0) (h : x^a < y^b) : x^((a:ℝ)/(b:ℝ)) < y := by
  have hb0 : (0:ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
  have hh := Real.rpow_lt_rpow (pow_nonneg hx.le a) h (show (0:ℝ) < 1/(b:ℝ) by positivity)
  have he1 : (x^a)^(1/(b:ℝ))=x^((a:ℝ)/(b:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
    congr 1
    ring
  have he2 : (y^b)^(1/(b:ℝ))=y := by
    simpa only [one_div] using Real.pow_rpow_inv_natCast hy.le hb
  rwa [he1,he2] at hh

theorem two_rpow_two_q_lt_three : (2:ℝ)^(2*q) < 3 := by
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2)
    (show 2*q < 30/19 by linarith [q_rational_bounds.2.1])
  have hh : (2:ℝ)^(30/19:ℝ) < 3 := rational_rpow_lt 2 3 (by norm_num) (by norm_num)
    30 19 (by omega) (by norm_num)
  exact h.trans hh

theorem xi_rational_bounds : (12/25:ℝ) < xi ∧ xi < 1/2 := by
  have hhalf : 1 < (1/2:ℝ)^(2*q-1)*(2-(1/2:ℝ)) := by
    have hpow : 0 < (2:ℝ)^(2*q) := Real.rpow_pos_of_pos (by norm_num) _
    have he : (1/2:ℝ)^(2*q-1)*(2-(1/2:ℝ))=3/(2:ℝ)^(2*q) := by
      rw [Real.rpow_sub (by norm_num),Real.rpow_one,Real.div_rpow (by norm_num) (by norm_num),Real.one_rpow]
      field_simp
      <;> ring
    rw [he]
    exact (lt_div_iff₀ hpow).mpr (by simpa using two_rpow_two_q_lt_three)
  have hsmall : (12/25:ℝ)^(2*q-1)*(2-(12/25:ℝ)) < 1 := by
    have hpow := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0:ℝ) < 12/25)
      (by norm_num : (12/25:ℝ) < 1) (show (4/7:ℝ) < 2*q-1 by linarith [q_rational_bounds.1])
    have hrat : (12/25:ℝ)^(4/7:ℝ) < 25/38 := rational_rpow_lt (12/25) (25/38)
      (by norm_num) (by norm_num) 4 7 (by omega) (by norm_num)
    have hm := mul_lt_mul_of_pos_right (hpow.trans hrat) (by norm_num : (0:ℝ) < 2-12/25)
    norm_num at hm
    norm_num
    exact hm
  have hs := xi_root_and_signs
  constructor
  · rcases lt_trichotomy (12/25:ℝ) xi with h | h | h
    · exact h
    · rw [h,hs.2.1] at hsmall
      linarith
    · have hh := hs.2.2.2.2 (12/25) h (by norm_num)
      linarith
  · rcases lt_trichotomy xi (1/2:ℝ) with h | h | h
    · exact h
    · rw [← h,hs.2.1] at hhalf
      linarith
    · have hh := hs.2.2.2.1 (1/2) (by norm_num) h
      linarith

theorem alpha_identity : alpha=1-xi^(2*q) ∧ 1-alpha=xi^(2*q) := by
  have hx := xi_root_and_signs.1
  have hx0 := hx.1
  have hx1 : 0 < 1-xi := sub_pos.mpr hx.2
  have hxp : 0 < xi^(2*q) := Real.rpow_pos_of_pos hx0 _
  have hyp : 0 < (1-xi)^q := Real.rpow_pos_of_pos hx1 _
  have h2p : 0 < (2:ℝ)^q := Real.rpow_pos_of_pos (by norm_num) _
  have he : (xi^2)^q=xi^(2*q) := by
    simpa only [Real.rpow_two] using (Real.rpow_mul hx0.le (2:ℝ) q).symm
  have ht : tau^q=(1-xi)^q/((2:ℝ)^q*xi^(2*q)) := by
    rw [tau,Real.div_rpow hx1.le (by positivity),Real.mul_rpow (by norm_num) (sq_nonneg xi),he]
  have hb : Bsup*tau^q=(1-xi^(2*q))/xi^(2*q) := by
    rw [Bsup,ht]
    field_simp
    <;> ring
  have ha : alpha=1-xi^(2*q) := by
    rw [alpha,hb]
    field_simp
  exact ⟨ha,by linarith⟩

theorem contact_fraction_bounds : (1/4:ℝ) < 1-alpha ∧ 1-alpha < 1/2 := by
  rw [alpha_identity.2]
  have hx := xi_root_and_signs.1
  constructor
  · have he := Real.rpow_lt_rpow_of_exponent_gt hx.1 hx.2
      (show 2*q < 8/5 by linarith [q_rational_bounds.2.2])
    have hbase := Real.rpow_lt_rpow (by norm_num : (0:ℝ) ≤ 12/25) xi_rational_bounds.1
      (by norm_num : (0:ℝ) < 8/5)
    have hrat : (1/4:ℝ) < (12/25:ℝ)^(8/5:ℝ) := by
      have hh := Real.rpow_lt_rpow (by norm_num : (0:ℝ) ≤ (1/4:ℝ)^5)
        (by norm_num : (1/4:ℝ)^5 < (12/25:ℝ)^8) (by norm_num : (0:ℝ) < 1/5)
      have hleft : ((1/4:ℝ)^5)^(1/5:ℝ)=(1/4:ℝ) := by
        simpa only [one_div] using Real.pow_rpow_inv_natCast (by norm_num : (0:ℝ) ≤ 1/4) (by omega : (5:ℕ) ≠ 0)
      have hright : ((12/25:ℝ)^8)^(1/5:ℝ)=(12/25:ℝ)^(8/5:ℝ) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 12/25)]
        norm_num
      rwa [hleft,hright] at hh
    exact hrat.trans (hbase.trans he)
  · have h := Real.rpow_lt_rpow_of_exponent_gt hx.1 hx.2 (show (1:ℝ) < 2*q by linarith [q_bounds.1])
    rw [Real.rpow_one] at h
    exact h.trans xi_rational_bounds.2

theorem lemma_D_5 : Targets.lemma_D_5 := by
  refine ⟨alpha_identity.1,alpha_identity.2,contact_fraction_bounds.1,contact_fraction_bounds.2,?_,?_⟩
  · linarith [contact_fraction_bounds.2]
  · linarith [contact_fraction_bounds.1]

end
end GD
