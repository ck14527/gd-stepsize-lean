import GD.OBSUpperBarrier

namespace GD
noncomputable section
open Set Filter
open scoped Topology

theorem sigma_hom (s u w : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) (hw : 0 ≤ w) :
    sigma (s*u) (s*w)=s^q*sigma u w := by
  rw [sigma,A_hom hs hu hw,Real.mul_rpow hs hu,Real.mul_rpow hs hw,
    Real.mul_rpow hs (A_nonneg hu hw),sigma]
  ring

theorem A_linear_upper (u w : ℝ) (hu : 0 ≤ u) (hw : 0 ≤ w) : A u w ≤ w+4*u := by
  have h := A_left_increment 0 u w (by norm_num) hu hw
  rw [A_zero_left w hw] at h
  linarith

theorem small_support_exists : ∃ δ : ℝ, 0 < δ ∧ ∀ u w : ℝ,
    0 < u → 0 < w → u/w ≤ δ → (Bsup/2)*u^q ≤ sigma u w := by
  have hq1 : 0 < 1-q := by linarith [q_rational_bounds.2.2]
  have hq := q_pos
  have hb := Bsup_pos
  let δ := (Bsup/(8*q))^(1/(1-q))
  have hδ : 0 < δ := Real.rpow_pos_of_pos (by positivity) _
  have hδpow : δ^(1-q)=Bsup/(8*q) := by
    dsimp only [δ]
    rw [← Real.rpow_mul (by positivity : 0 ≤ Bsup/(8*q)),one_div_mul_cancel hq1.ne',Real.rpow_one]
  have hbase : ∀ t : ℝ, 0 < t → t ≤ δ → (Bsup/2)*t^q ≤ sigma t 1 := by
    intro t ht htδ
    have ha := A_linear_upper t 1 ht.le (by norm_num)
    have hap := Real.rpow_le_rpow (A_nonneg ht.le (by norm_num)) ha hq.le
    have hbern := rpow_one_add_le_one_add_mul_self (show -1 ≤ 4*t by linarith) hq.le (by linarith [q_rational_bounds.2.2] : q ≤ 1)
    have hpow := Real.rpow_le_rpow ht.le htδ hq1.le
    rw [hδpow] at hpow
    have he : t^q*t^(1-q)=t := by rw [← Real.rpow_add ht]; ring_nf; rw [Real.rpow_one]
    have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4*q*t^q by positivity)
    have hh' : 4*q*t^q*(Bsup/(8*q))=(Bsup/2)*t^q := by field_simp; ring
    rw [hh'] at hh
    have hh'' : 4*q*t^q*t^(1-q)=4*q*t := by rw [mul_assoc (4*q),he]
    rw [hh''] at hh
    unfold sigma
    rw [Real.one_rpow]
    nlinarith
  refine ⟨δ,hδ,?_⟩
  intro u w hu hw hratio
  have ht := div_pos hu hw
  have hh := hbase (u/w) ht hratio
  have he := sigma_hom w (u/w) 1 hw.le ht.le (by norm_num)
  rw [mul_div_cancel₀ _ hw.ne',mul_one] at he
  rw [he]
  have huq : u^q=w^q*(u/w)^q := by rw [Real.div_rpow hu.le hw.le]; field_simp
  rw [huq]
  nlinarith [mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hw.le q)]

theorem U_q_lower (m : ℕ) (hm : 1 ≤ m) : phiMin^q*(m:ℝ) ≤ (U m)^q := by
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hu := (normalized_U_bounds m hm).1
  have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hm0 p)).mp hu
  have h := Real.rpow_le_rpow (mul_nonneg phiMin_bounds.1.le (Real.rpow_nonneg hm0.le p)) hh q_pos.le
  rwa [Real.mul_rpow phiMin_bounds.1.le (Real.rpow_nonneg hm0.le p),← Real.rpow_mul hm0.le,p_mul_q,Real.rpow_one] at h

/-- The paper's small-pivot estimate (75), proved for the actual sequences. -/
theorem small_pivot_constants : ∃ ε c0 : ℝ, ε ∈ Ioo (0:ℝ) 1 ∧ 0 < c0 ∧
    ∀ N m : ℕ, 1 ≤ m → m < N → (m:ℝ)/(N:ℝ) ≤ ε →
      c0*(m:ℝ) ≤ sigma (U m) (W (N-m)) := by
  obtain ⟨δ,hδ,hs⟩ := small_support_exists
  have hphi := phiMin_bounds.1
  have hb := Bsup_pos
  let γ := (δ*phiMin)^q
  have hγ : 0 < γ := Real.rpow_pos_of_pos (mul_pos hδ hphi) _
  let ε := γ/(1+γ)
  let c0 := (Bsup/2)*phiMin^q
  have hε : ε ∈ Ioo (0:ℝ) 1 := ⟨div_pos hγ (by linarith),(div_lt_one (by linarith)).mpr (by linarith)⟩
  have hc : 0 < c0 := mul_pos (by positivity) (Real.rpow_pos_of_pos hphi _)
  refine ⟨ε,c0,hε,hc,?_⟩
  intro N m hm hmN hsmall
  let r := N-m
  have hr : 1 ≤ r := by dsimp only [r]; omega
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hr0 : 0 < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hn0 : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hsum : (N:ℝ)=(m:ℝ)+(r:ℝ) := by dsimp only [r]; rw [Nat.cast_sub hmN.le]; ring
  have hratio : (m:ℝ)/(r:ℝ) ≤ γ := by
    have hh := (div_le_div_iff₀ hn0 (show 0 < 1+γ by linarith)).mp hsmall
    apply (div_le_iff₀ hr0).mpr
    rw [hsum] at hh
    nlinarith
  have hγp : γ^p=δ*phiMin := by
    dsimp only [γ]
    rw [← Real.rpow_mul (mul_pos hδ hphi).le,mul_comm q p,p_mul_q,Real.rpow_one]
  have hrpow := Real.rpow_le_rpow (div_pos hm0 hr0).le hratio p_pos.le
  rw [hγp,Real.div_rpow hm0.le hr0.le] at hrpow
  have hum := (proposition_5_2 m hm).1
  have hwr := (normalizedW_bounds r hr).1
  have hwr' : phiMin*(r:ℝ)^p ≤ W r := (le_div_iff₀ (Real.rpow_pos_of_pos hr0 p)).mp hwr
  have huratio : U m/W r ≤ δ := by
    apply (div_le_iff₀ (W_pos r hr)).mpr
    have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hr0 p)).mp hrpow
    nlinarith [mul_le_mul_of_nonneg_left hwr' hδ.le]
  have h := hs (U m) (W r) (U_pos (by omega : 0 < m)) (W_pos r hr) huratio
  have hu := mul_le_mul_of_nonneg_left (U_q_lower m hm) (show 0 ≤ Bsup/2 by positivity)
  change ((Bsup/2)*phiMin^q)*(m:ℝ) ≤ sigma (U m) (W r)
  have hh : ((Bsup/2)*phiMin^q)*(m:ℝ) ≤ (Bsup/2)*(U m)^q := by
    simpa only [mul_assoc] using hu
  exact hh.trans h

end
end GD
