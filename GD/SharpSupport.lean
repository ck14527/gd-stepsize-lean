import GD.SupportMaximum

namespace GD
noncomputable section
open Set

theorem support_parameter (t : ℝ) (ht : 0 < t) :
    ∃ x : ℝ, x ∈ Ioo (0:ℝ) 1 ∧ t=(1-x)/(2*x^2) ∧ A t 1=1/x^2 := by
  let d := Real.sqrt (1+8*t)
  let z := (1+d)/2
  have hd : d^2=1+8*t := Real.sq_sqrt (by linarith)
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hd1 : 1 < d := by nlinarith
  have hz1 : 1 < z := by dsimp [z]; linarith
  have hz0 : 0 < z := by linarith
  have hzq : z^2-z=2*t := by dsimp [z]; nlinarith
  have hA : A t 1=z^2 := by
    change (4*t+1+Real.sqrt (1^2+8*t*1))/2=z^2
    norm_num only [one_pow,mul_one]
    change (4*t+1+d)/2=z^2
    dsimp [z] at *
    nlinarith
  refine ⟨1/z,⟨by positivity,(div_lt_one hz0).mpr hz1⟩,?_,?_⟩
  · field_simp
    nlinarith [hzq]
  · rw [hA]
    field_simp

theorem support_ratio_identity (t x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1)
    (ht : t=(1-x)/(2*x^2)) (hA : A t 1=1/x^2) :
    ((A t 1)^q-1)/t^q=supportH x := by
  have hx0 := hx.1
  have hx1 : 0 < 1-x := sub_pos.mpr hx.2
  have hxp : 0 < x^(2*q) := Real.rpow_pos_of_pos hx0 _
  have hyp : 0 < (1-x)^q := Real.rpow_pos_of_pos hx1 _
  have h2p : 0 < (2:ℝ)^q := Real.rpow_pos_of_pos (by norm_num) _
  have he : (x^2)^q=x^(2*q) := by
    simpa only [Real.rpow_two] using (Real.rpow_mul hx0.le (2:ℝ) q).symm
  have htp : t^q=(1-x)^q/((2:ℝ)^q*x^(2*q)) := by
    rw [ht,Real.div_rpow hx1.le (by positivity),Real.mul_rpow (by norm_num) (sq_nonneg x),he]
  have hAp : (A t 1)^q=1/x^(2*q) := by
    rw [hA,Real.div_rpow (by norm_num) (sq_nonneg x),Real.one_rpow,he]
  rw [htp,hAp,supportH,Real.rpow_neg hx1.le]
  field_simp
  <;> ring

theorem support_parameter_injective (t x y : ℝ) (ht : 0 < t) (hx : 0 < x) (hy : 0 < y)
    (hxt : t=(1-x)/(2*x^2)) (hyt : t=(1-y)/(2*y^2)) : x=y := by
  have hqx : 2*t*x^2+x=1 := by
    have h := (eq_div_iff (show 2*x^2 ≠ 0 by positivity)).mp hxt
    nlinarith
  have hqy : 2*t*y^2+y=1 := by
    have h := (eq_div_iff (show 2*y^2 ≠ 0 by positivity)).mp hyt
    nlinarith
  rcases lt_trichotomy x y with h | h | h
  · have hs := (sq_lt_sq₀ hx.le hy.le).mpr h
    nlinarith [mul_lt_mul_of_pos_left hs ht]
  · exact h
  · have hs := (sq_lt_sq₀ hy.le hx.le).mpr h
    nlinarith [mul_lt_mul_of_pos_left hs ht]

theorem support_one (t : ℝ) (ht : 0 < t) :
    (A t 1)^q ≤ Bsup*t^q+1 ∧ ((A t 1)^q=Bsup*t^q+1 ↔ t=tau) := by
  obtain ⟨x,hx,hxt,hAx⟩ := support_parameter t ht
  have hp : 0 < t^q := Real.rpow_pos_of_pos ht _
  have hratio := support_ratio_identity t x hx hxt hAx
  have hmax := supportH_max x hx.1.le hx.2
  have hu : (A t 1)^q ≤ Bsup*t^q+1 := by
    have hh : ((A t 1)^q-1)/t^q ≤ Bsup := by rw [hratio]; exact hmax.1
    have hh' := (div_le_iff₀ hp).mp hh
    linarith
  have he : (A t 1)^q=Bsup*t^q+1 ↔ x=xi := by
    rw [← hmax.2,← hratio]
    constructor
    · intro h
      apply (div_eq_iff hp.ne').mpr
      linarith
    · intro h
      have hh := (div_eq_iff hp.ne').mp h
      linarith
  refine ⟨hu,he.trans ?_⟩
  constructor
  · intro h
    rw [h] at hxt
    exact hxt
  · intro htau
    apply support_parameter_injective t x xi ht hx.1 xi_root_and_signs.1.1 hxt
    exact htau

theorem A_zero_left (w : ℝ) (hw : 0 ≤ w) : A 0 w=w := by
  simp [A,Real.sqrt_sq hw]
  <;> ring

theorem A_zero_right (u : ℝ) : A u 0=2*u := by
  norm_num [A]
  <;> ring

theorem support_positive (u w : ℝ) (hu : 0 < u) (hw : 0 < w) :
    (A u w)^q ≤ Bsup*u^q+w^q ∧ ((A u w)^q=Bsup*u^q+w^q ↔ u/w=tau) := by
  have ht : 0 < u/w := div_pos hu hw
  have hwq : 0 < w^q := Real.rpow_pos_of_pos hw q
  have hA : A u w=w*A (u/w) 1 := by
    have h := A_hom hw.le ht.le (show (0:ℝ) ≤ 1 by norm_num)
    have hm : w*(u/w)=u := by field_simp
    simpa [hm] using h
  have hup : u^q=w^q*(u/w)^q := by
    rw [Real.div_rpow hu.le hw.le]
    field_simp
  have hAp : (A u w)^q=w^q*(A (u/w) 1)^q := by
    rw [hA,Real.mul_rpow hw.le (A_nonneg ht.le (by norm_num))]
  have h := support_one (u/w) ht
  have he : Bsup*(w^q*(u/w)^q)+w^q=w^q*(Bsup*(u/w)^q+1) := by ring
  rw [hAp,hup,he]
  constructor
  · exact mul_le_mul_of_nonneg_left h.1 hwq.le
  · exact (mul_right_inj' hwq.ne').trans h.2

/-- Lemma 6.4 with the actual infimum-defined root and every equality clause. -/
theorem lemma_6_4 : Targets.lemma_6_4 := by
  refine ⟨xi_root_and_signs.1,xi_root_and_signs.2.1,xi_root_and_signs.2.2.1,
    Bsup_gt_two_rpow,?_,?_,?_,?_⟩
  · intro u w hu hw
    rcases eq_or_lt_of_le hu with hu | hu
    · subst u
      rw [A_zero_left w hw,Real.zero_rpow q_pos.ne']
      simp
    rcases eq_or_lt_of_le hw with hw | hw
    · subst w
      rw [A_zero_right,Real.mul_rpow (by norm_num) hu.le,Real.zero_rpow q_pos.ne',add_zero]
      exact mul_le_mul_of_nonneg_right Bsup_gt_two_rpow.le (Real.rpow_pos_of_pos hu q).le
    · exact (support_positive u w hu hw).1
  · intro u w hu hw
    exact (support_positive u w hu hw).2
  · intro w hw
    rw [A_zero_left w hw]
  · intro u hu
    rw [A_zero_right,Real.mul_rpow (by norm_num) hu.le]
    exact mul_lt_mul_of_pos_right Bsup_gt_two_rpow (Real.rpow_pos_of_pos hu q)

end
end GD
