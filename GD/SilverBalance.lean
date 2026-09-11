import GD.SilverCalculus

namespace GD
noncomputable section
open Set

def silverY (x : ℝ) : ℝ := (1-x)/(1+x)
def silverBalance (x : ℝ) : ℝ := x^q+(silverY x)^q-1
def silverRight (x : ℝ) : ℝ := 2*(silverY x)^(q-1)/(1+x)^2

theorem silverY_pos (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) : 0 < silverY x :=
  div_pos (sub_pos.mpr hx.2) (by linarith [hx.1])

theorem silverBalance_derivative (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) :
    HasDerivAt silverBalance (q*(x^(q-1)-silverRight x)) x := by
  have hx0 := hx.1
  have hy0 := silverY_pos x hx
  have hp : 0 < 1+x := by linarith
  have hy := ((hasDerivAt_const x 1).sub (hasDerivAt_id x)).div
    ((hasDerivAt_const x 1).add (hasDerivAt_id x)) hp.ne'
  have h := ((Real.hasDerivAt_rpow_const (p:=q) (Or.inl hx0.ne')).add
    (hy.rpow_const (p:=q) (Or.inl hy0.ne'))).sub_const 1
  simp only [id_eq] at h
  convert h using 1
  unfold silverRight silverY
  field_simp
  <;> ring

theorem silverBalance_derivative_signs (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) :
    (0 < deriv silverBalance x ↔ Real.log 2 < silverLog x) ∧
    (deriv silverBalance x < 0 ↔ silverLog x < Real.log 2) := by
  have hx0 := hx.1
  have hy0 := silverY_pos x hx
  have hp : 0 < 1+x := by linarith
  have hm : 0 < 1-x := sub_pos.mpr hx.2
  have hxp : 0 < x^(q-1) := Real.rpow_pos_of_pos hx0 _
  have hyp : 0 < (silverY x)^(q-1) := Real.rpow_pos_of_pos hy0 _
  have hR : 0 < silverRight x := by unfold silverRight; positivity
  have hlogR : Real.log (silverRight x)=Real.log 2+(q-1)*(Real.log (1-x)-Real.log (1+x))-2*Real.log (1+x) := by
    rw [silverRight,Real.log_div (by positivity) (by positivity),Real.log_mul (by norm_num) hyp.ne',
      Real.log_rpow hy0,Real.log_pow,silverY,Real.log_div hm.ne' hp.ne']
    norm_num
  have hlogx : Real.log (x^(q-1))=(q-1)*Real.log x := Real.log_rpow hx0 _
  have he : Real.log (x^(q-1))-Real.log (silverRight x)=silverLog x-Real.log 2 := by
    rw [hlogR,hlogx,silverLog]
    ring
  rw [(silverBalance_derivative x hx).deriv]
  constructor
  · rw [mul_pos_iff_of_pos_left q_pos,sub_pos,← Real.log_lt_log_iff hR hxp]
    constructor <;> intro h <;> linarith
  · rw [mul_neg_iff]
    simp only [not_lt.mpr q_pos.le,false_and,q_pos,true_and,false_or,or_false]
    rw [sub_neg,← Real.log_lt_log_iff hxp hR]
    constructor <;> intro h <;> linarith

theorem rho_rpow_q : rho^q=2 := by
  rw [← two_rpow_p,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),p_mul_q,Real.rpow_one]

theorem silverBalance_endpoints : silverBalance 0=0 ∧ silverBalance silverB=0 := by
  have hb0 : 0 < silverB := by linarith [silverB_bounds.1]
  have hbp : 0 < 1+silverB := by linarith
  have hy : silverY silverB=silverB := by
    unfold silverY
    apply (div_eq_iff hbp.ne').mpr
    nlinarith [silverB_quad]
  have hbq : silverB^q=(1/2:ℝ) := by
    rw [silverB,Real.div_rpow (by norm_num) rho_pos.le,Real.one_rpow,rho_rpow_q]
  constructor
  · simp [silverBalance,silverY,Real.zero_rpow q_pos.ne']
  · rw [silverBalance,hy,hbq]
    norm_num

theorem silverBalance_continuousOn : ContinuousOn silverBalance (Icc 0 silverB) := by
  have hb1 : silverB < 1 := by linarith [silverB_bounds.2]
  have hy : ContinuousOn silverY (Icc 0 silverB) :=
    (continuousOn_const.sub continuousOn_id).div (continuousOn_const.add continuousOn_id)
      (fun x hx => (show 0 < 1+x by linarith [hx.1]).ne')
  exact ((Real.continuous_rpow_const q_pos.le).continuousOn.add
    (hy.rpow_const (fun _ _ => Or.inr q_pos.le))).sub continuousOn_const

/-- Exact nonnegativity on the half interval; equality at its two endpoints. -/
theorem silverBalance_nonneg (x : ℝ) (hx : x ∈ Icc 0 silverB) :
    0 ≤ silverBalance x ∧ (silverBalance x=0 ↔ x=0 ∨ x=silverB) := by
  obtain ⟨c,hc0,hcb,hleft,hright⟩ := silverLog_crossing
  have hb1 : silverB < 1 := by linarith [silverB_bounds.2]
  have hinc : StrictMonoOn silverBalance (Icc 0 c) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (silverBalance_continuousOn.mono (Icc_subset_Icc le_rfl hcb.le))
    intro y hy
    rw [interior_Icc] at hy
    exact (silverBalance_derivative_signs y ⟨hy.1,(hy.2.trans hcb).trans hb1⟩).1.mpr
      (hleft y hy.1 hy.2)
  have hdec : StrictAntiOn silverBalance (Icc c silverB) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (silverBalance_continuousOn.mono (Icc_subset_Icc hc0.le le_rfl))
    intro y hy
    rw [interior_Icc] at hy
    exact (silverBalance_derivative_signs y ⟨hc0.trans hy.1,hy.2.trans hb1⟩).2.mpr
      (hright y hy.1 hy.2)
  by_cases hx0 : x=0
  · subst x
    simp [silverBalance_endpoints.1]
  by_cases hxb : x=silverB
  · subst x
    simp [silverBalance_endpoints.2]
  have hxt : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hxb' : x < silverB := lt_of_le_of_ne hx.2 hxb
  have hpos : 0 < silverBalance x := by
    by_cases hxc : x ≤ c
    · have h := hinc ⟨le_rfl,hc0.le⟩ ⟨hx.1,hxc⟩ hxt
      rwa [silverBalance_endpoints.1] at h
    · have h := hdec ⟨le_of_not_ge hxc,hx.2⟩ ⟨hcb.le,le_rfl⟩ hxb'
      rwa [silverBalance_endpoints.2] at h
  exact ⟨hpos.le,⟨fun he => False.elim (hpos.ne' he),by rintro (h|h) <;> contradiction⟩⟩

end
end GD
