import GD.ContactFraction

namespace GD
noncomputable section
open Set

def silverB : ℝ := 1/rho
def silverQ (x : ℝ) : ℝ := -(1-q)+2*q*x-(1+q)*x^2
def silverLog (x : ℝ) : ℝ := (1-q)*(Real.log (1-x)-Real.log x)+(1+q)*Real.log (1+x)

theorem silverB_bounds : (2/5:ℝ) < silverB ∧ silverB < 5/12 := by
  unfold silverB
  refine ⟨(lt_div_iff₀ rho_pos).mpr ?_,(div_lt_iff₀ rho_pos).mpr ?_⟩ <;>
    linarith [rho_rational_bounds.1,rho_rational_bounds.2]

theorem silverB_quad : silverB^2+2*silverB=1 := by
  have hrho := rho_pos
  unfold silverB
  field_simp
  nlinarith [rho_sq]

theorem silverQ_strictMonoOn : StrictMonoOn silverQ (Icc 0 silverB) := by
  have hq : (3/4:ℝ) < q := by linarith [q_rational_bounds.1]
  intro x hx y hy hxy
  have hs : x+y < 5/6 := by linarith [silverB_bounds.2,hx.2,hy.2]
  have hpos : 0 < 2*q-(1+q)*(x+y) := by
    have hmul := mul_pos (show 0 < 1+q by linarith) (sub_pos.mpr hs)
    nlinarith
  have hp := mul_pos (sub_pos.mpr hxy) hpos
  unfold silverQ
  nlinarith

theorem silverQ_endpoints : silverQ 0 < 0 ∧ 0 < silverQ silverB := by
  have hq : (3/4:ℝ) < q := by linarith [q_rational_bounds.1]
  constructor
  · unfold silverQ
    nlinarith [q_bounds.2]
  · have he : silverQ silverB=(2+4*q)*silverB-2 := by
      unfold silverQ
      linear_combination -(1+q)*silverB_quad
    have hprod := mul_pos (show 0 < 2+4*q by linarith) (sub_pos.mpr silverB_bounds.1)
    rw [he]
    nlinarith

theorem silverLog_continuousOn {s : Set ℝ} (hs : ∀ x ∈ s, x ∈ Ioo (0:ℝ) 1) :
    ContinuousOn silverLog s := by
  have h1 : ContinuousOn (fun x : ℝ => Real.log (1-x)) s :=
    (continuousOn_const.sub continuousOn_id).log (fun x hx => (sub_pos.mpr (hs x hx).2).ne')
  have h2 : ContinuousOn Real.log s := continuousOn_id.log (fun x hx => (hs x hx).1.ne')
  have h3 : ContinuousOn (fun x : ℝ => Real.log (1+x)) s :=
    (continuousOn_const.add continuousOn_id).log (fun x hx => (show 0 < 1+x by linarith [(hs x hx).1]).ne')
  exact (continuousOn_const.mul (h1.sub h2)).add (continuousOn_const.mul h3)

theorem silverLog_derivative (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) :
    HasDerivAt silverLog (silverQ x/(x*(1-x)*(1+x))) x := by
  have hx0 := hx.1
  have hx1 : 0 < 1-x := sub_pos.mpr hx.2
  have hxp : 0 < 1+x := by linarith
  have hd1 := ((hasDerivAt_const x 1).sub (hasDerivAt_id x)).log hx1.ne'
  have hd2 := Real.hasDerivAt_log hx0.ne'
  have hd3 := ((hasDerivAt_const x 1).add (hasDerivAt_id x)).log hxp.ne'
  have h := ((hd1.sub hd2).const_mul (1-q)).add (hd3.const_mul (1+q))
  simp only [id_eq] at h
  convert h using 1
  unfold silverQ
  field_simp
  <;> ring

theorem silverLog_at_B : silverLog silverB=Real.log 2 := by
  have hb0 : 0 < silverB := by linarith [silverB_bounds.1]
  have hbp : 0 < 1+silverB := by linarith
  have he : 1-silverB=silverB*(1+silverB) := by nlinarith [silverB_quad]
  have hs : (1+silverB)^2=2 := by nlinarith [silverB_quad]
  rw [silverLog,he,Real.log_mul hb0.ne' hbp.ne']
  calc (1-q)*(Real.log silverB+Real.log (1+silverB)-Real.log silverB)+(1+q)*Real.log (1+silverB)
      = 2*Real.log (1+silverB) := by ring
       _ = Real.log ((1+silverB)^2) := by rw [Real.log_pow]; norm_num
       _ = Real.log 2 := by rw [hs]

/-- The logarithmic derivative comparison has exactly one interior crossing
before the symmetric point. The proof uses only a quadratic turning point. -/
theorem silverLog_crossing : ∃ c : ℝ, 0 < c ∧ c < silverB ∧
    (∀ x : ℝ, 0 < x → x < c → Real.log 2 < silverLog x) ∧
    (∀ x : ℝ, c < x → x < silverB → silverLog x < Real.log 2) := by
  have hb0 : 0 < silverB := by linarith [silverB_bounds.1]
  have hb1 : silverB < 1 := by linarith [silverB_bounds.2]
  have hQcts : Continuous silverQ := by unfold silverQ; fun_prop
  obtain ⟨a,ha,hQa⟩ := intermediate_value_Icc hb0.le hQcts.continuousOn
    (show (0:ℝ) ∈ Icc (silverQ 0) (silverQ silverB) from ⟨silverQ_endpoints.1.le,silverQ_endpoints.2.le⟩)
  have ha0 : 0 < a := by
    rcases eq_or_lt_of_le ha.1 with h | h
    · subst a; linarith [silverQ_endpoints.1]
    · exact h
  have hab : a < silverB := by
    rcases eq_or_lt_of_le ha.2 with h | h
    · rw [h] at hQa; linarith [silverQ_endpoints.2]
    · exact h
  have hdec : StrictAntiOn silverLog (Ioc 0 a) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioc _ _)
      (silverLog_continuousOn (fun x hx => ⟨hx.1,hx.2.trans_lt (hab.trans hb1)⟩))
    intro x hx
    rw [interior_Ioc] at hx
    have hxb : x < silverB := hx.2.trans hab
    have hx0 := hx.1
    have hx1 : 0 < 1-x := by linarith
    rw [(silverLog_derivative x ⟨hx.1,hxb.trans hb1⟩).deriv]
    have hneg := silverQ_strictMonoOn ⟨hx.1.le,hxb.le⟩ ha hx.2
    rw [hQa] at hneg
    exact div_neg_of_neg_of_pos hneg (by positivity)
  have hinc : StrictMonoOn silverLog (Icc a silverB) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (silverLog_continuousOn (fun x hx => ⟨ha0.trans_le hx.1,hx.2.trans_lt hb1⟩))
    intro x hx
    rw [interior_Icc] at hx
    have hx0 := ha0.trans hx.1
    have hx1 : 0 < 1-x := by linarith [hx.2]
    rw [(silverLog_derivative x ⟨hx0,hx.2.trans hb1⟩).deriv]
    have hpos := silverQ_strictMonoOn ha ⟨hx0.le,hx.2.le⟩ hx.1
    rw [hQa] at hpos
    exact div_pos hpos (by positivity)
  have hLa : silverLog a < Real.log 2 := by
    have h := hinc ⟨le_rfl,hab.le⟩ ⟨hab.le,le_rfl⟩ hab
    rwa [silverLog_at_B] at h
  let C := Real.log 2/(1-q)+Real.log 2+1
  let u := min (a/2) (Real.exp (-C))
  have hu0 : 0 < u := lt_min (by positivity) (Real.exp_pos _)
  have hua : u < a := (min_le_left _ _).trans_lt (by linarith)
  have huH : u < 1/2 := by linarith [silverB_bounds.2]
  have hulexp : u ≤ Real.exp (-C) := min_le_right _ _
  have hlgu : Real.log u ≤ -C := by
    have h := Real.log_le_log hu0 hulexp
    simpa using h
  have hl1 : -Real.log 2 ≤ Real.log (1-u) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 1/2) (show (1/2:ℝ) ≤ 1-u by linarith)
    simpa [Real.log_div] using h
  have hlp : 0 ≤ Real.log (1+u) := Real.log_nonneg (by linarith)
  have hq1 : 0 < 1-q := sub_pos.mpr q_bounds.2
  have hLu : Real.log 2 < silverLog u := by
    have h1 := mul_le_mul_of_nonneg_left (show C-Real.log 2 ≤ Real.log (1-u)-Real.log u by linarith) hq1.le
    have h2 := mul_nonneg (show 0 ≤ 1+q by linarith [q_pos]) hlp
    have he : (1-q)*(C-Real.log 2)=Real.log 2+(1-q) := by
      dsimp [C]
      field_simp
      <;> ring
    rw [he] at h1
    unfold silverLog
    linarith
  have hLcts : ContinuousOn silverLog (Icc u a) :=
    silverLog_continuousOn (fun x hx => ⟨hu0.trans_le hx.1,hx.2.trans_lt (hab.trans hb1)⟩)
  obtain ⟨c,hc,hLc⟩ := intermediate_value_Icc' hua.le hLcts
    (show Real.log 2 ∈ Icc (silverLog a) (silverLog u) from ⟨hLa.le,hLu.le⟩)
  have huc : u < c := by
    rcases eq_or_lt_of_le hc.1 with h | h
    · rw [← h] at hLc; linarith
    · exact h
  have hca : c < a := by
    rcases eq_or_lt_of_le hc.2 with h | h
    · rw [h] at hLc; linarith
    · exact h
  have hc0 := hu0.trans huc
  refine ⟨c,hc0,hca.trans hab,?_,?_⟩
  · intro x hx0 hxc
    have h := hdec ⟨hx0,(hxc.trans hca).le⟩ ⟨hc0,hca.le⟩ hxc
    rwa [hLc] at h
  · intro x hcx hxb
    by_cases hxa : x ≤ a
    · have h := hdec ⟨hc0,hca.le⟩ ⟨hc0.trans hcx,hxa⟩ hcx
      rwa [hLc] at h
    · have hax : a ≤ x := le_of_not_ge hxa
      have h := hinc ⟨hax,hxb.le⟩ ⟨hab.le,le_rfl⟩ hxb
      rwa [silverLog_at_B] at h

end
end GD
