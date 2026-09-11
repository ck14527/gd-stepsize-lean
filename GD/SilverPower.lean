import GD.SilverBalance

namespace GD
noncomputable section
open Set

theorem silver_one (t : ℝ) (ht : 1 ≤ t) :
    (K t 1)^q ≤ t^q+1 ∧ ((K t 1)^q=t^q+1 ↔ t=1) := by
  have ht0 : 0 < t := by linarith
  let z := K t 1
  let x := 1/z
  have hzrho : rho ≤ z := by
    have h := K_mono (show (0:ℝ) ≤ 1 by norm_num) (show (0:ℝ) ≤ 1 by norm_num) ht le_rfl
    simpa [z,K_diag] using h
  have hz0 : 0 < z := rho_pos.trans_le hzrho
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hxb : x ≤ silverB := by
    exact one_div_le_one_div_of_le rho_pos hzrho
  have hx1 : x < 1 := by linarith [silverB_bounds.2]
  have hzq : z^2=(t+1)*z+t := by simpa [z] using K_quad ht0.le (show (0:ℝ) ≤ 1 by norm_num)
  have hY : silverY x=t*x := by
    have hz1 : 0 < 1+z := by linarith
    dsimp [silverY,x]
    field_simp
    nlinarith [hzq]
  have hzqp : 0 < z^q := Real.rpow_pos_of_pos hz0 _
  have hxq : x^q=1/z^q := by
    dsimp [x]
    rw [Real.div_rpow (by norm_num) hz0.le,Real.one_rpow]
  have hYq : (silverY x)^q=t^q*x^q := by rw [hY,Real.mul_rpow ht0.le hx0.le]
  have he : silverBalance x=(t^q+1)/z^q-1 := by rw [silverBalance,hYq,hxq]; ring
  have hb := silverBalance_nonneg x ⟨hx0.le,hxb⟩
  have hp : z^q ≤ t^q+1 := by
    have hr : 1 ≤ (t^q+1)/z^q := by rw [he] at hb; linarith [hb.1]
    have h := (le_div_iff₀ hzqp).mp hr
    simpa using h
  have heq : z^q=t^q+1 ↔ silverBalance x=0 := by
    rw [he,sub_eq_zero]
    constructor
    · intro h
      rw [← h,div_self hzqp.ne']
    · intro h
      have hh := (div_eq_iff hzqp.ne').mp h
      linarith
  refine ⟨hp,heq.trans ?_⟩
  rw [hb.2]
  constructor
  · rintro (h|h)
    · exact False.elim (hx0.ne' h)
    · have hez : z=rho := by
        change 1/z=1/rho at h
        simpa only [one_div,inv_inj] using h
      rw [hez] at hzq
      have hm : (t-1)*(rho+1)=0 := by nlinarith [rho_sq]
      have hr : rho+1 ≠ 0 := by linarith [rho_pos]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hr)
  · intro ht1
    right
    dsimp [x,z,silverB]
    rw [ht1,K_diag (show (0:ℝ) ≤ 1 by norm_num),mul_one]

theorem silver_power_ordered (u v : ℝ) (hv : 0 < v) (hvu : v ≤ u) :
    (K u v)^q ≤ u^q+v^q ∧ ((K u v)^q=u^q+v^q ↔ u=v) := by
  have hu := hv.trans_le hvu
  have ht0 : 0 < u/v := div_pos hu hv
  have ht : 1 ≤ u/v := (le_div_iff₀ hv).mpr (by simpa using hvu)
  have hvq : 0 < v^q := Real.rpow_pos_of_pos hv _
  have h := silver_one (u/v) ht
  have hK : K u v=v*K (u/v) 1 := by
    have hh := K_hom hv.le ht0.le (show (0:ℝ) ≤ 1 by norm_num)
    have hm : v*(u/v)=u := by field_simp
    simpa [hm] using hh
  have hKp : (K u v)^q=v^q*(K (u/v) 1)^q := by
    rw [hK,Real.mul_rpow hv.le (K_nonneg ht0.le (show (0:ℝ) ≤ 1 by norm_num))]
  have hup : u^q=v^q*(u/v)^q := by
    rw [Real.div_rpow hu.le hv.le]
    field_simp
  have he : v^q*(u/v)^q+v^q=v^q*((u/v)^q+1) := by ring
  rw [hKp,hup,he]
  constructor
  · exact mul_le_mul_of_nonneg_left h.1 hvq.le
  · rw [mul_right_inj' hvq.ne',h.2,div_eq_one_iff_eq hv.ne']

theorem silver_power_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (K u v)^q ≤ u^q+v^q ∧ ((K u v)^q=u^q+v^q ↔ u=v ∨ u*v=0) := by
  rcases eq_or_lt_of_le hu with hu | hu
  · subst u
    rw [K_zero_left hv,Real.zero_rpow q_pos.ne']
    simp
  rcases eq_or_lt_of_le hv with hv | hv
  · subst v
    rw [K_zero_right hu.le,Real.zero_rpow q_pos.ne']
    simp
  have hn : u*v ≠ 0 := (mul_pos hu hv).ne'
  simp only [hn,or_false]
  rcases le_total u v with huv | hvu
  · have h := silver_power_ordered v u hu huv
    simpa only [K_symm v u,add_comm (v^q),eq_comm (a:=v) (b:=u)] using h
  · exact silver_power_ordered u v hv hvu

/-- Lemma 5.1, including all boundary and equality cases.
The compact-interval calculus proof is equivalent to the hyperbolic proof. -/
theorem lemma_5_1 : Targets.lemma_5_1 := by
  intro x y hx hy
  have hk0 := K_nonneg hx hy
  have hs0 : 0 ≤ x^q+y^q := add_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _)
  have h := silver_power_nonnegative x y hx hy
  have hq : q ≠ 0 := q_pos.ne'
  have hinv : 0 ≤ (1/q:ℝ) := (one_div_pos.mpr q_pos).le
  have hleft : ((K x y)^q)^(1/q)=K x y := by
    simpa only [one_div] using Real.rpow_rpow_inv hk0 hq
  have hright : ((x^q+y^q)^(1/q))^q=x^q+y^q := by
    simpa only [one_div] using Real.rpow_inv_rpow hs0 hq
  constructor
  · have hb := Real.rpow_le_rpow (Real.rpow_nonneg hk0 _) h.1 hinv
    rwa [hleft] at hb
  · constructor
    · intro he
      apply h.2.mp
      rw [he,hright]
    · intro he
      have hb := congrArg (fun z : ℝ => z^(1/q)) (h.2.mpr he)
      dsimp only at hb
      rwa [hleft] at hb

end
end GD
