import GD.SupportRoot

namespace GD
noncomputable section
open Set

def supportH (x : ℝ) : ℝ := (2:ℝ)^q*(1-x^(2*q))*(1-x)^(-q)

theorem rpow_sub_one_mul (x a : ℝ) (hx : 0 < x) : x^a=x^(a-1)*x := by
  calc x^a=x^((a-1)+1) := by congr 1; ring
       _=x^(a-1)*x := by rw [Real.rpow_add hx,Real.rpow_one]

theorem supportH_derivative (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt supportH
      ((2:ℝ)^q*q*(1-x)^(-q-1)*(1-x^(2*q-1)*(2-x))) x := by
  have hd1 := (hasDerivAt_const x 1).sub
    (Real.hasDerivAt_rpow_const (p:=2*q) (Or.inl hx0.ne'))
  have hd2 := ((hasDerivAt_const x 1).sub (hasDerivAt_id x)).rpow_const
    (p:=-q) (Or.inl (sub_pos.mpr hx1).ne')
  have h := (hd1.mul hd2).const_mul ((2:ℝ)^q)
  simp only [id_eq] at h
  have he1 := rpow_sub_one_mul x (2*q) hx0
  have he2 := rpow_sub_one_mul (1-x) (-q) (sub_pos.mpr hx1)
  convert h using 1
  · funext y
    unfold supportH
    ring
  · rw [he1,he2]
    ring

theorem supportH_continuousOn {s : Set ℝ} (hs : ∀ x ∈ s, x < 1) :
    ContinuousOn supportH s := by
  have hq : 0 ≤ 2*q := by linarith [q_pos]
  have ha : ContinuousOn (fun x : ℝ => 1-x^(2*q)) s :=
    continuousOn_const.sub (Real.continuous_rpow_const hq).continuousOn
  have hb : ContinuousOn (fun x : ℝ => (1-x)^(-q)) s :=
    (continuousOn_const.sub continuousOn_id).rpow_const
      (fun x hx => Or.inl (sub_pos.mpr (hs x hx)).ne')
  exact (continuousOn_const.mul ha).mul hb

theorem supportH_inc : StrictMonoOn supportH (Icc 0 xi) := by
  have hx1 := xi_root_and_signs.1.2
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (supportH_continuousOn (fun x hx => hx.2.trans_lt hx1))
  intro x hx
  rw [interior_Icc] at hx
  have hxlt : x < 1 := hx.2.trans hx1
  rw [(supportH_derivative x hx.1 hxlt).deriv]
  have hg := xi_root_and_signs.2.2.2.1 x hx.1 hx.2
  exact mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) q) q_pos)
    (Real.rpow_pos_of_pos (sub_pos.mpr hxlt) _)) (sub_pos.mpr hg)

theorem supportH_dec : StrictAntiOn supportH (Ico xi 1) := by
  have hx0 := xi_root_and_signs.1.1
  apply strictAntiOn_of_deriv_neg (convex_Ico _ _) (supportH_continuousOn (fun x hx => hx.2))
  intro x hx
  rw [interior_Ico] at hx
  have hxpos := hx0.trans hx.1
  rw [(supportH_derivative x hxpos hx.2).deriv]
  have hg := xi_root_and_signs.2.2.2.2 x hx.1 hx.2
  exact mul_neg_of_pos_of_neg (mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) q) q_pos)
    (Real.rpow_pos_of_pos (sub_pos.mpr hx.2) _)) (by linarith)

theorem Bsup_eq_supportH : Bsup=supportH xi := by
  have hx : 0 < 1-xi := sub_pos.mpr xi_root_and_signs.1.2
  rw [Bsup,supportH,Real.rpow_neg hx.le,div_eq_mul_inv]

theorem supportH_max (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    supportH x ≤ Bsup ∧ (supportH x=Bsup ↔ x=xi) := by
  rw [Bsup_eq_supportH]
  have hz0 := xi_root_and_signs.1.1
  have hz1 := xi_root_and_signs.1.2
  rcases lt_trichotomy x xi with hx | hx | hx
  · have hs := supportH_inc ⟨hx0,hx.le⟩ ⟨hz0.le,le_rfl⟩ hx
    exact ⟨hs.le,⟨fun he => False.elim (hs.ne he),fun he => False.elim (hx.ne he)⟩⟩
  · subst x
    simp
  · have hs := supportH_dec ⟨le_rfl,hz1⟩ ⟨hx.le,hx1⟩ hx
    exact ⟨hs.le,⟨fun he => False.elim (hs.ne he),fun he => False.elim (hx.ne' he)⟩⟩

theorem Bsup_gt_two_rpow : (2:ℝ)^q < Bsup := by
  have hz := xi_root_and_signs.1
  have h := supportH_inc ⟨le_rfl,hz.1.le⟩ ⟨hz.1.le,le_rfl⟩ hz.1
  have hq : 2*q ≠ 0 := (show 0 < 2*q by linarith [q_pos]).ne'
  have h0 : supportH 0=(2:ℝ)^q := by simp [supportH,Real.zero_rpow hq]
  rw [Bsup_eq_supportH]
  simpa only [h0] using h

end
end GD
