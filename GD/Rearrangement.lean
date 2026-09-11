import GD.Algebra
namespace GD
noncomputable section

theorem weighted_K {a c d : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a*K c d = K (a*c) (a*d) := (K_hom ha hc hd).symm

theorem first_form_nonpos {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a*b*(K c d)^2+c*d*(K a b)^2-(a*d+b*c)*K a b*K c d ≤ 0 ∧
    (a*b*(K c d)^2+c*d*(K a b)^2-(a*d+b*c)*K a b*K c d = 0 ↔ a*d=b*c) := by
  rw [factor_first]
  have h1 : a*K c d = K (a*c) (a*d) := weighted_K ha hc hd
  have h2 : c*K a b = K (a*c) (b*c) := by
    rw [weighted_K hc ha hb]; congr 1 <;> ring
  have h3 : b*K c d = K (b*c) (b*d) := weighted_K hb hc hd
  have h4 : d*K a b = K (a*d) (b*d) := by
    rw [weighted_K hd ha hb]; congr 1 <;> ring
  rw [h1,h2,h3,h4]
  rcases lt_trichotomy (a*d) (b*c) with h | h | h
  · have hleft := K_strict_right (mul_nonneg ha hc) (mul_nonneg ha hd) h
    have hright := K_strict_left (mul_nonneg ha hd) (mul_nonneg hb hd) h
    have hp := mul_neg_of_neg_of_pos (sub_neg.mpr hleft) (sub_pos.mpr hright)
    exact ⟨hp.le, iff_of_false hp.ne (ne_of_lt h)⟩
  · rw [h]; simp
  · have hleft := K_strict_right (mul_nonneg ha hc) (mul_nonneg hb hc) h
    have hright := K_strict_left (mul_nonneg hb hc) (mul_nonneg hb hd) h
    have hp := mul_neg_of_pos_of_neg (sub_pos.mpr hleft) (sub_neg.mpr hright)
    exact ⟨hp.le, iff_of_false hp.ne (ne_of_gt h)⟩

/-- First half of Theorem 3.1, including its exact equality condition. -/
theorem rearrangement_first {a b c d : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    K (K a b) (K c d) ≤ K (K a c) (K b d) ∧
    (K (K a b) (K c d) = K (K a c) (K b d) ↔ b=c ∨ a*d=b*c) := by
  classical
  have hb := ha.trans hab
  have hc := hb.trans hbc
  have hd := hc.trans hcd
  by_cases hb0 : b=0
  · have ha0 : a=0 := by linarith
    subst b; subst a
    simp [K_zero_left hc, K_zero_left hd, K_zero_left (K_nonneg hc hd), K_zero_left (show (0:ℝ) ≤ 0 by norm_num)]
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hu : 0 < K a b := K_pos ha hb (by linarith)
  have hv : 0 < K c d := K_pos hc hd (by linarith)
  let z := K (K a b) (K c d)
  have hz0 : 0 < z := K_pos hu.le hv.le (by linarith)
  have hzv : K c d < z := by have := K_gt_sum hu hv; dsimp [z]; linarith
  have hmax : max (K a c) (K b d) < z := by
    apply max_lt
    · exact lt_of_le_of_lt (K_mono ha hc (hab.trans hbc) hcd) hzv
    · exact lt_of_le_of_lt (K_mono hb hd hbc le_rfl) hzv
  have hsign := lemma_3_2 ha hc hb hd hmax
  have hf := first_form_nonpos ha hb hc hd
  have hweight : 0 < (K a b*K c d+K a b*z+K c d*z)/(K a b*K c d) := by positivity
  have hquart : quartic a b c d (a*d+b*c) z =
      2*(a*b*(K c d)^2+c*d*(K a b)^2-(a*d+b*c)*K a b*K c d)*
      ((K a b*K c d+K a b*z+K c d*z)/(K a b*K c d)) := by
    rw [lemma_3_4 ha hb hc hd hu hv]; ring
  have hqle : quartic a b c d (a*d+b*c) z ≤ 0 := by
    rw [hquart]; exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hf.1) hweight.le
  have hdiff := lemma_3_3_first ha hb hc hd z
  have hroot : pairedPoly a b c d z=0 := pairedPoly_root ha hb hc hd
  have hmnonneg : 0 ≤ 2*z^2*(d-a)*(c-b) := by
    have hda : 0 ≤ d-a := by linarith
    have hcb : 0 ≤ c-b := by linarith
    positivity
  have hpnonpos : pairedPoly a c b d z ≤ 0 := by
    have hm := mul_nonpos_of_nonneg_of_nonpos hmnonneg hqle
    linarith
  have hle : z ≤ K (K a c) (K b d) := by
    by_contra h; have hp := hsign.2.2.mpr (lt_of_not_ge h); linarith
  refine ⟨hle, ?_⟩
  constructor
  · intro heq
    by_contra h
    have hbcne : b ≠ c := fun e => h (Or.inl e)
    have hprodne : a*d ≠ b*c := fun e => h (Or.inr e)
    have hfn : a*b*(K c d)^2+c*d*(K a b)^2-(a*d+b*c)*K a b*K c d < 0 :=
      lt_of_le_of_ne hf.1 (fun e => hprodne (hf.2.mp e))
    have hqn : quartic a b c d (a*d+b*c) z < 0 := by
      rw [hquart]; exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hfn) hweight
    have hmpos : 0 < 2*z^2*(d-a)*(c-b) := by
      have hcb : 0 < c-b := sub_pos.mpr (lt_of_le_of_ne hbc hbcne)
      have hda : 0 < d-a := by linarith
      positivity
    have hpn : pairedPoly a c b d z < 0 := by
      have := mul_neg_of_pos_of_neg hmpos hqn; linarith
    have hzlt := hsign.1.mp hpn
    exact (ne_of_lt hzlt) heq
  · intro h
    rcases h with h | h
    · subst c; rfl
    · have hqzero : quartic a b c d (a*d+b*c) z=0 := by
        rw [hquart, hf.2.mpr h]; ring
      apply hsign.2.1.mp
      rw [hqzero] at hdiff; linarith

/-- Second half of Theorem 3.1, including its exact equality condition. -/
theorem rearrangement_second {a b c d : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    K (K a c) (K b d) ≤ K (K a d) (K b c) ∧
    (K (K a c) (K b d) = K (K a d) (K b c) ↔ a=b ∨ c=d) := by
  classical
  have hb := ha.trans hab
  have hc := hb.trans hbc
  have hd := hc.trans hcd
  by_cases hab0 : a=b
  · subst b
    rw [K_symm (K a c) (K a d)]
    simp
  by_cases hcd0 : c=d
  · subst d; simp
  have habs : a < b := lt_of_le_of_ne hab hab0
  have hcds : c < d := lt_of_le_of_ne hcd hcd0
  have hbpos : 0 < b := by linarith
  have hcpos : 0 < c := by linarith
  have hdpos : 0 < d := by linarith
  have hu : 0 < K a c := K_pos ha hc (by linarith)
  have hv : 0 < K b d := K_pos hb hd (by linarith)
  let z := K (K a c) (K b d)
  have hz0 : 0 < z := K_pos hu.le hv.le (by linarith)
  have hzv : K b d < z := by have := K_gt_sum hu hv; dsimp [z]; linarith
  have hmax : max (K a d) (K b c) < z := by
    apply max_lt
    · exact lt_of_le_of_lt (K_mono ha hd hab le_rfl) hzv
    · exact lt_of_le_of_lt (K_mono hb hc le_rfl hcd) hzv
  have hsign := lemma_3_2 ha hd hb hc hmax
  have hleft : b*K a c < c*K b d := by
    rw [weighted_K hb ha hc, weighted_K hc hb hd]
    have h1 : b*a ≤ c*b := by nlinarith
    have h2 : b*c < c*d := by nlinarith
    have h3 := K_mono (mul_nonneg hb ha) (mul_nonneg hb hc) h1 (le_refl (b*c))
    have h4 := K_strict_right (mul_nonneg hc hb) (mul_nonneg hb hc) h2
    linarith
  have hright : a*K b d < d*K a c := by
    rw [weighted_K ha hb hd, weighted_K hd ha hc]
    have h1 : a*b ≤ d*a := by nlinarith
    have h2 : a*d < d*c := by nlinarith
    exact lt_of_le_of_lt (K_mono (mul_nonneg ha hb) (mul_nonneg ha hd) h1 le_rfl)
      (K_strict_right (mul_nonneg hd ha) (mul_nonneg ha hd) h2)
  have hf : a*c*(K b d)^2+b*d*(K a c)^2-(a*b+c*d)*K a c*K b d < 0 := by
    rw [factor_second]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hleft) (sub_neg.mpr hright)
  have hq : quartic a b c d (a*b+c*d) z < 0 := by
    have hsym : quartic a b c d (a*b+c*d) z = quartic a c b d (a*b+c*d) z := by
      unfold quartic e1 e2 e3 e4; ring
    rw [hsym, lemma_3_4 ha hc hb hd hu hv]
    apply div_neg_of_neg_of_pos
    · exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hf) (by positivity)
    · positivity
  have hdiff := lemma_3_3_second ha hb hc hd z
  have hroot : pairedPoly a c b d z=0 := pairedPoly_root ha hc hb hd
  have hmpos : 0 < 2*z^2*(b-a)*(d-c) := by
    have hba : 0 < b-a := sub_pos.mpr habs
    have hdc : 0 < d-c := sub_pos.mpr hcds
    positivity
  have hpn : pairedPoly a d b c z < 0 := by
    have := mul_neg_of_pos_of_neg hmpos hq; linarith
  have hlt := hsign.1.mp hpn
  exact ⟨hlt.le, iff_of_false (ne_of_lt hlt) (by tauto)⟩

/-- Theorem 3.1, all four claims in the original statement. -/
theorem theorem_3_1 {a b c d : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    K (K a b) (K c d) ≤ K (K a c) (K b d) ∧
    K (K a c) (K b d) ≤ K (K a d) (K b c) ∧
    (K (K a b) (K c d) = K (K a c) (K b d) ↔ b=c ∨ a*d=b*c) ∧
    (K (K a c) (K b d) = K (K a d) (K b c) ↔ a=b ∨ c=d) := by
  exact ⟨(rearrangement_first ha hab hbc hcd).1, (rearrangement_second ha hab hbc hcd).1,
    (rearrangement_first ha hab hbc hcd).2, (rearrangement_second ha hab hbc hcd).2⟩

end
end GD
