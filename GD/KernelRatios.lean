import GD.Kernel
namespace GD
noncomputable section

theorem K_strict_mono {x y x' y' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxx : x ≤ x') (hyy : y ≤ y') (hs : x < x' ∨ y < y') : K x y < K x' y' := by
  rcases hs with h | h
  · exact (K_strict_left hx hy h).trans_le (K_mono (hx.trans hxx) hy le_rfl hyy)
  · exact (K_strict_right hx hy h).trans_le (K_mono hx (hy.trans hyy) hxx le_rfl)

/-- Proposition 2.6, multiplicative comparison (9) with all strictness clauses. -/
theorem K_ratio_bounds {x y x' y' : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hx' : 0 < x') (hy' : 0 < y') :
    min (x'/x) (y'/y) ≤ K x' y'/K x y ∧ K x' y'/K x y ≤ max (x'/x) (y'/y) ∧
    (x'/x ≠ y'/y → min (x'/x) (y'/y) < K x' y'/K x y ∧ K x' y'/K x y < max (x'/x) (y'/y)) := by
  let l := min (x'/x) (y'/y)
  let M := max (x'/x) (y'/y)
  have hl : 0 < l := lt_min (div_pos hx' hx) (div_pos hy' hy)
  have hM : 0 < M := lt_of_lt_of_le (div_pos hx' hx) (le_max_left _ _)
  have hxl : l*x ≤ x' := (le_div_iff₀ hx).mp (min_le_left _ _)
  have hyl : l*y ≤ y' := (le_div_iff₀ hy).mp (min_le_right _ _)
  have hxM : x' ≤ M*x := (div_le_iff₀ hx).mp (le_max_left _ _)
  have hyM : y' ≤ M*y := (div_le_iff₀ hy).mp (le_max_right _ _)
  have hk : 0 < K x y := K_pos hx.le hy.le (by linarith)
  have hlo := K_mono (mul_pos hl hx).le (mul_pos hl hy).le hxl hyl
  have hhi := K_mono hx'.le hy'.le hxM hyM
  rw [K_hom hl.le hx.le hy.le] at hlo
  rw [K_hom hM.le hx.le hy.le] at hhi
  refine ⟨(le_div_iff₀ hk).mpr hlo,(div_le_iff₀ hk).mpr hhi,?_⟩
  intro hne
  have hstrictlo : l*x < x' ∨ l*y < y' := by
    by_cases h : l*x < x'
    · exact Or.inl h
    · right
      have he : l*x=x' := le_antisymm hxl (le_of_not_gt h)
      apply lt_of_le_of_ne hyl
      intro he'
      have h1 : x'/x=l := (div_eq_iff hx.ne').mpr (by linarith)
      have h2 : y'/y=l := (div_eq_iff hy.ne').mpr (by linarith)
      exact hne (h1.trans h2.symm)
  have hstricthi : x' < M*x ∨ y' < M*y := by
    by_cases h : x' < M*x
    · exact Or.inl h
    · right
      have he : x'=M*x := le_antisymm hxM (le_of_not_gt h)
      apply lt_of_le_of_ne hyM
      intro he'
      have h1 : x'/x=M := (div_eq_iff hx.ne').mpr he
      have h2 : y'/y=M := (div_eq_iff hy.ne').mpr he'
      exact hne (h1.trans h2.symm)
  have h1 := K_strict_mono (mul_pos hl hx).le (mul_pos hl hy).le hxl hyl hstrictlo
  have h2 := K_strict_mono hx'.le hy'.le hxM hyM hstricthi
  rw [K_hom hl.le hx.le hy.le] at h1
  rw [K_hom hM.le hx.le hy.le] at h2
  exact ⟨(lt_div_iff₀ hk).mpr h1,(div_lt_iff₀ hk).mpr h2⟩

end
end GD
