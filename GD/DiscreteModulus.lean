import GD.DiscreteIncrements
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace GD
noncomputable section
open Set

def normalizedW (N : ℕ) : ℝ := W N/(N:ℝ)^p

theorem normalizedW_bounds (N : ℕ) (hN : 1 ≤ N) : phiMin ≤ normalizedW N ∧ normalizedW N ≤ rho := by
  have hn0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := Real.rpow_pos_of_pos hn0 p
  have hs := W_sandwich N hN
  have hu := U_ge_one N hN
  have hpow := (proposition_5_2 N hN).1
  have hmin := (normalized_U_bounds N hN).1
  constructor
  · exact hmin.trans (div_le_div_of_nonneg_right (by linarith : U N ≤ W N) hp.le)
  · apply (div_le_iff₀ hp).mpr
    exact hs.2.trans (mul_le_mul_of_nonneg_left hpow rho_pos.le)

theorem power_ratio_gap (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ 1-(x/(x+1))^p ∧ 1-(x/(x+1))^p ≤ p/x := by
  have hx0 : 0 < x := by linarith
  have hxp : 0 < x+1 := by linarith
  have ht : x/(x+1) ≤ 1 := (div_le_one hxp).mpr (by linarith)
  have hnon := Real.rpow_le_rpow (div_pos hx0 hxp).le ht p_pos.le
  rw [Real.one_rpow] at hnon
  have hs : -1 ≤ -(1/(x+1)) := by
    have h := (div_le_one hxp).mpr (show (1:ℝ) ≤ x+1 by linarith)
    linarith
  have hb := one_add_mul_self_le_rpow_one_add hs p_bounds.1.le
  have he : 1+ -(1/(x+1))=x/(x+1) := by field_simp
  rw [he] at hb
  have hl : 1-(x/(x+1))^p ≤ p/(x+1) := by
    have he' : p * -(1/(x+1))= -(p/(x+1)) := by ring
    rw [he'] at hb
    linarith
  refine ⟨sub_nonneg.mpr hnon,hl.trans ?_⟩
  exact div_le_div_of_nonneg_left p_pos.le hx0 (by linarith)

theorem normalizedW_increment (LF : ℝ)
    (hLF : ∀ x y : ℝ, x ∈ Icc (1:ℝ) 2 → y ∈ Icc (1:ℝ) 2 → |F x-F y| ≤ LF*|x-y|)
    (N : ℕ) (hN : 1 ≤ N) :
    |normalizedW (N+1)-normalizedW N| ≤ (4*max 1 LF+rho*p)/(N:ℝ) := by
  let x : ℝ := N
  have hx : 1 ≤ x := by change (1:ℝ) ≤ (N:ℝ); exact_mod_cast hN
  have hx0 : 0 < x := by linarith
  have hxp : 0 < x+1 := by linarith
  have ha : 0 < x^p := Real.rpow_pos_of_pos hx0 p
  have hb : 0 < (x+1)^p := Real.rpow_pos_of_pos hxp p
  have hab := Real.rpow_le_rpow hx0.le (show x ≤ x+1 by linarith) p_pos.le
  have hw := W_pos N hN
  have hd := W_increment_bound LF hLF N hN
  have hL : 0 ≤ max 1 LF := le_trans zero_le_one (le_max_left _ _)
  have hD := normalizedW_bounds N hN
  have hgap := power_ratio_gap x hx
  have hratio : x^p/(x+1)^p=(x/(x+1))^p := (Real.div_rpow hx0.le hxp.le p).symm
  have hfirst : (W (N+1)-W N)/(x+1)^p ≤ 4*max 1 LF/x := by
    calc
      _ ≤ (4*max 1 LF*x^(p-1))/(x+1)^p := div_le_div_of_nonneg_right hd.2 hb.le
      _ ≤ (4*max 1 LF*x^(p-1))/x^p := div_le_div_of_nonneg_left (by positivity) ha hab
      _ = 4*max 1 LF/x := by rw [Real.rpow_sub_one hx0.ne']; field_simp; ring
  have hsecond : normalizedW N*(1-x^p/(x+1)^p) ≤ rho*(p/x) := by
    rw [hratio]
    exact mul_le_mul hD.2 hgap.2 hgap.1 rho_pos.le
  have he : normalizedW (N+1)-normalizedW N=
      (W (N+1)-W N)/(x+1)^p-normalizedW N*(1-x^p/(x+1)^p) := by
    simp only [normalizedW,Nat.cast_add,Nat.cast_one]
    change W (N+1)/(x+1)^p-W N/x^p=
      (W (N+1)-W N)/(x+1)^p-(W N/x^p)*(1-x^p/(x+1)^p)
    field_simp
    <;> ring
  rw [he]
  have ht := abs_sub ((W (N+1)-W N)/(x+1)^p) (normalizedW N*(1-x^p/(x+1)^p))
  rw [abs_of_nonneg (div_nonneg hd.1.le hb.le),
    abs_of_nonneg (mul_nonneg (phiMin_bounds.1.le.trans hD.1) (by rw [hratio]; exact hgap.1))] at ht
  change _ ≤ (4*max 1 LF+rho*p)/x
  have he' : 4*max 1 LF/x+rho*(p/x)=(4*max 1 LF+rho*p)/x := by ring
  linarith

theorem C_eq_inverse_normalizedW (N : ℕ) : C N=1/normalizedW N := by
  unfold C etaF normalizedW
  rw [one_div_div]
  ring

theorem C_increment_bound (LF : ℝ)
    (hLF : ∀ x y : ℝ, x ∈ Icc (1:ℝ) 2 → y ∈ Icc (1:ℝ) 2 → |F x-F y| ≤ LF*|x-y|)
    (N : ℕ) (hN : 1 ≤ N) :
    |C (N+1)-C N| ≤ (4*max 1 LF+rho*p)/(phiMin^2*(N:ℝ)) := by
  have hn0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmin := phiMin_bounds.1
  have ha := (normalizedW_bounds N hN).1
  have hb := (normalizedW_bounds (N+1) (by omega)).1
  have ha0 : 0 < normalizedW N := hmin.trans_le ha
  have hb0 : 0 < normalizedW (N+1) := hmin.trans_le hb
  have hp : phiMin^2 ≤ normalizedW (N+1)*normalizedW N := by
    simpa only [pow_two] using mul_le_mul hb ha hmin.le hb0.le
  have he : |C (N+1)-C N|=|normalizedW (N+1)-normalizedW N|/(normalizedW (N+1)*normalizedW N) := by
    rw [C_eq_inverse_normalizedW,C_eq_inverse_normalizedW]
    have he' : 1/normalizedW (N+1)-1/normalizedW N=
        -(normalizedW (N+1)-normalizedW N)/(normalizedW (N+1)*normalizedW N) := by field_simp
    rw [he',abs_div,abs_neg,abs_of_pos (mul_pos hb0 ha0)]
  rw [he]
  calc
    _ ≤ |normalizedW (N+1)-normalizedW N|/phiMin^2 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hmin) hp
    _ ≤ ((4*max 1 LF+rho*p)/(N:ℝ))/phiMin^2 :=
      div_le_div_of_nonneg_right (normalizedW_increment LF hLF N hN) (sq_nonneg _)
    _ = (4*max 1 LF+rho*p)/(phiMin^2*(N:ℝ)) := by rw [div_div,mul_comm (N:ℝ)]

/-- Lemma D.2 with its original constants and quantification over every admissible LF. -/
theorem lemma_D_2 : Targets.lemma_D_2 := by
  intro LF hLF
  exact ⟨U_increment_bound LF hLF,W_increment_bound LF hLF,C_increment_bound LF hLF⟩

end
end GD
