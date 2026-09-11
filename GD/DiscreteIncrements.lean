import GD.ObjectivePhase

namespace GD
noncomputable section
open Set

theorem U_increment_bound (LF : ℝ)
    (hLF : ∀ x y : ℝ, x ∈ Icc (1:ℝ) 2 → y ∈ Icc (1:ℝ) 2 → |F x-F y| ≤ LF*|x-y|)
    (m : ℕ) (hm : 1 ≤ m) :
    0 < U m-U (m-1) ∧ U m-U (m-1) ≤ max 1 LF*(m:ℝ)^(p-1) := by
  have hpos : 0 < U m-U (m-1) := sub_pos.mpr (U_strictMono (by omega))
  refine ⟨hpos,?_⟩
  by_cases he : m=1
  · subst m
    simpa using (le_max_left (1:ℝ) LF)
  let k := (m-1).log2
  have hlo : 2^k ≤ m-1 := Nat.log2_self_le (by omega)
  have hhi : m ≤ 2^(k+1) := by
    have hh : m-1 < 2^(k+1) := Nat.lt_log2_self (n:=m-1)
    omega
  have hd : 0 < (2:ℝ)^k := by positivity
  have hr : 0 < rho^k := pow_pos rho_pos k
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlowc : (2:ℝ)^k ≤ (m-1:ℕ) := by exact_mod_cast hlo
  have hhighc : (m:ℝ) ≤ (2:ℝ)^(k+1) := by exact_mod_cast hhi
  have hmc : (m-1:ℕ)=(m:ℝ)-1 := by rw [Nat.cast_sub hm]; norm_num
  have hxl : (m-1:ℕ)/(2:ℝ)^k ∈ Icc (1:ℝ) 2 := by
    constructor
    · exact (le_div_iff₀ hd).mpr (by simpa using hlowc)
    · apply (div_le_iff₀ hd).mpr
      rw [pow_succ] at hhighc
      linarith
  have hxr : (m:ℝ)/(2:ℝ)^k ∈ Icc (1:ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ hd).mpr
      linarith
    · apply (div_le_iff₀ hd).mpr
      simpa [pow_succ,mul_comm] using hhighc
  have hf := hLF ((m:ℝ)/(2:ℝ)^k) ((m-1:ℕ)/(2:ℝ)^k) hxr hxl
  rw [F_grid k m (by omega) hhi,F_grid k (m-1) hlo (by omega)] at hf
  have hgap : (m:ℝ)/(2:ℝ)^k-(m-1:ℕ)/(2:ℝ)^k=1/(2:ℝ)^k := by rw [hmc]; ring
  have hUg : U m/rho^k-U (m-1)/rho^k=(U m-U (m-1))/rho^k := by ring
  rw [hgap,hUg,abs_of_pos (div_pos hpos hr),abs_of_pos (by positivity : 0 < 1/(2:ℝ)^k)] at hf
  have hf' := (div_le_iff₀ hr).mp hf
  have hepow : rho^k/(2:ℝ)^k=((2:ℝ)^k)^(p-1) := by
    rw [Real.rpow_sub hd,Real.rpow_one,← Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2),two_rpow_p]
  have hbase : (2:ℝ)^k ≤ (m:ℝ) := by linarith
  have hpow := Real.rpow_le_rpow hd.le hbase (by linarith [p_bounds.1] : 0 ≤ p-1)
  calc
    U m-U (m-1) ≤ LF*(rho^k/(2:ℝ)^k) := by convert hf' using 1 <;> ring
    _ ≤ max 1 LF*(rho^k/(2:ℝ)^k) := mul_le_mul_of_nonneg_right (le_max_right _ _) (div_pos hr hd).le
    _ = max 1 LF*((2:ℝ)^k)^(p-1) := by rw [hepow]
    _ ≤ max 1 LF*(m:ℝ)^(p-1) := mul_le_mul_of_nonneg_left hpow (le_trans zero_le_one (le_max_left _ _))

theorem A_left_increment (u v w : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hw : 0 ≤ w) :
    A v w-A u w ≤ 4*(v-u) := by
  have hv : 0 ≤ v := hu.trans huv
  let a := Real.sqrt (w^2+8*u*w)
  let b := Real.sqrt (w^2+8*v*w)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha : a^2=w^2+8*u*w := Real.sq_sqrt (by positivity)
  have hb : b^2=w^2+8*v*w := Real.sq_sqrt (by positivity)
  have haw : w ≤ a := by nlinarith [mul_nonneg hu hw]
  have hprod := mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr haw)
  have hsq : b^2 ≤ (a+4*(v-u))^2 := by nlinarith [sq_nonneg (v-u)]
  have hroot : b ≤ a+4*(v-u) := by nlinarith
  change (4*v+w+b)/2-(4*u+w+a)/2 ≤ 4*(v-u)
  linarith

theorem A_gt_right (u w : ℝ) (hu : 0 < u) (hw : 0 ≤ w) : w < A u w := by
  have hs := Real.sq_sqrt (show 0 ≤ w^2+8*u*w by positivity)
  have hs0 := Real.sqrt_nonneg (w^2+8*u*w)
  have hroot : w ≤ Real.sqrt (w^2+8*u*w) := by nlinarith [mul_nonneg hu.le hw]
  unfold A
  linarith

theorem W_increment_bound (LF : ℝ)
    (hLF : ∀ x y : ℝ, x ∈ Icc (1:ℝ) 2 → y ∈ Icc (1:ℝ) 2 → |F x-F y| ≤ LF*|x-y|)
    (N : ℕ) (hN : 1 ≤ N) :
    0 < W (N+1)-W N ∧ W (N+1)-W N ≤ 4*max 1 LF*(N:ℝ)^(p-1) := by
  have hw := W_pos N hN
  have hpivot := W_pivot_lower (N+1) 1 (by omega) (by omega)
  simp only [Nat.add_sub_cancel,U_one] at hpivot
  have hstrict := A_gt_right 1 (W N) (by norm_num) hw.le
  refine ⟨by linarith,?_⟩
  have hL : 0 ≤ max 1 LF := le_trans zero_le_one (le_max_left _ _)
  have hup : W (N+1) ≤ W N+4*max 1 LF*(N:ℝ)^(p-1) := by
    apply W_upper_of_pivots (N+1) (by omega) _ (by positivity)
    intro m hm hmN
    have hr : 1 ≤ N+1-m := by omega
    have hi := A_left_increment (U (m-1)) (U m) (W (N+1-m)) (U_nonneg _)
      (U_strictMono.monotone (by omega)) (W_pos _ hr).le
    have hbase : A (U (m-1)) (W (N+1-m)) ≤ W N := by
      by_cases he : m=1
      · subst m
        simp only [Nat.sub_self,U_zero,Nat.add_sub_cancel,A_zero_left _ hw.le]
        exact le_rfl
      · have hp := W_pivot_lower N (m-1) (by omega) (by omega)
        simpa only [show N-(m-1)=N+1-m by omega] using hp
    have hu := (U_increment_bound LF hLF m hm).2
    have hpow := Real.rpow_le_rpow (Nat.cast_nonneg m) (show (m:ℝ) ≤ (N:ℝ) by exact_mod_cast (show m ≤ N by omega))
      (by linarith [p_bounds.1] : 0 ≤ p-1)
    have hmul := mul_le_mul_of_nonneg_left hpow hL
    linarith
  linarith

end
end GD
