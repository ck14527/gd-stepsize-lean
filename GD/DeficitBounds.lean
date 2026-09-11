import GD.PowerEnvelope

namespace GD
noncomputable section

theorem Bsup_gt_one : 1 < Bsup := by
  have ht : 1 < (2:ℝ)^q := Real.one_lt_rpow (by norm_num) q_pos
  exact ht.trans Bsup_gt_two_rpow

theorem Bsup_pos : 0 < Bsup := lt_trans zero_lt_one Bsup_gt_one

theorem cstar_pos : 0 < cstar := Real.rpow_pos_of_pos Bsup_pos _

theorem W_power_bound (N : ℕ) (hN : 1 ≤ N) :
    (W N)^q ≤ Bsup*(N:ℝ) ∧ W N ≤ (Bsup*(N:ℝ))^p := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    have hn0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hb0 : 0 ≤ Bsup*(N:ℝ) := (mul_pos Bsup_pos hn0).le
    have hupper : W N ≤ (Bsup*(N:ℝ))^p := by
      by_cases hn : N=1
      · subst N
        rw [W_one,Nat.cast_one,mul_one]
        exact (Real.one_le_rpow Bsup_gt_one.le p_pos.le)
      apply W_upper_of_pivots N (by omega) _ (Real.rpow_nonneg hb0 _)
      intro m hm hmN
      have hr : 1 ≤ N-m := by omega
      have hup := (U_power_q m hm).1
      have hrec := (ih (N-m) (by omega) hr).1
      have hs := lemma_6_4.2.2.2.2.1 (U m) (W (N-m)) (U_nonneg m) (W_pos _ hr).le
      have hcast : (m:ℝ)+(N-m:ℕ)=(N:ℝ) := by
        rw [Nat.cast_sub hmN.le]
        ring
      have hbmul := mul_le_mul_of_nonneg_left hup Bsup_pos.le
      have hpow : (A (U m) (W (N-m)))^q ≤ Bsup*(N:ℝ) := by
        nlinarith [hs,hrec,hbmul]
      have hp := Real.rpow_le_rpow (Real.rpow_nonneg (A_nonneg (U_nonneg m) (W_pos _ hr).le) _) hpow p_pos.le
      rw [← Real.rpow_mul (A_nonneg (U_nonneg m) (W_pos _ hr).le),mul_comm q p,p_mul_q,Real.rpow_one] at hp
      exact hp
    refine ⟨?_,hupper⟩
    have hpow := Real.rpow_le_rpow (W_pos N hN).le hupper q_pos.le
    rwa [← Real.rpow_mul hb0,p_mul_q,Real.rpow_one] at hpow

theorem C_ge_cstar (N : ℕ) (hN : 1 ≤ N) : cstar ≤ C N := by
  have hw := W_pos N hN
  have hb := Real.rpow_pos_of_pos Bsup_pos p
  have he : cstar=1/Bsup^p := by rw [cstar,Real.rpow_neg Bsup_pos.le,one_div]
  have hupper := (W_power_bound N hN).2
  rw [Real.mul_rpow Bsup_pos.le (Nat.cast_nonneg N)] at hupper
  rw [C,etaF,mul_one_div,he]
  apply (le_div_iff₀ hw).mpr
  rw [one_div,inv_mul_eq_div]
  exact (div_le_iff₀ hb).mpr (by simpa only [mul_comm (Bsup^p)] using hupper)

theorem deficit_nonneg (N : ℕ) (hN : 1 ≤ N) : 0 ≤ deficit N := by
  exact sub_nonneg.mpr (W_power_bound N hN).1

theorem sigma_nonneg (u w : ℝ) (hu : 0 ≤ u) (hw : 0 ≤ w) : 0 ≤ sigma u w := by
  exact sub_nonneg.mpr (lemma_6_4.2.2.2.2.1 u w hu hw)

/-- Proposition D.3, with all three nonnegative terms proved for actual U,W. -/
theorem proposition_D_3 : Targets.proposition_D_3 := by
  constructor
  · intro N hN
    exact ⟨(W_power_bound N hN).1,C_ge_cstar N hN⟩
  · intro N m hm hmN hp
    exact ⟨deficit_identity N m hmN.le hp,
      mul_nonneg Bsup_pos.le (sub_nonneg.mpr (U_power_q m hm).1),
      deficit_nonneg (N-m) (by omega),
      sigma_nonneg (U m) (W (N-m)) (U_nonneg m) (W_pos _ (by omega)).le⟩

end
end GD
