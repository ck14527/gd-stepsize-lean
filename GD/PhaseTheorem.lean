import GD.PhaseRegularity

namespace GD
noncomputable section
open Set Filter
open scoped Topology

theorem periodic_fract (G : ℝ → ℝ) (hp : Function.Periodic G 1) (t : ℝ) : G (Int.fract t)=G t := by
  change G (t-(Int.floor t:ℝ))=G t
  simpa only [mul_one] using hp.sub_int_mul_eq (Int.floor t) (x:=t)

theorem Phi_unique (G : ℝ → ℝ) (hc : Continuous G) (hp : ∀ t, G (t+1)=G t)
    (hseed : ∀ N : ℕ, 1 ≤ N → U N=(N:ℝ)^p*G (phase N)) : G=Phi := by
  let H : ℝ → ℝ := fun x => x^p*G (Real.logb 2 x)
  have hcont : ContinuousOn H (Icc (1:ℝ) 2) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    exact ((Real.continuousAt_rpow_const x p (Or.inl hx0.ne')).mul
      (hc.continuousAt.comp (Real.continuousAt_logb hx0.ne'))).continuousWithinAt
  have hmatch : InterpolationMatches H := by
    intro k j hj hj'
    have hj1 : 1 ≤ j := (Nat.one_le_pow k 2 (by norm_num)).trans hj
    have hj0 : (0:ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have heG : G (Real.logb 2 ((j:ℝ)/(2:ℝ)^k))=G (phase j) := by
      rw [Real.logb_div hj0.ne' (by positivity),Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2),mul_one]
      have hper : G (Real.logb 2 (j:ℝ)-(k:ℝ))=G (Real.logb 2 (j:ℝ)) := by
        simpa only [mul_one] using (show Function.Periodic G 1 from hp).sub_nat_mul_eq k (x:=Real.logb 2 (j:ℝ))
      rw [hper]
      exact (periodic_fract G hp (Real.logb 2 (j:ℝ))).symm
    have hepow : ((j:ℝ)/(2:ℝ)^k)^p=(j:ℝ)^p/rho^k := by
      rw [Real.div_rpow hj0.le (by positivity),← Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2),two_rpow_p]
    change ((j:ℝ)/(2:ℝ)^k)^p*G (Real.logb 2 ((j:ℝ)/(2:ℝ)^k))=U j/rho^k
    rw [heG,hepow,hseed j hj1]
    ring
  have heH := F_unique H hcont hmatch
  funext t
  have hf := Int.fract_nonneg t
  have hf1 := Int.fract_lt_one t
  have hx := two_rpow_mem (Int.fract t) ⟨hf,hf1.le⟩
  have heF := heH hx
  have hepow : ((2:ℝ)^(Int.fract t))^p=rho^(Int.fract t) := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),mul_comm (Int.fract t) p,
      Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),two_rpow_p]
  change ((2:ℝ)^(Int.fract t))^p*G (Real.logb 2 ((2:ℝ)^(Int.fract t)))=F ((2:ℝ)^(Int.fract t)) at heF
  rw [Real.logb_rpow (by norm_num) (by norm_num),hepow] at heF
  rw [Phi,← heF,← mul_assoc,← Real.rpow_add rho_pos,neg_add_cancel,Real.rpow_zero,one_mul]
  exact (periodic_fract G hp t).symm

@[simp] theorem Phi_zero : Phi 0=1 := by simp [Phi,F_one]

theorem Phi_le_one (t : ℝ) : Phi t ≤ 1 := by
  have he : Phi t=Phi (Int.fract t) := (periodic_fract Phi Phi_periodic t).symm
  by_cases h : Int.fract t=0
  · rw [he,h,Phi_zero]
  · rw [he]
    exact (Phi_lt_one _ ⟨lt_of_le_of_ne (Int.fract_nonneg t) (Ne.symm h),Int.fract_lt_one t⟩).le

theorem phiMin_attained : ∃ t ∈ Icc (0:ℝ) 1, Phi t=phiMin ∧ ∀ x : ℝ, phiMin ≤ Phi x := by
  obtain ⟨t,ht,hmin⟩ := isCompact_Icc.exists_isMinOn (show (Icc (0:ℝ) 1).Nonempty by exact ⟨0,by norm_num⟩) Phi_continuous.continuousOn
  have hleast : IsLeast (Phi '' Icc (0:ℝ) 1) (Phi t) := by
    refine ⟨⟨t,ht,rfl⟩,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact hmin hx
  have he : phiMin=Phi t := hleast.csInf_eq
  refine ⟨t,ht,he.symm,?_⟩
  intro x
  rw [he,← periodic_fract Phi Phi_periodic x]
  exact hmin ⟨Int.fract_nonneg x,(Int.fract_lt_one x).le⟩

theorem phiMin_bounds : 0 < phiMin ∧ phiMin < 1 := by
  obtain ⟨t,ht,he,hbound⟩ := phiMin_attained
  constructor
  · rw [← he]
    exact Phi_pos t
  · exact (hbound (1/2)).trans_lt (Phi_lt_one (1/2) (by norm_num))

theorem Phi_sSup : sSup (Phi '' Icc (0:ℝ) 1)=1 := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨0,by norm_num,Phi_zero⟩,?_⟩
  rintro y ⟨x,hx,rfl⟩
  exact Phi_le_one x

theorem Phi_range : Phi '' Icc (0:ℝ) 1=Icc phiMin 1 := by
  obtain ⟨t,ht,he,hbound⟩ := phiMin_attained
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact ⟨hbound x,Phi_le_one x⟩
  · have hi := intermediate_value_Icc' ht.1 (Phi_continuous.continuousOn (s:=Icc 0 t))
    rw [Phi_zero,he] at hi
    exact hi.trans (image_mono (Icc_subset_Icc le_rfl ht.2))

/-- Theorem 5.5 with the exact stated Lipschitz constant and uniqueness. -/
theorem theorem_5_5 : Targets.theorem_5_5 :=
  ⟨Phi_positive_periodic_lipschitz,U_phase_exact,Phi_unique,
    phiMin_bounds.1,phiMin_bounds.2,Phi_sSup,Phi_lipschitz⟩

end
end GD
