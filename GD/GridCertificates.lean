import GD.OBSInterpolation

namespace GD
noncomputable section
open Set Filter
open scoped Topology

theorem finite_nat_inf (f : ℕ → ℝ) (l h : ℕ) (hlh : l < h) :
    ∃ j, l ≤ j ∧ j < h ∧
      sInf {z : ℝ | ∃ i : ℕ, l ≤ i ∧ i < h ∧ z=f i}=f j ∧
      ∀ i, l ≤ i → i < h → f j ≤ f i := by
  obtain ⟨j,hj,hmin⟩ := (Finset.Ico l h).exists_min_image f ⟨l,Finset.mem_Ico.mpr ⟨le_rfl,hlh⟩⟩
  have hleast : IsLeast {z : ℝ | ∃ i : ℕ, l ≤ i ∧ i < h ∧ z=f i} (f j) := by
    refine ⟨⟨j,(Finset.mem_Ico.mp hj).1,(Finset.mem_Ico.mp hj).2,rfl⟩,?_⟩
    rintro z ⟨i,hi,hi',rfl⟩
    exact hmin i (Finset.mem_Ico.mpr ⟨hi,hi'⟩)
  exact ⟨j,(Finset.mem_Ico.mp hj).1,(Finset.mem_Ico.mp hj).2,hleast.csInf_eq,
    fun i hi hi' => hmin i (Finset.mem_Ico.mpr ⟨hi,hi'⟩)⟩

theorem lowerGrid_attained (k : ℕ) : ∃ j, 2^k ≤ j ∧ j < 2^(k+1) ∧
    lowerGrid k=U j/((j+1:ℕ):ℝ)^p ∧
    ∀ i, 2^k ≤ i → i < 2^(k+1) → lowerGrid k ≤ U i/((i+1:ℕ):ℝ)^p := by
  obtain ⟨j,hj,hj',he,hm⟩ := finite_nat_inf (fun j => U j/((j+1:ℕ):ℝ)^p) (2^k) (2^(k+1))
    (by
      have : 0 < (2:ℕ)^k := by positivity
      rw [pow_succ]
      omega)
  change lowerGrid k=U j/((j+1:ℕ):ℝ)^p at he
  exact ⟨j,hj,hj',he,fun i hi hi' => by rw [he]; exact hm i hi hi'⟩

theorem upperGrid_attained (k : ℕ) : ∃ j, 2^k ≤ j ∧ j ≤ 2^(k+1) ∧
    upperGrid k=U j/(j:ℝ)^p ∧
    ∀ i, 2^k ≤ i → i ≤ 2^(k+1) → upperGrid k ≤ U i/(i:ℝ)^p := by
  obtain ⟨j,hj,hj',he,hm⟩ := finite_nat_inf (fun j => U j/(j:ℝ)^p) (2^k) (2^(k+1)+1)
    (by
      have : 0 < (2:ℕ)^k := by positivity
      rw [pow_succ]
      omega)
  have hs : {z : ℝ | ∃ i : ℕ, 2^k ≤ i ∧ i < 2^(k+1)+1 ∧ z=U i/(i:ℝ)^p}=
      {z : ℝ | ∃ i : ℕ, 2^k ≤ i ∧ i ≤ 2^(k+1) ∧ z=U i/(i:ℝ)^p} := by
    ext z
    simp only [mem_setOf_eq,Nat.lt_add_one_iff]
  rw [hs] at he
  change upperGrid k=U j/(j:ℝ)^p at he
  exact ⟨j,hj,by omega,he,fun i hi hi' => by rw [he]; exact hm i hi (by omega)⟩

theorem lowerGrid_le_candidate (k j : ℕ) (hj : 2^k ≤ j) (hj' : j < 2^(k+1)) :
    lowerGrid k ≤ U j/((j+1:ℕ):ℝ)^p := by
  obtain ⟨i,hi,hi',he,hm⟩ := lowerGrid_attained k
  exact hm j hj hj'

theorem upperGrid_le_candidate (k j : ℕ) (hj : 2^k ≤ j) (hj' : j ≤ 2^(k+1)) :
    upperGrid k ≤ U j/(j:ℝ)^p := by
  obtain ⟨i,hi,hi',he,hm⟩ := upperGrid_attained k
  exact hm j hj hj'

theorem Phi_mantissa_ratio (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    Phi t=F ((2:ℝ)^t)/((2:ℝ)^t)^p := by
  rw [Phi_eq_profile t ht,phaseProfile,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    mul_comm t p,Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),two_rpow_p,
    Real.rpow_neg rho_pos.le,div_eq_inv_mul]

theorem grid_lower_sandwich (k : ℕ) : lowerGrid k ≤ phiMin ∧ phiMin ≤ upperGrid k := by
  constructor
  · obtain ⟨t,ht,he,hmin⟩ := phiMin_attained
    let x := (2:ℝ)^t
    let j := cellIndex k x
    have hx := two_rpow_mem t ht
    have hj := cell_bounds k x hx
    have hp : 1 ≤ (2:ℕ)^k := Nat.one_le_pow _ _ (by norm_num)
    have hj1 : 1 ≤ j := hp.trans hj.1
    have hpos : 0 < (j:ℝ) := by exact_mod_cast (show 0 < j by omega)
    have hpos' : 0 < ((j+1:ℕ):ℝ) := by positivity
    have hxm : (j:ℝ)/(2:ℝ)^k ∈ Icc (1:ℝ) 2 := by
      rw [← obsNode_rpow k j hj1]
      exact two_rpow_mem _ (obsNode_mem k j hj.1 (by omega))
    have hmono := F_strictMonoOn.monotoneOn hxm hx hj.2.2.1
    rw [F_grid k j hj.1 (by omega)] at hmono
    have hpow := Real.rpow_le_rpow (show 0 ≤ x by dsimp only [x]; positivity) hj.2.2.2 p_pos.le
    have hrho := rho_pos
    have heq : (U j/rho^k)/(((j+1:ℕ):ℝ)/(2:ℝ)^k)^p=U j/((j+1:ℕ):ℝ)^p := by
      rw [Real.div_rpow hpos'.le (by positivity),← Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2),two_rpow_p]
      field_simp
    rw [← he,Phi_mantissa_ratio t ht]
    apply (lowerGrid_le_candidate k j hj.1 (by omega)).trans
    rw [← heq]
    apply (div_le_div_of_nonneg_left (div_nonneg (U_nonneg j) (by positivity))
      (Real.rpow_pos_of_pos (by dsimp only [x]; positivity) p) hpow).trans
    exact div_le_div_of_nonneg_right hmono (Real.rpow_nonneg (by dsimp only [x]; positivity) _)
  · obtain ⟨j,hj,hj',he,hm⟩ := upperGrid_attained k
    rw [he]
    exact (normalized_U_bounds j ((Nat.one_le_pow k 2 (by norm_num)).trans hj)).1

theorem grid_certificate_gap (k : ℕ) :
    0 ≤ upperGrid k-lowerGrid k ∧ upperGrid k-lowerGrid k ≤ p/(2:ℝ)^k := by
  have hs := grid_lower_sandwich k
  refine ⟨by linarith,?_⟩
  obtain ⟨j,hj,hj',he,hm⟩ := lowerGrid_attained k
  have hj1 : 1 ≤ j := (Nat.one_le_pow k 2 (by norm_num)).trans hj
  have hj0 : 0 < (j:ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hp : 0 < (j:ℝ)^p := Real.rpow_pos_of_pos hj0 p
  have hp' : 0 < ((j:ℝ)+1)^p := Real.rpow_pos_of_pos (by linarith) p
  have hu := (proposition_5_2 j hj1).1
  have hr := power_ratio_gap (j:ℝ) (by exact_mod_cast hj1)
  have heq : U j/(j:ℝ)^p-U j/((j+1:ℕ):ℝ)^p=
      (U j/(j:ℝ)^p)*(1-((j:ℝ)/((j:ℝ)+1))^p) := by
    rw [Real.div_rpow hj0.le (by positivity)]
    push_cast
    field_simp
    <;> ring
  have hule : U j/(j:ℝ)^p ≤ 1 := (div_le_one hp).mpr hu
  have hmul := mul_le_mul_of_nonneg_right hule hr.1
  rw [one_mul] at hmul
  have hupper := upperGrid_le_candidate k j hj hj'.le
  have hfin : p/(j:ℝ) ≤ p/(2:ℝ)^k :=
    div_le_div_of_nonneg_left p_pos.le (by positivity) (by exact_mod_cast hj)
  rw [he]
  have hh : U j/(j:ℝ)^p-U j/((j+1:ℕ):ℝ)^p ≤ p/(2:ℝ)^k := by
    rw [heq]
    have hh : (U j/(j:ℝ)^p)*(1-((j:ℝ)/((j:ℝ)+1))^p) ≤ p/(j:ℝ) := by
      simpa only [one_mul] using hmul.trans hr.2
    exact hh.trans hfin
  linarith

theorem lowerGrid_mono : Monotone lowerGrid := by
  apply monotone_nat_of_le_succ
  intro k
  obtain ⟨n,hn,hn',he,hm⟩ := lowerGrid_attained (k+1)
  let j := n/2
  have hj : 2^k ≤ j ∧ j < 2^(k+1) := by dsimp only [j]; rw [pow_succ] at hn hn'; omega
  have hj1 : 1 ≤ j := (Nat.one_le_pow k 2 (by norm_num)).trans hj.1
  have hrho := rho_pos
  have hnum : rho*U j ≤ U n := by
    rw [← U_even]
    exact U_strictMono.monotone (by dsimp only [j]; omega)
  have hn1 : 0 < ((n+1:ℕ):ℝ) := by positivity
  have hjp : 0 < ((j+1:ℕ):ℝ) := by positivity
  have hden : ((n+1:ℕ):ℝ)^p ≤ rho*((j+1:ℕ):ℝ)^p := by
    have hh : ((n+1:ℕ):ℝ) ≤ 2*((j+1:ℕ):ℝ) := by exact_mod_cast (show n+1 ≤ 2*(j+1) by dsimp only [j]; omega)
    have hh' := Real.rpow_le_rpow hn1.le hh p_pos.le
    rwa [Real.mul_rpow (by norm_num) hjp.le,two_rpow_p] at hh'
  have heq : U j/((j+1:ℕ):ℝ)^p=(rho*U j)/(rho*((j+1:ℕ):ℝ)^p) := by field_simp <;> ring
  rw [he]
  apply (lowerGrid_le_candidate k j hj.1 hj.2).trans
  rw [heq]
  exact (div_le_div_of_nonneg_left (mul_nonneg hrho.le (U_nonneg j)) (Real.rpow_pos_of_pos hn1 p) hden).trans
    (div_le_div_of_nonneg_right hnum (Real.rpow_nonneg hn1.le p))

theorem upperGrid_antitone : Antitone upperGrid := by
  apply antitone_nat_of_succ_le
  intro k
  obtain ⟨j,hj,hj',he,hm⟩ := upperGrid_attained k
  have hrho := rho_pos
  have hh := upperGrid_le_candidate (k+1) (2*j) (by rw [pow_succ]; omega) (by rw [pow_succ]; omega)
  have heq : U (2*j)/((2*j:ℕ):ℝ)^p=U j/(j:ℝ)^p := by
    rw [U_even,Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num) (Nat.cast_nonneg j),two_rpow_p]
    exact mul_div_mul_left _ _ hrho.ne'
  rwa [heq,← he] at hh

theorem grid_certificate_limits : Tendsto lowerGrid atTop (𝓝 phiMin) ∧ Tendsto upperGrid atTop (𝓝 phiMin) := by
  have herr : Tendsto (fun k : ℕ => p/(2:ℝ)^k) atTop (𝓝 0) := by simpa using dyadic_mesh_tendsto.const_mul p
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g:=fun k => phiMin-p/(2:ℝ)^k) (h:=fun _ => phiMin)
    · simpa using tendsto_const_nhds.sub herr
    · exact tendsto_const_nhds
    · intro k
      have h := grid_lower_sandwich k
      have hg := (grid_certificate_gap k).2
      linarith
    · exact fun k => (grid_lower_sandwich k).1
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g:=fun _ => phiMin) (h:=fun k => phiMin+p/(2:ℝ)^k)
    · exact tendsto_const_nhds
    · simpa using tendsto_const_nhds.add herr
    · exact fun k => (grid_lower_sandwich k).2
    · intro k
      have h := grid_lower_sandwich k
      have hg := (grid_certificate_gap k).2
      linarith

theorem theorem_C_3_bounds : Targets.theorem_C_3_bounds :=
  ⟨fun k => ⟨(grid_lower_sandwich k).1,(grid_lower_sandwich k).2,grid_certificate_gap k⟩,
    lowerGrid_mono,upperGrid_antitone,grid_certificate_limits⟩

end
end GD
