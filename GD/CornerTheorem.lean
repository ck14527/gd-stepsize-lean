import GD.DyadicDerivatives
import GD.CornerCertificate

namespace GD
noncomputable section
open Set Filter
open scoped Topology

def rightDyadicSlope (k j l : ℕ) : ℝ := slope (k+l) (j*2^l)

theorem rightDyadic_indices (k j l : ℕ) (hj : 2^k ≤ j) (hj' : j < 2^(k+1)) :
    2^(k+l) ≤ j*2^l ∧ j*2^l < 2^(k+l+1) := by
  constructor
  · rw [pow_add]
    exact Nat.mul_le_mul_right _ hj
  · have h := Nat.mul_lt_mul_of_pos_right hj' (show 0 < (2:ℕ)^l by positivity)
    simpa [← pow_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem rightDyadic_antitone (k j : ℕ) (hj : 2^k ≤ j) (hj' : j < 2^(k+1)) :
    Antitone (rightDyadicSlope k j) := by
  apply antitone_nat_of_succ_le
  intro l
  have hi := rightDyadic_indices k j l hj hj'
  have hn : 1 ≤ j*2^l := (Nat.one_le_pow (k+l) 2 (by norm_num)).trans hi.1
  have hw := (weights_bounds (R (j*2^l)) (R_gt_one _ hn).le).2.1
  have hs := (slope_children (k+l) (j*2^l) hn).1
  have he : j*2^(l+1)=2*(j*2^l) := by ring
  unfold rightDyadicSlope
  rw [show k+(l+1)=k+l+1 by omega,he,hs]
  exact mul_le_of_le_one_left (slope_pos (k+l) (j*2^l)).le hw

theorem rightDyadic_tendsto (k j : ℕ) (hj : 2^k ≤ j) (hj' : j < 2^(k+1)) :
    Tendsto (rightDyadicSlope k j) atTop (𝓝 (derivativeProfile ((j:ℝ)/(2:ℝ)^k))) := by
  have hx := cell_interval_subset k j hj hj' (show (j:ℝ)/(2:ℝ)^k ∈ Icc ((j:ℝ)/(2:ℝ)^k) (((j+1:ℕ):ℝ)/(2:ℝ)^k) from
    ⟨le_rfl,div_le_div_of_nonneg_right (by exact_mod_cast (show j ≤ j+1 by omega)) (by positivity)⟩)
  have ht : Tendsto (fun l : ℕ => k+l) atTop atTop := by simpa only [Nat.add_comm] using tendsto_add_atTop_nat k
  apply ((slopeGrid_tendsto _ hx).comp ht).congr'
  exact Eventually.of_forall (fun l => by
    have hi := rightDyadic_indices k j l hj hj'
    have he : (j:ℝ)/(2:ℝ)^k=((j*2^l:ℕ):ℝ)/(2:ℝ)^(k+l) := by
      push_cast
      rw [pow_add]
      field_simp
      <;> ring
    change slopeGrid (k+l) ((j:ℝ)/(2:ℝ)^k)=rightDyadicSlope k j l
    rw [slopeGrid,he,cellIndex_eq_of_mem (k+l) (j*2^l) hi.1 hi.2 _ ⟨le_rfl,?_⟩]
    · rfl
    · exact div_lt_div_of_pos_right (by exact_mod_cast (show j*2^l < j*2^l+1 by omega)) (by positivity))

theorem rightDyadic_limit_le (k j l : ℕ) (hj : 2^k ≤ j) (hj' : j < 2^(k+1)) :
    derivativeProfile ((j:ℝ)/(2:ℝ)^k) ≤ rightDyadicSlope k j l := by
  apply le_of_tendsto (rightDyadic_tendsto k j hj hj')
  filter_upwards [eventually_ge_atTop l] with n hn
  exact rightDyadic_antitone k j hj hj' hn

theorem corner_slope_gap : slope 7 192 < slope 7 191 := by
  have hrho := rho_pos
  have hp : 0 < (2:ℝ)^7/rho^7 := by positivity
  have h := mul_pos hp corner_discrete_gap
  have he : slope 7 191-slope 7 192=((2:ℝ)^7/rho^7)*(2*U 192-U 191-U 193) := by
    unfold slope
    norm_num only [show (191:ℕ)+1=192 by omega,show (192:ℕ)+1=193 by omega]
    ring
  exact sub_pos.mp (he ▸ h)

theorem corollary_C_2 : Targets.corollary_C_2 := by
  let dl := leftDyadicDerivative 1 3
  let dr := derivativeProfile (3/2)
  have hl : HasDerivWithinAt F dl (Iic (3/2)) (3/2) := by
    simpa only [Nat.cast_ofNat,pow_one] using (F_hasDeriv_left_dyadic 1 3 (by norm_num) (by norm_num)).Iic_of_Iio
  have hr : HasDerivWithinAt F dr (Ici (3/2)) (3/2) := (F_hasDeriv_right (3/2) (by norm_num)).Ici_of_Ioi
  have hL : slope 7 191 ≤ dl := by
    simpa only [leftDyadicSlope,show (1:ℕ)+6=7 by omega,show (3:ℕ)*2^6-1=191 by norm_num] using leftDyadic_le_limit 1 3 6 (by norm_num) (by norm_num)
  have hR : dr ≤ slope 7 192 := by
    simpa only [rightDyadicSlope,Nat.cast_ofNat,pow_one,show (1:ℕ)+6=7 by omega,show (3:ℕ)*2^6=192 by norm_num] using rightDyadic_limit_le 1 3 6 (by norm_num) (by norm_num)
  have hlt : dr < dl := hR.trans_lt (corner_slope_gap.trans_le hL)
  refine ⟨dl,dr,hl,hr,hlt,?_⟩
  intro hd
  have hld := UniqueDiffWithinAt.eq_deriv (Iic (3/2:ℝ)) ((uniqueDiffOn_Iic (3/2:ℝ)) (3/2) (by simp)) hl hd.hasDerivAt.hasDerivWithinAt
  have hrd := UniqueDiffWithinAt.eq_deriv (Ici (3/2:ℝ)) ((uniqueDiffOn_Ici (3/2:ℝ)) (3/2) (by simp)) hr hd.hasDerivAt.hasDerivWithinAt
  rw [hld,hrd] at hlt
  exact lt_irrefl _ hlt

end
end GD
