import GD.Subdivision
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue

namespace GD
noncomputable section
open Set Filter
open scoped Topology

theorem cminus_pos : 0 < cminus := by
  have hrho := rho_pos
  have hh : 1/(2*rho) < 1 := (div_lt_one (by positivity)).mpr (by linarith [rho_gt_two])
  exact mul_pos (by linarith [rho_gt_two]) (sub_pos.mpr hh)

theorem cplus_pos : 0 < cplus :=
  mul_pos (by linarith [rho_gt_two]) (Real.exp_pos _)

theorem grid_increment_bounds (k j : ℕ) (hlo : 2^k ≤ j) (hhi : j < 2^(k+1)) :
    cminus/(2:ℝ)^k ≤ U (j+1)/rho^k-U j/rho^k ∧
    U (j+1)/rho^k-U j/rho^k ≤ cplus/(2:ℝ)^k := by
  have hrho := rho_pos
  have h := slope_uniform_bounds k j hlo hhi
  have he : U (j+1)/rho^k-U j/rho^k=slope k j/(2:ℝ)^k := by
    unfold slope
    field_simp
    <;> ring
  rw [he]
  exact ⟨div_le_div_of_nonneg_right h.1 (by positivity),div_le_div_of_nonneg_right h.2 (by positivity)⟩

theorem grid_delta_bounds (k j d : ℕ) (hlo : 2^k ≤ j) (hhi : j+d ≤ 2^(k+1)) :
    cminus*(d:ℝ)/(2:ℝ)^k ≤ U (j+d)/rho^k-U j/rho^k ∧
    U (j+d)/rho^k-U j/rho^k ≤ cplus*(d:ℝ)/(2:ℝ)^k := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hprev := ih (by omega)
    have hinc := grid_increment_bounds k (j+d) (by omega) (by omega)
    have he : U (j+(d+1))/rho^k-U j/rho^k=
        (U ((j+d)+1)/rho^k-U (j+d)/rho^k)+(U (j+d)/rho^k-U j/rho^k) := by
      rw [show j+(d+1)=j+d+1 by omega]
      ring
    constructor
    · calc cminus*((d+1:ℕ):ℝ)/(2:ℝ)^k = cminus/(2:ℝ)^k+cminus*(d:ℝ)/(2:ℝ)^k := by push_cast; ring
           _ ≤ _ := add_le_add hinc.1 hprev.1
           _ = _ := he.symm
    · calc U (j+(d+1))/rho^k-U j/rho^k = _ := he
           _ ≤ _ := add_le_add hinc.2 hprev.2
           _ = cplus*((d+1:ℕ):ℝ)/(2:ℝ)^k := by push_cast; ring

theorem grid_segment_bounds (k j n : ℕ) (hlo : 2^k ≤ j) (hjn : j ≤ n) (hhi : n ≤ 2^(k+1)) :
    cminus*((n:ℝ)-(j:ℝ))/(2:ℝ)^k ≤ U n/rho^k-U j/rho^k ∧
    U n/rho^k-U j/rho^k ≤ cplus*((n:ℝ)-(j:ℝ))/(2:ℝ)^k := by
  have h := grid_delta_bounds k j (n-j) hlo (by omega)
  simpa [Nat.add_sub_of_le hjn,Nat.cast_sub hjn] using h

def cellIndex (k : ℕ) (x : ℝ) : ℕ := min (Nat.floor (x*(2:ℝ)^k)) (2^(k+1)-1)

theorem cellIndex_mono (k : ℕ) : Monotone (cellIndex k) := by
  intro x y hxy
  exact min_le_min (Nat.floor_mono (mul_le_mul_of_nonneg_right hxy (by positivity))) le_rfl

theorem cell_bounds (k : ℕ) (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    2^k ≤ cellIndex k x ∧ cellIndex k x+1 ≤ 2^(k+1) ∧
    (cellIndex k x:ℝ)/(2:ℝ)^k ≤ x ∧ x ≤ ((cellIndex k x+1:ℕ):ℝ)/(2:ℝ)^k := by
  have hd : 0 < (2:ℝ)^k := by positivity
  have hp : 0 < (2:ℕ)^k := by positivity
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have he : (2:ℕ)^(k+1)=2*2^k := by rw [pow_succ]; ring
  have hflo : 2^k ≤ Nat.floor (x*(2:ℝ)^k) := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ x*(2:ℝ)^k)).mpr
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    nlinarith [hx.1]
  have hcap : 2^k ≤ 2^(k+1)-1 := by omega
  have hil : 2^k ≤ cellIndex k x := le_min hflo hcap
  have hiu : cellIndex k x ≤ 2^(k+1)-1 := min_le_right _ _
  refine ⟨hil,by omega,?_,?_⟩
  · apply (div_le_iff₀ hd).mpr
    have hif : cellIndex k x ≤ Nat.floor (x*(2:ℝ)^k) := min_le_left _ _
    have hic : (cellIndex k x:ℝ) ≤ (Nat.floor (x*(2:ℝ)^k):ℝ) := by exact_mod_cast hif
    exact hic.trans (Nat.floor_le (by positivity))
  · apply (le_div_iff₀ hd).mpr
    by_cases hle : Nat.floor (x*(2:ℝ)^k) ≤ 2^(k+1)-1
    · rw [cellIndex,min_eq_left hle]
      simpa only [Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one (x*(2:ℝ)^k)).le
    · have hge : 2^(k+1)-1 ≤ Nat.floor (x*(2:ℝ)^k) := by omega
      rw [cellIndex,min_eq_right hge,show 2^(k+1)-1+1=2^(k+1) by omega]
      simp only [Nat.cast_pow,Nat.cast_ofNat,pow_succ,Nat.cast_mul]
      norm_num only [Nat.cast_ofNat,Nat.cast_pow]
      nlinarith [hx.2]

theorem F_cell_bounds (k : ℕ) (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    U (cellIndex k x)/rho^k ≤ F x ∧ F x ≤ U (cellIndex k x+1)/rho^k := by
  obtain ⟨hlo,hhi,hxlo,hxhi⟩ := cell_bounds k x hx
  let S : Set ℝ := {y | ∃ l j : ℕ,
    2^l ≤ j ∧ j ≤ 2^(l+1) ∧ (j:ℝ)/(2:ℝ)^l ≤ x ∧ y=U j/rho^l}
  have hm : U (cellIndex k x)/rho^k ∈ S := ⟨k,cellIndex k x,hlo,by omega,hxlo,rfl⟩
  have hu : ∀ y ∈ S, y ≤ U (cellIndex k x+1)/rho^k := by
    rintro y ⟨l,j,_,_,he,rfl⟩
    exact dyadic_grid_order j l (cellIndex k x+1) k (he.trans hxhi)
  change U (cellIndex k x)/rho^k ≤ sSup S ∧ sSup S ≤ U (cellIndex k x+1)/rho^k
  exact ⟨le_csSup ⟨_,hu⟩ hm,csSup_le ⟨_,hm⟩ hu⟩

theorem F_bounds_with_mesh (k : ℕ) (x y : ℝ)
    (hx : x ∈ Icc (1:ℝ) 2) (hy : y ∈ Icc (1:ℝ) 2) (hxy : x ≤ y) :
    cminus*(y-x)-(cminus+cplus)/(2:ℝ)^k ≤ F y-F x ∧
    F y-F x ≤ cplus*(y-x+2/(2:ℝ)^k) := by
  let i := cellIndex k x
  let j := cellIndex k y
  have hix := cell_bounds k x hx
  have hjy := cell_bounds k y hy
  have hiFx := F_cell_bounds k x hx
  have hjFy := F_cell_bounds k y hy
  have hij : i ≤ j := cellIndex_mono k hxy
  have hgrid := grid_segment_bounds k i j hix.1 hij (by omega)
  have hgrid' := grid_segment_bounds k i (j+1) hix.1 (by omega) hjy.2.1
  have hinc := grid_increment_bounds k i hix.1 (by omega)
  have hd : 0 < (2:ℝ)^k := by positivity
  have hi_next : ((i+1:ℕ):ℝ)/(2:ℝ)^k=(i:ℝ)/(2:ℝ)^k+1/(2:ℝ)^k := by push_cast; ring
  have hj_next : ((j+1:ℕ):ℝ)/(2:ℝ)^k=(j:ℝ)/(2:ℝ)^k+1/(2:ℝ)^k := by push_cast; ring
  have hgeomlo : y-x-1/(2:ℝ)^k ≤ ((j:ℝ)-(i:ℝ))/(2:ℝ)^k := by
    have hyhi : y ≤ (j:ℝ)/(2:ℝ)^k+1/(2:ℝ)^k := by
      simpa only [Nat.cast_add,Nat.cast_one,add_div] using hjy.2.2.2
    have hxlo : (i:ℝ)/(2:ℝ)^k ≤ x := hix.2.2.1
    rw [sub_div]
    linarith
  have hgeomhi : (((j+1:ℕ):ℝ)-(i:ℝ))/(2:ℝ)^k ≤ y-x+2/(2:ℝ)^k := by
    have hxhi : x ≤ (i:ℝ)/(2:ℝ)^k+1/(2:ℝ)^k := by
      simpa only [Nat.cast_add,Nat.cast_one,add_div] using hix.2.2.2
    have hylo : (j:ℝ)/(2:ℝ)^k ≤ y := hjy.2.2.1
    rw [sub_div,hj_next]
    have htwo : 2/(2:ℝ)^k=1/(2:ℝ)^k+1/(2:ℝ)^k := by ring
    linarith
  have hmullo := mul_le_mul_of_nonneg_left hgeomlo cminus_pos.le
  have hmulhi := mul_le_mul_of_nonneg_left hgeomhi cplus_pos.le
  constructor
  · calc cminus*(y-x)-(cminus+cplus)/(2:ℝ)^k =
            cminus*(y-x-1/(2:ℝ)^k)-cplus/(2:ℝ)^k := by ring
         _ ≤ cminus*(((j:ℝ)-(i:ℝ))/(2:ℝ)^k)-cplus/(2:ℝ)^k := sub_le_sub_right hmullo _
         _ ≤ (U j/rho^k-U i/rho^k)-(U (i+1)/rho^k-U i/rho^k) := by
           simpa [mul_div_assoc] using sub_le_sub hgrid.1 hinc.2
         _ ≤ F y-F x := by dsimp [i,j] at *; linarith [hiFx.2,hjFy.1]
  · calc F y-F x ≤ U (j+1)/rho^k-U i/rho^k := by dsimp [i,j] at *; linarith [hiFx.1,hjFy.2]
         _ ≤ cplus*(((j+1:ℕ):ℝ)-(i:ℝ))/(2:ℝ)^k := hgrid'.2
         _ ≤ cplus*(y-x+2/(2:ℝ)^k) := by simpa [mul_div_assoc] using hmulhi

/-- Both exact constants in (26), for the actual supremum-defined F. -/
theorem F_bilipschitz_bounds (x y : ℝ)
    (hx : x ∈ Icc (1:ℝ) 2) (hy : y ∈ Icc (1:ℝ) 2) (hxy : x ≤ y) :
    cminus*(y-x) ≤ F y-F x ∧ F y-F x ≤ cplus*(y-x) := by
  have hinv : Tendsto (fun k : ℕ => ((2:ℝ)^k)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2))
  have hlo : Tendsto (fun k => cminus*(y-x)-(cminus+cplus)/(2:ℝ)^k)
      atTop (𝓝 (cminus*(y-x))) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x:=cminus*(y-x))).sub (hinv.const_mul (cminus+cplus))
  have hhi : Tendsto (fun k => cplus*(y-x+2/(2:ℝ)^k))
      atTop (𝓝 (cplus*(y-x))) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_const_nhds (x:=y-x)).add (hinv.const_mul 2)).const_mul cplus
  exact ⟨le_of_tendsto_of_tendsto' hlo tendsto_const_nhds (fun k => (F_bounds_with_mesh k x y hx hy hxy).1),
    le_of_tendsto_of_tendsto' tendsto_const_nhds hhi (fun k => (F_bounds_with_mesh k x y hx hy hxy).2)⟩

theorem F_strictMonoOn : StrictMonoOn F (Icc (1:ℝ) 2) := by
  intro x hx y hy hxy
  have h := (F_bilipschitz_bounds x y hx hy hxy.le).1
  have hp := mul_pos cminus_pos (sub_pos.mpr hxy)
  linarith

theorem F_abs_bound (x y : ℝ) (hx : x ∈ Icc (1:ℝ) 2) (hy : y ∈ Icc (1:ℝ) 2) :
    |F x-F y| ≤ cplus*|x-y| := by
  rcases le_total x y with hxy | hyx
  · have h := F_bilipschitz_bounds x y hx hy hxy
    have hF : F x ≤ F y := by nlinarith [mul_nonneg cminus_pos.le (sub_nonneg.mpr hxy)]
    rw [abs_of_nonpos (sub_nonpos.mpr hF),abs_of_nonpos (sub_nonpos.mpr hxy)]
    nlinarith
  · have h := F_bilipschitz_bounds y x hy hx hyx
    have hF : F y ≤ F x := by nlinarith [mul_nonneg cminus_pos.le (sub_nonneg.mpr hyx)]
    rw [abs_of_nonneg (sub_nonneg.mpr hF),abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact h.2

theorem F_lipschitzOn : LipschitzOnWith ⟨cplus,cplus_pos.le⟩ F (Icc (1:ℝ) 2) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simpa only [Real.dist_eq] using F_abs_bound x y hx hy

theorem F_continuousOn : ContinuousOn F (Icc (1:ℝ) 2) := F_lipschitzOn.continuousOn

theorem F_range : F '' Icc (1:ℝ) 2=Icc 1 rho := by
  apply le_antisymm
  · rintro z ⟨x,hx,rfl⟩
    have h1 := F_strictMonoOn.monotoneOn (show (1:ℝ) ∈ Icc 1 2 by norm_num) hx hx.1
    have h2 := F_strictMonoOn.monotoneOn hx (show (2:ℝ) ∈ Icc 1 2 by norm_num) hx.2
    simpa using And.intro h1 h2
  · simpa using intermediate_value_Icc (by norm_num : (1:ℝ) ≤ 2) F_continuousOn

theorem cell_point_mem (k : ℕ) (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    (cellIndex k x:ℝ)/(2:ℝ)^k ∈ Icc (1:ℝ) 2 := by
  have h := cell_bounds k x hx
  have hd : 0 < (2:ℝ)^k := by positivity
  constructor
  · apply (le_div_iff₀ hd).mpr
    have hh : (2:ℝ)^k ≤ (cellIndex k x:ℝ) := by exact_mod_cast h.1
    simpa using hh
  · exact h.2.2.1.trans hx.2

theorem cell_point_tendsto (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    Tendsto (fun k => (cellIndex k x:ℝ)/(2:ℝ)^k) atTop (𝓝[Icc (1:ℝ) 2] x) := by
  have hinv : Tendsto (fun k : ℕ => ((2:ℝ)^k)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2))
  have hgap : Tendsto (fun k => x-(cellIndex k x:ℝ)/(2:ℝ)^k) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun k => sub_nonneg.mpr (cell_bounds k x hx).2.2.1)
      (g:=fun k => ((2:ℝ)^k)⁻¹) _ hinv
    intro k
    have h := (cell_bounds k x hx).2.2.2
    simp only [Nat.cast_add,Nat.cast_one,add_div,one_div] at h
    linarith
  have hl := (tendsto_const_nhds (x:=x)).sub hgap
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨by simpa using hl,Filter.Eventually.of_forall (fun k => cell_point_mem k x hx)⟩

theorem F_unique (G : ℝ → ℝ) (hG : ContinuousOn G (Icc (1:ℝ) 2))
    (hm : InterpolationMatches G) : EqOn G F (Icc (1:ℝ) 2) := by
  intro x hx
  have hGl := (hG x hx).tendsto.comp (cell_point_tendsto x hx)
  have hFl := (F_continuousOn x hx).tendsto.comp (cell_point_tendsto x hx)
  have he : ∀ k, G ((cellIndex k x:ℝ)/(2:ℝ)^k)=F ((cellIndex k x:ℝ)/(2:ℝ)^k) := by
    intro k
    have h := cell_bounds k x hx
    rw [hm k _ h.1 (by omega),F_grid k _ h.1 (by omega)]
  exact tendsto_nhds_unique (hGl.congr' (Filter.Eventually.of_forall he)) hFl

theorem F_midpoint (k j : ℕ) (hlo : 2^k ≤ j) (hhi : j < 2^(k+1)) :
    F (((j:ℝ)+1/2)/(2:ℝ)^k)=
      K (F ((j:ℝ)/(2:ℝ)^k)) (F (((j:ℝ)+1)/(2:ℝ)^k))/rho := by
  have hrho := rho_pos
  have he : 2^(k+1)=2*(2:ℕ)^k := by rw [pow_succ]; ring
  have he2 : 2^(k+1+1)=2*(2:ℕ)^(k+1) := by rw [pow_succ]; ring
  have hx : ((j:ℝ)+1/2)/(2:ℝ)^k=((2*j+1:ℕ):ℝ)/(2:ℝ)^(k+1) := by
    push_cast
    rw [pow_succ]
    field_simp
    <;> ring
  have hj1 : (j:ℝ)+1=((j+1:ℕ):ℝ) := by push_cast; rfl
  rw [hx,F_grid (k+1) (2*j+1) (by omega) (by omega),F_grid k j hlo hhi.le,hj1,
    F_grid k (j+1) (by omega) (by omega),U_odd]
  have hk := K_hom (show 0 ≤ 1/rho^k by positivity) (U_nonneg j) (U_nonneg (j+1))
  simp only [one_div,← div_eq_inv_mul] at hk
  rw [hk,pow_succ]
  ring

/-- The full statement of Theorem 5.4, including exact constants and uniqueness. -/
theorem theorem_5_4 : Targets.theorem_5_4 := by
  refine ⟨F_interpolation_matches,F_one,F_two,F_continuousOn,F_range,?_,F_unique,F_midpoint⟩
  intro x y hx hxy hy
  exact F_bilipschitz_bounds x y ⟨hx,by linarith⟩ ⟨by linarith,hy⟩ hxy.le

end
end GD
