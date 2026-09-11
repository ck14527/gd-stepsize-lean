import GD.SlopeLimit

namespace GD
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 1200000

theorem cellIndex_eq_of_mem (k j : ℕ) (hj : 2^k ≤ j) (hj' : j < 2^(k+1))
    (x : ℝ) (hx : x ∈ Ico ((j:ℝ)/(2:ℝ)^k) (((j+1:ℕ):ℝ)/(2:ℝ)^k)) : cellIndex k x=j := by
  have hp : 0 < (2:ℝ)^k := by positivity
  have hx0 : 0 ≤ x := (div_nonneg (Nat.cast_nonneg j) hp.le).trans hx.1
  have hf : Nat.floor (x*(2:ℝ)^k)=j := by
    apply (Nat.floor_eq_iff (mul_nonneg hx0 hp.le)).mpr
    constructor
    · exact (div_le_iff₀ hp).mp hx.1
    · have hh := (lt_div_iff₀ hp).mp hx.2
      simpa only [Nat.cast_add,Nat.cast_one] using hh
  rw [cellIndex,hf,min_eq_left (by omega)]

theorem slopeGrid_level_error (k l : ℕ) (hkl : k ≤ l) (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    |slopeGrid l x-slopeGrid k x| ≤ slopeTail k := by
  have hu := slopeGrid_corrected_antitone x hx hkl
  have hl := slopeGrid_corrected_monotone x hx hkl
  dsimp only at hu hl
  have ht := slopeTail_pos l
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem descendant_slope_close (k j l n : ℕ) (hj : 2^k ≤ j) (hj' : j < 2^(k+1))
    (hn : j*2^l ≤ n) (hn' : n < (j+1)*2^l) :
    |slope (k+l) n-slope k j| ≤ slopeTail k := by
  have hp : 0 < (2:ℝ)^k := by positivity
  have hpl : 0 < (2:ℝ)^l := by positivity
  let z : ℝ := ((n:ℝ)+1/2)/(2:ℝ)^l
  let x : ℝ := z/(2:ℝ)^k
  have hz : (j:ℝ) < z ∧ z < ((j+1:ℕ):ℝ) := by
    have hnc : (j:ℝ)*(2:ℝ)^l ≤ (n:ℝ) := by exact_mod_cast hn
    have hn'c : (n:ℝ)+1 ≤ ((j+1:ℕ):ℝ)*(2:ℝ)^l := by exact_mod_cast (show n+1 ≤ (j+1)*2^l by omega)
    exact ⟨(lt_div_iff₀ hpl).mpr (by linarith),(div_lt_iff₀ hpl).mpr (by linarith)⟩
  have hxc : x ∈ Ico ((j:ℝ)/(2:ℝ)^k) (((j+1:ℕ):ℝ)/(2:ℝ)^k) :=
    ⟨(div_lt_div_of_pos_right hz.1 hp).le,div_lt_div_of_pos_right hz.2 hp⟩
  have hgridlo : (1:ℝ) ≤ (j:ℝ)/(2:ℝ)^k := by
    apply (le_div_iff₀ hp).mpr
    simpa using (show (2:ℝ)^k ≤ (j:ℝ) by exact_mod_cast hj)
  have hgridhi : ((j+1:ℕ):ℝ)/(2:ℝ)^k ≤ 2 := by
    apply (div_le_iff₀ hp).mpr
    have hh : ((j+1:ℕ):ℝ) ≤ (2:ℝ)^(k+1) := by exact_mod_cast (show j+1 ≤ 2^(k+1) by omega)
    simpa [pow_succ,mul_comm] using hh
  have hx : x ∈ Icc (1:ℝ) 2 := ⟨hgridlo.trans hxc.1,hxc.2.le.trans hgridhi⟩
  have hnlo : 2^(k+l) ≤ n := by rw [pow_add]; exact (Nat.mul_le_mul_right (2^l) hj).trans hn
  have hnhi : n < 2^(k+l+1) := by
    have hh := hn'.trans_le (Nat.mul_le_mul_right (2^l) (show j+1 ≤ 2^(k+1) by omega))
    simpa [← pow_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
  have hxl : x ∈ Ico ((n:ℝ)/(2:ℝ)^(k+l)) (((n+1:ℕ):ℝ)/(2:ℝ)^(k+l)) := by
    have he : x=((n:ℝ)+1/2)/(2:ℝ)^(k+l) := by dsimp only [x,z]; rw [pow_add]; ring
    rw [he]
    exact ⟨div_le_div_of_nonneg_right (by linarith) (by positivity),
      div_lt_div_of_pos_right (by push_cast; linarith) (by positivity)⟩
  have hh := slopeGrid_level_error k (k+l) (by omega) x hx
  simpa only [slopeGrid,cellIndex_eq_of_mem k j hj hj' x hxc,
    cellIndex_eq_of_mem (k+l) n hnlo hnhi x hxl] using hh

theorem local_grid_increment (k j l n : ℕ) (hj : 2^k ≤ j) (hj' : j < 2^(k+1))
    (hn : j*2^l ≤ n) (hn' : n < (j+1)*2^l) :
    |(U (n+1)/rho^(k+l)-U n/rho^(k+l))-slope k j/(2:ℝ)^(k+l)| ≤ slopeTail k/(2:ℝ)^(k+l) := by
  have h := descendant_slope_close k j l n hj hj' hn hn'
  have hrho := rho_pos
  have he : (U (n+1)/rho^(k+l)-U n/rho^(k+l))-slope k j/(2:ℝ)^(k+l)=
      (slope (k+l) n-slope k j)/(2:ℝ)^(k+l) := by
    unfold slope
    field_simp
    <;> ring
  rw [he,abs_div,abs_of_pos (by positivity : (0:ℝ) < (2:ℝ)^(k+l))]
  exact div_le_div_of_nonneg_right h (by positivity)

theorem local_grid_delta (k j l n d : ℕ) (hj : 2^k ≤ j) (hj' : j < 2^(k+1))
    (hn : j*2^l ≤ n) (hn' : n+d ≤ (j+1)*2^l) :
    |(U (n+d)/rho^(k+l)-U n/rho^(k+l))-slope k j*(d:ℝ)/(2:ℝ)^(k+l)| ≤ slopeTail k*(d:ℝ)/(2:ℝ)^(k+l) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hi := ih (by omega)
    have hs := local_grid_increment k j l (n+d) hj hj' (by omega) (by omega)
    have he : (U (n+(d+1))/rho^(k+l)-U n/rho^(k+l))-slope k j*((d+1:ℕ):ℝ)/(2:ℝ)^(k+l)=
        ((U ((n+d)+1)/rho^(k+l)-U (n+d)/rho^(k+l))-slope k j/(2:ℝ)^(k+l))+
        ((U (n+d)/rho^(k+l)-U n/rho^(k+l))-slope k j*(d:ℝ)/(2:ℝ)^(k+l)) := by
      rw [show n+(d+1)=n+d+1 by omega]
      push_cast
      ring
    rw [he]
    have hh := (abs_add_le _ _).trans (add_le_add hs hi)
    convert hh using 1 <;> push_cast <;> ring

theorem coarse_grid_horizon_bounds (k j l : ℕ) (x : ℝ)
    (hx : x ∈ Icc ((j:ℝ)/(2:ℝ)^k) (((j+1:ℕ):ℝ)/(2:ℝ)^k)) :
    j*2^l ≤ gridHorizon x (k+l) ∧ gridHorizon x (k+l) ≤ (j+1)*2^l := by
  have hx0 : 0 ≤ x := (div_nonneg (Nat.cast_nonneg _) (by positivity)).trans hx.1
  have hpow : 0 < (2:ℝ)^k := by positivity
  have hl := mul_le_mul_of_nonneg_right ((div_le_iff₀ hpow).mp hx.1) (show 0 ≤ (2:ℝ)^l by positivity)
  have hu := mul_le_mul_of_nonneg_right ((le_div_iff₀ hpow).mp hx.2) (show 0 ≤ (2:ℝ)^l by positivity)
  have he : x*(2:ℝ)^(k+l)=x*(2:ℝ)^k*(2:ℝ)^l := by rw [pow_add]; ring
  constructor
  · apply (Nat.le_floor_iff (mul_nonneg hx0 (by positivity))).mpr
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,he] using hl
  · have hf := Nat.floor_le (mul_nonneg hx0 (show 0 ≤ (2:ℝ)^(k+l) by positivity))
    have hh : (gridHorizon x (k+l):ℝ) ≤ ((j+1)*2^l:ℕ) := by
      change (Nat.floor (x*(2:ℝ)^(k+l)):ℝ) ≤ ((j+1)*2^l:ℕ)
      push_cast
      rw [he] at hf
      rw [he]
      simpa only [Nat.cast_add,Nat.cast_one] using hf.trans hu
    exact_mod_cast hh

theorem cell_interval_subset (k j : ℕ) (hj : 2^k ≤ j) (hj' : j < 2^(k+1)) :
    Icc ((j:ℝ)/(2:ℝ)^k) (((j+1:ℕ):ℝ)/(2:ℝ)^k) ⊆ Icc (1:ℝ) 2 := by
  intro x hx
  have hp : 0 < (2:ℝ)^k := by positivity
  constructor
  · apply le_trans _ hx.1
    apply (le_div_iff₀ hp).mpr
    simpa using (show (2:ℝ)^k ≤ (j:ℝ) by exact_mod_cast hj)
  · apply le_trans hx.2
    apply (div_le_iff₀ hp).mpr
    have h : ((j+1:ℕ):ℝ) ≤ (2:ℝ)^(k+1) := by exact_mod_cast (show j+1 ≤ 2^(k+1) by omega)
    simpa [pow_succ,mul_comm] using h

theorem F_local_affine_error (k j : ℕ) (hj : 2^k ≤ j) (hj' : j < 2^(k+1))
    (x y : ℝ)
    (hx : x ∈ Icc ((j:ℝ)/(2:ℝ)^k) (((j+1:ℕ):ℝ)/(2:ℝ)^k))
    (hy : y ∈ Icc ((j:ℝ)/(2:ℝ)^k) (((j+1:ℕ):ℝ)/(2:ℝ)^k)) (hxy : x ≤ y) :
    |F y-F x-slope k j*(y-x)| ≤ slopeTail k*(y-x) := by
  have hxg := cell_interval_subset k j hj hj' hx
  have hyg := cell_interval_subset k j hj hj' hy
  have ht : Tendsto (fun l : ℕ => k+l) atTop atTop := by simpa only [Nat.add_comm] using tendsto_add_atTop_nat k
  have hxl := (gridHorizon_tendsto x hxg).comp ht
  have hyl := (gridHorizon_tendsto y hyg).comp ht
  have hxF := (F_continuousOn x hxg).tendsto.comp hxl
  have hyF := (F_continuousOn y hyg).tendsto.comp hyl
  have hxR := hxl.mono_right nhdsWithin_le_nhds
  have hyR := hyl.mono_right nhdsWithin_le_nhds
  have hl := ((hyF.sub hxF).sub ((hyR.sub hxR).const_mul (slope k j))).abs
  have hr := (hyR.sub hxR).const_mul (slopeTail k)
  apply le_of_tendsto_of_tendsto' hl hr
  intro l
  let n := gridHorizon x (k+l)
  let m := gridHorizon y (k+l)
  have hn := coarse_grid_horizon_bounds k j l x hx
  have hm := coarse_grid_horizon_bounds k j l y hy
  have hnm : n ≤ m := Nat.floor_mono (mul_le_mul_of_nonneg_right hxy (by positivity))
  have h := local_grid_delta k j l n (m-n) hj hj' hn.1 (by omega)
  have hnx := gridHorizon_bounds x hxg (k+l)
  have hmy := gridHorizon_bounds y hyg (k+l)
  change |F ((m:ℝ)/(2:ℝ)^(k+l))-F ((n:ℝ)/(2:ℝ)^(k+l))-
    slope k j*((m:ℝ)/(2:ℝ)^(k+l)-(n:ℝ)/(2:ℝ)^(k+l))| ≤
    slopeTail k*((m:ℝ)/(2:ℝ)^(k+l)-(n:ℝ)/(2:ℝ)^(k+l))
  rw [F_grid (k+l) m hmy.1 hmy.2,F_grid (k+l) n hnx.1 hnx.2]
  rw [Nat.add_sub_of_le hnm,Nat.cast_sub hnm] at h
  convert h using 1 <;> ring

theorem F_local_affine_abs (k j : ℕ) (hj : 2^k ≤ j) (hj' : j < 2^(k+1))
    (x y : ℝ)
    (hx : x ∈ Icc ((j:ℝ)/(2:ℝ)^k) (((j+1:ℕ):ℝ)/(2:ℝ)^k))
    (hy : y ∈ Icc ((j:ℝ)/(2:ℝ)^k) (((j+1:ℕ):ℝ)/(2:ℝ)^k)) :
    |F y-F x-slope k j*(y-x)| ≤ slopeTail k*|y-x| := by
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact F_local_affine_error k j hj hj' x y hx hy hxy
  · have he : F y-F x-slope k j*(y-x)=-(F x-F y-slope k j*(x-y)) := by ring
    rw [he,abs_neg,abs_of_nonpos (sub_nonpos.mpr hyx),neg_sub]
    exact F_local_affine_error k j hj hj' y x hy hx hyx

theorem F_local_secant (k j : ℕ) (hj : 2^k ≤ j) (hj' : j < 2^(k+1))
    (x y : ℝ)
    (hx : x ∈ Icc ((j:ℝ)/(2:ℝ)^k) (((j+1:ℕ):ℝ)/(2:ℝ)^k))
    (hy : y ∈ Icc ((j:ℝ)/(2:ℝ)^k) (((j+1:ℕ):ℝ)/(2:ℝ)^k)) (hne : y ≠ x) :
    |(F y-F x)/(y-x)-slope k j| ≤ slopeTail k := by
  have h := F_local_affine_abs k j hj hj' x y hx hy
  have he : (F y-F x)/(y-x)-slope k j=(F y-F x-slope k j*(y-x))/(y-x) := by
    field_simp [sub_ne_zero.mpr hne] <;> ring
  rw [he,abs_div]
  exact (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hne))).mpr h

end
end GD
