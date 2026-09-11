import GD.DerivativeRegularity

namespace GD
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 1200000

def leftDyadicSlope (k j l : ℕ) : ℝ := slope (k+l) (j*2^l-1)
def leftDyadicDerivative (k j : ℕ) : ℝ := limUnder atTop (leftDyadicSlope k j)

theorem leftDyadic_indices (k j l : ℕ) (hj : 2^k < j) (hj' : j ≤ 2^(k+1)) :
    2^(k+l) ≤ j*2^l-1 ∧ j*2^l-1 < 2^(k+l+1) := by
  have hp : 0 < (2:ℕ)^l := by positivity
  have h1 := Nat.mul_le_mul_right (2^l) (show 2^k+1 ≤ j by omega)
  have h2 := Nat.mul_le_mul_right (2^l) hj'
  rw [Nat.add_mul,one_mul] at h1
  rw [pow_succ] at h2
  rw [pow_add,show k+l+1=k+1+l by omega,pow_add,pow_succ]
  omega

theorem leftDyadic_children (k j l : ℕ) (hj : 2^k < j) (hj' : j ≤ 2^(k+1)) :
    leftDyadicSlope k j (l+1)=w1 (R (j*2^l-1))*leftDyadicSlope k j l := by
  have hi := leftDyadic_indices k j l hj hj'
  have hp : 1 ≤ (2:ℕ)^(k+l) := Nat.one_le_pow _ _ (by norm_num)
  have hn : 1 ≤ j*2^l-1 := hp.trans hi.1
  have he : j*2^(l+1)-1=2*(j*2^l-1)+1 := by
    rw [pow_succ]
    have hh : j*(2^l*2)=2*(j*2^l) := by ring
    rw [hh]
    omega
  unfold leftDyadicSlope
  rw [show k+(l+1)=k+l+1 by omega,he]
  exact (slope_children (k+l) (j*2^l-1) hn).2

theorem leftDyadic_monotone (k j : ℕ) (hj : 2^k < j) (hj' : j ≤ 2^(k+1)) :
    Monotone (leftDyadicSlope k j) := by
  apply monotone_nat_of_le_succ
  intro l
  have hi := leftDyadic_indices k j l hj hj'
  have hn : 1 ≤ j*2^l-1 := (Nat.one_le_pow (k+l) 2 (by norm_num)).trans hi.1
  have hw := (weights_bounds (R (j*2^l-1)) (R_gt_one _ hn).le).2.2.1
  rw [leftDyadic_children k j l hj hj']
  exact le_mul_of_one_le_left (slope_pos (k+l) (j*2^l-1)).le hw

theorem leftDyadic_tendsto (k j : ℕ) (hj : 2^k < j) (hj' : j ≤ 2^(k+1)) :
    Tendsto (leftDyadicSlope k j) atTop (𝓝 (leftDyadicDerivative k j)) := by
  have hb : BddAbove (range (leftDyadicSlope k j)) := by
    refine ⟨cplus,?_⟩
    rintro z ⟨l,rfl⟩
    have hi := leftDyadic_indices k j l hj hj'
    exact (slope_uniform_bounds (k+l) _ hi.1 hi.2).2
  apply tendsto_nhds_limUnder
  exact ⟨⨆ l, leftDyadicSlope k j l,tendsto_atTop_ciSup (leftDyadic_monotone k j hj hj') hb⟩

theorem leftDyadic_le_limit (k j l : ℕ) (hj : 2^k < j) (hj' : j ≤ 2^(k+1)) :
    leftDyadicSlope k j l ≤ leftDyadicDerivative k j := by
  apply ge_of_tendsto (leftDyadic_tendsto k j hj hj')
  filter_upwards [eventually_ge_atTop l] with n hn
  exact leftDyadic_monotone k j hj hj' hn

theorem leftDyadic_endpoint (k j l : ℕ) (hj : 2^k < j) :
    (((j*2^l-1+1:ℕ):ℝ)/(2:ℝ)^(k+l))=(j:ℝ)/(2:ℝ)^k := by
  have hp : 0 < j*2^l := mul_pos (lt_of_le_of_lt (Nat.zero_le _) hj) (show 0 < (2:ℕ)^l by positivity)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ j*2^l),Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add]
  field_simp <;> ring

theorem F_hasDeriv_left_dyadic (k j : ℕ) (hj : 2^k < j) (hj' : j < 2^(k+1)) :
    HasDerivWithinAt F (leftDyadicDerivative k j) (Iio ((j:ℝ)/(2:ℝ)^k)) ((j:ℝ)/(2:ℝ)^k) := by
  let x : ℝ := (j:ℝ)/(2:ℝ)^k
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp : x ∉ Iio x)]
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have ht : Tendsto (fun l : ℕ => slopeTail (k+l)) atTop (𝓝 0) :=
    slopeTail_tendsto.comp (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat k)
  have he := ((leftDyadic_tendsto k j hj hj'.le).sub_const (leftDyadicDerivative k j)).abs
  simp only [sub_self,abs_zero] at he
  have hsum := ht.add he
  simp only [zero_add] at hsum
  obtain ⟨l,hl⟩ := (hsum.eventually (gt_mem_nhds heps)).exists
  let n := j*2^l-1
  have hn := leftDyadic_indices k j l hj hj'.le
  have hright : ((n+1:ℕ):ℝ)/(2:ℝ)^(k+l)=x := leftDyadic_endpoint k j l hj
  have hleft : (n:ℝ)/(2:ℝ)^(k+l) < x := by
    rw [← hright]
    apply div_lt_div_of_pos_right _ (by positivity)
    exact_mod_cast (show n < n+1 by omega)
  have hmem : ∀ᶠ y in 𝓝[Iio x] x, (n:ℝ)/(2:ℝ)^(k+l) < y := nhdsWithin_le_nhds (Ioi_mem_nhds hleft)
  filter_upwards [hmem,self_mem_nhdsWithin] with y hy hyx
  have hxcell : x ∈ Icc ((n:ℝ)/(2:ℝ)^(k+l)) (((n+1:ℕ):ℝ)/(2:ℝ)^(k+l)) := ⟨hleft.le,hright.symm.le⟩
  have hycell : y ∈ Icc ((n:ℝ)/(2:ℝ)^(k+l)) (((n+1:ℕ):ℝ)/(2:ℝ)^(k+l)) := ⟨hy.le,hyx.le.trans hright.symm.le⟩
  have hb := F_local_secant (k+l) n hn.1 hn.2 x y hxcell hycell hyx.ne
  have htri := abs_sub_le ((F y-F x)/(y-x)) (leftDyadicSlope k j l) (leftDyadicDerivative k j)
  change |(F y-F x)/(y-x)-leftDyadicSlope k j l| ≤ slopeTail (k+l) at hb
  rw [Real.dist_eq,slope_def_field]
  linarith

theorem theorem_C_1_regularity_part : Targets.theorem_C_1_regularity_part := by
  refine ⟨derivativeProfile,derivativeProfile_bounds,?_,?_⟩
  · exact fun x hx hnd => ⟨derivativeProfile_continuousAt_nondyadic x hx hnd,F_hasDeriv_nondyadic x hx hnd⟩
  · intro x hx hdy
    obtain ⟨k,j,rfl⟩ := hdy
    have hp : 0 < (2:ℝ)^k := by positivity
    have hj : 2^k < j := by
      have h := (lt_div_iff₀ hp).mp hx.1
      simp only [one_mul] at h
      exact_mod_cast h
    have hj' : j < 2^(k+1) := by
      have h := (div_lt_iff₀ hp).mp hx.2
      have he : (2:ℝ)*(2:ℝ)^k=(2:ℝ)^(k+1) := by ring
      rw [he] at h
      exact_mod_cast h
    exact ⟨leftDyadicDerivative k j,derivativeProfile _,(F_hasDeriv_left_dyadic k j hj hj').Iic_of_Iio,
      (F_hasDeriv_right _ hx).Ici_of_Ioi⟩

end
end GD
