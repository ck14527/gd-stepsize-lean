import GD.BinaryLogTail
import GD.DyadicDerivatives

namespace GD
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 1200000

def pathLower (ε : ℕ → Bool) (k : ℕ) : ℝ := (binaryIndex ε k:ℝ)/(2:ℝ)^k
def pathUpper (ε : ℕ → Bool) (k : ℕ) : ℝ := ((binaryIndex ε k+1:ℕ):ℝ)/(2:ℝ)^k
def binaryPoint (ε : ℕ → Bool) : ℝ := limUnder atTop (pathLower ε)
def FollowsPath (ε : ℕ → Bool) (x : ℝ) : Prop := ∀ k, x ∈ Icc (pathLower ε k) (pathUpper ε k)

theorem path_bounds (ε : ℕ → Bool) (k : ℕ) : 1 ≤ pathLower ε k ∧ pathUpper ε k ≤ 2 := by
  have h := binaryIndex_bounds ε k
  have hp : 0 < (2:ℝ)^k := by positivity
  constructor
  · apply (le_div_iff₀ hp).mpr
    simpa using (show (2:ℝ)^k ≤ (binaryIndex ε k:ℝ) by exact_mod_cast h.1)
  · apply (div_le_iff₀ hp).mpr
    have hh : ((binaryIndex ε k+1:ℕ):ℝ) ≤ (2:ℝ)^(k+1) := by exact_mod_cast (show binaryIndex ε k+1 ≤ 2^(k+1) by omega)
    simpa [pow_succ,mul_comm] using hh

theorem path_width (ε : ℕ → Bool) (k : ℕ) : pathUpper ε k=pathLower ε k+1/(2:ℝ)^k := by
  unfold pathUpper pathLower
  push_cast
  ring

theorem path_nested (ε : ℕ → Bool) : Monotone (pathLower ε) ∧ Antitone (pathUpper ε) := by
  have hp : ∀ k : ℕ, 0 < (2:ℝ)^k := fun _ => by positivity
  constructor
  · apply monotone_nat_of_le_succ
    intro k
    unfold pathLower
    rw [binaryIndex,pow_succ]
    cases hb : ε k <;> simp only [hb,Bool.false_eq_true,↓reduceIte,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
    all_goals apply (div_le_div_iff₀ (hp k) (by positivity)).mpr <;> nlinarith [hp k]
  · apply antitone_nat_of_succ_le
    intro k
    unfold pathUpper
    rw [binaryIndex,pow_succ]
    cases hb : ε k <;> simp only [hb,Bool.false_eq_true,↓reduceIte,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
    all_goals apply (div_le_div_iff₀ (by positivity) (hp k)).mpr <;> nlinarith [hp k]

theorem pathLower_tendsto (ε : ℕ → Bool) : Tendsto (pathLower ε) atTop (𝓝 (binaryPoint ε)) := by
  have hb : BddAbove (range (pathLower ε)) := by
    refine ⟨2,?_⟩
    rintro y ⟨k,rfl⟩
    have h := (path_bounds ε k).2
    rw [path_width] at h
    have hp : 0 < 1/(2:ℝ)^k := by positivity
    linarith
  exact tendsto_nhds_limUnder ⟨_,tendsto_atTop_ciSup (path_nested ε).1 hb⟩

theorem pathUpper_tendsto (ε : ℕ → Bool) : Tendsto (pathUpper ε) atTop (𝓝 (binaryPoint ε)) := by
  have h := (pathLower_tendsto ε).add dyadic_mesh_tendsto
  simp only [add_zero] at h
  simpa only [← path_width] using h

theorem binaryPoint_follows (ε : ℕ → Bool) : FollowsPath ε (binaryPoint ε) := by
  intro k
  constructor
  · apply ge_of_tendsto (pathLower_tendsto ε)
    filter_upwards [eventually_ge_atTop k] with l hl
    exact (path_nested ε).1 hl
  · apply le_of_tendsto (pathUpper_tendsto ε)
    filter_upwards [eventually_ge_atTop k] with l hl
    exact (path_nested ε).2 hl

theorem binaryPoint_unique (ε : ℕ → Bool) (x : ℝ) (hx : FollowsPath ε x) : x=binaryPoint ε := by
  exact le_antisymm (ge_of_tendsto' (pathUpper_tendsto ε) (fun k => (hx k).2))
    (le_of_tendsto' (pathLower_tendsto ε) (fun k => (hx k).1))

theorem binaryPoint_mem (ε : ℕ → Bool) : binaryPoint ε ∈ Icc (1:ℝ) 2 := by
  have h := binaryPoint_follows ε 0
  simpa [pathLower,pathUpper,binaryIndex] using h

theorem binaryProduct_nondyadic (ε : ℕ → Bool) (x : ℝ) (hx : x ∈ Ioo (1:ℝ) 2)
    (hnd : ¬IsDyadic x) (hpath : FollowsPath ε x) : binaryProductLimit ε=derivativeProfile x := by
  have he : ∀ k, binaryProduct k ε=slopeGrid k x := by
    intro k
    have hj := binaryIndex_bounds ε k
    have hh := hpath k
    have hright : x < pathUpper ε k := by
      apply lt_of_le_of_ne hh.2
      intro h
      exact hnd ⟨k,binaryIndex ε k+1,h⟩
    rw [binaryProduct_eq_slope,slopeGrid,cellIndex_eq_of_mem k _ hj.1 hj.2 x ⟨hh.1,hright⟩]
  have hp := (binaryProduct_tendsto ε).congr' (Eventually.of_forall he)
  exact tendsto_nhds_unique hp (slopeGrid_tendsto x ⟨hx.1.le,hx.2.le⟩)

theorem binaryIndex_zero_tail (ε : ℕ → Bool) (K : ℕ) (hε : ∀ l, ε (K+l)=false) (l : ℕ) :
    binaryIndex ε (K+l)=binaryIndex ε K*2^l := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [show K+(l+1)=(K+l)+1 by omega,binaryIndex,hε,if_neg (by decide : false ≠ true),add_zero,ih,pow_succ]
    ring

theorem binaryIndex_one_tail (ε : ℕ → Bool) (K : ℕ) (hε : ∀ l, ε (K+l)=true) (l : ℕ) :
    binaryIndex ε (K+l)+1=(binaryIndex ε K+1)*2^l := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [show K+(l+1)=(K+l)+1 by omega,binaryIndex,hε,if_pos rfl,pow_succ]
    nlinarith

theorem binaryPoint_zero_tail (ε : ℕ → Bool) (K : ℕ) (hε : ∀ l, ε (K+l)=false) :
    binaryPoint ε=pathLower ε K := by
  have ht : Tendsto (fun l : ℕ => K+l) atTop atTop := by simpa only [Nat.add_comm] using tendsto_add_atTop_nat K
  have he : ∀ l, pathLower ε (K+l)=pathLower ε K := by
    intro l
    unfold pathLower
    rw [binaryIndex_zero_tail ε K hε l,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add]
    field_simp
    <;> ring
  exact tendsto_nhds_unique ((pathLower_tendsto ε).comp ht)
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun l => (he l).symm)))

theorem binaryPoint_one_tail (ε : ℕ → Bool) (K : ℕ) (hε : ∀ l, ε (K+l)=true) :
    binaryPoint ε=pathUpper ε K := by
  have ht : Tendsto (fun l : ℕ => K+l) atTop atTop := by simpa only [Nat.add_comm] using tendsto_add_atTop_nat K
  have he : ∀ l, pathUpper ε (K+l)=pathUpper ε K := by
    intro l
    unfold pathUpper
    rw [binaryIndex_one_tail ε K hε l,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add]
    field_simp
    <;> ring
  exact tendsto_nhds_unique ((pathUpper_tendsto ε).comp ht)
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun l => (he l).symm)))

theorem binaryProduct_zero_tail_derivative (ε : ℕ → Bool) (K : ℕ) (hε : ∀ l, ε (K+l)=false)
    (hx : binaryPoint ε ∈ Ioo (1:ℝ) 2) :
    HasDerivWithinAt F (binaryProductLimit ε) (Ici (binaryPoint ε)) (binaryPoint ε) := by
  have he : ∀ l, binaryProduct (K+l) ε=slopeGrid (K+l) (binaryPoint ε) := by
    intro l
    have htail : ∀ i, ε ((K+l)+i)=false := by intro i; simpa [Nat.add_assoc] using hε (l+i)
    have hp := binaryPoint_zero_tail ε (K+l) htail
    have hi := binaryIndex_bounds ε (K+l)
    have hwidth : pathLower ε (K+l) < pathUpper ε (K+l) := by
      rw [path_width]
      have : 0 < 1/(2:ℝ)^(K+l) := by positivity
      linarith
    rw [binaryProduct_eq_slope,slopeGrid,hp,pathLower,cellIndex_eq_of_mem (K+l) _ hi.1 hi.2 _ ⟨le_rfl,hwidth⟩]
  have ht : Tendsto (fun l : ℕ => K+l) atTop atTop := by simpa only [Nat.add_comm] using tendsto_add_atTop_nat K
  have hlim := ((binaryProduct_tendsto ε).comp ht).congr' (Eventually.of_forall he)
  have hEq := tendsto_nhds_unique hlim ((slopeGrid_tendsto _ ⟨hx.1.le,hx.2.le⟩).comp ht)
  rw [hEq]
  exact (F_hasDeriv_right _ hx).Ici_of_Ioi

theorem binaryProduct_one_tail_derivative (ε : ℕ → Bool) (K : ℕ) (hε : ∀ l, ε (K+l)=true)
    (hx : binaryPoint ε ∈ Ioo (1:ℝ) 2) :
    HasDerivWithinAt F (binaryProductLimit ε) (Iic (binaryPoint ε)) (binaryPoint ε) := by
  let j := binaryIndex ε K+1
  have hi := binaryIndex_bounds ε K
  have hj : 2^K < j := by dsimp only [j]; omega
  have hpoint : binaryPoint ε=(j:ℝ)/(2:ℝ)^K := binaryPoint_one_tail ε K hε
  have hj' : j < 2^(K+1) := by
    have h := hx.2
    rw [hpoint] at h
    have hh := (div_lt_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^K)).mp h
    have he : (2:ℝ)*(2:ℝ)^K=(2:ℝ)^(K+1) := by ring
    rw [he] at hh
    exact_mod_cast hh
  have he : ∀ l, binaryProduct (K+l) ε=leftDyadicSlope K j l := by
    intro l
    rw [binaryProduct_eq_slope,leftDyadicSlope]
    have hh := binaryIndex_one_tail ε K hε l
    congr 1
    change binaryIndex ε (K+l)+1=j*2^l at hh
    omega
  have ht : Tendsto (fun l : ℕ => K+l) atTop atTop := by simpa only [Nat.add_comm] using tendsto_add_atTop_nat K
  have hEq := tendsto_nhds_unique (((binaryProduct_tendsto ε).comp ht).congr' (Eventually.of_forall he))
    (leftDyadic_tendsto K j hj hj'.le)
  rw [hEq,hpoint]
  exact (F_hasDeriv_left_dyadic K j hj hj').Iic_of_Iio

end
end GD
