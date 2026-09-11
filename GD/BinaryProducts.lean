import GD.SlopeLimit

namespace GD
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 1200000

def binaryIndex (ε : ℕ → Bool) : ℕ → ℕ
  | 0 => 1
  | k+1 => 2*binaryIndex ε k+if ε k then 1 else 0

def binaryRatio (ε : ℕ → Bool) : ℕ → ℝ
  | 0 => rho
  | k+1 => if ε k then T1 (binaryRatio ε k) else T0 (binaryRatio ε k)

def binaryWeight (ε : ℕ → Bool) (k : ℕ) : ℝ :=
  if ε k then w1 (binaryRatio ε k) else w0 (binaryRatio ε k)

def binaryProduct (k : ℕ) (ε : ℕ → Bool) : ℝ :=
  (rho-1)*∏ i ∈ Finset.range k, binaryWeight ε i

def binaryProductLimit (ε : ℕ → Bool) : ℝ := limUnder atTop (fun k => binaryProduct k ε)

theorem binaryIndex_bounds (ε : ℕ → Bool) (k : ℕ) :
    2^k ≤ binaryIndex ε k ∧ binaryIndex ε k < 2^(k+1) := by
  induction k with
  | zero => norm_num [binaryIndex]
  | succ k ih =>
    rw [binaryIndex,pow_succ,show k+1+1=(k+1)+1 by omega,pow_succ]
    split <;> omega

theorem binaryRatio_eq_R (ε : ℕ → Bool) (k : ℕ) : binaryRatio ε k=R (binaryIndex ε k) := by
  induction k with
  | zero =>
    have hU2 : U 2=rho := by simpa using U_even 1
    simp [binaryRatio,binaryIndex,R,hU2]
  | succ k ih =>
    have hi := binaryIndex_bounds ε k
    have hn : 1 ≤ binaryIndex ε k := (Nat.one_le_pow k 2 (by norm_num)).trans hi.1
    have hs := lemma_5_3 (binaryIndex ε k) hn
    simp only [binaryRatio,binaryIndex,ih]
    cases he : ε k
    · simpa only [he,Bool.false_eq_true,↓reduceIte,add_zero] using hs.1.symm
    · simpa only [he,↓reduceIte] using hs.2.1.symm

theorem binaryProduct_eq_slope (ε : ℕ → Bool) (k : ℕ) : binaryProduct k ε=slope k (binaryIndex ε k) := by
  induction k with
  | zero =>
    have hU2 : U 2=rho := by simpa using U_even 1
    simp [binaryProduct,binaryIndex,slope,hU2]
  | succ k ih =>
    have hi := binaryIndex_bounds ε k
    have hn : 1 ≤ binaryIndex ε k := (Nat.one_le_pow k 2 (by norm_num)).trans hi.1
    have hs := slope_children k (binaryIndex ε k) hn
    have he : binaryProduct (k+1) ε=binaryWeight ε k*binaryProduct k ε := by
      unfold binaryProduct
      rw [Finset.prod_range_succ]
      ring
    rw [he,ih,binaryWeight,binaryRatio_eq_R,binaryIndex]
    cases hb : ε k
    · simpa only [hb,Bool.false_eq_true,↓reduceIte,add_zero] using hs.1.symm
    · simpa only [hb,↓reduceIte] using hs.2.symm

theorem binaryWeight_bounds (ε : ℕ → Bool) (k : ℕ) :
    0 < binaryWeight ε k ∧ |binaryWeight ε k-1| ≤ levelError k := by
  have hi := binaryIndex_bounds ε k
  have hn : 1 ≤ binaryIndex ε k := (Nat.one_le_pow k 2 (by norm_num)).trans hi.1
  have hw := grid_weight_bounds k _ hi.1 hi.2
  have hp := weights_bounds (R (binaryIndex ε k)) (R_gt_one _ hn).le
  rw [binaryWeight,binaryRatio_eq_R]
  cases hb : ε k
  · simp only [hb,Bool.false_eq_true,↓reduceIte]
    exact ⟨hp.1,abs_le.mpr ⟨by linarith [hw.1],by linarith [hw.2.1]⟩⟩
  · simp only [hb,↓reduceIte]
    exact ⟨by linarith [hp.2.2.1],abs_le.mpr ⟨by linarith [hw.2.2.1],by linarith [hw.2.2.2]⟩⟩

theorem binaryProduct_bounds (ε : ℕ → Bool) (k : ℕ) : cminus ≤ binaryProduct k ε ∧ binaryProduct k ε ≤ cplus := by
  rw [binaryProduct_eq_slope]
  exact slope_uniform_bounds k _ (binaryIndex_bounds ε k).1 (binaryIndex_bounds ε k).2

theorem binaryProduct_step (ε : ℕ → Bool) (k : ℕ) :
    |binaryProduct (k+1) ε-binaryProduct k ε| ≤ cplus*levelError k := by
  have hw := binaryWeight_bounds ε k
  have hp := binaryProduct_bounds ε k
  have hpos : 0 ≤ binaryProduct k ε := cminus_pos.le.trans hp.1
  have he : binaryProduct (k+1) ε-binaryProduct k ε=binaryProduct k ε*(binaryWeight ε k-1) := by
    unfold binaryProduct
    rw [Finset.prod_range_succ]
    ring
  rw [he,abs_mul,abs_of_nonneg hpos]
  exact mul_le_mul hp.2 hw.2 (abs_nonneg _) cplus_pos.le

theorem binaryProduct_corrected (ε : ℕ → Bool) :
    Antitone (fun k => binaryProduct k ε+slopeTail k) ∧
    Monotone (fun k => binaryProduct k ε-slopeTail k) := by
  constructor
  · apply antitone_nat_of_succ_le
    intro k
    have h := (abs_le.mp (binaryProduct_step ε k)).2
    rw [slopeTail_step k]
    linarith
  · apply monotone_nat_of_le_succ
    intro k
    have h := (abs_le.mp (binaryProduct_step ε k)).1
    rw [slopeTail_step k]
    linarith

theorem binaryProduct_tendsto (ε : ℕ → Bool) :
    Tendsto (fun k => binaryProduct k ε) atTop (𝓝 (binaryProductLimit ε)) := by
  let f := fun k => binaryProduct k ε+slopeTail k
  have hb : BddBelow (range f) := by
    refine ⟨cminus,?_⟩
    rintro y ⟨k,rfl⟩
    have h := (binaryProduct_bounds ε k).1
    have ht := slopeTail_pos k
    change cminus ≤ binaryProduct k ε+slopeTail k
    linarith
  have h := (tendsto_atTop_ciInf (binaryProduct_corrected ε).1 hb).sub slopeTail_tendsto
  apply tendsto_nhds_limUnder
  refine ⟨⨅ k, f k,?_⟩
  simpa only [f,sub_zero,add_sub_cancel_right] using h

theorem binaryProduct_error (ε : ℕ → Bool) (k : ℕ) :
    |binaryProduct k ε-binaryProductLimit ε| ≤ slopeTail k := by
  have hp := (binaryProduct_tendsto ε).add slopeTail_tendsto
  have hm := (binaryProduct_tendsto ε).sub slopeTail_tendsto
  simp only [add_zero,sub_zero] at hp hm
  have hu : binaryProductLimit ε ≤ binaryProduct k ε+slopeTail k := by
    apply le_of_tendsto hp
    filter_upwards [eventually_ge_atTop k] with l hl
    exact (binaryProduct_corrected ε).1 hl
  have hl : binaryProduct k ε-slopeTail k ≤ binaryProductLimit ε := by
    apply ge_of_tendsto hm
    filter_upwards [eventually_ge_atTop k] with l hl
    exact (binaryProduct_corrected ε).2 hl
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem binaryProduct_uniform : TendstoUniformly binaryProduct binaryProductLimit atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro eps heps
  filter_upwards [slopeTail_tendsto.eventually (gt_mem_nhds heps)] with k hk
  intro ε
  rw [Real.dist_eq,abs_sub_comm]
  exact (binaryProduct_error ε k).trans_lt hk

end
end GD
