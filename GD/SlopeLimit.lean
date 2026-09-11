import GD.GridCertificates

namespace GD
noncomputable section
open Set Filter
open scoped Topology

def slopeGrid (k : ℕ) (x : ℝ) : ℝ := slope k (cellIndex k x)
def slopeTail (k : ℕ) : ℝ := cplus/(2*rho*(2:ℝ)^k)
def derivativeProfile (x : ℝ) : ℝ := limUnder atTop (fun k => slopeGrid k x)

theorem cellIndex_children (k : ℕ) (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    cellIndex (k+1) x=2*cellIndex k x ∨ cellIndex (k+1) x=2*cellIndex k x+1 := by
  have h := gridHorizon_double x (by linarith [hx.1]) k
  have hg := gridHorizon_bounds x hx k
  have hp : 0 < (2:ℕ)^k := by positivity
  have he : (2:ℕ)^(k+1)=2*2^k := by ring
  have he' : (2:ℕ)^(k+1+1)=2*2^(k+1) := by ring
  change min (gridHorizon x (k+1)) (2^(k+1+1)-1)=2*min (gridHorizon x k) (2^(k+1)-1) ∨
    min (gridHorizon x (k+1)) (2^(k+1+1)-1)=2*min (gridHorizon x k) (2^(k+1)-1)+1
  omega

theorem slopeGrid_bounds (k : ℕ) (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    cminus ≤ slopeGrid k x ∧ slopeGrid k x ≤ cplus := by
  have h := cell_bounds k x hx
  exact slope_uniform_bounds k _ h.1 (by omega)

theorem slopeGrid_step (k : ℕ) (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    |slopeGrid (k+1) x-slopeGrid k x| ≤ cplus*levelError k := by
  let j := cellIndex k x
  have hj := cell_bounds k x hx
  have hj1 : 1 ≤ j := (Nat.one_le_pow k 2 (by norm_num)).trans hj.1
  have hw := grid_weight_bounds k j hj.1 (by omega)
  have hs := slope_children k j hj1
  have hsp := slope_pos k j
  have hbound := (slopeGrid_bounds k x hx).2
  change slope k j ≤ cplus at hbound
  have herr := (errorBudget_bounds k).2.2
  have helper : ∀ w : ℝ, 1-levelError k ≤ w → w ≤ 1+levelError k →
      |w*slope k j-slope k j| ≤ cplus*levelError k := by
    intro w hlo hhi
    have hl := mul_le_mul_of_nonneg_right hlo hsp.le
    have hh := mul_le_mul_of_nonneg_right hhi hsp.le
    have hb := mul_le_mul_of_nonneg_right hbound herr.le
    apply abs_le.mpr
    constructor <;> nlinarith
  rcases cellIndex_children k x hx with he | he
  · change |slope (k+1) (cellIndex (k+1) x)-slope k j| ≤ _
    rw [he,hs.1]
    exact helper _ hw.1 hw.2.1
  · change |slope (k+1) (cellIndex (k+1) x)-slope k j| ≤ _
    rw [he,hs.2]
    exact helper _ hw.2.2.1 hw.2.2.2

theorem slopeTail_pos (k : ℕ) : 0 < slopeTail k := by
  have := cplus_pos
  have := rho_pos
  unfold slopeTail
  positivity

theorem slopeTail_step (k : ℕ) : slopeTail k=cplus*levelError k+slopeTail (k+1) := by
  have := rho_pos
  unfold slopeTail levelError
  rw [pow_succ]
  field_simp
  <;> ring

theorem slopeTail_tendsto : Tendsto slopeTail atTop (𝓝 0) := by
  have h := dyadic_mesh_tendsto.const_mul (cplus/(2*rho))
  have he : (fun k : ℕ => (cplus/(2*rho))*(1/(2:ℝ)^k))=slopeTail := by
    funext k
    unfold slopeTail
    ring
  rw [he,mul_zero] at h
  exact h

theorem slopeGrid_corrected_antitone (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    Antitone (fun k => slopeGrid k x+slopeTail k) := by
  apply antitone_nat_of_succ_le
  intro k
  have h := (abs_le.mp (slopeGrid_step k x hx)).2
  rw [slopeTail_step k]
  linarith

theorem slopeGrid_corrected_monotone (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    Monotone (fun k => slopeGrid k x-slopeTail k) := by
  apply monotone_nat_of_le_succ
  intro k
  have h := (abs_le.mp (slopeGrid_step k x hx)).1
  rw [slopeTail_step k]
  linarith

theorem slopeGrid_tendsto (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    Tendsto (fun k => slopeGrid k x) atTop (𝓝 (derivativeProfile x)) := by
  let f := fun k => slopeGrid k x+slopeTail k
  have hb : BddBelow (range f) := by
    refine ⟨cminus,?_⟩
    rintro y ⟨k,rfl⟩
    have h := (slopeGrid_bounds k x hx).1
    have hh := slopeTail_pos k
    change cminus ≤ slopeGrid k x+slopeTail k
    linarith
  have h := (tendsto_atTop_ciInf (slopeGrid_corrected_antitone x hx) hb).sub slopeTail_tendsto
  apply tendsto_nhds_limUnder
  refine ⟨⨅ k, f k,?_⟩
  simpa only [sub_zero,add_sub_cancel_right,f] using h

theorem slopeGrid_error (k : ℕ) (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    |slopeGrid k x-derivativeProfile x| ≤ slopeTail k := by
  have hp := (slopeGrid_tendsto x hx).add slopeTail_tendsto
  have hm := (slopeGrid_tendsto x hx).sub slopeTail_tendsto
  simp only [add_zero,sub_zero] at hp hm
  have hu : derivativeProfile x ≤ slopeGrid k x+slopeTail k := by
    apply le_of_tendsto hp
    filter_upwards [eventually_ge_atTop k] with l hl
    exact slopeGrid_corrected_antitone x hx hl
  have hl : slopeGrid k x-slopeTail k ≤ derivativeProfile x := by
    apply ge_of_tendsto hm
    filter_upwards [eventually_ge_atTop k] with l hl
    exact slopeGrid_corrected_monotone x hx hl
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem slopeGrid_uniform : TendstoUniformlyOn slopeGrid derivativeProfile atTop (Icc (1:ℝ) 2) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  filter_upwards [slopeTail_tendsto.eventually (gt_mem_nhds heps)] with k hk
  intro x hx
  rw [Real.dist_eq,abs_sub_comm]
  exact (slopeGrid_error k x hx).trans_lt hk

theorem derivativeProfile_bounds (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    cminus ≤ derivativeProfile x ∧ derivativeProfile x ≤ cplus :=
  ⟨ge_of_tendsto' (slopeGrid_tendsto x hx) (fun k => (slopeGrid_bounds k x hx).1),
    le_of_tendsto' (slopeGrid_tendsto x hx) (fun k => (slopeGrid_bounds k x hx).2)⟩

end
end GD
