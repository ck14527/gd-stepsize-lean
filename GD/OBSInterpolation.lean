import GD.OBSPhaseTheorem
import Mathlib.Topology.LocallyFinite

namespace GD
noncomputable section
open Set Filter
open scoped Topology

/-- The logarithmic nodes in §6.2, indexed by the horizon. -/
def obsNode (k j : ℕ) : ℝ := Real.logb 2 ((j:ℝ)/(2:ℝ)^k)

def obsSegment (k j : ℕ) (t : ℝ) : ℝ :=
  C j+(t-obsNode k j)/(obsNode k (j+1)-obsNode k j)*(C (j+1)-C j)

def psiInterp (k : ℕ) (t : ℝ) : ℝ :=
  obsSegment k (cellIndex k ((2:ℝ)^t)) t

theorem obsNode_strictMono (k : ℕ) : StrictMonoOn (obsNode k) (Ici 1) := by
  intro i hi j hj hij
  have hi0 : 0 < (i:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hi)
  have hj0 : 0 < (j:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hj)
  apply (Real.logb_lt_logb_iff (by norm_num : (1:ℝ) < 2) (by positivity : (0:ℝ) < (i:ℝ)/(2:ℝ)^k) (by positivity : (0:ℝ) < (j:ℝ)/(2:ℝ)^k)).mpr
  exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by positivity)

theorem obsNode_mem (k j : ℕ) (hj : 2^k ≤ j) (hj' : j ≤ 2^(k+1)) :
    obsNode k j ∈ Icc (0:ℝ) 1 := by
  apply logb_two_mem
  constructor
  · apply (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^k)).mpr
    simpa using (show (2:ℝ)^k ≤ (j:ℝ) by exact_mod_cast hj)
  · apply (div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^k)).mpr
    have h : (j:ℝ) ≤ (2:ℝ)^(k+1) := by exact_mod_cast hj'
    simpa [pow_succ,mul_comm] using h

theorem obsNode_endpoints (k : ℕ) : obsNode k (2^k)=0 ∧ obsNode k (2^(k+1))=1 := by
  simp [obsNode,Nat.cast_pow,pow_succ,Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]

theorem obsNode_rpow (k j : ℕ) (hj : 1 ≤ j) :
    (2:ℝ)^(obsNode k j)=(j:ℝ)/(2:ℝ)^k := by
  apply Real.rpow_logb (by norm_num) (by norm_num)
  positivity

theorem obs_cell (k : ℕ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    let j := cellIndex k ((2:ℝ)^t)
    2^k ≤ j ∧ j+1 ≤ 2^(k+1) ∧ t ∈ Icc (obsNode k j) (obsNode k (j+1)) := by
  have h := cell_bounds k _ (two_rpow_mem t ht)
  have hi : 0 < (cellIndex k ((2:ℝ)^t):ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (show 0 < (2:ℕ)^k by positivity) h.1)
  refine ⟨h.1,h.2.1,?_,?_⟩
  · apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) (by positivity : (0:ℝ) < (cellIndex k ((2:ℝ)^t):ℝ)/(2:ℝ)^k)).mpr h.2.2.1
  · apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2) (by positivity : (0:ℝ) < ((cellIndex k ((2:ℝ)^t)+1:ℕ):ℝ)/(2:ℝ)^k)).mpr h.2.2.2

theorem obsSegment_left (k j : ℕ) : obsSegment k j (obsNode k j)=C j := by
  simp [obsSegment]

theorem obsSegment_right (k j : ℕ) (hj : 1 ≤ j) : obsSegment k j (obsNode k (j+1))=C (j+1) := by
  have hn := obsNode_strictMono k hj (by first | omega | (change 1 ≤ _; omega)) (by omega : j < j+1)
  simp [obsSegment,ne_of_gt (sub_pos.mpr hn)]

/-- The selected formula agrees with either adjacent formula at a shared node. -/
theorem psiInterp_on_cell (k j : ℕ) (hj : 2^k ≤ j) (hj' : j+1 ≤ 2^(k+1))
    (t : ℝ) (ht : t ∈ Icc (obsNode k j) (obsNode k (j+1))) :
    psiInterp k t=obsSegment k j t := by
  have hp : 1 ≤ (2:ℕ)^k := Nat.one_le_pow _ _ (by norm_num)
  have htu : t ∈ Icc (0:ℝ) 1 := ⟨(obsNode_mem k j hj (by first | omega | (change 1 ≤ _; omega))).1.trans ht.1,
    ht.2.trans (obsNode_mem k (j+1) (by first | omega | (change 1 ≤ _; omega)) hj').2⟩
  let i := cellIndex k ((2:ℝ)^t)
  have hi := obs_cell k t htu
  change 2^k ≤ i ∧ i+1 ≤ 2^(k+1) ∧ t ∈ Icc (obsNode k i) (obsNode k (i+1)) at hi
  change obsSegment k i t=obsSegment k j t
  rcases lt_trichotomy i j with hij | hij | hij
  · have hle : obsNode k (i+1) ≤ obsNode k j :=
      (obsNode_strictMono k).monotoneOn (by first | omega | (change 1 ≤ _; omega)) (by first | omega | (change 1 ≤ _; omega)) (by first | omega | (change 1 ≤ _; omega))
    have he : t=obsNode k (i+1) := le_antisymm hi.2.2.2 (hle.trans ht.1)
    have he' : t=obsNode k j := le_antisymm (hi.2.2.2.trans hle) ht.1
    have hij' : i+1=j := (obsNode_strictMono k).injOn (by first | omega | (change 1 ≤ _; omega)) (by first | omega | (change 1 ≤ _; omega)) (he.symm.trans he')
    rw [he,obsSegment_right k i (by first | omega | (change 1 ≤ _; omega))]
    rw [← he,he',obsSegment_left,hij']
  · subst j
    rfl
  · have hle : obsNode k (j+1) ≤ obsNode k i :=
      (obsNode_strictMono k).monotoneOn (by first | omega | (change 1 ≤ _; omega)) (by first | omega | (change 1 ≤ _; omega)) (by first | omega | (change 1 ≤ _; omega))
    have he : t=obsNode k (j+1) := le_antisymm ht.2 (hle.trans hi.2.2.1)
    have he' : t=obsNode k i := le_antisymm (ht.2.trans hle) hi.2.2.1
    have hij' : j+1=i := (obsNode_strictMono k).injOn (by first | omega | (change 1 ≤ _; omega)) (by first | omega | (change 1 ≤ _; omega)) (he.symm.trans he')
    rw [he',obsSegment_left]
    rw [← he',he,obsSegment_right k j (by first | omega | (change 1 ≤ _; omega)),hij']

theorem psiInterp_nodes (k j : ℕ) (hj : 2^k ≤ j) (hj' : j ≤ 2^(k+1)) :
    psiInterp k (obsNode k j)=C j := by
  by_cases h : j < 2^(k+1)
  · rw [psiInterp_on_cell k j hj (by first | omega | (change 1 ≤ _; omega)) _ ⟨le_rfl,
      ((obsNode_strictMono k).monotoneOn (by change 1 ≤ j; exact (Nat.one_le_pow k 2 (by norm_num)).trans hj) (by first | omega | (change 1 ≤ _; omega)) (by first | omega | (change 1 ≤ _; omega)))⟩,
      obsSegment_left]
  · have he : j=2^(k+1) := by omega
    have hp : 1 ≤ (2:ℕ)^k := Nat.one_le_pow _ _ (by norm_num)
    have hh : j-1+1=j := by omega
    have hlo : 2^k ≤ j-1 := by rw [he,pow_succ]; omega
    rw [psiInterp_on_cell k (j-1) hlo (by first | omega | (change 1 ≤ _; omega)) _]
    · simpa only [hh] using obsSegment_right k (j-1) (by omega)
    · rw [hh]
      exact ⟨(obsNode_strictMono k).monotoneOn (by first | omega | (change 1 ≤ _; omega)) (by first | omega | (change 1 ≤ _; omega)) (by first | omega | (change 1 ≤ _; omega)),le_rfl⟩

theorem psiInterp_continuousOn (k : ℕ) : ContinuousOn (psiInterp k) (Icc (0:ℝ) 1) := by
  let J := {j : ℕ // j ∈ Finset.Ico (2^k) (2^(k+1))}
  letI : Fintype J := Fintype.ofFinset (Finset.Ico (2^k) (2^(k+1))) (fun _ => Iff.rfl)
  let cells : J → Set ℝ := fun j => Icc (obsNode k j) (obsNode k (j+1))
  have hcov : Icc (0:ℝ) 1=⋃ j : J, cells j := by
    ext t
    constructor
    · intro ht
      have h := obs_cell k t ht
      exact mem_iUnion.mpr ⟨⟨cellIndex k ((2:ℝ)^t),Finset.mem_Ico.mpr ⟨h.1,by omega⟩⟩,h.2.2⟩
    · intro ht
      obtain ⟨j,hj⟩ := mem_iUnion.mp ht
      have hh := Finset.mem_Ico.mp j.property
      exact ⟨(obsNode_mem k j hh.1 hh.2.le).1.trans hj.1,
        hj.2.trans (obsNode_mem k (j+1) (by first | omega | (change 1 ≤ _; omega)) (by first | omega | (change 1 ≤ _; omega))).2⟩
  rw [hcov]
  apply (locallyFinite_of_finite cells).continuousOn_iUnion (fun _ => isClosed_Icc)
  intro j
  have hc : Continuous (obsSegment k j) := by unfold obsSegment; fun_prop
  apply hc.continuousOn.congr
  intro t ht
  have hh := Finset.mem_Ico.mp j.property
  exact psiInterp_on_cell k j hh.1 (by first | omega | (change 1 ≤ _; omega)) t ht

theorem psiInterp_uniform : TendstoUniformlyOn psiInterp Psi atTop (Icc (0:ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  obtain ⟨k0,hk0⟩ := Psi_OBSPhase.2 (eps/2) (by linarith)
  have herr := dyadic_mesh_tendsto.const_mul obsLip
  simp only [mul_zero] at herr
  filter_upwards [eventually_ge_atTop k0,herr.eventually (gt_mem_nhds (show (0:ℝ) < eps/2 by linarith))] with k hk he
  intro t ht
  let j := cellIndex k ((2:ℝ)^t)
  have hj := obs_cell k t ht
  change 2^k ≤ j ∧ j+1 ≤ 2^(k+1) ∧ t ∈ Icc (obsNode k j) (obsNode k (j+1)) at hj
  have hp : 1 ≤ (2:ℕ)^k := Nat.one_le_pow _ _ (by norm_num)
  have hd : 0 < obsNode k (j+1)-obsNode k j := sub_pos.mpr (obsNode_strictMono k (by first | omega | (change 1 ≤ _; omega)) (by first | omega | (change 1 ≤ _; omega)) (by first | omega | (change 1 ≤ _; omega)))
  let θ := (t-obsNode k j)/(obsNode k (j+1)-obsNode k j)
  have hθ : 0 ≤ θ ∧ θ ≤ 1 := ⟨div_nonneg (sub_nonneg.mpr hj.2.2.1) hd.le,
    (div_le_one hd).mpr (by linarith [hj.2.2.2])⟩
  have hcell := cell_bounds k _ (two_rpow_mem t ht)
  have endpoint_error : ∀ n : ℕ, (n=j ∨ n=j+1) → |C n-Psi t| < eps := by
    intro n hn
    have hnlo : 2^k ≤ n := by rcases hn with rfl | rfl <;> omega
    have hnhi : n ≤ 2^(k+1) := by rcases hn with rfl | rfl <;> omega
    have hg := hk0 k hk n hnlo hnhi
    rw [Psi_grid_phase k n hnlo hnhi] at hg
    have hnm : (n:ℝ)/(2:ℝ)^k ∈ Icc (1:ℝ) 2 := by
      rw [← obsNode_rpow k n (by first | omega | (change 1 ≤ _; omega))]
      exact two_rpow_mem _ (obsNode_mem k n hnlo hnhi)
    have hl := obsMantissa_lipschitz ((n:ℝ)/(2:ℝ)^k) ((2:ℝ)^t) hnm (two_rpow_mem t ht)
    have hd' : |(n:ℝ)/(2:ℝ)^k-(2:ℝ)^t| ≤ 1/(2:ℝ)^k := by
      rcases hn with rfl | rfl
      · rw [abs_of_nonpos (sub_nonpos.mpr hcell.2.2.1)]
        have hh := hcell.2.2.2
        push_cast at hh
        rw [add_div] at hh
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr hcell.2.2.2)]
        push_cast
        rw [add_div]
        have hh := hcell.2.2.1
        linarith
    rw [Psi_on_unit t ht]
    have hm := mul_le_mul_of_nonneg_left hd' obsLip_pos.le
    have htri := abs_sub_le (C n) (obsMantissa ((n:ℝ)/(2:ℝ)^k)) (obsMantissa ((2:ℝ)^t))
    nlinarith
  have hl := endpoint_error j (Or.inl rfl)
  have hr := endpoint_error (j+1) (Or.inr rfl)
  have hrepr : psiInterp k t-Psi t=(1-θ)*(C j-Psi t)+θ*(C (j+1)-Psi t) := by
    dsimp only [psiInterp,obsSegment,θ,j]
    ring
  rw [Real.dist_eq,abs_sub_comm,hrepr]
  calc
    _ ≤ |(1-θ)*(C j-Psi t)|+|θ*(C (j+1)-Psi t)| := abs_add_le _ _
    _ = (1-θ)*|C j-Psi t|+θ*|C (j+1)-Psi t| := by rw [abs_mul,abs_mul,abs_of_nonneg (by linarith : 0 ≤ 1-θ),abs_of_nonneg hθ.1]
    _ ≤ max |C j-Psi t| |C (j+1)-Psi t| := by
      have h1 := mul_le_mul_of_nonneg_left (le_max_left |C j-Psi t| |C (j+1)-Psi t|) (show 0 ≤ 1-θ by linarith)
      have h2 := mul_le_mul_of_nonneg_left (le_max_right |C j-Psi t| |C (j+1)-Psi t|) hθ.1
      nlinarith
    _ < eps := max_lt hl hr

theorem psiInterp_unique (k : ℕ) (g : ℝ → ℝ)
    (hg : ∀ j : ℕ, 2^k ≤ j → j+1 ≤ 2^(k+1) →
      ∀ t ∈ Icc (obsNode k j) (obsNode k (j+1)), g t=obsSegment k j t) :
    EqOn g (psiInterp k) (Icc (0:ℝ) 1) := by
  intro t ht
  have h := obs_cell k t ht
  exact hg _ h.1 h.2.1 t h.2.2

theorem Psi_unique_uniform (g : ℝ → ℝ) (hg : PeriodicLipschitzPositive g)
    (hu : TendstoUniformlyOn psiInterp g atTop (Icc (0:ℝ) 1)) : g=Psi := by
  funext t
  rw [← periodic_fract g hg.2.1 t,← periodic_fract Psi Psi_periodic t]
  have ht : Int.fract t ∈ Icc (0:ℝ) 1 := ⟨Int.fract_nonneg t,(Int.fract_lt_one t).le⟩
  exact tendsto_nhds_unique (hu.tendsto_at ht) (psiInterp_uniform.tendsto_at ht)

namespace Targets
/-- The complete scalar phase statement, with the paper's actual logarithmic
piecewise-affine interpolants, their uniqueness, and the stated Lipschitz constant.
The external smooth-convex GD certificate interface is audited separately. -/
def theorem_6_3 : Prop :=
  theorem_6_3_block_version ∧
  (∀ k, ContinuousOn (psiInterp k) (Icc (0:ℝ) 1)) ∧
  (∀ k j, 2^k ≤ j → j ≤ 2^(k+1) → psiInterp k (obsNode k j)=C j) ∧
  (∀ k j, 2^k ≤ j → j+1 ≤ 2^(k+1) →
    ∀ t ∈ Icc (obsNode k j) (obsNode k (j+1)), psiInterp k t=obsSegment k j t) ∧
  (∀ k g, (∀ j, 2^k ≤ j → j+1 ≤ 2^(k+1) →
    ∀ t ∈ Icc (obsNode k j) (obsNode k (j+1)), g t=obsSegment k j t) →
    EqOn g (psiInterp k) (Icc (0:ℝ) 1)) ∧
  TendstoUniformlyOn psiInterp Psi atTop (Icc (0:ℝ) 1) ∧
  (∀ g, PeriodicLipschitzPositive g → TendstoUniformlyOn psiInterp g atTop (Icc (0:ℝ) 1) → g=Psi) ∧
  (∀ x y, |Psi x-Psi y| ≤ (2*obsLip*Real.log 2)*|x-y|)
end Targets

theorem theorem_6_3 : Targets.theorem_6_3 :=
  ⟨theorem_6_3_block_version,psiInterp_continuousOn,psiInterp_nodes,psiInterp_on_cell,
    psiInterp_unique,psiInterp_uniform,Psi_unique_uniform,Psi_lipschitz⟩

end
end GD
