import GD.GridCertificates

namespace GD
noncomputable section

/-- A table update uses only entries computed at smaller indices. -/
def tableStep (v : Array ℝ) (n : ℕ) : ℝ :=
  if n%2=0 then rho*v[n/2]! else K v[n/2]! v[n/2+1]!

def cachedU : ℕ → Array ℝ
  | 0 => #[0,1]
  | n+1 => (cachedU n).push (tableStep (cachedU n) (n+2))

@[simp] theorem cachedU_size (n : ℕ) : (cachedU n).size=n+2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [cachedU,ih]

theorem tableStep_correct (v : Array ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hv : ∀ j, j < n → v[j]! =U j) : tableStep v n=U n := by
  unfold tableStep
  rw [hv _ (by omega)]
  split_ifs with he
  · rw [show n=2*(n/2) by omega,U_even]
    congr 2 <;> omega
  · rw [hv _ (by omega)]
    conv_rhs => rw [show n=2*(n/2)+1 by omega,U_odd]

theorem cachedU_correct (n j : ℕ) (hj : j ≤ n+1) : (cachedU n)[j]! =U j := by
  induction n generalizing j with
  | zero => interval_cases j <;> simp [cachedU]
  | succ n ih =>
    by_cases h : j ≤ n+1
    · have he : j ≠ (cachedU n).size := by rw [cachedU_size]; omega
      simpa only [cachedU,getElem!_def,Array.getElem?_push,if_neg he] using ih j h
    · have he : j=n+2 := by omega
      subst j
      have hc := tableStep_correct (cachedU n) (n+2) (by omega)
        (fun i hi => ih i (by omega))
      simpa only [cachedU,getElem!_def,Array.getElem?_push,cachedU_size,if_pos rfl,Option.getD_some] using hc

/-- A left-to-right scan with the known upper bound 1 as initial value. -/
def scanMin (f : ℕ → ℝ) (lo : ℕ) : ℕ → ℝ
  | 0 => 1
  | n+1 => min (scanMin f lo n) (f (lo+n))

theorem scanMin_spec (f : ℕ → ℝ) (lo n : ℕ) :
    scanMin f lo n ≤ 1 ∧
    (∀ i, lo ≤ i → i < lo+n → scanMin f lo n ≤ f i) ∧
    (∀ z, z ≤ 1 → (∀ i, lo ≤ i → i < lo+n → z ≤ f i) → z ≤ scanMin f lo n) := by
  induction n with
  | zero =>
    refine ⟨le_rfl,?_,?_⟩
    · intro i hi hi'; omega
    · intro z hz hh; exact hz
  | succ n ih =>
    refine ⟨(min_le_left _ _).trans ih.1,?_,?_⟩
    · intro i hi hi'
      by_cases h : i < lo+n
      · exact (min_le_left _ _).trans (ih.2.1 i hi h)
      · have he : i=lo+n := by omega
        subst i
        exact min_le_right _ _
    · intro z hz hh
      exact le_min (ih.2.2 z hz (fun i hi hi' => hh i hi (by omega)))
        (hh (lo+n) (by omega) (by omega))

theorem scanMin_eq (f : ℕ → ℝ) (lo n : ℕ) (z : ℝ)
    (hz : z ≤ 1) (hmin : ∀ i, lo ≤ i → i < lo+n → z ≤ f i)
    (hatt : ∃ i, lo ≤ i ∧ i < lo+n ∧ f i=z) : scanMin f lo n=z := by
  obtain ⟨i,hi,hi',he⟩ := hatt
  exact le_antisymm (he ▸ (scanMin_spec f lo n).2.1 i hi hi')
    ((scanMin_spec f lo n).2.2 z hz hmin)

def gridAlgorithm (k : ℕ) : ℝ × ℝ :=
  let v := cachedU (2^(k+1)-1)
  (scanMin (fun j => v[j]!/((j+1:ℕ):ℝ)^p) (2^k) (2^k),
   scanMin (fun j => v[j]!/(j:ℝ)^p) (2^k) (2^k+1))

theorem gridAlgorithm_correct (k : ℕ) : gridAlgorithm k=(lowerGrid k,upperGrid k) := by
  have hp : 0 < (2:ℕ)^k := by positivity
  have hp' : 0 < (2:ℕ)^(k+1) := by positivity
  have hc (j : ℕ) (hj : j ≤ 2^(k+1)) : (cachedU (2^(k+1)-1))[j]! =U j :=
    cachedU_correct _ _ (by omega)
  have hm : phiMin ≤ 1 := phiMin_bounds.2.le
  apply Prod.ext
  · obtain ⟨j,hj,hj',he,hmin⟩ := lowerGrid_attained k
    apply scanMin_eq
    · exact (grid_lower_sandwich k).1.trans hm
    · intro i hi hi'
      have hi'' : i < 2^(k+1) := by rw [pow_succ]; omega
      rw [hc i hi''.le]
      exact hmin i hi hi''
    · refine ⟨j,hj,?_,?_⟩
      · rw [pow_succ] at hj'; omega
      · rw [hc j hj'.le,he]
  · obtain ⟨j,hj,hj',he,hmin⟩ := upperGrid_attained k
    apply scanMin_eq
    · rw [he]
      exact (div_le_one (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < j by omega)) p)).mpr
        (proposition_5_2 j (by omega)).1
    · intro i hi hi'
      have hi'' : i ≤ 2^(k+1) := by rw [pow_succ]; omega
      rw [hc i hi'']
      exact hmin i hi hi''
    · refine ⟨j,hj,?_,?_⟩
      · rw [pow_succ] at hj'; omega
      · rw [hc j hj',he]

/-- Scalar real-RAM operations: an even update costs 1; an odd radical update
costs at most 10. Array access and integer indexing are not scalar operations. -/
def tableWork : ℕ → ℕ
  | 0 => 0
  | n+1 => tableWork n + if (n+2)%2=0 then 1 else 10

theorem tableWork_bound (n : ℕ) : tableWork n ≤ 10*n := by
  induction n with
  | zero => simp [tableWork]
  | succ n ih => simp only [tableWork]; split_ifs <;> omega

/-- Constants cost 5; each scan candidate costs power, division and minimum.
Real powers are primitive scalar operations in this stated arithmetic model. -/
def gridWork (k : ℕ) : ℕ :=
  5+tableWork (2^(k+1)-1)+3*2^k+3*(2^k+1)

theorem gridWork_bound (k : ℕ) : gridWork k ≤ 30*2^k := by
  have h := tableWork_bound (2^(k+1)-1)
  have hp : 0 < (2:ℕ)^k := by positivity
  unfold gridWork
  rw [pow_succ]
  rw [pow_succ] at h
  omega

namespace Targets
/-- All analytical clauses of C.3 and an explicit linear-work cached algorithm.
The optional printed decimal example is not part of this proposition. -/
def theorem_C_3 : Prop := theorem_C_3_bounds ∧
  (∀ k, gridAlgorithm k=(lowerGrid k,upperGrid k)) ∧
  (∀ k, gridWork k ≤ 30*2^k)
end Targets

theorem theorem_C_3 : Targets.theorem_C_3 :=
  ⟨theorem_C_3_bounds,gridAlgorithm_correct,gridWork_bound⟩

end
end GD
