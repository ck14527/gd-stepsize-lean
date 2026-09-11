import GD.SmallPivots

namespace GD
noncomputable section
open Set Filter
open scoped Topology

theorem foldr_max_mem_or_zero (xs : List ℝ) : xs.foldr max 0=0 ∨ xs.foldr max 0 ∈ xs := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rcases le_total x (xs.foldr max 0) with h | h
    · rw [max_eq_right h]
      exact ih.imp_right (fun hh => List.mem_cons_of_mem x hh)
    · rw [max_eq_left h]
      exact Or.inr (List.mem_cons_self ..)

theorem W_maximizing_pivot (N : ℕ) (hN : 2 ≤ N) :
    ∃ m : ℕ, 1 ≤ m ∧ m < N ∧ W N=A (U m) (W (N-m)) := by
  have hp := W_pos N (by omega)
  rw [W.eq_def N,dif_neg (by omega : ¬N ≤ 1)] at hp ⊢
  have hm := foldr_max_mem_or_zero (List.ofFn (fun i : Fin (N-1) => A (U (i.val+1)) (W (N-(i.val+1)))))
  rcases hm with hm | hm
  · rw [hm] at hp
    exact (lt_irrefl 0 hp).elim
  · obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    exact ⟨i.val+1,by omega,by have := i.isLt; omega,hi.symm⟩

/-- Finite first-macroscopic-pivot alternative. The discarded mass is charged
to the actual deficit, including the deficit of the surviving subtree. -/
theorem first_macro_alternative (ε c0 : ℝ) (hc0 : 0 ≤ c0)
    (hsmall : ∀ N m : ℕ, 1 ≤ m → m < N → (m:ℝ)/(N:ℝ) ≤ ε →
      c0*(m:ℝ) ≤ sigma (U m) (W (N-m))) :
    ∀ N : ℕ, 1 ≤ N →
      c0*((N:ℝ)-1)+deficit 1 ≤ deficit N ∨
      ∃ s m : ℕ, 1 ≤ m ∧ m < s ∧ s ≤ N ∧ ε < (m:ℝ)/(s:ℝ) ∧
        W s=A (U m) (W (s-m)) ∧ c0*((N:ℝ)-(s:ℝ))+deficit s ≤ deficit N := by
  intro N hN
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hn : N=1
    · subst N
      exact Or.inl (by simp)
    obtain ⟨m,hm,hmN,he⟩ := W_maximizing_pivot N (by omega)
    rcases lt_or_ge ε ((m:ℝ)/(N:ℝ)) with hmacro | hsm
    · exact Or.inr ⟨N,m,hm,hmN,le_rfl,hmacro,he,by simp⟩
    have hidentity := (proposition_D_3.2 N m hm hmN he)
    have hstep : c0*(m:ℝ)+deficit (N-m) ≤ deficit N := by
      have h := hsmall N m hm hmN hsm
      linarith [hidentity.1,hidentity.2.1]
    have hcast : (N-m:ℕ)=(N:ℝ)-(m:ℝ) := Nat.cast_sub hmN.le
    rcases ih (N-m) (by omega) (by omega) with h | ⟨s,j,hj,hjs,hsN,hmacro,hs,hd⟩
    · left
      rw [hcast] at h
      nlinarith
    · right
      refine ⟨s,j,hj,hjs,by omega,hmacro,hs,?_⟩
      rw [hcast] at hd
      nlinarith

theorem low_deficit_first_macro (ε c0 : ℝ) (hc0 : 0 < c0)
    (hsmall : ∀ N m : ℕ, 1 ≤ m → m < N → (m:ℝ)/(N:ℝ) ≤ ε →
      c0*(m:ℝ) ≤ sigma (U m) (W (N-m))) (N : ℕ) (hN : 2 ≤ N)
    (hE : deficit N/(N:ℝ) < c0/2) :
    ∃ s m : ℕ, 1 ≤ m ∧ m < s ∧ s ≤ N ∧ ε < (m:ℝ)/(s:ℝ) ∧
      W s=A (U m) (W (s-m)) ∧ c0*((N:ℝ)-(s:ℝ))+deficit s ≤ deficit N := by
  rcases first_macro_alternative ε c0 hc0.le hsmall N (by omega) with h | h
  · have hn0 : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hn2 : (2:ℝ) ≤ N := by exact_mod_cast hN
    have hh := (div_lt_iff₀ hn0).mp hE
    have h1 := deficit_nonneg 1 (by omega)
    nlinarith
  · exact h

end
end GD
