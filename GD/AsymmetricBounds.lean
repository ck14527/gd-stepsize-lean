import GD.PhaseDefinitions
namespace GD
noncomputable section

theorem A_mono {u w u' w' : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w)
    (huu : u ≤ u') (hww : w ≤ w') : A u w ≤ A u' w' := by
  have hsq := (sq_le_sq₀ hw (hw.trans hww)).mpr hww
  have hprod := mul_le_mul huu hww hw (hu.trans huu)
  have hd : w^2+8*u*w ≤ w'^2+8*u'*w' := by nlinarith
  have hs := Real.sqrt_le_sqrt hd
  unfold A; linarith

@[simp] theorem W_one : W 1=1 := by rw [W]; norm_num

theorem U_ge_one (n : ℕ) (hn : 1 ≤ n) : 1 ≤ U n := by
  simpa using U_strictMono.monotone hn

theorem foldr_max_upper (xs : List ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hxs : ∀ x ∈ xs, x ≤ b) : xs.foldr max 0 ≤ b := by
  induction xs with
  | nil => exact hb
  | cons x xs ih =>
    simp only [List.foldr_cons,max_le_iff]
    exact ⟨hxs x (by simp),ih (fun y hy => hxs y (by simp [hy]))⟩

theorem le_foldr_max {xs : List ℝ} {x : ℝ} (hx : x ∈ xs) : x ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    simp only [List.foldr_cons]
    rcases hx with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-- Every admissible asymmetric pivot is represented in the actual recursion. -/
theorem W_pivot_lower (N m : ℕ) (hm : 1 ≤ m) (hmN : m < N) :
    A (U m) (W (N-m)) ≤ W N := by
  rw [W.eq_def N,dif_neg (by omega : ¬N ≤ 1)]
  apply le_foldr_max
  apply List.mem_ofFn.mpr
  refine ⟨⟨m-1,by omega⟩,?_⟩
  simp only [show m-1+1=m by omega]

/-- Proposition 6.2's finite-horizon sandwich, for the recursively defined W. -/
theorem W_sandwich (N : ℕ) (hN : 1 ≤ N) : 2*U N-1 ≤ W N ∧ W N ≤ rho*U N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hn : N=1
    · subst N; simp only [W_one,U_one]
      constructor <;> nlinarith [rho_gt_two]
    have hn2 : 2 ≤ N := by omega
    have huN := U_ge_one N hN
    have ih' : ∀ j : ℕ, 1 ≤ j → j < N → 2*U j-1 ≤ W j ∧ W j ≤ rho*U j :=
      fun j hj hjN => ih j hjN hj
    have up : W N ≤ rho*U N := by
      rw [W.eq_def N,dif_neg (by omega : ¬N ≤ 1)]
      apply foldr_max_upper _ _ (mul_nonneg rho_pos.le (U_nonneg N))
      intro v hv
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
      have hi : i.val < N-1 := i.isLt
      have hrec := ih' (N-(i.val+1)) (by omega) (by omega)
      have hu := U_ge_one (N-(i.val+1)) (by omega)
      have hw : 0 ≤ W (N-(i.val+1)) := by linarith
      have h1 := A_mono (U_nonneg (i.val+1)) hw le_rfl hrec.2
      have h2 := lemma_D_1_upper (U_pos (by omega : 0 < i.val+1)) (U_pos (by omega : 0 < N-(i.val+1)))
      have h3 := mul_le_mul_of_nonneg_left (corollary_4_2.2.1 (i.val+1) (N-(i.val+1))) rho_pos.le
      have hsum : i.val+1+(N-(i.val+1))=N := by omega
      rw [hsum] at h3
      exact (h1.trans h2).trans h3
    have low : 2*U N-1 ≤ W N := by
      let a := N/2
      let b := N-a
      have ha : 1 ≤ a := by dsimp [a]; omega
      have hb : 1 ≤ b := by dsimp [a,b]; omega
      have haN : a < N := by dsimp [a]; omega
      have hbN : b < N := by dsimp [a,b]; omega
      have hr := (ih' b hb hbN).1
      have hua := U_ge_one a ha
      have hub := U_ge_one b hb
      have h1 := lemma_D_1_lower hua hub
      have h2 := A_mono (U_nonneg a) (show 0 ≤ 2*U b-1 by linarith) le_rfl hr
      have h3 := W_pivot_lower N a ha haN
      have hbal : K (U a) (U b)=U N := by
        dsimp [a,b]
        rw [show N-N/2=(N+1)/2 by omega]
        exact (corollary_4_2.2.2 N hn2).symm
      rw [hbal] at h1
      exact (h1.trans h2).trans h3
    exact ⟨low,up⟩

/-- The algebraic identity (70). The nonnegative summands are proved in
GD.DeficitBounds using the separately established support and power bounds. -/
theorem deficit_identity (N m : ℕ) (hmN : m ≤ N) (hp : W N=A (U m) (W (N-m))) :
    deficit N=Bsup*((m:ℝ)-(U m)^q)+deficit (N-m)+sigma (U m) (W (N-m)) := by
  unfold deficit sigma
  rw [hp,Nat.cast_sub hmN]
  ring

end
end GD
