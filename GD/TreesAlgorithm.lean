import GD.Balanced
namespace GD
noncomputable section

inductive Tree where
  | leaf : Tree
  | join : Tree → Tree → Tree
  deriving DecidableEq

def Tree.leaves : Tree → ℕ
  | .leaf => 1
  | .join l r => l.leaves+r.leaves

def Tree.value : Tree → ℝ
  | .leaf => 1
  | .join l r => K l.value r.value

theorem Tree.value_nonneg (t : Tree) : 0 ≤ t.value := by
  induction t with
  | leaf => norm_num [value]
  | join l r hl hr => exact K_nonneg hl hr

theorem Tree.leaves_pos (t : Tree) : 0 < t.leaves := by
  induction t with
  | leaf => norm_num [leaves]
  | join l r hl hr => simp only [leaves]; omega

theorem Tree.value_le_U (t : Tree) : t.value ≤ U t.leaves := by
  induction t with
  | leaf => simp [value,leaves]
  | join l r hl hr =>
    exact (K_mono l.value_nonneg r.value_nonneg hl hr).trans (corollary_4_2.2.1 _ _)

/-- Strict monotonicity forces optimal children at every optimal root. -/
theorem Tree.root_optimal_iff (l r : Tree) :
    (Tree.join l r).value=U (l.leaves+r.leaves) ↔
    l.value=U l.leaves ∧ r.value=U r.leaves ∧
    K (U l.leaves) (U r.leaves)=U (l.leaves+r.leaves) := by
  classical
  have hl := l.value_le_U
  have hr := r.value_le_U
  have hub := corollary_4_2.2.1 l.leaves r.leaves
  change K l.value r.value=_ ↔ _
  constructor
  · intro he
    have hel : l.value=U l.leaves := by
      by_contra h
      have hlt := K_strict_left l.value_nonneg r.value_nonneg (lt_of_le_of_ne hl h)
      have hle := K_mono (U_nonneg l.leaves) r.value_nonneg le_rfl hr
      linarith
    have her : r.value=U r.leaves := by
      by_contra h
      have hlt := K_strict_right l.value_nonneg r.value_nonneg (lt_of_le_of_ne hr h)
      have hle := K_mono l.value_nonneg (U_nonneg r.leaves) hl le_rfl
      linarith
    exact ⟨hel,her,by simpa [hel,her] using he⟩
  · rintro ⟨hl,hr,he⟩; simpa [hl,hr] using he

def Tree.AllSplitsOptimal : Tree → Prop
  | .leaf => True
  | .join l r =>
      K (U l.leaves) (U r.leaves)=U (l.leaves+r.leaves) ∧
      l.AllSplitsOptimal ∧ r.AllSplitsOptimal

/-- The recursive optimal-tree characterization in Corollary 4.6.
The separate arithmetic classification of each split is Lemma 4.3. -/
theorem corollary_4_6 (t : Tree) : t.value=U t.leaves ↔ t.AllSplitsOptimal := by
  induction t with
  | leaf => simp [Tree.value,Tree.leaves,Tree.AllSplitsOptimal]
  | join l r hl hr =>
    change (Tree.join l r).value=U (l.leaves+r.leaves) ↔ _
    rw [Tree.root_optimal_iff]
    simp only [Tree.AllSplitsOptimal,← hl,← hr]
    tauto

def bitStep (bit : Bool) (ab : ℝ × ℝ) : ℝ × ℝ :=
  if bit then (K ab.1 ab.2,rho*ab.2) else (rho*ab.1,K ab.1 ab.2)

def natStep (bit : Bool) (n : ℕ) : ℕ := 2*n + if bit then 1 else 0

def runBits : List Bool → ℝ × ℝ → ℝ × ℝ
  | [], ab => ab
  | bit::bits, ab => runBits bits (bitStep bit ab)

def readBits : List Bool → ℕ → ℕ
  | [], n => n
  | bit::bits, n => readBits bits (natStep bit n)

theorem bitStep_correct (bit : Bool) (n : ℕ) :
    bitStep bit (U n,U (n+1)) = (U (natStep bit n),U (natStep bit n+1)) := by
  cases bit <;> simp only [bitStep,natStep,Bool.false_eq_true,if_false,if_true,Nat.add_zero]
  · rw [U_even,U_odd]
  · rw [U_odd,show 2*n+1+1=2*(n+1) by omega,U_even]

theorem runBits_correct (bits : List Bool) (n : ℕ) :
    runBits bits (U n,U (n+1))=(U (readBits bits n),U (readBits bits n+1)) := by
  induction bits generalizing n with
  | nil => rfl
  | cons bit bits ih =>
    simp only [runBits,readBits]
    rw [bitStep_correct,ih]

/-- Algorithm 1: exact correctness for the given most-significant-first bits.
Real arithmetic is modeled exactly. Runtime bit costs are not asserted here. -/
theorem algorithm_1 (bits : List Bool) :
    (runBits bits (0,1)).1=U (readBits bits 0) := by
  have h := runBits_correct bits 0
  simpa using congrArg Prod.fst h

end
end GD
