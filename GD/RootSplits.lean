import GD.Equality
import GD.TreesAlgorithm
namespace GD
noncomputable section

def OptimalSplit (N m : ℕ) : Prop := 1 ≤ m ∧ m < N ∧ K (U m) (U (N-m))=U N

theorem odd_factor_unique (k l v w : ℕ) (hv : v%2=1) (hw : w%2=1)
    (h : 2^k*v=2^l*w) : k=l ∧ v=w := by
  induction k generalizing l with
  | zero =>
    cases l with
    | zero => simpa using h
    | succ l =>
      have hp := congrArg (fun n : ℕ => n%2) h
      simp [pow_succ,Nat.mul_mod,hv] at hp
  | succ k ih =>
    cases l with
    | zero =>
      have hp := congrArg (fun n : ℕ => n%2) h
      simp [pow_succ,Nat.mul_mod,hw] at hp
    | succ l =>
      have he : 2*(2^k*v)=2*(2^l*w) := by simpa [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
      have hlo : 2^k*v=2^l*w := by omega
      obtain ⟨hkl,hvw⟩ := ih l hlo
      exact ⟨by omega,hvw⟩

/-- A direct integer-arithmetic form of all root optimizers. -/
theorem root_split_iff (N m : ℕ) (hm : 1 ≤ m) (hmN : m < N) :
    OptimalSplit N m ↔ 2*m=N ∨
      ∃ k r : ℕ, 1 ≤ r ∧ N=2^k*(2*r+1) ∧ (m=2^k*r ∨ m=2^k*(r+1)) := by
  have hsum : m+(N-m)=N := by omega
  have ht := lemma_4_3 m (N-m) hm (by omega)
  rw [hsum] at ht
  simp only [OptimalSplit,hm,hmN,true_and]
  rw [ht]
  constructor
  · rintro (h | ⟨k,r,hr,h⟩)
    · left; omega
    · right
      rcases h with ⟨hmv,hnv⟩ | ⟨hnv,hmv⟩
      · refine ⟨k,r,hr,?_,Or.inl hmv⟩
        calc N = m+(N-m) := hsum.symm
             _ = 2^k*(2*r+1) := by rw [hnv,hmv]; ring
      · refine ⟨k,r,hr,?_,Or.inr hmv⟩
        calc N = m+(N-m) := hsum.symm
             _ = 2^k*(2*r+1) := by rw [hnv,hmv]; ring
  · rintro (h | ⟨k,r,hr,hN,hmv⟩)
    · left; omega
    · right; refine ⟨k,r,hr,?_⟩
      rcases hmv with hmv | hmv
      · left; refine ⟨hmv,?_⟩
        have he : N=m+2^k*(r+1) := by rw [hN,hmv]; ring
        omega
      · right; refine ⟨?_,hmv⟩
        have he : N=m+2^k*r := by rw [hN,hmv]; ring
        omega

/-- Corollary 4.4 in one formula valid for all odd parts and dyadic valuations.
For odd N the balanced alternative is impossible; for a power of two the
scaled-consecutive alternative is excluded. This avoids natural subtraction
in the exponent l-1 while specifying exactly the same three cases. -/
theorem corollary_4_4 (nu l m : ℕ) (hodd : nu%2=1)
    (hm : 1 ≤ m) (hmN : m < nu*2^l) :
    OptimalSplit (nu*2^l) m ↔
    2*m=nu*2^l ∨
      (1 < nu ∧ (m=2^l*((nu-1)/2) ∨ m=2^l*((nu+1)/2))) := by
  classical
  rw [root_split_iff _ _ hm hmN]
  constructor
  · rintro (h | ⟨k,r,hr,hN,hmv⟩)
    · exact Or.inl h
    · have hf : 2^k*(2*r+1)=2^l*nu := by simpa [Nat.mul_comm] using hN.symm
      obtain ⟨hkl,hrnu⟩ := odd_factor_unique k l (2*r+1) nu (by omega) hodd hf
      subst k
      have hnu : 1 < nu := by omega
      have hr1 : (nu-1)/2=r := by omega
      have hr2 : (nu+1)/2=r+1 := by omega
      exact Or.inr ⟨hnu,by simpa [hr1,hr2] using hmv⟩
  · rintro (h | ⟨hnu,hmv⟩)
    · exact Or.inl h
    · right
      let r := (nu-1)/2
      have hr : 1 ≤ r := by dsimp [r]; omega
      have hnuform : nu=2*r+1 := by dsimp [r]; omega
      refine ⟨l,r,hr,?_,?_⟩
      · rw [hnuform]; ring
      · have hr2 : (nu+1)/2=r+1 := by omega
        simpa [r,hr2] using hmv

/-- Corollary 4.6 with its explicit, arithmetic equality patterns. -/
def Tree.AllEqualityPatterns : Tree → Prop
  | .leaf => True
  | .join l r => EqualityPattern l.leaves r.leaves ∧ l.AllEqualityPatterns ∧ r.AllEqualityPatterns

theorem all_splits_iff_patterns (t : Tree) : t.AllSplitsOptimal ↔ t.AllEqualityPatterns := by
  induction t with
  | leaf => rfl
  | join l r hl hr =>
    simp only [Tree.AllSplitsOptimal,Tree.AllEqualityPatterns,
      lemma_4_3 _ _ l.leaves_pos r.leaves_pos,hl,hr]

theorem optimal_tree_iff_patterns (t : Tree) : t.value=U t.leaves ↔ t.AllEqualityPatterns :=
  (corollary_4_6 t).trans (all_splits_iff_patterns t)

end
end GD
