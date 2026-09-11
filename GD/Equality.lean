import GD.Balanced
namespace GD
noncomputable section

def ScaledConsecutive (m n : ℕ) : Prop :=
  ∃ k r : ℕ, 1 ≤ r ∧
    ((m=2^k*r ∧ n=2^k*(r+1)) ∨ (n=2^k*r ∧ m=2^k*(r+1)))

def EqualityPattern (m n : ℕ) : Prop := m=n ∨ ScaledConsecutive m n

theorem equal_children (n : ℕ) : K (U n) (U n)=U (n+n) := by
  rw [show n+n=2*n by omega,U_even,K_diag (U_nonneg n)]

theorem consecutive_children (n : ℕ) : K (U n) (U (n+1))=U (n+(n+1)) := by
  rw [show n+(n+1)=2*n+1 by omega,U_odd]

theorem scaled_consecutive_sufficient {m n : ℕ} (h : ScaledConsecutive m n) :
    K (U m) (U n)=U (m+n) := by
  obtain ⟨k,r,hr,h|h⟩ := h
  · obtain ⟨rfl,rfl⟩ := h
    rw [U_dyadic,U_dyadic,K_hom (pow_nonneg rho_pos.le _) (U_nonneg r) (U_nonneg (r+1)),consecutive_children,
      show 2^k*r+2^k*(r+1)=2^k*(r+(r+1)) by ring,U_dyadic]
  · obtain ⟨rfl,rfl⟩ := h
    rw [K_symm,show 2^k*(r+1)+2^k*r=2^k*r+2^k*(r+1) by omega]
    rw [U_dyadic,U_dyadic,K_hom (pow_nonneg rho_pos.le _) (U_nonneg r) (U_nonneg (r+1)),consecutive_children,
      show 2^k*r+2^k*(r+1)=2^k*(r+(r+1)) by ring,U_dyadic]

/-- A nonconsecutive even-odd pair is strictly suboptimal. -/
theorem strict_even_odd {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    K (U (2*a)) (U (2*b+1)) < U (2*a+(2*b+1)) := by
  classical
  have va := U_nonneg a
  have vb := U_nonneg b
  have vb1 := U_nonneg (b+1)
  have hva : 0 < U a := U_pos ha
  have habu : U a < U b := U_strictMono hab
  have hbbu : U b < U (b+1) := U_strictMono (by omega)
  have hr := rearrangement_first va le_rfl habu.le hbbu.le
  have hn : K (K (U a) (U a)) (K (U b) (U (b+1))) ≠
      K (K (U a) (U b)) (K (U a) (U (b+1))) := by
    intro h
    rcases hr.2.mp h with h | h
    · exact (ne_of_lt habu) h
    · have := mul_lt_mul_of_pos_left hbbu hva
      linarith
  have hs := lt_of_le_of_ne hr.1 hn
  have hu := K_mono (K_nonneg va vb) (K_nonneg va vb1)
    (corollary_4_2.2.1 a b) (corollary_4_2.2.1 a (b+1))
  have ht := hs.trans_le hu
  simpa only [U_even,U_odd,K_diag va,show 2*a+(2*b+1)=2*(a+b)+1 by omega,
    show a+(b+1)=a+b+1 by omega] using ht

/-- A nonconsecutive odd-even pair is strictly suboptimal, including a=0. -/
theorem strict_odd_even {a b : ℕ} (hab : a+1 < b) :
    K (U (2*a+1)) (U (2*b)) < U (2*a+1+2*b) := by
  classical
  have va := U_nonneg a
  have va1 := U_nonneg (a+1)
  have vb := U_nonneg b
  have hvb : 0 < U b := U_pos (by omega)
  have haa : U a < U (a+1) := U_strictMono (by omega)
  have habu : U (a+1) < U b := U_strictMono hab
  have hr := rearrangement_first va haa.le habu.le le_rfl
  have hn : K (K (U a) (U (a+1))) (K (U b) (U b)) ≠
      K (K (U a) (U b)) (K (U (a+1)) (U b)) := by
    intro h
    rcases hr.2.mp h with h | h
    · exact (ne_of_lt habu) h
    · have := mul_lt_mul_of_pos_right haa hvb; linarith
  have hs := lt_of_le_of_ne hr.1 hn
  have hu := K_mono (K_nonneg va vb) (K_nonneg va1 vb)
    (corollary_4_2.2.1 a b) (corollary_4_2.2.1 (a+1) b)
  have ht := hs.trans_le hu
  simpa only [U_even,U_odd,K_diag vb,show 2*a+1+2*b=2*(a+b)+1 by omega,
    show a+1+b=a+b+1 by omega] using ht

/-- Unequal odd child counts never tie. -/
theorem strict_odd_odd {a b : ℕ} (hab : a < b) :
    K (U (2*a+1)) (U (2*b+1)) < U ((2*a+1)+(2*b+1)) := by
  classical
  have va := U_nonneg a
  have haa : U a < U (a+1) := U_strictMono (by omega)
  have habu : U (a+1) ≤ U b := U_strictMono.monotone (by omega)
  have hbb : U b < U (b+1) := U_strictMono (by omega)
  have h1 := rearrangement_first va haa.le habu hbb.le
  have h2 := rearrangement_second va haa.le habu hbb.le
  have hn : K (K (U a) (U b)) (K (U (a+1)) (U (b+1))) ≠
      K (K (U a) (U (b+1))) (K (U (a+1)) (U b)) := by
    intro h
    rcases h2.2.mp h with h | h
    · exact (ne_of_lt haa) h
    · exact (ne_of_lt hbb) h
  have hs := h1.1.trans_lt (lt_of_le_of_ne h2.1 hn)
  have hu := K_mono (K_nonneg va (U_nonneg (b+1))) (K_nonneg (U_nonneg (a+1)) (U_nonneg b))
    (corollary_4_2.2.1 a (b+1)) (corollary_4_2.2.1 (a+1) b)
  have ht := hs.trans_le hu
  simpa only [U_odd,show (2*a+1)+(2*b+1)=2*(a+b+1) by omega,U_even,
    show a+(b+1)=a+b+1 by omega,show a+1+b=a+b+1 by omega,K_diag (U_nonneg (a+b+1))] using ht

theorem equalityPattern_symm {m n : ℕ} (h : EqualityPattern m n) : EqualityPattern n m := by
  rcases h with h | ⟨k,r,hr,h⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨k,r,hr,h.symm⟩

/-- Lemma 4.3: both directions, with positivity of the integer indices retained. -/
theorem lemma_4_3 (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    K (U m) (U n)=U (m+n) ↔ EqualityPattern m n := by
  classical
  constructor
  · suffices hall : ∀ t m n : ℕ, m+n=t → 1 ≤ m → 1 ≤ n →
        K (U m) (U n)=U (m+n) → EqualityPattern m n by exact hall (m+n) m n rfl hm hn
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      have ordered : ∀ m n : ℕ, m+n=t → 1 ≤ m → 1 ≤ n → m ≤ n →
          K (U m) (U n)=U (m+n) → EqualityPattern m n := by
        intro m n hsum hm hn hmn heq
        by_cases he : m=n
        · exact Or.inl he
        let a := m/2
        let b := n/2
        by_cases hme : m%2=0
        · have hmv : m=2*a := by dsimp [a]; omega
          have ha : 1 ≤ a := by omega
          by_cases hne : n%2=0
          · have hnv : n=2*b := by dsimp [b]; omega
            have hb : 1 ≤ b := by omega
            have hab : a+b < t := by omega
            have hlo : K (U a) (U b)=U (a+b) := by
              rw [hmv,hnv,U_even,U_even,K_hom rho_pos.le (U_nonneg a) (U_nonneg b),
                show 2*a+2*b=2*(a+b) by omega,U_even] at heq
              exact (mul_left_cancel₀ rho_pos.ne') heq
            have hp := ih (a+b) hab a b rfl ha hb hlo
            rcases hp with hp | ⟨k,r,hr,hp⟩
            · exact Or.inl (by omega)
            · refine Or.inr ⟨k+1,r,hr,?_⟩
              rcases hp with ⟨hae,hbe⟩ | ⟨hbe,hae⟩
              · left; constructor <;> simp only [hmv,hnv,hae,hbe,pow_succ] <;> ring
              · right; constructor <;> simp only [hmv,hnv,hae,hbe,pow_succ] <;> ring
          · have hnv : n=2*b+1 := by dsimp [b]; omega
            have heab : a=b := by
              have hab_le : a ≤ b := by omega
              rcases eq_or_lt_of_le hab_le with h | h
              · exact h
              · have hs := strict_even_odd ha h
                rw [← hmv,← hnv] at hs
                exact False.elim ((ne_of_lt hs) heq)
            have hnnext : n=m+1 := by omega
            exact Or.inr ⟨0,m,hm,Or.inl ⟨by simp,by simp [hnnext]⟩⟩
        · have hmv : m=2*a+1 := by dsimp [a]; omega
          by_cases hne : n%2=0
          · have hnv : n=2*b := by dsimp [b]; omega
            have heab : a+1=b := by
              have hab_le : a+1 ≤ b := by omega
              rcases eq_or_lt_of_le hab_le with h | h
              · exact h
              · have hs := strict_odd_even h
                rw [← hmv,← hnv] at hs
                exact False.elim ((ne_of_lt hs) heq)
            have hnnext : n=m+1 := by omega
            exact Or.inr ⟨0,m,hm,Or.inl ⟨by simp,by simp [hnnext]⟩⟩
          · have hnv : n=2*b+1 := by dsimp [b]; omega
            have hab : a < b := by omega
            have hs := strict_odd_odd hab
            rw [← hmv,← hnv] at hs
            exact False.elim ((ne_of_lt hs) heq)
      intro m n hsum hm hn heq
      rcases le_total m n with h | h
      · exact ordered m n hsum hm hn h heq
      · exact equalityPattern_symm (ordered n m (by omega) hn hm h (by simpa [K_symm,Nat.add_comm] using heq))
  · intro h
    rcases h with h | h
    · subst n; exact equal_children m
    · exact scaled_consecutive_sufficient h

end
end GD
