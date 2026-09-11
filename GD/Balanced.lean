import GD.Rearrangement
namespace GD
noncomputable section

/-- Precisely the nonnegative-domain assumptions of Theorem 4.1. -/
structure CompositionLaw where
  op : ℝ → ℝ → ℝ
  scale : ℝ
  scale_gt_one : 1 < scale
  nonneg : ∀ {x y}, 0 ≤ x → 0 ≤ y → 0 ≤ op x y
  comm : ∀ x y, op x y = op y x
  zero_left : ∀ {x}, 0 ≤ x → op 0 x = x
  diag : ∀ {x}, 0 ≤ x → op x x = scale*x
  hom : ∀ {t x y}, 0 ≤ t → 0 ≤ x → 0 ≤ y → op (t*x) (t*y)=t*op x y
  strict_left : ∀ {x x' y}, 0 ≤ x → 0 ≤ y → x < x' → op x y < op x' y
  rearr : ∀ {a b c d}, 0 ≤ a → a ≤ b → b ≤ c → c ≤ d →
    op (op a b) (op c d) ≤ op (op a c) (op b d) ∧
    op (op a c) (op b d) ≤ op (op a d) (op b c)

namespace CompositionLaw
variable (C : CompositionLaw)

theorem scale_pos : 0 < C.scale := lt_trans (by norm_num) C.scale_gt_one

theorem mono {x x' y y' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxx : x ≤ x') (hyy : y ≤ y') : C.op x y ≤ C.op x' y' := by
  have hl : C.op x y ≤ C.op x' y := by
    rcases lt_or_eq_of_le hxx with h | h
    · exact (C.strict_left hx hy h).le
    · rw [h]
  have hr : C.op x' y ≤ C.op x' y' := by
    rw [C.comm x' y, C.comm x' y']
    rcases lt_or_eq_of_le hyy with h | h
    · exact (C.strict_left hy (hx.trans hxx) h).le
    · rw [h]
  exact hl.trans hr

def V (C : CompositionLaw) (n : ℕ) : ℝ :=
  if n=0 then 0 else if n=1 then 1 else C.op (C.V (n/2)) (C.V ((n+1)/2))
termination_by n
 decreasing_by all_goals omega

@[simp] theorem V_zero : C.V 0 = 0 := by rw [V]; simp
@[simp] theorem V_one : C.V 1 = 1 := by rw [V]; simp

theorem V_rec {n : ℕ} (hn : 2 ≤ n) :
    C.V n = C.op (C.V (n/2)) (C.V ((n+1)/2)) := by
  rw [V]; simp [show n ≠ 0 by omega, show n ≠ 1 by omega]

theorem V_nonneg (n : ℕ) : 0 ≤ C.V n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : 2 ≤ n
    · rw [C.V_rec hn]
      exact C.nonneg (ih _ (by omega)) (ih _ (by omega))
    · interval_cases n <;> simp

theorem V_even_op (r : ℕ) : C.V (2*r) = C.op (C.V r) (C.V r) := by
  by_cases hr : r=0
  · subst r; simp [C.zero_left (show (0:ℝ) ≤ 0 by norm_num)]
  · rw [C.V_rec (by omega)]
    congr 2 <;> omega

theorem V_even (r : ℕ) : C.V (2*r) = C.scale*C.V r := by
  rw [C.V_even_op, C.diag (C.V_nonneg r)]

theorem V_odd (r : ℕ) : C.V (2*r+1) = C.op (C.V r) (C.V (r+1)) := by
  by_cases hr : r=0
  · subst r; simp [C.zero_left (show (0:ℝ) ≤ 1 by norm_num)]
  · rw [C.V_rec (by omega)]
    congr 2 <;> omega

theorem V_succ_lt (n : ℕ) : C.V n < C.V (n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n; simp
    let r := n/2
    have hr : r < n := by dsimp [r]; omega
    have hi := ih r hr
    by_cases he : n%2=0
    · have hne : n=2*r := by dsimp [r]; omega
      rw [hne, C.V_even_op, C.V_odd]
      rw [C.comm (C.V r) (C.V (r+1))]
      exact C.strict_left (C.V_nonneg r) (C.V_nonneg r) hi
    · have hno : n=2*r+1 := by dsimp [r]; omega
      have hnext : n+1=2*(r+1) := by omega
      rw [hnext,C.V_even_op,hno,C.V_odd]
      exact C.strict_left (C.V_nonneg r) (C.V_nonneg (r+1)) hi

theorem V_strictMono : StrictMono C.V := strictMono_nat_of_lt_succ (C.V_succ_lt)

theorem V_mono : Monotone C.V := C.V_strictMono.monotone

/-- The supercomposition conclusion of Theorem 4.1. -/
theorem supercomposition (m n : ℕ) : C.op (C.V m) (C.V n) ≤ C.V (m+n) := by
  suffices hall : ∀ t m n : ℕ, m+n=t → C.op (C.V m) (C.V n) ≤ C.V (m+n) by
    exact hall (m+n) m n rfl
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    have ordered : ∀ m n : ℕ, m+n=t → m ≤ n → C.op (C.V m) (C.V n) ≤ C.V (m+n) := by
      intro m n hsum hmn
      by_cases hm : m=0
      · subst m; simp [C.zero_left (C.V_nonneg n)]
      by_cases hmn_eq : m=n
      · subst n
        rw [show m+m=2*m by omega,C.V_even_op]
      let a := m/2
      let b := n/2
      have ha : a ≤ b := by dsimp [a,b]; omega
      have hab : a+b < t := by dsimp [a,b]; omega
      have hab1 : a+b+1 < t := by dsimp [a,b]; omega
      have iab := ih (a+b) hab a b rfl
      have iab1 := ih (a+(b+1)) (by omega) a (b+1) rfl
      have ia1b := ih (a+1+b) (by omega) (a+1) b rfl
      have va := C.V_nonneg a
      have vb := C.V_nonneg b
      have va1 := C.V_nonneg (a+1)
      have vb1 := C.V_nonneg (b+1)
      by_cases hme : m%2=0
      · have hmval : m=2*a := by dsimp [a]; omega
        by_cases hne : n%2=0
        · have hnval : n=2*b := by dsimp [b]; omega
          calc
            C.op (C.V m) (C.V n) = C.scale*C.op (C.V a) (C.V b) := by
              rw [hmval,hnval,C.V_even,C.V_even,C.hom C.scale_pos.le va vb]
            _ ≤ C.scale*C.V (a+b) := mul_le_mul_of_nonneg_left iab C.scale_pos.le
            _ = C.V (m+n) := by rw [hmval,hnval,show 2*a+2*b=2*(a+b) by omega,C.V_even]
        · have hnval : n=2*b+1 := by dsimp [b]; omega
          have hr := (C.rearr va le_rfl (C.V_mono ha) (C.V_mono (by omega : b ≤ b+1))).1
          calc
            C.op (C.V m) (C.V n) = C.op (C.op (C.V a) (C.V a)) (C.op (C.V b) (C.V (b+1))) := by
              rw [hmval,hnval,C.V_even_op,C.V_odd]
            _ ≤ C.op (C.op (C.V a) (C.V b)) (C.op (C.V a) (C.V (b+1))) := hr
            _ ≤ C.op (C.V (a+b)) (C.V (a+(b+1))) := C.mono (C.nonneg va vb) (C.nonneg va vb1) iab iab1
            _ = C.V (m+n) := by rw [hmval,hnval,show 2*a+(2*b+1)=2*(a+b)+1 by omega,C.V_odd,show a+(b+1)=a+b+1 by omega]
      · have hmval : m=2*a+1 := by dsimp [a]; omega
        by_cases hne : n%2=0
        · have hnval : n=2*b := by dsimp [b]; omega
          have hab : a+1 ≤ b := by omega
          have hr := (C.rearr va (C.V_mono (by omega : a ≤ a+1)) (C.V_mono hab) le_rfl).1
          calc
            C.op (C.V m) (C.V n) = C.op (C.op (C.V a) (C.V (a+1))) (C.op (C.V b) (C.V b)) := by
              rw [hmval,hnval,C.V_odd,C.V_even_op]
            _ ≤ C.op (C.op (C.V a) (C.V b)) (C.op (C.V (a+1)) (C.V b)) := hr
            _ ≤ C.op (C.V (a+b)) (C.V (a+1+b)) := C.mono (C.nonneg va vb) (C.nonneg va1 vb) iab ia1b
            _ = C.V (m+n) := by rw [hmval,hnval,show 2*a+1+2*b=2*(a+b)+1 by omega,C.V_odd,show a+1+b=a+b+1 by omega]
        · have hnval : n=2*b+1 := by dsimp [b]; omega
          have hab : a+1 ≤ b := by omega
          have hr := C.rearr va (C.V_mono (by omega : a ≤ a+1)) (C.V_mono hab) (C.V_mono (by omega : b ≤ b+1))
          calc
            C.op (C.V m) (C.V n) = C.op (C.op (C.V a) (C.V (a+1))) (C.op (C.V b) (C.V (b+1))) := by
              rw [hmval,hnval,C.V_odd,C.V_odd]
            _ ≤ C.op (C.op (C.V a) (C.V (b+1))) (C.op (C.V (a+1)) (C.V b)) := hr.1.trans hr.2
            _ ≤ C.op (C.V (a+(b+1))) (C.V (a+1+b)) := C.mono (C.nonneg va vb1) (C.nonneg va1 vb) iab1 ia1b
            _ = C.V (m+n) := by rw [hmval,hnval,show 2*a+1+(2*b+1)=2*(a+b+1) by omega,C.V_even_op,show a+(b+1)=a+b+1 by omega,show a+1+b=a+b+1 by omega]
    intro m n hsum
    rcases le_total m n with h | h
    · exact ordered m n hsum h
    · rw [C.comm, Nat.add_comm]
      exact ordered n m (by omega) h

/-- Bellman optimality expressed without an opaque maximization oracle. -/
theorem balanced_maximizes {N : ℕ} (hN : 2 ≤ N) :
    (∀ m : ℕ, 1 ≤ m → m < N → C.op (C.V m) (C.V (N-m)) ≤ C.V N) ∧
    C.op (C.V (N/2)) (C.V ((N+1)/2)) = C.V N := by
  constructor
  · intro m hm hmN
    have := C.supercomposition m (N-m)
    simpa [Nat.add_sub_of_le hmN.le] using this
  · exact (C.V_rec hN).symm

end CompositionLaw

def silverLaw : CompositionLaw where
  op := K
  scale := rho
  scale_gt_one := lt_trans (by norm_num) rho_gt_two
  nonneg := K_nonneg
  comm := K_symm
  zero_left := K_zero_left
  diag := K_diag
  hom := K_hom
  strict_left := K_strict_left
  rearr := fun ha hab hbc hcd =>
    ⟨(theorem_3_1 ha hab hbc hcd).1, (theorem_3_1 ha hab hbc hcd).2.1⟩

def U : ℕ → ℝ := silverLaw.V

@[simp] theorem U_zero : U 0=0 := silverLaw.V_zero
@[simp] theorem U_one : U 1=1 := silverLaw.V_one

theorem U_nonneg (n : ℕ) : 0 ≤ U n := silverLaw.V_nonneg n

theorem U_strictMono : StrictMono U := silverLaw.V_strictMono

theorem U_pos {n : ℕ} (hn : 0 < n) : 0 < U n := by
  have := U_strictMono hn
  simpa using this

theorem U_even (n : ℕ) : U (2*n)=rho*U n := silverLaw.V_even n

theorem U_odd (n : ℕ) : U (2*n+1)=K (U n) (U (n+1)) := silverLaw.V_odd n

/-- Corollary 4.2. U is defined recursively, and the all-splits inequality is proved. -/
theorem corollary_4_2 : StrictMono U ∧
    (∀ m n : ℕ, K (U m) (U n) ≤ U (m+n)) ∧
    (∀ N : ℕ, 2 ≤ N → U N=K (U (N/2)) (U ((N+1)/2))) :=
  ⟨U_strictMono, silverLaw.supercomposition, fun _ h => silverLaw.V_rec h⟩

/-- Exact scaling (21), including the convention N=0. -/
theorem U_dyadic (k n : ℕ) : U (2^k*n)=rho^k*U n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,show 2^k*2*n=2*(2^k*n) by ring,U_even,ih,pow_succ]
    ring

end
end GD

namespace GD
noncomputable section

def BellmanSpec (op : ℝ → ℝ → ℝ) (W : ℕ → ℝ) : Prop :=
  W 1=1 ∧
  (∀ N : ℕ, 2 ≤ N → ∀ m : ℕ, 1 ≤ m → m < N → op (W m) (W (N-m)) ≤ W N) ∧
  (∀ N : ℕ, 2 ≤ N → ∃ m : ℕ, 1 ≤ m ∧ m < N ∧ W N=op (W m) (W (N-m)))

/-- Final Bellman-uniqueness assertion of the abstract Theorem 4.1. -/
theorem CompositionLaw.bellman_unique (C : CompositionLaw) (W : ℕ → ℝ)
    (hW : BellmanSpec C.op W) (N : ℕ) (hN : 1 ≤ N) : W N=C.V N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hn : N=1
    · subst N; simpa using hW.1
    have hn2 : 2 ≤ N := by omega
    have ih' : ∀ j : ℕ, 1 ≤ j → j < N → W j=C.V j := fun j hj hjN => ih j hjN hj
    apply le_antisymm
    · obtain ⟨m,hm,hmN,hval⟩ := hW.2.2 N hn2
      rw [hval,ih' m hm hmN,ih' (N-m) (by omega) (by omega)]
      simpa [Nat.add_sub_of_le hmN.le] using C.supercomposition m (N-m)
    · have hub := hW.2.1 N hn2 (N/2) (by omega) (by omega)
      rw [ih' (N/2) (by omega) (by omega),ih' (N-N/2) (by omega) (by omega)] at hub
      rw [C.V_rec hn2]
      simpa [show N-N/2=(N+1)/2 by omega] using hub

/-- Theorem 4.1, including the Bellman conclusion for every prescribed horizon. -/
theorem theorem_4_1 (C : CompositionLaw) :
    StrictMono C.V ∧
    (∀ m n : ℕ, C.op (C.V m) (C.V n) ≤ C.V (m+n)) ∧
    (∀ W : ℕ → ℝ, BellmanSpec C.op W → ∀ N : ℕ, 1 ≤ N → W N=C.V N) :=
  ⟨C.V_strictMono,C.supercomposition,C.bellman_unique⟩
end
end GD
