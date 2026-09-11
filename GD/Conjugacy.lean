import GD.RootSplits
import GD.Objective
namespace GD
noncomputable section

def phi (x y : ℝ) := (-x-y+Real.sqrt ((x+y+2)^2+4*(x+1)*(y+1)))/2
def J (a b : ℝ) := 2*a*b/(a+b+Real.sqrt (disc a b))

theorem affine_conjugacy (x y : ℝ) : x+y+phi x y+1=K (x+1) (y+1) := by
  have hd : (x+y+2)^2+4*(x+1)*(y+1)=disc (x+1) (y+1) := by unfold disc; ring
  unfold phi K; rw [hd]; ring

theorem J_as_K {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : J a b=a*b/K a b := by
  have hK : K a b ≠ 0 := (K_pos ha.le hb.le (by linarith)).ne'
  have hs : a+b+Real.sqrt (disc a b) ≠ 0 := by unfold K at hK; exact fun h => hK (by rw [h]; ring)
  unfold J K; field_simp; ring

theorem reciprocal_kernel {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    K (1/x) (1/y)=K x y/(x*y) := by
  have hhom := K_hom (mul_pos hx hy).le (one_div_pos.mpr hx).le (one_div_pos.mpr hy).le
  have h1 : x*y*(1/x)=y := by field_simp
  have h2 : x*y*(1/y)=x := by field_simp
  rw [h1,h2,K_symm y x] at hhom
  apply (eq_div_iff (mul_ne_zero hx.ne' hy.ne')).mpr
  nlinarith only [hhom]

theorem reciprocal_conjugacy {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    J (1/x) (1/y)=1/K x y := by
  rw [J_as_K (one_div_pos.mpr hx) (one_div_pos.mpr hy),reciprocal_kernel hx hy]
  field_simp

def Tree.primitiveSum : Tree → ℝ
  | .leaf => 0
  | .join l r => l.primitiveSum+r.primitiveSum+phi l.primitiveSum r.primitiveSum

def Tree.sRate : Tree → ℝ
  | .leaf => 1
  | .join l r => J l.sRate r.sRate

theorem Tree.value_pos (t : Tree) : 0 < t.value := by
  induction t with
  | leaf => norm_num [value]
  | join l r hl hr => exact K_pos hl.le hr.le (by linarith)

/-- Proposition 2.5's affine identity, for every individual composition tree. -/
theorem Tree.primitive_conjugacy (t : Tree) : t.primitiveSum+1=t.value := by
  induction t with
  | leaf => norm_num [primitiveSum,value]
  | join l r hl hr =>
    change l.primitiveSum+r.primitiveSum+phi l.primitiveSum r.primitiveSum+1=K l.value r.value
    rw [affine_conjugacy,hl,hr]

/-- Proposition 2.5's reciprocal identity, for every individual composition tree. -/
theorem Tree.s_conjugacy (t : Tree) : t.sRate=1/t.value := by
  induction t with
  | leaf => norm_num [sRate,value]
  | join l r hl hr =>
    change J l.sRate r.sRate=1/K l.value r.value
    rw [hl,hr,reciprocal_conjugacy l.value_pos r.value_pos]

/-- Balanced ConPP optimality, in step-count notation n=N-1. -/
theorem theorem_4_5_balanced (n : ℕ) (hn : 1 ≤ n) :
    U (n+1)-1 = (U ((n-1)/2+1)-1)+(U ((n-1+1)/2+1)-1)+
      phi (U ((n-1)/2+1)-1) (U ((n-1+1)/2+1)-1) := by
  have hleft : (n-1)/2+1=(n+1)/2 := by omega
  have hright : (n-1+1)/2+1=(n+2)/2 := by omega
  rw [hleft,hright]
  have h := affine_conjugacy (U ((n+1)/2)-1) (U ((n+2)/2)-1)
  simp only [sub_add_cancel] at h
  rw [← corollary_4_2.2.2 (n+1) (by omega)] at h
  linarith

end
end GD

namespace GD
noncomputable section

def balancedTree (N : ℕ) : Tree :=
  if h : N ≤ 1 then .leaf else .join (balancedTree (N/2)) (balancedTree ((N+1)/2))
termination_by N
 decreasing_by all_goals omega

theorem balancedTree_leaves (N : ℕ) (hN : 1 ≤ N) : (balancedTree N).leaves=N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hn : N ≤ 1
    · have : N=1 := by omega
      subst N; rw [balancedTree]; simp [Tree.leaves]
    · rw [balancedTree,dif_neg hn,Tree.leaves]
      rw [ih (N/2) (by omega) (by omega),ih ((N+1)/2) (by omega) (by omega)]
      omega

theorem balancedTree_value (N : ℕ) (hN : 1 ≤ N) : (balancedTree N).value=U N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hn : N ≤ 1
    · have : N=1 := by omega
      subst N; rw [balancedTree]; simp [Tree.value]
    · rw [balancedTree,dif_neg hn,Tree.value]
      rw [ih (N/2) (by omega) (by omega),ih ((N+1)/2) (by omega) (by omega)]
      exact (corollary_4_2.2.2 N (by omega)).symm

/-- The maximum is attained by a concrete tree, not just an upper bound. -/
theorem primitive_tree_optimum (N : ℕ) (hN : 1 ≤ N) :
    (balancedTree N).leaves=N ∧ (balancedTree N).primitiveSum=U N-1 ∧
    (∀ t : Tree, t.leaves=N → t.primitiveSum ≤ U N-1) := by
  refine ⟨balancedTree_leaves N hN,?_,?_⟩
  · have := (balancedTree N).primitive_conjugacy
    rw [balancedTree_value N hN] at this; linarith
  · intro t ht
    have hval := t.value_le_U
    rw [ht] at hval
    linarith [t.primitive_conjugacy]

theorem s_tree_optimum (N : ℕ) (hN : 1 ≤ N) :
    (balancedTree N).sRate=1/U N ∧
    (∀ t : Tree, t.leaves=N → 1/U N ≤ t.sRate) := by
  constructor
  · rw [Tree.s_conjugacy,balancedTree_value N hN]
  · intro t ht
    rw [Tree.s_conjugacy]
    exact one_div_le_one_div_of_le t.value_pos (by simpa [ht] using t.value_le_U)

/-- Proposition 2.5, scalar identities, attained optima, and the common Bellman law.
Imported convex-optimization closure/certificate theorems are separate inputs
in the manuscript and are not asserted here. -/
theorem proposition_2_5 (N : ℕ) (hN : 1 ≤ N) :
    (balancedTree N).primitiveSum+1=U N ∧
    1/(balancedTree N).sRate=U N ∧
    (∀ t : Tree, t.leaves=N → t.value ≤ U N) ∧
    (2 ≤ N → (∀ m : ℕ, 1 ≤ m → m < N → K (U m) (U (N-m)) ≤ U N) ∧
      ∃ m : ℕ, 1 ≤ m ∧ m < N ∧ U N=K (U m) (U (N-m))) := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [Tree.primitive_conjugacy,balancedTree_value N hN]
  · rw [(s_tree_optimum N hN).1]; simp
  · intro t ht; simpa [ht] using t.value_le_U
  · intro hn
    refine ⟨?_,N/2,by omega,by omega,?_⟩
    · intro m hm hmN; simpa [Nat.add_sub_of_le hmN.le] using corollary_4_2.2.1 m (N-m)
    · rw [corollary_4_2.2.2 N hn,show N-N/2=(N+1)/2 by omega]

/-- The three and only three tied splits at even nondyadic leaf counts. -/
theorem theorem_4_5_ties (nu l m : ℕ) (hodd : nu%2=1) (hnu : 1 < nu)
    (hm : 1 ≤ m) (hmN : m < nu*2^(l+1)) :
    OptimalSplit (nu*2^(l+1)) m ↔
      m=(nu-1)*2^l ∨ m=nu*2^l ∨ m=(nu+1)*2^l := by
  rw [corollary_4_4 nu (l+1) m hodd hm hmN]
  have hmid : 2*m=nu*2^(l+1) ↔ m=nu*2^l := by
    rw [pow_succ]; constructor <;> intro h <;> nlinarith
  have hleft : 2^(l+1)*((nu-1)/2)=(nu-1)*2^l := by
    have hv : 2*((nu-1)/2)=nu-1 := by omega
    calc 2^(l+1)*((nu-1)/2)=2^l*(2*((nu-1)/2)) := by rw [pow_succ]; ring
         _ = (nu-1)*2^l := by rw [hv]; ring
  have hright : 2^(l+1)*((nu+1)/2)=(nu+1)*2^l := by
    have hv : 2*((nu+1)/2)=nu+1 := by omega
    calc 2^(l+1)*((nu+1)/2)=2^l*(2*((nu+1)/2)) := by rw [pow_succ]; ring
         _ = (nu+1)*2^l := by rw [hv]; ring
  rw [hmid,hleft,hright]
  simp only [hnu,true_and]
  tauto

end
end GD

namespace GD
noncomputable section

def mu (a b : ℝ) : ℝ := 1+(Real.sqrt (disc a b)-(a+b))/(2*a*b)

theorem mu_via_K {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    mu a b=1+(K a b-a-b)/(a*b) := by
  unfold mu K
  field_simp
  ring

/-- Equality of the numerical joining steps, not just of optimal scalar rates. -/
theorem join_step_conjugacy {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    mu (1/(x+1)) (1/(y+1))=phi x y := by
  have hxp : 0 < x+1 := by linarith
  have hyp : 0 < y+1 := by linarith
  rw [mu_via_K (one_div_pos.mpr hxp) (one_div_pos.mpr hyp),reciprocal_kernel hxp hyp]
  have h := affine_conjugacy x y
  have hs : 1+(K (x+1) (y+1)/((x+1)*(y+1))-1/(x+1)-1/(y+1))/
      ((1/(x+1))*(1/(y+1)))=K (x+1) (y+1)-x-y-1 := by
    field_simp
    ring
  rw [hs]
  linarith
end
end GD
