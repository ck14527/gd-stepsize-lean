import GD.RootSplits
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace GD
noncomputable section
open Finset

def Tree.joinEmbedding : Tree × Tree ↪ Tree where
  toFun t := .join t.1 t.2
  inj' := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    cases h
    rfl

/-- Explicit finite enumeration; its mathematical meaning is proved below. -/
def optimalTrees (N : ℕ) : Finset Tree := by
  classical
  exact if N=1 then {Tree.leaf} else
    (Finset.range (N-1)).biUnion (fun i =>
      if hs : OptimalSplit N (i+1) then
        ((optimalTrees (i+1)).product (optimalTrees (N-(i+1)))).map Tree.joinEmbedding
      else ∅)
termination_by N
decreasing_by all_goals simp_wf; have := hs.2.1; omega

theorem mem_optimalTrees (N : ℕ) (t : Tree) :
    t ∈ optimalTrees N ↔ t.leaves=N ∧ t.value=U N := by
  classical
  induction N using Nat.strong_induction_on generalizing t with
  | h N ih =>
    by_cases hn : N=1
    · subst N
      rw [optimalTrees.eq_def]
      simp only [ite_true,Finset.mem_singleton]
      cases t with
      | leaf => simp [Tree.leaves,Tree.value]
      | join l r =>
        have hl := l.leaves_pos
        have hr := r.leaves_pos
        constructor
        · intro hh; cases hh
        · rintro ⟨hh,_⟩
          change l.leaves+r.leaves=1 at hh
          omega
    · rw [optimalTrees.eq_def,if_neg hn,Finset.mem_biUnion]
      constructor
      · rintro ⟨i,hi,ht⟩
        have hin : i+1 < N := by simp only [Finset.mem_range] at hi; omega
        have hir : N-(i+1) < N := by omega
        split_ifs at ht with hs
        · obtain ⟨ab,hab,rfl⟩ := Finset.mem_map.mp ht
          obtain ⟨hl,hr⟩ := Finset.mem_product.mp hab
          obtain ⟨hlN,hlv⟩ := (ih (i+1) hin ab.1).mp hl
          obtain ⟨hrN,hrv⟩ := (ih (N-(i+1)) hir ab.2).mp hr
          constructor
          · change ab.1.leaves+ab.2.leaves=N
            omega
          · change K ab.1.value ab.2.value=U N
            rw [hlv,hrv]
            exact hs.2.2
        · simp at ht
      · rintro ⟨htN,htv⟩
        cases t with
        | leaf => exact False.elim (hn (by simpa [Tree.leaves] using htN.symm))
        | join l r =>
          have hl := l.leaves_pos
          have hr := r.leaves_pos
          change l.leaves+r.leaves=N at htN
          have hlN : l.leaves < N := by omega
          have hrN : r.leaves < N := by omega
          have hv : (Tree.join l r).value=U (l.leaves+r.leaves) := by simpa [htN] using htv
          obtain ⟨hlv,hrv,hs⟩ := (Tree.root_optimal_iff l r).mp hv
          refine ⟨l.leaves-1,by simp; omega,?_⟩
          have hidx : l.leaves-1+1=l.leaves := by omega
          have hrem : N-l.leaves=r.leaves := by omega
          rw [hidx]
          have hp : OptimalSplit N l.leaves := ⟨hl,hlN,by simpa [hrem,htN] using hs⟩
          rw [dif_pos hp]
          apply Finset.mem_map.mpr
          refine ⟨(l,r),?_,rfl⟩
          apply Finset.mem_product.mpr
          constructor
          · exact (ih l.leaves hlN l).mpr ⟨rfl,hlv⟩
          · rw [hrem]
            exact (ih r.leaves hrN r).mpr ⟨rfl,hrv⟩

def T (N : ℕ) : ℕ := (optimalTrees N).card

def optimalSplitSet (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (OptimalSplit N)

theorem mem_optimalSplitSet (N m : ℕ) :
    m ∈ optimalSplitSet N ↔ OptimalSplit N m := by
  classical
  simp only [optimalSplitSet,Finset.mem_filter,Finset.mem_range]
  exact ⟨fun h => h.2,fun h => ⟨h.2.1,h⟩⟩

@[simp] theorem T_one : T 1=1 := by
  simp [T,optimalTrees]

def rootTrees (N m : ℕ) : Finset Tree :=
  ((optimalTrees m).product (optimalTrees (N-m))).map Tree.joinEmbedding

theorem mem_rootTrees (N m : ℕ) (t : Tree) :
    t ∈ rootTrees N m ↔ ∃ l r : Tree,
      l ∈ optimalTrees m ∧ r ∈ optimalTrees (N-m) ∧ t=Tree.join l r := by
  classical
  rw [rootTrees,Finset.mem_map]
  constructor
  · rintro ⟨⟨l,r⟩,hab,he⟩
    obtain ⟨hl,hr⟩ := Finset.mem_product.mp hab
    exact ⟨l,r,hl,hr,he.symm⟩
  · rintro ⟨l,r,hl,hr,rfl⟩
    exact ⟨(l,r),Finset.mem_product.mpr ⟨hl,hr⟩,rfl⟩

theorem optimalTrees_root_union (N : ℕ) (hN : 2 ≤ N) :
    optimalTrees N=(optimalSplitSet N).biUnion (rootTrees N) := by
  classical
  ext t
  rw [mem_optimalTrees,Finset.mem_biUnion]
  constructor
  · rintro ⟨hl,hv⟩
    cases t with
    | leaf => simp only [Tree.leaves] at hl; omega
    | join l r =>
      change l.leaves+r.leaves=N at hl
      have ht : (Tree.join l r).value=U (l.leaves+r.leaves) := by simpa [hl] using hv
      obtain ⟨hvl,hvr,hs⟩ := (Tree.root_optimal_iff l r).mp ht
      have hsub : N-l.leaves=r.leaves := by omega
      refine ⟨l.leaves,(mem_optimalSplitSet _ _).mpr ?_,(mem_rootTrees _ _ _).mpr ?_⟩
      · exact ⟨l.leaves_pos,by have := r.leaves_pos; omega,by simpa [hsub,hl] using hs⟩
      · refine ⟨l,r,(mem_optimalTrees _ _).mpr ⟨rfl,hvl⟩,?_,rfl⟩
        rw [hsub]
        exact (mem_optimalTrees _ _).mpr ⟨rfl,hvr⟩
  · rintro ⟨m,hm,ht⟩
    have hp := (mem_optimalSplitSet _ _).mp hm
    obtain ⟨l,r,hl,hr,rfl⟩ := (mem_rootTrees _ _ _).mp ht
    obtain ⟨hlN,hlv⟩ := (mem_optimalTrees _ _).mp hl
    obtain ⟨hrN,hrv⟩ := (mem_optimalTrees _ _).mp hr
    constructor
    · change l.leaves+r.leaves=N
      have := hp.2.1
      omega
    · change K l.value r.value=U N
      rw [hlv,hrv]
      exact hp.2.2

theorem rootTrees_disjoint (N m n : ℕ) (hmn : m ≠ n) :
    Disjoint (rootTrees N m) (rootTrees N n) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t hm hn
  obtain ⟨l,r,hl,hr,rfl⟩ := (mem_rootTrees _ _ _).mp hm
  obtain ⟨l',r',hl',hr',he⟩ := (mem_rootTrees _ _ _).mp hn
  have hll : l=l' := (Tree.join.inj he).1
  have h1 := ((mem_optimalTrees _ _).mp hl).1
  have h2 := ((mem_optimalTrees _ _).mp hl').1
  rw [hll] at h1
  exact hmn (h1.symm.trans h2)

theorem T_recurrence (N : ℕ) (hN : 2 ≤ N) :
    T N=∑ m ∈ optimalSplitSet N, T m*T (N-m) := by
  classical
  unfold T
  rw [optimalTrees_root_union N hN]
  rw [Finset.card_biUnion (by
    intro m hm n hn hmn
    exact rootTrees_disjoint N m n hmn)]
  apply Finset.sum_congr rfl
  intro m hm
  simp [rootTrees]

theorem optimalSplitSet_dyadic (k : ℕ) :
    optimalSplitSet (2^(k+1))={2^k} := by
  classical
  ext m
  rw [mem_optimalSplitSet,Finset.mem_singleton]
  have hp : 0 < 2^k := by positivity
  have hpow : 2^(k+1)=2*2^k := by rw [pow_succ]; ring
  constructor
  · intro h
    have hc := (corollary_4_4 1 (k+1) m (by norm_num) h.1 (by simpa using h.2.1)).mp (by simpa using h)
    simp only [one_mul,lt_self_iff_false,false_and,or_false] at hc
    omega
  · intro hm
    subst m
    refine ⟨hp,by omega,?_⟩
    rw [hpow,show 2*2^k-2^k=2^k by omega]
    simpa [two_mul] using equal_children (2^k)

theorem T_dyadic (k : ℕ) : T (2^k)=1 := by
  induction k with
  | zero => simpa using T_one
  | succ k ih =>
    have hp : 1 ≤ 2^k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [T_recurrence _ (by rw [pow_succ]; omega),optimalSplitSet_dyadic]
    simp only [Finset.sum_singleton]
    have hs : 2^(k+1)-2^k=2^k := by rw [pow_succ]; omega
    rw [hs,ih]

theorem optimalSplitSet_odd (n : ℕ) (hn : 1 ≤ n) :
    optimalSplitSet (2*n+1)={n,n+1} := by
  classical
  ext m
  rw [mem_optimalSplitSet]
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro h
    have hc := (corollary_4_4 (2*n+1) 0 m (by omega) h.1 (by simpa using h.2.1)).mp (by simpa using h)
    norm_num at hc
    omega
  · intro h
    have hm : 1 ≤ m := by omega
    have hmN : m < 2*n+1 := by omega
    have hc := (corollary_4_4 (2*n+1) 0 m (by omega) hm (by simpa using hmN))
    simp only [pow_zero,mul_one] at hc
    apply hc.mpr
    right
    constructor
    · omega
    · norm_num
      omega

theorem T_odd (n : ℕ) (hn : 1 ≤ n) :
    T (2*n+1)=2*T n*T (n+1) := by
  classical
  rw [T_recurrence _ (by omega),optimalSplitSet_odd n hn]
  rw [Finset.sum_pair (by omega : n ≠ n+1)]
  rw [show 2*n+1-n=n+1 by omega,show 2*n+1-(n+1)=n by omega]
  ring

theorem optimalSplitSet_even_odd_part (n k : ℕ) (hn : 1 ≤ n) :
    optimalSplitSet ((2*n+1)*2^(k+1))=
      {2^(k+1)*n,2^k*(2*n+1),2^(k+1)*(n+1)} := by
  classical
  have hp : 0 < 2^k := by positivity
  have he : 2^(k+1)=2*2^k := by rw [pow_succ]; ring
  have hab : 2^(k+1)*n < 2^k*(2*n+1) := by rw [he]; nlinarith
  have hbc : 2^k*(2*n+1) < 2^(k+1)*(n+1) := by rw [he]; nlinarith
  have hsum : 2^(k+1)*n+2^(k+1)*(n+1)=(2*n+1)*2^(k+1) := by ring
  have hbal : 2*(2^k*(2*n+1))=(2*n+1)*2^(k+1) := by rw [he]; ring
  have ha0 : 1 ≤ 2^(k+1)*n := by
    have : 0 < 2^(k+1)*n := by positivity
    omega
  have hdiv : (2*n+1+1)/2=n+1 := by omega
  ext m
  rw [mem_optimalSplitSet]
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro h
    have hc := (corollary_4_4 (2*n+1) (k+1) m (by omega) h.1 h.2.1).mp h
    norm_num at hc
    rw [hdiv] at hc
    omega
  · intro h
    have hm : 1 ≤ m := by omega
    have hmN : m < (2*n+1)*2^(k+1) := by omega
    apply (corollary_4_4 (2*n+1) (k+1) m (by omega) hm hmN).mpr
    norm_num
    rw [hdiv]
    omega

theorem T_even_odd_part (n k : ℕ) (hn : 1 ≤ n) :
    T ((2*n+1)*2^(k+1))=
      2*T (2^(k+1)*n)*T (2^(k+1)*(n+1))+(T (2^k*(2*n+1)))^2 := by
  classical
  have hp : 0 < 2^k := by positivity
  have he : 2^(k+1)=2*2^k := by rw [pow_succ]; ring
  have hab : 2^(k+1)*n < 2^k*(2*n+1) := by rw [he]; nlinarith
  have hbc : 2^k*(2*n+1) < 2^(k+1)*(n+1) := by rw [he]; nlinarith
  have hsum : 2^(k+1)*n+2^(k+1)*(n+1)=(2*n+1)*2^(k+1) := by ring
  have hbal : 2*(2^k*(2*n+1))=(2*n+1)*2^(k+1) := by rw [he]; ring
  have ha0 : 1 ≤ 2^(k+1)*n := by
    have : 0 < 2^(k+1)*n := by positivity
    omega
  rw [T_recurrence _ (by omega),optimalSplitSet_even_odd_part n k hn]
  have hnot : 2^(k+1)*n ∉ ({2^k*(2*n+1),2^(k+1)*(n+1)} : Finset ℕ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  rw [Finset.sum_insert hnot,Finset.sum_pair hbc.ne]
  rw [show (2*n+1)*2^(k+1)-2^(k+1)*n=2^(k+1)*(n+1) by omega,
      show (2*n+1)*2^(k+1)-2^k*(2*n+1)=2^k*(2*n+1) by omega,
      show (2*n+1)*2^(k+1)-2^(k+1)*(n+1)=2^(k+1)*n by omega]
  ring

/-- Theorem B.1: actual finite tree counts, recurrence, and all three cases.
The odd factor is written 2*n+1; the positive dyadic valuation is k+1. -/
theorem theorem_B_1 :
    T 1=1 ∧
    (∀ N : ℕ, 2 ≤ N → T N=∑ m ∈ optimalSplitSet N, T m*T (N-m)) ∧
    (∀ k : ℕ, T (2^k)=1) ∧
    (∀ n : ℕ, 1 ≤ n → T (2*n+1)=2*T n*T (n+1)) ∧
    (∀ n k : ℕ, 1 ≤ n → T ((2*n+1)*2^(k+1))=
      2*T (2^(k+1)*n)*T (2^(k+1)*(n+1))+(T (2^k*(2*n+1)))^2) :=
  ⟨T_one,T_recurrence,T_dyadic,T_odd,T_even_odd_part⟩

end
end GD
