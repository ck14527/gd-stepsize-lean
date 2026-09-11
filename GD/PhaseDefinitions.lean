import GD.Asymmetric

/-! Actual real-valued sequences and canonical candidates; no analytic claims. -/
namespace GD
noncomputable section
open Set Filter
open scoped Topology

def p : ℝ := Real.log rho / Real.log 2
def q : ℝ := 1/p

def W (N : ℕ) : ℝ :=
  if h : N ≤ 1 then N else
    (List.ofFn (fun i : Fin (N-1) => A (U (i.val+1)) (W (N-(i.val+1))))).foldr max 0
termination_by N
 decreasing_by all_goals omega

def s (N : ℕ) : ℝ := 1/U N
def etaF (N : ℕ) : ℝ := 1/W N
def B (N : ℕ) : ℝ := 1/(2*U N-1)
def C (N : ℕ) : ℝ := (N:ℝ)^p * etaF N

def IsDyadic (x : ℝ) : Prop := ∃ k j : ℕ, x=(j:ℝ)/(2:ℝ)^k

def F (x : ℝ) : ℝ := sSup {y : ℝ | ∃ k j : ℕ,
  2^k ≤ j ∧ j ≤ 2^(k+1) ∧ (j:ℝ)/(2:ℝ)^k ≤ x ∧ y=U j/rho^k}

def InterpolationMatches (G : ℝ → ℝ) : Prop := ∀ k j : ℕ,
  2^k ≤ j → j ≤ 2^(k+1) → G ((j:ℝ)/(2:ℝ)^k)=U j/rho^k

def phase (N : ℕ) : ℝ := Int.fract (Real.log (N:ℝ)/Real.log 2)
def Phi (t : ℝ) : ℝ := rho^(-Int.fract t)*F ((2:ℝ)^(Int.fract t))
def phiMin : ℝ := sInf (Phi '' Icc 0 1)
def cminus : ℝ := (rho-1)*(1-1/(2*rho))
def cplus : ℝ := (rho-1)*Real.exp (1/(2*rho))

def PeriodicLipschitzPositive (g : ℝ → ℝ) : Prop :=
  (∀ t, 0 < g t) ∧ (∀ t, g (t+1)=g t) ∧
  ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, |g x-g y| ≤ L*|x-y|

def Clust (a : ℕ → ℝ) : Set ℝ := {l | ∃ ns : ℕ → ℕ,
  StrictMono ns ∧ Tendsto (fun j => a (ns j)) atTop (𝓝 l)}

def R (N : ℕ) : ℝ := U (N+1)/U N
def T0 (r : ℝ) : ℝ := K 1 r/rho
def T1 (r : ℝ) : ℝ := rho*r/K 1 r

def w0 (r : ℝ) : ℝ := if r=1 then 1 else 2*(T0 r-1)/(r-1)
def w1 (r : ℝ) : ℝ := if r=1 then 1 else 2*(r-T0 r)/(r-1)

def lowerGrid (k : ℕ) : ℝ := sInf {z | ∃ j : ℕ,
  2^k ≤ j ∧ j < 2^(k+1) ∧ z=U j/((j+1:ℕ):ℝ)^p}
def upperGrid (k : ℕ) : ℝ := sInf {z | ∃ j : ℕ,
  2^k ≤ j ∧ j ≤ 2^(k+1) ∧ z=U j/(j:ℝ)^p}

def xi : ℝ := sInf {x : ℝ | x ∈ Ioo 0 1 ∧ x^(2*q-1)*(2-x)=1}
def tau : ℝ := (1-xi)/(2*xi^2)
def Bsup : ℝ := (2:ℝ)^q*(1-xi^(2*q))/(1-xi)^q
def cstar : ℝ := Bsup^(-p)
def alpha : ℝ := Bsup*tau^q/(1+Bsup*tau^q)
def sigma (u w : ℝ) : ℝ := Bsup*u^q+w^q-(A u w)^q
def deficit (N : ℕ) : ℝ := Bsup*(N:ℝ)-(W N)^q

def OBSPhase (g : ℝ → ℝ) : Prop :=
  PeriodicLipschitzPositive g ∧
  ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
    ∀ N : ℕ, 2^k ≤ N → N ≤ 2^(k+1) → |C N-g (phase N)| < eps

def Psi : ℝ → ℝ := fun t => limUnder atTop
  (fun k : ℕ => C (Nat.floor ((2:ℝ)^((k:ℝ)+Int.fract t))))

end
end GD
