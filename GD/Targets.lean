import GD.PhaseDefinitions

/-! ANALYTICAL STATEMENT REGISTRY. These proposition definitions are NOT theorem
proofs, assumptions or axioms. Separate theorem declarations now prove many
of these targets; see audit/coverage.json for exact scope. -/
namespace GD
noncomputable section
open Set Filter
open scoped Topology

namespace Targets

/-- Full real inequality and equality cases of Lemma 5.1. -/
def lemma_5_1 : Prop := ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
  K x y ≤ (x^q+y^q)^(1/q) ∧ (K x y=(x^q+y^q)^(1/q) ↔ x=y ∨ x*y=0)

def proposition_5_2 : Prop := ∀ N : ℕ, 1 ≤ N →
  U N ≤ (N:ℝ)^p ∧ (U N=(N:ℝ)^p ↔ ∃ k : ℕ, N=2^k)

/-- N.log2 is the natural floor-logarithm. -/
def lemma_5_3 : Prop := ∀ N : ℕ, 1 ≤ N →
  R (2*N)=T0 (R N) ∧ R (2*N+1)=T1 (R N) ∧
  1 < R N ∧ R N ≤ rho ∧ R N-1 ≤ (rho-1)/(2:ℝ)^(N.log2) ∧
  (rho-1)/(2:ℝ)^(N.log2) ≤ 2*(rho-1)/(N:ℝ)

def theorem_5_4 : Prop :=
  InterpolationMatches F ∧ F 1=1 ∧ F 2=rho ∧
  ContinuousOn F (Icc 1 2) ∧ F '' Icc 1 2=Icc 1 rho ∧
  (∀ x y : ℝ, 1 ≤ x → x < y → y ≤ 2 →
    cminus*(y-x) ≤ F y-F x ∧ F y-F x ≤ cplus*(y-x)) ∧
  (∀ G : ℝ → ℝ, ContinuousOn G (Icc 1 2) → InterpolationMatches G → EqOn G F (Icc 1 2)) ∧
  (∀ k j : ℕ, 2^k ≤ j → j < 2^(k+1) →
    F (((j:ℝ)+1/2)/(2:ℝ)^k)=K (F ((j:ℝ)/(2:ℝ)^k)) (F (((j:ℝ)+1)/(2:ℝ)^k))/rho)

def theorem_5_5 : Prop :=
  PeriodicLipschitzPositive Phi ∧
  (∀ N : ℕ, 1 ≤ N → U N=(N:ℝ)^p*Phi (phase N)) ∧
  (∀ G : ℝ → ℝ, Continuous G → (∀ t, G (t+1)=G t) →
    (∀ N : ℕ, 1 ≤ N → U N=(N:ℝ)^p*G (phase N)) → G=Phi) ∧
  0 < phiMin ∧ phiMin < 1 ∧ sSup (Phi '' Icc 0 1)=1 ∧
  (∀ x y : ℝ, |Phi x-Phi y| ≤ (2*Real.log 2*cplus+rho*Real.log rho)*|x-y|)

def corollary_5_7 : Prop :=
  Clust (fun N : ℕ => U N/(N:ℝ)^p)=Icc phiMin 1 ∧
  Clust (fun N : ℕ => (N:ℝ)^p*s N)=Icc 1 (1/phiMin) ∧
  ¬(∃ l, Tendsto (fun N : ℕ => U N/(N:ℝ)^p) atTop (𝓝 l)) ∧
  ¬(∃ l, Tendsto (fun N : ℕ => (N:ℝ)^p*s N) atTop (𝓝 l))

/-- Explicit remainder bound implies the uniform big-O statement. -/
def theorem_5_8_scalar : Prop :=
  (∀ N : ℕ, 1 ≤ N → B N=1/(2*(N:ℝ)^p*Phi (phase N)-1)) ∧
  (∀ N : ℕ, 1 ≤ N → 0 < B N-(N:ℝ)^(-p)/(2*Phi (phase N)) ∧
    B N-(N:ℝ)^(-p)/(2*Phi (phase N)) ≤ (N:ℝ)^(-2*p)/(2*phiMin^2)) ∧
  Clust (fun N : ℕ => (N:ℝ)^p*B N)=Icc (1/2) (1/(2*phiMin))

def proposition_6_2 : Prop :=
  (∀ N : ℕ, 1 ≤ N → 2*U N-1 ≤ W N ∧ W N ≤ rho*U N) ∧
  (∀ m : ℕ, 1 ≤ m → ∃ c : ℝ,
    Tendsto (fun k : ℕ => C (m*2^k)) atTop (𝓝 c) ∧
    1/(rho*Phi (phase m)) ≤ c ∧ c ≤ 1/(2*Phi (phase m)))

/-- Block uniformity, uniqueness and cluster interval; the explicit linear
interpolants are included in the full target in OBSInterpolation.lean. -/
def theorem_6_3_block_version : Prop :=
  OBSPhase Psi ∧ (∀ G : ℝ → ℝ, OBSPhase G → G=Psi) ∧
  Clust C=Icc (sInf (Psi '' Icc 0 1)) (sSup (Psi '' Icc 0 1))

def lemma_6_4 : Prop :=
  xi ∈ Ioo 0 1 ∧ xi^(2*q-1)*(2-xi)=1 ∧
  (∀ x : ℝ, x ∈ Ioo 0 1 → x^(2*q-1)*(2-x)=1 → x=xi) ∧
  (2:ℝ)^q < Bsup ∧
  (∀ u w : ℝ, 0 ≤ u → 0 ≤ w → (A u w)^q ≤ Bsup*u^q+w^q) ∧
  (∀ u w : ℝ, 0 < u → 0 < w → ((A u w)^q=Bsup*u^q+w^q ↔ u/w=tau)) ∧
  (∀ w : ℝ, 0 ≤ w → (A 0 w)^q=w^q) ∧
  (∀ u : ℝ, 0 < u → (A u 0)^q < Bsup*u^q)

def theorem_6_5 : Prop :=
  cstar < sInf (Psi '' Icc 0 1) ∧
  sInf (Psi '' Icc 0 1) < sSup (Psi '' Icc 0 1) ∧
  sSup (Psi '' Icc 0 1) ≤ cstar/phiMin

/-- C.1's regularity component. The full target is in DerivativeTheorem.lean. -/
def theorem_C_1_regularity_part : Prop :=
  ∃ D : ℝ → ℝ, (∀ x ∈ Icc (1:ℝ) 2, cminus ≤ D x ∧ D x ≤ cplus) ∧
    (∀ x ∈ Ioo (1:ℝ) 2, ¬IsDyadic x → ContinuousAt D x ∧ HasDerivAt F (D x) x) ∧
    (∀ x ∈ Ioo (1:ℝ) 2, IsDyadic x →
      ∃ dl dr : ℝ, HasDerivWithinAt F dl (Iic x) x ∧ HasDerivWithinAt F dr (Ici x) x)

def corollary_C_2 : Prop := ∃ dl dr : ℝ,
  HasDerivWithinAt F dl (Iic (3/2)) (3/2) ∧
  HasDerivWithinAt F dr (Ici (3/2)) (3/2) ∧ dr < dl ∧ ¬DifferentiableAt ℝ F (3/2)

def theorem_C_3_bounds : Prop :=
  (∀ k : ℕ, lowerGrid k ≤ phiMin ∧ phiMin ≤ upperGrid k ∧
    0 ≤ upperGrid k-lowerGrid k ∧ upperGrid k-lowerGrid k ≤ p/(2:ℝ)^k) ∧
  Monotone lowerGrid ∧ Antitone upperGrid ∧
  Tendsto lowerGrid atTop (𝓝 phiMin) ∧ Tendsto upperGrid atTop (𝓝 phiMin)

def lemma_D_2 : Prop := ∀ LF : ℝ,
  (∀ x y : ℝ, x ∈ Icc (1:ℝ) 2 → y ∈ Icc (1:ℝ) 2 → |F x-F y| ≤ LF*|x-y|) →
  let LU := max 1 LF
  (∀ m : ℕ, 1 ≤ m → 0 < U m-U (m-1) ∧ U m-U (m-1) ≤ LU*(m:ℝ)^(p-1)) ∧
  (∀ N : ℕ, 1 ≤ N → 0 < W (N+1)-W N ∧ W (N+1)-W N ≤ 4*LU*(N:ℝ)^(p-1)) ∧
  (∀ N : ℕ, 1 ≤ N → |C (N+1)-C N| ≤ (4*LU+rho*p)/(phiMin^2*(N:ℝ)))

def proposition_D_3 : Prop :=
  (∀ N : ℕ, 1 ≤ N → (W N)^q ≤ Bsup*(N:ℝ) ∧ cstar ≤ C N) ∧
  (∀ N m : ℕ, 1 ≤ m → m < N → W N=A (U m) (W (N-m)) →
    deficit N=Bsup*((m:ℝ)-(U m)^q)+deficit (N-m)+sigma (U m) (W (N-m)) ∧
    0 ≤ Bsup*((m:ℝ)-(U m)^q) ∧ 0 ≤ deficit (N-m) ∧ 0 ≤ sigma (U m) (W (N-m)))

def lemma_D_4 : Prop := (∀ x ∈ Ioo (1:ℝ) 2, F x < x^p) ∧
  (∀ t ∈ Ioo (0:ℝ) 1, Phi t < 1)

def lemma_D_5 : Prop := alpha=1-xi^(2*q) ∧ 1-alpha=xi^(2*q) ∧
  1/4 < 1-alpha ∧ 1-alpha < 1/2 ∧ 1/2 < alpha ∧ alpha < 1

def theorem_D_6 : Prop := ∃ c : ℝ,
  Tendsto (fun k : ℕ => C (2^k)) atTop (𝓝 c) ∧ cstar < c

def lemma_D_7 : Prop := ∀ c : ℝ, (∀ t : ℝ, Psi t=c) → c=cstar

def theorem_D_8 : Prop := (∀ t : ℝ, cstar < Psi t) ∧ cstar < sInf (Psi '' Icc 0 1)

def proposition_D_9 : Prop := ∀ t : ℝ, Psi t ≤ cstar/phiMin

end Targets
end
end GD
