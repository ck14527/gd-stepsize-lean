import GD.RayLimits
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace GD
noncomputable section
open Set

theorem dyadic_grid_order (j k n l : ℕ)
    (h : (j:ℝ)/(2:ℝ)^k ≤ (n:ℝ)/(2:ℝ)^l) :
    U j/rho^k ≤ U n/rho^l := by
  have hrho := rho_pos
  have hc : (j:ℝ)*(2:ℝ)^l ≤ (n:ℝ)*(2:ℝ)^k :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mp h
  have hi : 2^l*j ≤ 2^k*n := by
    have hreal : (2:ℝ)^l*(j:ℝ) ≤ (2:ℝ)^k*(n:ℝ) := by nlinarith
    exact_mod_cast hreal
  have hu := U_strictMono.monotone hi
  rw [U_dyadic,U_dyadic] at hu
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- The actual supremum candidate interpolates every prescribed grid value. -/
theorem F_grid (k j : ℕ) (hlo : 2^k ≤ j) (hhi : j ≤ 2^(k+1)) :
    F ((j:ℝ)/(2:ℝ)^k)=U j/rho^k := by
  let S : Set ℝ := {y | ∃ k' j' : ℕ,
    2^k' ≤ j' ∧ j' ≤ 2^(k'+1) ∧
    (j':ℝ)/(2:ℝ)^k' ≤ (j:ℝ)/(2:ℝ)^k ∧ y=U j'/rho^k'}
  have hm : U j/rho^k ∈ S := ⟨k,j,hlo,hhi,le_rfl,rfl⟩
  have hb : ∀ y ∈ S, y ≤ U j/rho^k := by
    rintro y ⟨k',j',_,_,he,rfl⟩
    exact dyadic_grid_order j' k' j k he
  change sSup S=U j/rho^k
  exact le_antisymm (csSup_le ⟨_,hm⟩ hb) (le_csSup ⟨_,hb⟩ hm)

theorem F_interpolation_matches : InterpolationMatches F := F_grid

@[simp] theorem F_one : F 1=1 := by
  have h := F_grid 0 1 (by norm_num) (by norm_num)
  simpa using h

@[simp] theorem F_two : F 2=rho := by
  have h := F_grid 0 2 (by norm_num) (by norm_num)
  have hu : U 2=rho := by simpa using U_even 1
  simpa [hu] using h

theorem phase_floor (N : ℕ) :
    phase N=Real.logb 2 (N:ℝ)-(N.log2:ℝ) := by
  have hf : ⌊Real.logb 2 (N:ℝ)⌋=(N.log2:ℤ) := by
    simpa [Int.log_natCast,Nat.log2_eq_log_two] using
      (Real.floor_logb_natCast (b:=2) (Nat.cast_nonneg N))
  change Int.fract (Real.logb 2 (N:ℝ))=_
  rw [Int.fract,hf,Int.cast_natCast]

theorem phase_mantissa (N : ℕ) (hN : 1 ≤ N) :
    (2:ℝ)^(phase N)=(N:ℝ)/(2:ℝ)^N.log2 := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  rw [phase_floor,Real.rpow_sub (by norm_num),Real.rpow_natCast,
    Real.rpow_logb (by norm_num) (by norm_num) hn]

theorem rho_logb (x : ℝ) (hx : 0 < x) : rho^(Real.logb 2 x)=x^p := by
  calc rho^(Real.logb 2 x) = ((2:ℝ)^p)^(Real.logb 2 x) := by rw [two_rpow_p]
       _ = ((2:ℝ)^(Real.logb 2 x))^p := by
         rw [← Real.rpow_mul (by norm_num),mul_comm p,Real.rpow_mul (by norm_num)]
       _ = x^p := by rw [Real.rpow_logb (by norm_num) (by norm_num) hx]

theorem rho_phase (N : ℕ) (hN : 1 ≤ N) :
    rho^(phase N)=(N:ℝ)^p/rho^N.log2 := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  rw [phase_floor,Real.rpow_sub rho_pos,rho_logb _ hn,Real.rpow_natCast]

/-- Exact phase identity, independently of the pending regularity results. -/
theorem U_phase_exact (N : ℕ) (hN : 1 ≤ N) : U N=(N:ℝ)^p*Phi (phase N) := by
  have hrho := rho_pos
  have hn : N ≠ 0 := by omega
  have hnp : (0:ℝ) < N := by exact_mod_cast hN
  have hp : 0 < (N:ℝ)^p := Real.rpow_pos_of_pos hnp p
  have hf : Int.fract (phase N)=phase N := Int.fract_fract _
  rw [Phi,hf,phase_mantissa N hN,
    F_grid N.log2 N (Nat.log2_self_le hn) (Nat.lt_log2_self.le),
    Real.rpow_neg rho_pos.le,rho_phase N hN]
  field_simp
  <;> ring

theorem Phi_seed (N : ℕ) (hN : 1 ≤ N) : Phi (phase N)=U N/(N:ℝ)^p := by
  have hp : 0 < (N:ℝ)^p := Real.rpow_pos_of_pos (by exact_mod_cast hN) p
  apply (eq_div_iff hp.ne').mpr
  nlinarith [U_phase_exact N hN]

end
end GD
