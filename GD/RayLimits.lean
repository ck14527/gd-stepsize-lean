import GD.AsymmetricBounds
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic

namespace GD
noncomputable section
open Set Filter
open scoped Topology

theorem p_pos : 0 < p := by
  exact div_pos (Real.log_pos (by linarith [rho_gt_two])) (Real.log_pos (by norm_num))

theorem q_pos : 0 < q := by unfold q; exact one_div_pos.mpr p_pos

theorem p_mul_q : p*q=1 := by unfold q; exact mul_one_div_cancel p_pos.ne'

theorem two_rpow_p : (2:ℝ)^p=rho := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [p]
  have he : Real.log 2*(Real.log rho/Real.log 2)=Real.log rho := by field_simp
  rw [he,Real.exp_log rho_pos]

theorem nat_dyadic_rpow (m k : ℕ) :
    ((m*2^k:ℕ):ℝ)^p=(m:ℝ)^p*rho^k := by
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [Real.mul_rpow (Nat.cast_nonneg m) (by positivity)]
  rw [← Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2),two_rpow_p]

theorem A_hom {t u w : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (hw : 0 ≤ w) :
    A (t*u) (t*w)=t*A u w := by
  have hd : (t*w)^2+8*(t*u)*(t*w)=t^2*(w^2+8*u*w) := by ring
  unfold A
  rw [hd,Real.sqrt_mul (sq_nonneg t),Real.sqrt_sq ht]
  ring

theorem W_pos (N : ℕ) (hN : 1 ≤ N) : 0 < W N := by
  have := (W_sandwich N hN).1
  have := U_ge_one N hN
  linarith

/-- A bound on every admissible pivot bounds the maximum in the actual recursion. -/
theorem W_upper_of_pivots (N : ℕ) (hN : 2 ≤ N) (b : ℝ) (hb : 0 ≤ b)
    (hp : ∀ m : ℕ, 1 ≤ m → m < N → A (U m) (W (N-m)) ≤ b) : W N ≤ b := by
  rw [W.eq_def N,dif_neg (by omega : ¬N ≤ 1)]
  apply foldr_max_upper _ _ hb
  intro v hv
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
  apply hp (i.val+1) (by omega)
  have := i.isLt
  omega

/-- Doubling is proved from the Bellman recursion, without importing a paper axiom. -/
theorem W_double (N : ℕ) (hN : 1 ≤ N) : rho*W N ≤ W (2*N) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hn : N=1
    · subst N
      have h := (W_sandwich 2 (by omega)).1
      have hU2 : U 2=rho := by simpa using U_even 1
      rw [W_one]
      rw [hU2] at h
      nlinarith [rho_gt_two]
    have hn2 : 2 ≤ N := by omega
    rw [mul_comm rho (W N)]
    apply (le_div_iff₀ rho_pos).mp
    have hb : 0 ≤ W (2*N)/rho := (div_pos (W_pos _ (by omega)) rho_pos).le
    apply W_upper_of_pivots N hn2 _ hb
    intro m hm hmN
    have hr : 1 ≤ N-m := by omega
    have hi := ih (N-m) (by omega) hr
    have ha := A_mono (U_nonneg (2*m)) (mul_pos rho_pos (W_pos _ hr)).le le_rfl hi
    have hp := W_pivot_lower (2*N) (2*m) (by omega) (by omega)
    have hs : 2*N-2*m=2*(N-m) := by omega
    rw [hs,U_even] at hp
    rw [U_even,A_hom rho_pos.le (U_nonneg m) (W_pos _ hr).le] at ha
    exact (le_div_iff₀ rho_pos).mpr (by nlinarith [ha.trans hp])

theorem W_ray_monotone (m : ℕ) (hm : 1 ≤ m) :
    Monotone (fun k : ℕ => W (m*2^k)/rho^k) := by
  have hrho := rho_pos
  apply monotone_nat_of_le_succ
  intro k
  have hn : 1 ≤ m*2^k := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by positivity))
  have hd := W_double (m*2^k) hn
  have hs : m*2^(k+1)=2*(m*2^k) := by ring
  rw [hs,pow_succ]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hd (pow_nonneg rho_pos.le k)]

theorem W_ray_upper (m k : ℕ) (hm : 1 ≤ m) :
    W (m*2^k)/rho^k ≤ rho*U m := by
  have hrho := rho_pos
  have hn : 1 ≤ m*2^k := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by positivity))
  have h := (W_sandwich (m*2^k) hn).2
  have hscale : U (m*2^k)=rho^k*U m := by rw [Nat.mul_comm m,U_dyadic]
  rw [hscale] at h
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

theorem W_ray_limit_exists (m : ℕ) (hm : 1 ≤ m) :
    ∃ d : ℝ, 0 < d ∧ d ≤ rho*U m ∧
      Tendsto (fun k : ℕ => W (m*2^k)/rho^k) atTop (𝓝 d) := by
  let f := fun k : ℕ => W (m*2^k)/rho^k
  have hmono : Monotone f := W_ray_monotone m hm
  have hb : BddAbove (range f) := ⟨rho*U m,by rintro y ⟨k,rfl⟩; exact W_ray_upper m k hm⟩
  refine ⟨⨆ k, f k,?_,?_,tendsto_atTop_ciSup hmono hb⟩
  · have h0 := le_ciSup hb 0
    have hp : 0 < f 0 := by simpa [f] using W_pos m hm
    exact hp.trans_le h0
  · exact ciSup_le (fun k => W_ray_upper m k hm)

theorem W_ray_limit_lower (m : ℕ) (hm : 1 ≤ m) (d : ℝ)
    (hd : Tendsto (fun k : ℕ => W (m*2^k)/rho^k) atTop (𝓝 d)) :
    2*U m ≤ d := by
  have hrho := rho_pos
  have hinv : Tendsto (fun k : ℕ => (rho^k)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by linarith [rho_gt_two]))
  have hl : Tendsto (fun k : ℕ => 2*U m-(rho^k)⁻¹) atTop (𝓝 (2*U m)) := by
    simpa using tendsto_const_nhds.sub hinv
  apply le_of_tendsto_of_tendsto' hl hd
  intro k
  have hn : 1 ≤ m*2^k := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by positivity))
  have hs : U (m*2^k)=rho^k*U m := by rw [Nat.mul_comm m,U_dyadic]
  have hb := (W_sandwich (m*2^k) hn).1
  rw [hs] at hb
  apply (le_div_iff₀ (by positivity)).mpr
  have he : (2*U m-(rho^k)⁻¹)*rho^k=2*(rho^k*U m)-1 := by
    field_simp
    <;> ring
  rwa [he]

end
end GD
