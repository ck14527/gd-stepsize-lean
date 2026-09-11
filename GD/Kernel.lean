import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Exact real kernels of the manuscript. No floating point numbers are used. -/
namespace GD
noncomputable section

def rho : ℝ := 1 + Real.sqrt 2
def disc (x y : ℝ) : ℝ := x^2 + 6*x*y + y^2
def K (x y : ℝ) : ℝ := (x+y+Real.sqrt (disc x y))/2
def negRoot (x y : ℝ) : ℝ := (x+y-Real.sqrt (disc x y))/2
def A (u w : ℝ) : ℝ := (4*u+w+Real.sqrt (w^2+8*u*w))/2

theorem rho_gt_two : 2 < rho := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2:ℝ)
  dsimp [rho]; nlinarith

theorem rho_pos : 0 < rho := lt_trans (by norm_num) rho_gt_two

theorem rho_sq : rho^2 = 2*rho+1 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  dsimp [rho]; nlinarith

theorem disc_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ disc x y := by unfold disc; positivity

theorem K_symm (x y : ℝ) : K x y = K y x := by
  unfold K disc; congr 2 <;> ring

theorem K_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ K x y := by
  unfold K; positivity

theorem K_quad {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (K x y)^2 = (x+y)*K x y+x*y := by
  have hs := Real.sq_sqrt (disc_nonneg hx hy)
  dsimp [K, disc] at *; nlinarith

theorem K_ge_sum {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x+y ≤ K x y := by
  have hs := Real.sq_sqrt (disc_nonneg hx hy)
  have hn := Real.sqrt_nonneg (disc x y)
  have hp : 0 ≤ x*y := mul_nonneg hx hy
  dsimp [K, disc] at *; nlinarith

theorem K_gt_sum {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : x+y < K x y := by
  have hs := Real.sq_sqrt (disc_nonneg hx.le hy.le)
  have hn := Real.sqrt_nonneg (disc x y)
  have hp : 0 < x*y := mul_pos hx hy
  dsimp [K, disc] at *; nlinarith

theorem K_zero_left {x : ℝ} (hx : 0 ≤ x) : K 0 x = x := by
  simp [K, disc, Real.sqrt_sq hx]

theorem K_zero_right {x : ℝ} (hx : 0 ≤ x) : K x 0 = x := by
  rw [K_symm]; exact K_zero_left hx

theorem K_pos {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hs : 0 < x+y) :
    0 < K x y := lt_of_lt_of_le hs (K_ge_sum hx hy)

theorem K_hom {t x y : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    K (t*x) (t*y) = t*K x y := by
  have hd : disc (t*x) (t*y) = t^2 * disc x y := by unfold disc; ring
  have hs : Real.sqrt (t^2 * disc x y) = t * Real.sqrt (disc x y) := by
    rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
  unfold K; rw [hd, hs]; ring

theorem K_diag {x : ℝ} (hx : 0 ≤ x) : K x x = rho*x := by
  have h : disc x x = x^2*8 := by unfold disc; ring
  have hs : Real.sqrt (8:ℝ) = 2*Real.sqrt 2 := by
    have h1 := Real.sq_sqrt (show (0:ℝ) ≤ 8 by norm_num)
    have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hn1 := Real.sqrt_nonneg (8:ℝ)
    have hn2 := Real.sqrt_nonneg (2:ℝ)
    nlinarith
  unfold K; rw [h, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx, hs]
  unfold rho; ring

theorem K_mono {x y x' y' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxx : x ≤ x') (hyy : y ≤ y') : K x y ≤ K x' y' := by
  have hd : disc x y ≤ disc x' y' := by
    unfold disc
    have : x*y ≤ x'*y' := mul_le_mul hxx hyy hy (hx.trans hxx)
    have h1 := sq_le_sq₀ hx (hx.trans hxx)
    have h2 := sq_le_sq₀ hy (hy.trans hyy)
    nlinarith [h1.mpr hxx, h2.mpr hyy]
  have hs := Real.sqrt_le_sqrt hd
  dsimp [K]; linarith

theorem K_strict_left {x x' y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxx : x < x') : K x y < K x' y := by
  have hd : disc x y ≤ disc x' y := by
    unfold disc
    have h1 := (sq_le_sq₀ hx (hx.trans hxx.le)).mpr hxx.le
    have h2 : x*y ≤ x'*y := mul_le_mul_of_nonneg_right hxx.le hy
    nlinarith
  have hs := Real.sqrt_le_sqrt hd
  dsimp [K]; linarith

theorem K_strict_right {x y y' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hyy : y < y') : K x y < K x y' := by
  rw [K_symm x y, K_symm x y']; exact K_strict_left hy hx hyy

theorem K_continuous : Continuous (fun xy : ℝ × ℝ => K xy.1 xy.2) := by
  unfold K disc; fun_prop

/-- Comparison with the positive root; the strict positivity of z is essential. -/
theorem K_le_iff {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) :
    K x y ≤ z ↔ 0 ≤ z^2-(x+y)*z-x*y := by
  have hk := K_quad hx hy
  have hks := K_ge_sum hx hy
  have hk0 := K_nonneg hx hy
  constructor
  · intro h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ z+K x y-x-y by linarith)]
  · intro h
    by_contra hh
    have hzK : z < K x y := lt_of_not_ge hh
    nlinarith [mul_pos (sub_pos.mpr hzK) (show 0 < K x y+z-x-y by linarith)]

theorem K_lt_iff {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) :
    K x y < z ↔ 0 < z^2-(x+y)*z-x*y := by
  have hk := K_quad hx hy
  have hks := K_ge_sum hx hy
  constructor
  · intro h
    nlinarith [mul_pos (sub_pos.mpr h) (show 0 < z+K x y-x-y by linarith)]
  · intro h
    have hle := (K_le_iff hx hy hz).mpr h.le
    rcases lt_or_eq_of_le hle with hl | he
    · exact hl
    · rw [he] at hk; linarith

end
end GD
