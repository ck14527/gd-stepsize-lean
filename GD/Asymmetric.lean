import GD.Conjugacy
namespace GD
noncomputable section

theorem A_nonneg {u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) : 0 ≤ A u w := by
  unfold A; positivity

theorem A_quad {u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) :
    (A u w)^2-(4*u+w)*A u w+4*u^2=0 := by
  have hd : 0 ≤ w^2+8*u*w := by positivity
  have hs := Real.sq_sqrt hd
  unfold A; nlinarith

theorem A_small_root_le {u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) :
    4*u+w-A u w ≤ 2*u := by
  have hd : 0 ≤ w^2+8*u*w := by positivity
  have hs := Real.sq_sqrt hd
  have hnn := Real.sqrt_nonneg (w^2+8*u*w)
  unfold A
  nlinarith [mul_nonneg hu hw]

theorem A_le_of_quadratic_nonneg {u w z : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hz : 2*u < z) (hq : 0 ≤ z^2-(4*u+w)*z+4*u^2) : A u w ≤ z := by
  have ha := A_quad hu hw
  have hb := A_small_root_le hu hw
  by_contra hn
  have hlt : z < A u w := lt_of_not_ge hn
  have hp := mul_pos (sub_pos.mpr hlt) (show 0 < z-(4*u+w-A u w) by linarith)
  nlinarith

theorem le_A_of_quadratic_nonpos {u w z : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hz : 2*u < z) (hq : z^2-(4*u+w)*z+4*u^2 ≤ 0) : z ≤ A u w := by
  have ha := A_quad hu hw
  have hb := A_small_root_le hu hw
  by_contra hn
  have hlt : A u w < z := lt_of_not_ge hn
  have hp := mul_pos (sub_pos.mpr hlt) (show 0 < z-(4*u+w-A u w) by linarith)
  nlinarith

/-- The polynomial comparison used for the upper reciprocal sandwich. -/
theorem A_upper_algebra (x y s v : ℝ) (hs : s^2=2)
    (hv : v^2=x^2+6*x*y+y^2) :
    ((7-2*s)*x+(5+2*s)*y)^2-((1+2*s)*v)^2 =
      8*(6-4*s)*(x-(2+3*s/2)*y)^2 := by
  linear_combination (-4*s^2 - 4*s - 1)*hv + (72*s*y^2 - 128*x*y + 84*y^2)*hs

/-- Lemma D.1, upper comparison. -/
theorem lemma_D_1_upper {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : A x (rho*y) ≤ rho*K x y := by
  let s := Real.sqrt 2
  let v := Real.sqrt (disc x y)
  have hs : s^2=2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 2
  have hslt : s < 3/2 := by nlinarith
  have hv : v^2=x^2+6*x*y+y^2 := Real.sq_sqrt (disc_nonneg hx.le hy.le)
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hc : 0 ≤ 8*(6-4*s) := by nlinarith
  have hid := A_upper_algebra x y s v hs hv
  have hn := mul_nonneg hc (sq_nonneg (x-(2+3*s/2)*y))
  have hD : 0 < (7-2*s)*x+(5+2*s)*y := by
    have h7 : 0 < 7-2*s := by linarith
    positivity
  have hE : 0 ≤ (1+2*s)*v := by positivity
  have hsqrt : (1+2*s)*v ≤ (7-2*s)*x+(5+2*s)*y := by nlinarith
  have hk := K_quad hx.le hy.le
  have hkp := K_gt_sum hx hy
  have hrho : rho=1+s := rfl
  have hKv : 2*K x y=x+y+v := by unfold K; dsimp [v]; ring
  have hfactor : 0 ≤ 4*x+rho^2*y-(2*rho-1)*K x y := by
    rw [rho_sq,hrho]
    have hi : 4*x+(2*(1+s)+1)*y-(2*(1+s)-1)*K x y =
        (((7-2*s)*x+(5+2*s)*y)-(1+2*s)*v)/2 := by
      linear_combination -((1+2*s)/2)*hKv
    linarith
  have hQ : 0 ≤ (rho*K x y)^2-(4*x+rho*y)*(rho*K x y)+4*x^2 := by
    have hi : (rho*K x y)^2-(4*x+rho*y)*(rho*K x y)+4*x^2 =
        x*(4*x+rho^2*y-(2*rho-1)*K x y) := by
      linear_combination rho^2*hk + (x*K x y)*rho_sq
    rw [hi]; exact mul_nonneg hx.le hfactor
  apply A_le_of_quadratic_nonneg hx.le (mul_pos rho_pos hy).le _ hQ
  nlinarith [rho_gt_two, mul_pos (show 0 < rho-2 by linarith [rho_gt_two]) (K_pos hx.le hy.le (by linarith))]

/-- Lemma D.1, affine lower comparison. -/
theorem lemma_D_1_lower {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    2*K x y-1 ≤ A x (2*y-1) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  let v := Real.sqrt (disc x y)
  have hv : v^2=x^2+6*x*y+y^2 := Real.sq_sqrt (disc_nonneg hx0.le hy0.le)
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hpoly : ((2*x+1)*v)^2-(2*x^2+2*x*y+3*x+y)^2 =
      8*x^2*(2*x*y-x+y-1) := by
    linear_combination (2*x+1)^2*hv
  have hfac : 0 ≤ 2*x*y-x+y-1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  have hpos1 : 0 ≤ (2*x+1)*v := by positivity
  have hpos2 : 0 ≤ 2*x^2+2*x*y+3*x+y := by positivity
  have hroot : 2*x^2+2*x*y+3*x+y ≤ (2*x+1)*v := by
    nlinarith [mul_nonneg (show 0 ≤ 8*x^2 by positivity) hfac]
  have hk := K_quad hx0.le hy0.le
  have hkgt := K_gt_sum hx0 hy0
  have hKv : 2*K x y=x+y+v := by unfold K; dsimp [v]; ring
  have hQ : (2*K x y-1)^2-(4*x+2*y-1)*(2*K x y-1)+4*x^2 ≤ 0 := by
    have hi : (2*K x y-1)^2-(4*x+2*y-1)*(2*K x y-1)+4*x^2 =
        2*x^2+2*x*y+3*x+y-(2*x+1)*v := by
      linear_combination 4*hk-(2*x+1)*hKv
    linarith
  apply le_A_of_quadratic_nonpos hx0.le (by linarith) (by linarith)
  simpa only [add_sub_assoc] using hQ

end
end GD
