import GD.AdjacentRatios
import GD.DyadicInterpolation

namespace GD
noncomputable section

theorem weights_sum (r : ℝ) : w0 r+w1 r=2 := by
  by_cases hr : r=1
  · norm_num [w0,w1,hr]
  · unfold w0 w1
    rw [if_neg hr,if_neg hr]
    field_simp [sub_ne_zero.mpr hr]
    <;> ring

/-- Rationalized radical formula for the subdivision error.
It replaces Taylor's theorem in the manuscript's weight estimate. -/
theorem weight_error_formula (r : ℝ) (hr : 1 < r) :
    1-w0 r=(r-1)/(rho*((rho-1)*(r+1)+Real.sqrt (disc 1 r))) := by
  let d := Real.sqrt (disc 1 r)
  have hd : d^2=1+6*r+r^2 := by
    simpa [d,disc] using Real.sq_sqrt (disc_nonneg (show (0:ℝ) ≤ 1 by norm_num) (by linarith : 0 ≤ r))
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hrho := rho_pos
  have hrho1 : 0 < rho-1 := by linarith [rho_gt_two]
  have hh : (rho-1)^2=2 := by nlinarith [rho_sq]
  have hs : 0 < (rho-1)*(r+1)+d := by positivity
  have hw : rho*(r-1)*(1-w0 r)=(rho-1)*(r+1)-d := by
    unfold w0 T0 K
    rw [if_neg hr.ne']
    change rho*(r-1)*(1-2*((1+r+d)/2/rho-1)/(r-1))=(rho-1)*(r+1)-d
    field_simp [(sub_pos.mpr hr).ne']
    <;> ring
  have hid : ((rho-1)*(r+1)-d)*((rho-1)*(r+1)+d)=(r-1)^2 := by
    linear_combination (r+1)^2*hh-hd
  have he : (r-1)*((1-w0 r)*(rho*((rho-1)*(r+1)+d)))=(r-1)*(r-1) := by
    linear_combination ((rho-1)*(r+1)+d)*hw+hid
  apply (eq_div_iff (mul_pos rho_pos hs).ne').mpr
  exact mul_left_cancel₀ (sub_pos.mpr hr).ne' he

theorem weights_bounds (r : ℝ) (hr : 1 ≤ r) :
    0 < w0 r ∧ w0 r ≤ 1 ∧ 1 ≤ w1 r ∧
    0 ≤ 1-w0 r ∧ 1-w0 r ≤ (r-1)/(4*rho*(rho-1)) := by
  have hrho := rho_pos
  have hrho1 : 0 < rho-1 := by linarith [rho_gt_two]
  by_cases he : r=1
  · simp [he,w0,w1]
  have hrt : 1 < r := lt_of_le_of_ne hr (Ne.symm he)
  have hk := K_strict_right (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1) hrt
  rw [K_diag (show (0:ℝ) ≤ 1 by norm_num),mul_one] at hk
  have hT : 1 < T0 r := (lt_div_iff₀ rho_pos).mpr (by simpa using hk)
  have hwpos : 0 < w0 r := by
    rw [w0,if_neg he]
    exact div_pos (by linarith) (sub_pos.mpr hrt)
  let d := Real.sqrt (disc 1 r)
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hd : d^2=1+6*r+r^2 := by
    simpa [d,disc] using Real.sq_sqrt (disc_nonneg (show (0:ℝ) ≤ 1 by norm_num) (by linarith : 0 ≤ r))
  have hh : (rho-1)^2=2 := by nlinarith [rho_sq]
  have hdlo : 2*(rho-1) ≤ d := by nlinarith
  have hs : 4*(rho-1) ≤ (rho-1)*(r+1)+d := by nlinarith
  have hden : 4*rho*(rho-1) ≤ rho*((rho-1)*(r+1)+d) := by
    nlinarith [mul_le_mul_of_nonneg_left hs rho_pos.le]
  have hden0 : 0 < 4*rho*(rho-1) := by positivity
  have hformula := weight_error_formula r hrt
  have herr0 : 0 ≤ 1-w0 r := by
    rw [hformula]
    exact div_nonneg (sub_nonneg.mpr hr) (hden0.le.trans hden)
  have herr : 1-w0 r ≤ (r-1)/(4*rho*(rho-1)) := by
    rw [hformula]
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hr) hden0 hden
  have hsum := weights_sum r
  exact ⟨hwpos,by linarith,by linarith,herr0,herr⟩

def slope (k j : ℕ) : ℝ := (2:ℝ)^k/rho^k*(U (j+1)-U j)

theorem slope_pos (k j : ℕ) : 0 < slope k j := by
  have hrho := rho_pos
  have hu : U j < U (j+1) := U_strictMono (by omega)
  unfold slope
  exact mul_pos (div_pos (by positivity) (pow_pos hrho k)) (sub_pos.mpr hu)

theorem slope_children (k j : ℕ) (hj : 1 ≤ j) :
    slope (k+1) (2*j)=w0 (R j)*slope k j ∧
    slope (k+1) (2*j+1)=w1 (R j)*slope k j := by
  have hrho := rho_pos
  have hu := U_pos hj
  have hR := R_gt_one j hj
  have hdiff : U (j+1)-U j ≠ 0 := (sub_pos.mpr (U_strictMono (by omega))).ne'
  have hs : K (U j) (U (j+1))=U j*K 1 (R j) := by
    have h := K_hom hu.le (show (0:ℝ) ≤ 1 by norm_num) (show 0 ≤ R j by linarith)
    have hm : U j*R j=U (j+1) := by unfold R; field_simp
    simpa only [mul_one,hm] using h
  constructor
  · rw [slope,slope,w0,if_neg hR.ne',U_odd,U_even,hs,pow_succ,pow_succ]
    unfold T0 R
    field_simp
    <;> ring
  · rw [slope,slope,w1,if_neg hR.ne',
      show 2*j+1+1=2*(j+1) by omega,U_even,U_odd,hs,pow_succ,pow_succ]
    unfold T0 R
    field_simp
    <;> ring

def errorBudget (k : ℕ) : ℝ := (1-1/(2:ℝ)^k)/(2*rho)
def levelError (k : ℕ) : ℝ := 1/(4*rho*(2:ℝ)^k)

theorem errorBudget_bounds (k : ℕ) :
    0 ≤ errorBudget k ∧ errorBudget k ≤ 1/(2*rho) ∧ 0 < levelError k := by
  have hrho := rho_pos
  have hp : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
  have hd : 0 < (2:ℝ)^k := by positivity
  have he : 1/(2:ℝ)^k ≤ 1 := (div_le_one hd).mpr hp
  unfold errorBudget levelError
  refine ⟨div_nonneg (sub_nonneg.mpr he) (by positivity),?_,by positivity⟩
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [one_div_pos.mpr hd]

theorem errorBudget_succ (k : ℕ) :
    errorBudget (k+1)=errorBudget k+levelError k := by
  have hrho := rho_pos
  unfold errorBudget levelError
  rw [pow_succ]
  field_simp
  <;> ring

theorem grid_weight_bounds (k j : ℕ) (hlo : 2^k ≤ j) (hhi : j < 2^(k+1)) :
    1-levelError k ≤ w0 (R j) ∧ w0 (R j) ≤ 1+levelError k ∧
    1-levelError k ≤ w1 (R j) ∧ w1 (R j) ≤ 1+levelError k := by
  have hrho := rho_pos
  have hrho1 : 0 < rho-1 := by linarith [rho_gt_two]
  have hj : 1 ≤ j := (Nat.one_le_iff_ne_zero.mpr (by positivity)).trans hlo
  have hw := weights_bounds (R j) (R_gt_one j hj).le
  have hR := R_level_bound k j hlo hhi
  have hbound : (R j-1)/(4*rho*(rho-1)) ≤ levelError k := by
    have h := div_le_div_of_nonneg_right hR (show 0 ≤ 4*rho*(rho-1) by positivity)
    calc (R j-1)/(4*rho*(rho-1)) ≤ ((rho-1)/(2:ℝ)^k)/(4*rho*(rho-1)) := h
         _ = levelError k := by
           unfold levelError
           field_simp
           <;> ring
  have hepos := (errorBudget_bounds k).2.2
  have hs := weights_sum (R j)
  refine ⟨?_,?_,?_,?_⟩ <;> linarith [hw.2.2.2.2.trans hbound]

theorem slope_budget_bounds (k j : ℕ) (hlo : 2^k ≤ j) (hhi : j < 2^(k+1)) :
    (rho-1)*(1-errorBudget k) ≤ slope k j ∧
    slope k j ≤ (rho-1)*Real.exp (errorBudget k) := by
  have hrho := rho_pos
  have hrho1 : 0 < rho-1 := by linarith [rho_gt_two]
  have hcap : 1/(2*rho) < 1 := (div_lt_one (by positivity)).mpr (by linarith [rho_gt_two])
  induction k generalizing j with
  | zero =>
    have hj : j=1 := by norm_num at hlo hhi; omega
    subst j
    have hu2 : U 2=rho := by simpa using U_even 1
    simp [slope,errorBudget,hu2]
  | succ k ih =>
    let n := j/2
    have he : 2^(k+1)=2*2^k := by rw [pow_succ]; ring
    have he2 : 2^(k+1+1)=2*2^(k+1) := by rw [pow_succ]; ring
    have hnlo : 2^k ≤ n := by dsimp [n]; omega
    have hnhi : n < 2^(k+1) := by dsimp [n]; omega
    have hn : 1 ≤ n := (Nat.one_le_iff_ne_zero.mpr (by positivity)).trans hnlo
    have hi := ih n hnlo hnhi
    have hwb := grid_weight_bounds k n hnlo hnhi
    have hsc := slope_children k n hn
    have heb := errorBudget_bounds k
    have hk1 : errorBudget k < 1 := heb.2.1.trans_lt hcap
    have hk1' : errorBudget (k+1) < 1 := (errorBudget_bounds (k+1)).2.1.trans_lt hcap
    have her := errorBudget_succ k
    have hele : levelError k < 1 := by linarith
    have hw : ∃ w : ℝ, slope (k+1) j=w*slope k n ∧
        1-levelError k ≤ w ∧ w ≤ 1+levelError k := by
      by_cases hj : j%2=0
      · have hj' : j=2*n := by dsimp [n]; omega
        exact ⟨w0 (R n),by simpa [hj'] using hsc.1,hwb.1,hwb.2.1⟩
      · have hj' : j=2*n+1 := by dsimp [n]; omega
        exact ⟨w1 (R n),by simpa [hj'] using hsc.2,hwb.2.2.1,hwb.2.2.2⟩
    obtain ⟨w,hweq,hwlo,hwhi⟩ := hw
    rw [hweq,her]
    have hspos := (slope_pos k n).le
    constructor
    · have hmul := mul_le_mul hwlo hi.1 (mul_nonneg hrho1.le (sub_pos.mpr hk1).le)
        (by linarith : 0 ≤ w)
      have hprod : 0 ≤ (rho-1)*levelError k*errorBudget k :=
        mul_nonneg (mul_nonneg hrho1.le heb.2.2.le) heb.1
      nlinarith
    · have hmul := mul_le_mul hwhi hi.2 hspos (by linarith : 0 ≤ 1+levelError k)
      have hex := Real.add_one_le_exp (levelError k)
      have hmul2 := mul_le_mul_of_nonneg_right hex
        (mul_nonneg hrho1.le (Real.exp_pos (errorBudget k)).le)
      rw [Real.exp_add]
      nlinarith

theorem slope_uniform_bounds (k j : ℕ) (hlo : 2^k ≤ j) (hhi : j < 2^(k+1)) :
    cminus ≤ slope k j ∧ slope k j ≤ cplus := by
  have hrho1 : 0 < rho-1 := by linarith [rho_gt_two]
  have h := slope_budget_bounds k j hlo hhi
  have he := (errorBudget_bounds k).2.1
  constructor
  · unfold cminus
    nlinarith
  · unfold cplus
    exact h.2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hrho1.le)

end
end GD
