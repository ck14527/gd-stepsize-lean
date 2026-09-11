import GD.Kernel

namespace GD
noncomputable section

def e1 (a b c d : ℝ) := a+b+c+d
def e2 (a b c d : ℝ) := a*b+a*c+a*d+b*c+b*d+c*d
def e3 (a b c d : ℝ) := a*b*c+a*b*d+a*c*d+b*c*d
def e4 (a b c d : ℝ) := a*b*c*d
def quartic (a b c d E z : ℝ) :=
  z^4-e1 a b c d*z^3-(e2 a b c d+2*E)*z^2-e3 a b c d*z+e4 a b c d

def qpoly (u v z : ℝ) := z^2-(u+v)*z-u*v

def pairedPoly (a b c d z : ℝ) :=
  qpoly (K a b) (K c d) z * qpoly (K a b) (negRoot c d) z *
    qpoly (negRoot a b) (K c d) z * qpoly (negRoot a b) (negRoot c d) z

/-- The expression (45), before substituting the pair sums and products. -/
def vietaPoly (a b c d z : ℝ) :=
  let L := z^2+c*z-d
  let M := -2*z*(z^2+d)
  let N := z^2*(z^2-c*z-d)
  b^2*L^2-b*M^2+N^2-a*b*L*M+(a^2+2*b)*L*N+a*M*N

/-- Eq. (47), with the elementary symmetric coefficients exposed. -/
def symPoly (a b c d S z : ℝ) :=
  z^8-2*e1 a b c d*z^7+((e1 a b c d)^2-2*S)*z^6+
  2*(e1 a b c d*S-e3 a b c d)*z^5+
  (-(e2 a b c d)^2-2*e1 a b c d*e3 a b c d-14*e4 a b c d+
    6*e2 a b c d*S-4*S^2)*z^4+
  2*(e3 a b c d*S-e1 a b c d*e4 a b c d)*z^3+
  ((e3 a b c d)^2-2*e4 a b c d*S)*z^2-
  2*e3 a b c d*e4 a b c d*z+(e4 a b c d)^2

theorem vieta_expansion (a b c d z : ℝ) :
    vietaPoly (a+b) (a*b) (c+d) (c*d) z = symPoly a b c d (a*b+c*d) z := by
  unfold vietaPoly symPoly e1 e2 e3 e4; ring

theorem difference_first_polynomial (a b c d z : ℝ) :
    vietaPoly (a+c) (a*c) (b+d) (b*d) z - vietaPoly (a+b) (a*b) (c+d) (c*d) z =
      2*z^2*(d-a)*(c-b)*quartic a b c d (a*d+b*c) z := by
  unfold vietaPoly quartic e1 e2 e3 e4; ring

theorem difference_second_polynomial (a b c d z : ℝ) :
    vietaPoly (a+d) (a*d) (b+c) (b*c) z - vietaPoly (a+c) (a*c) (b+d) (b*d) z =
      2*z^2*(b-a)*(d-c)*quartic a b c d (a*b+c*d) z := by
  unfold vietaPoly quartic e1 e2 e3 e4; ring

theorem K_negRoot_sum (x y : ℝ) : K x y + negRoot x y = x+y := by
  unfold K negRoot; ring

theorem K_negRoot_product {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    K x y * negRoot x y = -x*y := by
  have hs := Real.sq_sqrt (disc_nonneg hx hy)
  unfold K negRoot; dsimp [disc] at *; nlinarith

/-- Four quadratic factors reduce to (45) using only Vieta relations. -/
theorem conjugate_elimination (u s v t a b c d z : ℝ)
    (h1 : u+s=a) (h2 : u*s = -b) (h3 : v+t=c) (h4 : v*t = -d) :
    qpoly u v z * qpoly u t z * qpoly s v z * qpoly s t z = vietaPoly a b c d z := by
  rw [← h1, ← h3, show b = -u*s by linarith, show d = -v*t by linarith]
  unfold qpoly vietaPoly; ring

theorem pairedPoly_vieta {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (z : ℝ) :
    pairedPoly a b c d z = vietaPoly (a+b) (a*b) (c+d) (c*d) z := by
  exact conjugate_elimination _ _ _ _ _ _ _ _ _ (K_negRoot_sum _ _)
    (by nlinarith [K_negRoot_product ha hb]) (K_negRoot_sum _ _)
    (by nlinarith [K_negRoot_product hc hd])

/-- Lemma 3.3, first identity, for the actual conjugate-root product (13). -/
theorem lemma_3_3_first {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (z : ℝ) :
    pairedPoly a c b d z - pairedPoly a b c d z =
      2*z^2*(d-a)*(c-b)*quartic a b c d (a*d+b*c) z := by
  rw [pairedPoly_vieta ha hc hb hd, pairedPoly_vieta ha hb hc hd]
  exact difference_first_polynomial _ _ _ _ _

/-- Lemma 3.3, second identity. -/
theorem lemma_3_3_second {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (z : ℝ) :
    pairedPoly a d b c z - pairedPoly a c b d z =
      2*z^2*(b-a)*(d-c)*quartic a b c d (a*b+c*d) z := by
  rw [pairedPoly_vieta ha hd hb hc, pairedPoly_vieta ha hc hb hd]
  exact difference_second_polynomial _ _ _ _ _

/-- A polynomial-ideal certificate for the quartic evaluation; denominator cleared. -/
theorem quartic_reduction (a b c d E u v z : ℝ)
    (hu : u^2=(a+b)*u+a*b) (hv : v^2=(c+d)*v+c*d)
    (hz : z^2=(u+v)*z+u*v) :
    u*v*quartic a b c d E z = 2*(a*b*v^2+c*d*u^2-E*u*v)*(u*v+u*z+v*z) := by
  unfold quartic e1 e2 e3 e4
  linear_combination (-2*E*u*v - a*b*u*v - a*c*u*v - a*d*u*v - a*u^2*v - a*u*v^2 - a*u*v*z - b*c*u*v - b*d*u*v - b*u^2*v - b*u*v^2 - b*u*v*z - c*d*u*v - c*u^2*v - c*u*v^2 - c*u*v*z - d*u^2*v - d*u*v^2 - d*u*v*z + u^3*v + 3*u^2*v^2 + u^2*v*z + u*v^3 + u*v^2*z + u*v*z^2) * hz +
    (-2*a*c*d*v - 2*a*c*d*z - 2*a*c*v^2 - 2*a*c*v*z - 2*a*d*v^2 - 2*a*d*v*z + 2*a*v^3 + 2*a*v^2*z - 2*b*c*d*v - 2*b*c*d*z - 2*b*c*v^2 - 2*b*c*v*z - 2*b*d*v^2 - 2*b*d*v*z + 2*b*v^3 + 2*b*v^2*z - 2*c*d*u*v - 2*c*d*u*z - c*d*v^2 - 3*c*d*v*z - c*u*v^2 - c*u*v*z - c*v^3 - 3*c*v^2*z - d*u*v^2 - d*u*v*z - d*v^3 - 3*d*v^2*z + u^2*v^2 + u^2*v*z + 3*u*v^3 + 5*u*v^2*z + v^4 + 5*v^3*z) * hu +
    (2*a^2*b*v + 2*a^2*b*z + 2*a^2*u*v + 2*a^2*u*z + 2*a*b^2*v + 2*a*b^2*z + 5*a*b*u*v + 6*a*b*u*z + a*b*v^2 + 3*a*b*v*z + a*u*v^2 + 4*a*u*v*z + 2*b^2*u*v + 2*b^2*u*z + b*u*v^2 + 4*b*u*v*z + u*v^2*z) * hv

/-- Factorization (15). -/
theorem factor_first (a b c d u v : ℝ) :
    a*b*v^2+c*d*u^2-(a*d+b*c)*u*v = (a*v-c*u)*(b*v-d*u) := by ring

/-- Factorization (16). -/
theorem factor_second (a b c d u v : ℝ) :
    a*c*v^2+b*d*u^2-(a*b+c*d)*u*v = (c*v-b*u)*(a*v-d*u) := by ring

end
end GD

namespace GD
noncomputable section

theorem lemma_3_4 {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hu : 0 < K a b) (hv : 0 < K c d) (E : ℝ) :
    quartic a b c d E (K (K a b) (K c d)) =
      2*(a*b*(K c d)^2+c*d*(K a b)^2-E*K a b*K c d)*
      (K a b*K c d+K a b*K (K a b) (K c d)+K c d*K (K a b) (K c d)) /
      (K a b*K c d) := by
  apply (eq_div_iff (mul_ne_zero hu.ne' hv.ne')).mpr
  nlinarith only [quartic_reduction a b c d E (K a b) (K c d) (K (K a b) (K c d))
    (K_quad ha hb) (K_quad hc hd) (K_quad hu.le hv.le)]

theorem negRoot_nonpos {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : negRoot x y ≤ 0 := by
  linarith [K_negRoot_sum x y, K_ge_sum hx hy]

theorem negRoot_abs_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : -negRoot x y ≤ K x y := by
  linarith [K_negRoot_sum x y]

theorem qpoly_factor {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (z : ℝ) :
    qpoly u v z = (z-K u v)*(z-negRoot u v) := by
  have h1 := K_negRoot_sum u v
  have h2 := K_negRoot_product hu hv
  unfold qpoly; linear_combination z*h1-h2

theorem auxiliary_factors_pos {u v s t z : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hsu : s ≤ u) (htv : t ≤ v) (hzu : u < z) (hzv : v < z) :
    0 < qpoly u (-t) z ∧ 0 < qpoly (-s) v z ∧ 0 < qpoly (-s) (-t) z := by
  have hz : 0 < z := lt_of_le_of_lt hu hzu
  have hst : s*t ≤ u*v := mul_le_mul hsu htv ht hu
  have huvz : u*v < z^2 := by
    have h1 := mul_le_mul_of_nonneg_left hzv.le hu
    have h2 := mul_lt_mul_of_pos_right hzu hz
    nlinarith
  unfold qpoly
  refine ⟨?_,?_,?_⟩
  · nlinarith [mul_pos hz (sub_pos.mpr hzu), mul_nonneg ht (show 0 ≤ z+u by linarith)]
  · nlinarith [mul_pos hz (sub_pos.mpr hzv), mul_nonneg hs (show 0 ≤ z+v by linarith)]
  · nlinarith [mul_nonneg (add_nonneg hs ht) hz.le]

/-- Lemma 3.2 in an equivalent, three-way order form. -/
theorem lemma_3_2 {a b c d z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hz : max (K a b) (K c d) < z) :
    (pairedPoly a b c d z < 0 ↔ z < K (K a b) (K c d)) ∧
    (pairedPoly a b c d z = 0 ↔ z = K (K a b) (K c d)) ∧
    (0 < pairedPoly a b c d z ↔ K (K a b) (K c d) < z) := by
  have hu := K_nonneg ha hb
  have hv := K_nonneg hc hd
  have hzu := lt_of_le_of_lt (le_max_left (K a b) (K c d)) hz
  have hzv := lt_of_le_of_lt (le_max_right (K a b) (K c d)) hz
  have hz0 := lt_of_le_of_lt hu hzu
  have hh := auxiliary_factors_pos hu hv
    (neg_nonneg.mpr (negRoot_nonpos ha hb)) (neg_nonneg.mpr (negRoot_nonpos hc hd))
    (negRoot_abs_le ha hb) (negRoot_abs_le hc hd) hzu hzv
  simp only [neg_neg] at hh
  have hroot : 0 < z-negRoot (K a b) (K c d) := by linarith [negRoot_nonpos hu hv]
  have hprod : 0 < (z-negRoot (K a b) (K c d))*
      qpoly (K a b) (negRoot c d) z * qpoly (negRoot a b) (K c d) z *
      qpoly (negRoot a b) (negRoot c d) z :=
    mul_pos (mul_pos (mul_pos hroot hh.1) hh.2.1) hh.2.2
  have hp : pairedPoly a b c d z = (z-K (K a b) (K c d))*
      ((z-negRoot (K a b) (K c d))*qpoly (K a b) (negRoot c d) z *
       qpoly (negRoot a b) (K c d) z * qpoly (negRoot a b) (negRoot c d) z) := by
    unfold pairedPoly; rw [qpoly_factor hu hv]; ring
  rw [hp]
  constructor
  · constructor
    · intro h
      by_contra hn
      have hh := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn)) hprod.le
      linarith
    · intro h
      exact mul_neg_of_neg_of_pos (sub_neg.mpr h) hprod
  constructor
  · simp only [mul_eq_zero, hprod.ne', or_false, sub_eq_zero]
  · exact (mul_pos_iff_of_pos_right hprod).trans sub_pos

theorem pairedPoly_root {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    pairedPoly a b c d (K (K a b) (K c d)) = 0 := by
  have h := K_quad (K_nonneg ha hb) (K_nonneg hc hd)
  have hq : qpoly (K a b) (K c d) (K (K a b) (K c d)) = 0 := by
    unfold qpoly; linarith
  unfold pairedPoly; rw [hq]; ring

end
end GD
