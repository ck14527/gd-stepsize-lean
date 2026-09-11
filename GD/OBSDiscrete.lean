import GD.DiscreteModulus
import GD.Proposition62

namespace GD
noncomputable section
open Set Filter
open scoped Topology

def obsLip : ℝ := (4*max 1 cplus+rho*p)/phiMin^2
def obsGrid (k : ℕ) (x : ℝ) : ℝ := C (gridHorizon x k)

theorem obsLip_pos : 0 < obsLip := by
  have hL : 0 < max 1 cplus := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact div_pos (add_pos (mul_pos (by norm_num) hL) (mul_pos rho_pos p_pos)) (sq_pos_of_pos phiMin_bounds.1)

theorem C_adjacent (N : ℕ) (hN : 1 ≤ N) : |C (N+1)-C N| ≤ obsLip/(N:ℝ) := by
  have h := C_increment_bound cplus F_abs_bound N hN
  simpa only [obsLip,div_div] using h

theorem C_block_delta (k m d : ℕ) (hm : 2^k ≤ m) :
    |C (m+d)-C m| ≤ obsLip*(d:ℝ)/(2:ℝ)^k := by
  have hp : 0 < (2:ℝ)^k := by positivity
  induction d with
  | zero => simp
  | succ d ih =>
    have hm1 : 1 ≤ m+d := (Nat.one_le_pow k 2 (by norm_num)).trans (by omega)
    have ha := C_adjacent (m+d) hm1
    have hc : (2:ℝ)^k ≤ (m+d:ℕ) := by exact_mod_cast (show 2^k ≤ m+d by omega)
    have hu := div_le_div_of_nonneg_left obsLip_pos.le hp hc
    have ht := abs_sub_le (C (m+(d+1))) (C (m+d)) (C m)
    have he : obsLip*((d+1:ℕ):ℝ)/(2:ℝ)^k=obsLip*(d:ℝ)/(2:ℝ)^k+obsLip/(2:ℝ)^k := by push_cast; ring
    rw [he]
    have hs : m+(d+1)=m+d+1 := by omega
    rw [hs] at ht ⊢
    exact ht.trans (add_le_add (ha.trans hu) ih) |>.trans_eq (by ring)

theorem C_block_distance (k m n : ℕ) (hm : 2^k ≤ m) (hn : 2^k ≤ n) :
    |C m-C n| ≤ obsLip*|(m:ℝ)-(n:ℝ)|/(2:ℝ)^k := by
  have ordered : ∀ m n : ℕ, 2^k ≤ m → m ≤ n →
      |C n-C m| ≤ obsLip*((n:ℝ)-(m:ℝ))/(2:ℝ)^k := by
    intro m n hm hmn
    have h := C_block_delta k m (n-m) hm
    simpa only [Nat.add_sub_of_le hmn,Nat.cast_sub hmn] using h
  rcases le_total m n with h | h
  · have hc : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast h
    simpa only [abs_sub_comm (C n),abs_of_nonpos (sub_nonpos.mpr hc),neg_sub] using ordered m n hm h
  · have hc : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast h
    simpa only [abs_of_nonneg (sub_nonneg.mpr hc)] using ordered n m hn h

theorem obsGrid_modulus (k : ℕ) (x y : ℝ) (hx : x ∈ Icc (1:ℝ) 2) (hy : y ∈ Icc (1:ℝ) 2) :
    |obsGrid k x-obsGrid k y| ≤ obsLip*(|x-y|+1/(2:ℝ)^k) := by
  have hp : 0 < (2:ℝ)^k := by positivity
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith [hy.1]
  have hfx := Nat.floor_le (show 0 ≤ x*(2:ℝ)^k by positivity)
  have hfy := Nat.floor_le (show 0 ≤ y*(2:ℝ)^k by positivity)
  have hfx' := Nat.lt_floor_add_one (x*(2:ℝ)^k)
  have hfy' := Nat.lt_floor_add_one (y*(2:ℝ)^k)
  have hd : |(gridHorizon x k:ℝ)-(gridHorizon y k:ℝ)| ≤ |x-y| * (2:ℝ)^k+1 := by
    apply abs_le.mpr
    have ha := le_abs_self (x-y)
    have hb := neg_le_abs (x-y)
    have hma := mul_le_mul_of_nonneg_right ha hp.le
    have hmb := mul_le_mul_of_nonneg_right hb hp.le
    dsimp only [gridHorizon]
    constructor <;> nlinarith
  have hC := C_block_distance k (gridHorizon x k) (gridHorizon y k)
    (gridHorizon_bounds x hx k).1 (gridHorizon_bounds y hy k).1
  apply hC.trans
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd obsLip_pos.le) hp.le
  convert hh using 1 <;> field_simp <;> ring

theorem C_double (N : ℕ) (hN : 1 ≤ N) : C (2*N) ≤ C N := by
  have hn0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw := W_pos N hN
  have hw2 := W_pos (2*N) (by omega)
  have hd := W_double N hN
  have hp := Real.rpow_pos_of_pos hn0 p
  simp only [C,etaF,mul_one_div,Nat.cast_mul,Nat.cast_ofNat]
  rw [Real.mul_rpow (by norm_num) hn0.le,two_rpow_p]
  apply (div_le_div_iff₀ hw2 hw).mpr
  nlinarith [mul_le_mul_of_nonneg_left hd hp.le]

theorem gridHorizon_double (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    gridHorizon x (k+1)=2*gridHorizon x k ∨ gridHorizon x (k+1)=2*gridHorizon x k+1 := by
  have hp : 0 < (2:ℝ)^k := by positivity
  have h0 : 0 ≤ x*(2:ℝ)^k := mul_nonneg hx hp.le
  have h1 := Nat.floor_le h0
  have h2 := Nat.lt_floor_add_one (x*(2:ℝ)^k)
  have hl : 2*gridHorizon x k ≤ gridHorizon x (k+1) := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ x*(2:ℝ)^(k+1))).mpr
    simp only [gridHorizon,Nat.cast_mul,Nat.cast_ofNat,pow_succ]
    nlinarith
  have hu : gridHorizon x (k+1) < 2*gridHorizon x k+2 := by
    have h := Nat.floor_le (show 0 ≤ x*(2:ℝ)^(k+1) by positivity)
    have hc : (gridHorizon x (k+1):ℝ) < (2*gridHorizon x k+2:ℕ) := by
      simp only [gridHorizon,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,pow_succ] at h ⊢
      nlinarith
    exact_mod_cast hc
  omega

theorem obsGrid_step (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) (k : ℕ) :
    obsGrid (k+1) x ≤ obsGrid k x+obsLip/(2:ℝ)^(k+1) := by
  have hn := (gridHorizon_bounds x hx k).1
  have hn1 : 1 ≤ gridHorizon x k := (Nat.one_le_pow k 2 (by norm_num)).trans hn
  have hc := C_double (gridHorizon x k) hn1
  have hp : 0 ≤ obsLip/(2:ℝ)^(k+1) := div_nonneg obsLip_pos.le (by positivity)
  unfold obsGrid
  rcases gridHorizon_double x (by linarith [hx.1]) k with he | he
  · rw [he]
    linarith
  · rw [he]
    have hi := C_adjacent (2*gridHorizon x k) (by omega)
    have hden : (2:ℝ)^(k+1) ≤ (2*gridHorizon x k:ℕ) := by
      have hh : (2:ℕ)^(k+1) ≤ 2*gridHorizon x k := by rw [pow_succ]; omega
      exact_mod_cast hh
    have hi' := div_le_div_of_nonneg_left obsLip_pos.le (by positivity : 0 < (2:ℝ)^(k+1)) hden
    have hdiff := le_abs_self (C (2*gridHorizon x k+1)-C (2*gridHorizon x k))
    linarith

end
end GD
