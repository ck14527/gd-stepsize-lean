import GD.AsymmetricBounds
import GD.Targets
namespace GD
noncomputable section

theorem K_one_mean_bound (r : ℝ) (hr : 1 ≤ r) : K 1 r ≤ rho*(r+1)/2 := by
  let v := Real.sqrt (disc 1 r)
  let t := Real.sqrt 2
  have ht : t^2=2 := Real.sq_sqrt (by norm_num)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg 2
  have hv : v^2=1+6*r+r^2 := by simpa [v,disc] using Real.sq_sqrt (disc_nonneg (show (0:ℝ) ≤ 1 by norm_num) (by linarith : 0 ≤ r))
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hid : (t*(r+1))^2-v^2=(r-1)^2 := by linear_combination (r+1)^2*ht-hv
  have hpos : 0 ≤ t*(r+1) := by positivity
  have hroot : v ≤ t*(r+1) := by nlinarith [sq_nonneg (r-1)]
  change (1+r+v)/2 ≤ (1+t)*(r+1)/2
  nlinarith

theorem T0_contract {r : ℝ} (hr : 1 ≤ r) : T0 r-1 ≤ (r-1)/2 := by
  unfold T0
  exact (by
    have hc : K 1 r/rho ≤ (r+1)/2 := (div_le_iff₀ rho_pos).mpr (by nlinarith [K_one_mean_bound r hr])
    linarith)

theorem T1_kernel_form {r : ℝ} (hr : 1 ≤ r) : T1 r=rho*(K 1 r-1-r) := by
  have hk := K_quad (show (0:ℝ) ≤ 1 by norm_num) (show 0 ≤ r by linarith)
  have hk0 : 0 < K 1 r := K_pos (by norm_num) (by linarith) (by linarith)
  unfold T1
  apply (div_eq_iff hk0.ne').mpr
  linear_combination -rho*hk

theorem T1_contract {r : ℝ} (hr : 1 ≤ r) : T1 r-1 ≤ (r-1)/2 := by
  rw [T1_kernel_form hr]
  have hh := mul_le_mul_of_nonneg_left (K_one_mean_bound r hr) rho_pos.le
  have hid : rho*(rho*(r+1)/2-1-r)=(r+1)/2 := by
    linear_combination ((r+1)/2)*rho_sq
  nlinarith

theorem R_gt_one (N : ℕ) (hN : 1 ≤ N) : 1 < R N := by
  unfold R
  apply (lt_div_iff₀ (U_pos hN)).mpr
  simpa using U_strictMono (show N < N+1 by omega)

theorem R_rec (N : ℕ) (hN : 1 ≤ N) : R (2*N)=T0 (R N) ∧ R (2*N+1)=T1 (R N) := by
  have hu : 0 < U N := U_pos hN
  have hu1 : 0 < U (N+1) := U_pos (by omega)
  have hr : 0 ≤ R N := (R_gt_one N hN).le.trans' (by norm_num)
  have hscale : K (U N) (U (N+1))=U N*K 1 (R N) := by
    have h := K_hom hu.le (show (0:ℝ) ≤ 1 by norm_num) hr
    have hmul : U N*R N=U (N+1) := by unfold R; field_simp
    exact (by simpa only [mul_one,hmul] using h)
  have hkpos : 0 < K 1 (R N) := K_pos (by norm_num) hr (by linarith)
  constructor
  · unfold R T0
    rw [U_even,U_odd,hscale]
    change (U N*K 1 (R N))/(rho*U N)=K 1 (R N)/rho
    field_simp [hu.ne',rho_pos.ne'] <;> ring
  · unfold R T1
    rw [U_odd,show 2*N+1+1=2*(N+1) by omega,U_even,hscale]
    change (rho*U (N+1))/(U N*K 1 (R N))=rho*(U (N+1)/U N)/K 1 (R N)
    field_simp [hu.ne',hkpos.ne']

/-- A dyadic-block form of the contraction bound, proved without derivatives. -/
theorem R_level_bound (k N : ℕ) (hlo : 2^k ≤ N) (hhi : N < 2^(k+1)) :
    R N-1 ≤ (rho-1)/(2:ℝ)^k := by
  induction k generalizing N with
  | zero =>
    have hN : N=1 := by norm_num at hlo hhi; omega
    subst N
    have hU2 : U 2=rho := by have := U_even 1; simpa using this
    simp [R,hU2]
  | succ k ih =>
    let n := N/2
    have hpow : 2^(k+1)=2*2^k := by rw [pow_succ]; ring
    have hpow2 : 2^(k+1+1)=2*2^(k+1) := by rw [pow_succ]; ring
    have hlow : 2^k ≤ n := by dsimp [n]; omega
    have hhigh : n < 2^(k+1) := by dsimp [n]; omega
    have hn : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) hlow
    have hrec := R_rec n hn
    have hi := ih n hlow hhigh
    have hr : 1 ≤ R n := (R_gt_one n hn).le
    have hc : R N-1 ≤ (R n-1)/2 := by
      by_cases he : N%2=0
      · have hN : N=2*n := by dsimp [n]; omega
        rw [hN,hrec.1]; exact T0_contract hr
      · have hN : N=2*n+1 := by dsimp [n]; omega
        rw [hN,hrec.2]; exact T1_contract hr
    calc R N-1 ≤ ((rho-1)/(2:ℝ)^k)/2 := by linarith
         _ = (rho-1)/(2:ℝ)^(k+1) := by rw [pow_succ]; ring

/-- Lemma 5.3, every clause, with N.log2 encoding the integer floor logarithm. -/
theorem lemma_5_3 : Targets.lemma_5_3 := by
  intro N hN
  have hn0 : N ≠ 0 := by omega
  have hl := Nat.log2_self_le hn0
  have hh := Nat.lt_log2_self (n:=N)
  have hb := R_level_bound N.log2 N hl hh
  have hden : (1:ℝ) ≤ (2:ℝ)^N.log2 := one_le_pow₀ (by norm_num)
  have hdenpos : (0:ℝ) < (2:ℝ)^N.log2 := by positivity
  have hNN : (N:ℝ) < 2*(2:ℝ)^N.log2 := by
    have h := (show (N:ℝ) < ((2^(N.log2+1):ℕ):ℝ) by exact_mod_cast hh)
    simpa [Nat.cast_pow,pow_succ,mul_comm] using h
  have hupper : R N ≤ rho := by
    have hfrac : (rho-1)/(2:ℝ)^N.log2 ≤ rho-1 := (div_le_iff₀ hdenpos).mpr (by nlinarith [rho_gt_two])
    linarith
  refine ⟨(R_rec N hN).1,(R_rec N hN).2,R_gt_one N hN,hupper,hb,?_⟩
  apply (div_le_div_iff₀ hdenpos (show (0:ℝ) < N by exact_mod_cast hN)).mpr
  nlinarith [mul_pos (show 0 < rho-1 by linarith [rho_gt_two]) (sub_pos.mpr hNN)]

end
end GD
