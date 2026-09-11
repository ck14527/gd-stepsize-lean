import GD.OBSMantissa

namespace GD
noncomputable section
open Set Filter
open scoped Topology

theorem periodic_extension_lipschitz (g : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hend : g 0=g 1)
    (hg : ∀ x y : ℝ, x ∈ Icc (0:ℝ) 1 → y ∈ Icc (0:ℝ) 1 → |g x-g y| ≤ L*|x-y|) :
    ∀ x y : ℝ, |g (Int.fract x)-g (Int.fract y)| ≤ L*|x-y| := by
  have ordered : ∀ x y : ℝ, x ≤ y → |g (Int.fract x)-g (Int.fract y)| ≤ L*(y-x) := by
    intro x y hxy
    let a := Int.fract x
    let b := Int.fract y
    have ha : a ∈ Icc (0:ℝ) 1 := ⟨Int.fract_nonneg x,(Int.fract_lt_one x).le⟩
    have hb : b ∈ Icc (0:ℝ) 1 := ⟨Int.fract_nonneg y,(Int.fract_lt_one y).le⟩
    change |g a-g b| ≤ _
    by_cases he : Int.floor x=Int.floor y
    · have hab : a-b=x-y := by change (x-(Int.floor x:ℝ))-(y-(Int.floor y:ℝ))=x-y; rw [he]; ring
      have h := hg a b ha hb
      rw [hab,abs_of_nonpos (sub_nonpos.mpr hxy)] at h
      simpa only [neg_sub] using h
    · have hf : Int.floor x+1 ≤ Int.floor y := by have := Int.floor_mono hxy; omega
      have hfc : (Int.floor x:ℝ)+1 ≤ (Int.floor y:ℝ) := by exact_mod_cast hf
      have hgap : 1-a+b ≤ y-x := by change 1-(x-(Int.floor x:ℝ))+(y-(Int.floor y:ℝ)) ≤ y-x; linarith
      have h1 := hg a 1 ha (by norm_num)
      have h0 := hg 0 b (by norm_num) hb
      rw [← hend,abs_of_nonpos (by linarith [ha.2] : a-1 ≤ 0)] at h1
      rw [zero_sub,abs_neg,abs_of_nonneg hb.1] at h0
      have ht := abs_sub_le (g a) (g 0) (g b)
      have hm := mul_le_mul_of_nonneg_left hgap hL
      linarith
  intro x y
  rcases le_total x y with h | h
  · simpa [abs_of_nonpos (sub_nonpos.mpr h),neg_sub] using ordered x y h
  · simpa only [abs_sub_comm (g (Int.fract y)),abs_of_nonneg (sub_nonneg.mpr h)] using ordered y x h

theorem Psi_eq_mantissa (t : ℝ) : Psi t=obsMantissa ((2:ℝ)^(Int.fract t)) := by
  unfold Psi obsMantissa obsGrid gridHorizon
  congr 1
  funext k
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2),Real.rpow_natCast,mul_comm]

theorem Psi_periodic (t : ℝ) : Psi (t+1)=Psi t := by
  rw [Psi_eq_mantissa,Psi_eq_mantissa,Int.fract_add_one]

theorem Psi_on_unit (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : Psi t=obsMantissa ((2:ℝ)^t) := by
  rw [Psi_eq_mantissa]
  rcases lt_or_eq_of_le ht.2 with h | rfl
  · rw [Int.fract_eq_self.mpr ⟨ht.1,h⟩]
  · simpa using obsMantissa_endpoints.symm

theorem Psi_pos (t : ℝ) : 0 < Psi t := by
  rw [Psi_eq_mantissa]
  exact cstar_pos.trans_le (obsMantissa_bounds _
    (two_rpow_mem _ ⟨Int.fract_nonneg t,(Int.fract_lt_one t).le⟩)).1

theorem Psi_lipschitz : ∀ x y : ℝ, |Psi x-Psi y| ≤ (2*obsLip*Real.log 2)*|x-y| := by
  have hlog := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hL : 0 ≤ 2*obsLip*Real.log 2 := mul_nonneg (mul_nonneg (by norm_num) obsLip_pos.le) hlog.le
  have hend : obsMantissa ((2:ℝ)^(0:ℝ))=obsMantissa ((2:ℝ)^(1:ℝ)) := by simpa using obsMantissa_endpoints.symm
  have hg : ∀ x y : ℝ, x ∈ Icc (0:ℝ) 1 → y ∈ Icc (0:ℝ) 1 →
      |obsMantissa ((2:ℝ)^x)-obsMantissa ((2:ℝ)^y)| ≤ (2*obsLip*Real.log 2)*|x-y| := by
    intro x y hx hy
    have h := (obsMantissa_lipschitz _ _ (two_rpow_mem x hx) (two_rpow_mem y hy)).trans
      (mul_le_mul_of_nonneg_left (two_power_lipschitz x y hx hy) obsLip_pos.le)
    convert h using 1 <;> ring
  intro x y
  rw [Psi_eq_mantissa,Psi_eq_mantissa]
  exact periodic_extension_lipschitz (fun t => obsMantissa ((2:ℝ)^t)) _ hL hend hg x y

theorem Psi_positive_periodic_lipschitz : PeriodicLipschitzPositive Psi := by
  refine ⟨Psi_pos,Psi_periodic,2*obsLip*Real.log 2,?_,Psi_lipschitz⟩
  exact mul_nonneg (mul_nonneg (by norm_num) obsLip_pos.le) (Real.log_pos (by norm_num)).le

theorem Psi_continuous : Continuous Psi := by
  obtain ⟨L,hL,h⟩ := Psi_positive_periodic_lipschitz.2.2
  have hl : LipschitzWith ⟨L,hL⟩ Psi := by
    apply LipschitzWith.of_dist_le_mul
    simpa only [Real.dist_eq] using h
  exact hl.continuous

theorem logb_two_mem (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) : Real.logb 2 x ∈ Icc (0:ℝ) 1 := by
  have hx0 : 0 < x := by linarith [hx.1]
  constructor
  · exact Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hx.1
  · exact (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) hx0).mpr (by simpa using hx.2)

theorem Psi_logb (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) : Psi (Real.logb 2 x)=obsMantissa x := by
  have hx0 : 0 < x := by linarith [hx.1]
  rw [Psi_on_unit _ (logb_two_mem x hx),Real.rpow_logb (by norm_num) (by norm_num) hx0]

theorem Psi_grid_phase (k N : ℕ) (hlo : 2^k ≤ N) (hhi : N ≤ 2^(k+1)) :
    Psi (phase N)=obsMantissa ((N:ℝ)/(2:ℝ)^k) := by
  have hN : 1 ≤ N := (Nat.one_le_pow k 2 (by norm_num)).trans hlo
  have hn0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : 0 < (2:ℝ)^k := by positivity
  have hx : (N:ℝ)/(2:ℝ)^k ∈ Icc (1:ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ hp).mpr
      have hc : (2:ℝ)^k ≤ (N:ℝ) := by exact_mod_cast hlo
      simpa using hc
    · apply (div_le_iff₀ hp).mpr
      have hc : (N:ℝ) ≤ (2:ℝ)^(k+1) := by exact_mod_cast hhi
      simpa [pow_succ,mul_comm] using hc
  rw [← Psi_logb _ hx,Real.logb_div hn0.ne' hp.ne',Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2),mul_one]
  have hp' : Function.Periodic Psi 1 := Psi_periodic
  have hs := hp'.sub_nat_mul_eq k (x:=Real.logb 2 (N:ℝ))
  rw [mul_one] at hs
  rw [hs]
  exact periodic_fract Psi Psi_periodic _

theorem Psi_OBSPhase : OBSPhase Psi := by
  refine ⟨Psi_positive_periodic_lipschitz,?_⟩
  intro eps heps
  obtain ⟨k0,hk0⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp obsGrid_uniform) eps heps)
  refine ⟨k0,?_⟩
  intro k hk N hlo hhi
  have hp : 0 < (2:ℝ)^k := by positivity
  have hx : (N:ℝ)/(2:ℝ)^k ∈ Icc (1:ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ hp).mpr
      have hc : (2:ℝ)^k ≤ (N:ℝ) := by exact_mod_cast hlo
      simpa using hc
    · apply (div_le_iff₀ hp).mpr
      have hc : (N:ℝ) ≤ (2:ℝ)^(k+1) := by exact_mod_cast hhi
      simpa [pow_succ,mul_comm] using hc
  have h := hk0 k hk _ hx
  have he : obsGrid k ((N:ℝ)/(2:ℝ)^k)=C N := by
    unfold obsGrid gridHorizon
    rw [div_mul_cancel₀ _ hp.ne',Nat.floor_natCast]
  rw [he,Real.dist_eq,← Psi_grid_phase k N hlo hhi,abs_sub_comm] at h
  exact h

end
end GD
