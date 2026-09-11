import GD.StrictEnvelope

namespace GD
noncomputable section
open Set Filter
open scoped Topology

def phaseProfile (t : ℝ) : ℝ := rho^(-t)*F ((2:ℝ)^t)
def phaseLip : ℝ := 2*Real.log 2*cplus+rho*Real.log rho

theorem phaseLip_pos : 0 < phaseLip := by
  have h2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hr := Real.log_pos (by linarith [rho_gt_two] : 1 < rho)
  exact add_pos (mul_pos (mul_pos (by norm_num) h2) cplus_pos) (mul_pos rho_pos hr)

theorem two_rpow_mem (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : (2:ℝ)^t ∈ Icc (1:ℝ) 2 := by
  constructor
  · exact Real.one_le_rpow (by norm_num) ht.1
  · simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) ht.2

theorem F_mem_range (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) : F x ∈ Icc (1:ℝ) rho := by
  rw [← F_range]
  exact ⟨x,hx,rfl⟩

theorem exp_power_derivative (b c t : ℝ) (hb : 0 < b) :
    HasDerivAt (fun x : ℝ => b^(c*x)) (b^(c*t)*(Real.log b*c)) t := by
  have he : (fun x : ℝ => b^(c*x))=(fun x : ℝ => Real.exp (Real.log b*(c*x))) := by
    ext x
    exact Real.rpow_def_of_pos hb _
  rw [he,Real.rpow_def_of_pos hb]
  convert (((hasDerivAt_id t).const_mul c).const_mul (Real.log b)).exp using 1 <;> simp only [id_eq] <;> ring

theorem two_power_lipschitz (x y : ℝ) (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) :
    |(2:ℝ)^x-(2:ℝ)^y| ≤ (2*Real.log 2)*|x-y| := by
  have hlog := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt (fun x : ℝ => (2:ℝ)^x)
      ((2:ℝ)^t*Real.log 2) (Icc (0:ℝ) 1) t := by
    intro t _
    simpa using (exp_power_derivative 2 1 t (by norm_num)).hasDerivWithinAt
  have hb : ∀ t ∈ Icc (0:ℝ) 1, ‖(2:ℝ)^t*Real.log 2‖ ≤ 2*Real.log 2 := by
    intro t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hlog.le)]
    exact mul_le_mul_of_nonneg_right (two_rpow_mem t ht).2 hlog.le
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc 0 1) hy hx

theorem rho_neg_power_lipschitz (x y : ℝ) (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) :
    |rho^(-x)-rho^(-y)| ≤ Real.log rho*|x-y| := by
  have hlog := Real.log_pos (by linarith [rho_gt_two] : 1 < rho)
  have hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt (fun x : ℝ => rho^(-x))
      (-(rho^(-t)*Real.log rho)) (Icc (0:ℝ) 1) t := by
    intro t _
    simpa using (exp_power_derivative rho (-1) t rho_pos).hasDerivWithinAt
  have hb : ∀ t ∈ Icc (0:ℝ) 1, ‖-(rho^(-t)*Real.log rho)‖ ≤ Real.log rho := by
    intro t ht
    have hle : rho^(-t) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by linarith [rho_gt_two] : 1 ≤ rho) (show -t ≤ 0 by linarith [ht.1])
      simpa using h
    rw [norm_neg,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg rho_pos.le _) hlog.le)]
    simpa using mul_le_mul_of_nonneg_right hle hlog.le
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc 0 1) hy hx

theorem phaseProfile_endpoints : phaseProfile 0=1 ∧ phaseProfile 1=1 := by
  constructor
  · simp [phaseProfile,F_one]
  · simp [phaseProfile,F_two,Real.rpow_neg_one,rho_pos.ne']

theorem phaseProfile_lipschitz (x y : ℝ) (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) :
    |phaseProfile x-phaseProfile y| ≤ phaseLip*|x-y| := by
  have hlog := Real.log_pos (by linarith [rho_gt_two] : 1 < rho)
  have hFx := F_mem_range _ (two_rpow_mem x hx)
  have hFy := F_mem_range _ (two_rpow_mem y hy)
  have hF := (F_abs_bound _ _ (two_rpow_mem x hx) (two_rpow_mem y hy)).trans
    (mul_le_mul_of_nonneg_left (two_power_lipschitz x y hx hy) cplus_pos.le)
  have hr := rho_neg_power_lipschitz x y hx hy
  have ha : 0 ≤ rho^(-x) := Real.rpow_nonneg rho_pos.le _
  have hle : rho^(-x) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith [rho_gt_two] : 1 ≤ rho) (show -x ≤ 0 by linarith [hx.1])
  have hb : 0 ≤ F ((2:ℝ)^y) := by linarith [hFy.1]
  have he : phaseProfile x-phaseProfile y=
      rho^(-x)*(F ((2:ℝ)^x)-F ((2:ℝ)^y))+(rho^(-x)-rho^(-y))*F ((2:ℝ)^y) := by
    unfold phaseProfile
    ring
  rw [he]
  calc
    _ ≤ |rho^(-x)*(F ((2:ℝ)^x)-F ((2:ℝ)^y))|+|(rho^(-x)-rho^(-y))*F ((2:ℝ)^y)| := abs_add_le _ _
    _ = rho^(-x)*|F ((2:ℝ)^x)-F ((2:ℝ)^y)|+|rho^(-x)-rho^(-y)| * F ((2:ℝ)^y) := by
      rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
    _ ≤ 1*(cplus*((2*Real.log 2)*|x-y|))+(Real.log rho*|x-y|)*rho :=
      add_le_add (mul_le_mul hle hF (abs_nonneg _) (by norm_num))
        (mul_le_mul hr hFy.2 hb (by positivity))
    _ = phaseLip*|x-y| := by unfold phaseLip; ring

theorem Phi_eq_profile (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : Phi t=phaseProfile t := by
  rcases lt_or_eq_of_le ht.2 with h | rfl
  · rw [Phi,Int.fract_eq_self.mpr ⟨ht.1,h⟩]
    rfl
  · simp [Phi,phaseProfile_endpoints.2,F_one]

theorem Phi_pos (t : ℝ) : 0 < Phi t := by
  have h := F_mem_range _ (two_rpow_mem (Int.fract t) ⟨Int.fract_nonneg t,(Int.fract_lt_one t).le⟩)
  exact mul_pos (Real.rpow_pos_of_pos rho_pos _) (by linarith [h.1])

theorem Phi_periodic (t : ℝ) : Phi (t+1)=Phi t := by simp only [Phi,Int.fract_add_one]

theorem Phi_lipschitz : ∀ x y : ℝ, |Phi x-Phi y| ≤ phaseLip*|x-y| := by
  have ordered : ∀ x y : ℝ, x ≤ y → |Phi x-Phi y| ≤ phaseLip*(y-x) := by
    intro x y hxy
    let a := Int.fract x
    let b := Int.fract y
    have ha : a ∈ Icc (0:ℝ) 1 := ⟨Int.fract_nonneg x,(Int.fract_lt_one x).le⟩
    have hb : b ∈ Icc (0:ℝ) 1 := ⟨Int.fract_nonneg y,(Int.fract_lt_one y).le⟩
    change |phaseProfile a-phaseProfile b| ≤ _
    by_cases he : Int.floor x=Int.floor y
    · have hab : a-b=x-y := by change (x-(Int.floor x:ℝ))-(y-(Int.floor y:ℝ))=x-y; rw [he]; ring
      have h := phaseProfile_lipschitz a b ha hb
      rw [hab,abs_of_nonpos (sub_nonpos.mpr hxy)] at h
      simpa only [neg_sub] using h
    · have hf : Int.floor x+1 ≤ Int.floor y := by
        have := Int.floor_mono hxy
        omega
      have hfc : (Int.floor x:ℝ)+1 ≤ (Int.floor y:ℝ) := by exact_mod_cast hf
      have hgap : 1-a+b ≤ y-x := by change 1-(x-(Int.floor x:ℝ))+(y-(Int.floor y:ℝ)) ≤ y-x; linarith
      have h1 := phaseProfile_lipschitz a 1 ha (by norm_num)
      have h0 := phaseProfile_lipschitz 0 b (by norm_num) hb
      rw [phaseProfile_endpoints.2,abs_of_nonpos (by linarith [ha.2] : a-1 ≤ 0)] at h1
      rw [phaseProfile_endpoints.1,zero_sub,abs_neg,abs_of_nonneg hb.1] at h0
      have heq : phaseProfile a-phaseProfile b=(phaseProfile a-1)+(1-phaseProfile b) := by ring
      have ht := abs_add_le (phaseProfile a-1) (1-phaseProfile b)
      rw [← heq] at ht
      have hg := mul_le_mul_of_nonneg_left hgap phaseLip_pos.le
      linarith
  intro x y
  rcases le_total x y with h | h
  · simpa [abs_of_nonpos (sub_nonpos.mpr h),neg_sub] using ordered x y h
  · simpa only [abs_sub_comm (Phi y),abs_of_nonneg (sub_nonneg.mpr h)] using ordered y x h

theorem Phi_continuous : Continuous Phi := by
  have h : LipschitzWith ⟨phaseLip,phaseLip_pos.le⟩ Phi := by
    apply LipschitzWith.of_dist_le_mul
    simpa only [Real.dist_eq] using Phi_lipschitz
  exact h.continuous

theorem Phi_positive_periodic_lipschitz : PeriodicLipschitzPositive Phi :=
  ⟨Phi_pos,Phi_periodic,phaseLip,phaseLip_pos.le,Phi_lipschitz⟩

end
end GD
