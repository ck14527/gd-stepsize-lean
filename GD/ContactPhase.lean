import GD.DeficitConcentration
import GD.D8Repair

namespace GD
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 1200000

theorem periodic_phase_scale (g : ℝ → ℝ) (hg : Function.Periodic g 1) (N k : ℕ) (hN : 1 ≤ N) :
    g (phase N)=g (Real.logb 2 ((N:ℝ)/(2:ℝ)^k)) := by
  have hn0 : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  rw [Real.logb_div hn0.ne' (by positivity),Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2),mul_one]
  have hh := hg.sub_nat_mul_eq k (x:=Real.logb 2 (N:ℝ))
  rw [mul_one] at hh
  rw [hh]
  exact periodic_fract g hg _

theorem periodic_phase_scaled_tendsto (g : ℝ → ℝ) (hg : Function.Periodic g 1) (hc : Continuous g)
    (n v : ℕ → ℕ) (x : ℝ) (hx : 0 < x) (hn : Tendsto n atTop atTop)
    (hs : Tendsto (fun k => (n k:ℝ)/(2:ℝ)^(v k)) atTop (𝓝 x)) :
    Tendsto (fun k => g (phase (n k))) atTop (𝓝 (g (Real.logb 2 x))) := by
  have h := (hc.continuousAt.comp (Real.continuousAt_logb (b:=2) hx.ne')).tendsto.comp hs
  apply h.congr'
  filter_upwards [hn.eventually (eventually_ge_atTop 1)] with k hk
  exact (periodic_phase_scale g hg (n k) (v k) hk).symm

theorem C_scaled_tendsto (n v : ℕ → ℕ) (x : ℝ) (hx : 0 < x) (hn : Tendsto n atTop atTop)
    (hs : Tendsto (fun k => (n k:ℝ)/(2:ℝ)^(v k)) atTop (𝓝 x)) :
    Tendsto (fun k => C (n k)) atTop (𝓝 (Psi (Real.logb 2 x))) := by
  have hp := periodic_phase_scaled_tendsto Psi Psi_periodic Psi_continuous n v x hx hn hs
  have he := (OBSPhase_error Psi Psi_OBSPhase).comp hn
  have h := he.add hp
  simpa only [Function.comp_apply,sub_add_cancel,zero_add] using h

theorem U_phase_power (m : ℕ) (hm : 1 ≤ m) : (U m)^q/(m:ℝ)=(Phi (phase m))^q := by
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  rw [U_phase_exact m hm,Real.mul_rpow (Real.rpow_nonneg hm0.le p) (Phi_pos _).le,rpow_p_q _ hm0.le]
  exact mul_div_cancel_left₀ _ hm0.ne'

/-- Contact propagation for the actual canonical profiles. The continuation
sizes come from the finite spine theorem, and all limits are proved above. -/
theorem phase_contact (t : ℝ) (ht : Psi t=cstar) :
    Phi (t+Real.logb 2 alpha)=1 ∧ Psi (t+Real.logb 2 (1-alpha))=cstar := by
  let x := (2:ℝ)^t
  have hx : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  let n := fun k : ℕ => Nat.floor (x*(2:ℝ)^k)
  have hn : Tendsto n atTop atTop := scaled_floor_atTop x hx
  have hnx : Tendsto (fun k => (n k:ℝ)/(2:ℝ)^k) atTop (𝓝 x) := scaled_floor_limit x hx.le
  have hxlog : Real.logb 2 x=t := Real.logb_rpow (by norm_num) (by norm_num)
  have hCn := C_scaled_tendsto n id x hx hn hnx
  rw [hxlog,ht] at hCn
  obtain ⟨ν,s,m,hν,hs,hmN,hrN,hU,hEr⟩ := deficit_concentration n hn (deficit_tendsto_of_C n hn hCn)
  have hα : 0 < alpha := lt_trans (by norm_num : (0:ℝ) < 1/2) lemma_D_5.2.2.2.2.1
  have hrα : 0 < 1-alpha := sub_pos.mpr lemma_D_5.2.2.2.2.2
  have hnv : Tendsto (fun k => n (ν k)) atTop atTop := hn.comp hν.tendsto_atTop
  have hmat : Tendsto m atTop atTop := nat_atTop_of_ratio m (n ∘ ν) hnv alpha hα hmN
  let r := fun k => s k-m k
  have hrat : Tendsto r atTop atTop := nat_atTop_of_ratio r (n ∘ ν) hnv (1-alpha) hrα hrN
  have hnpos : ∀ k, 0 < (n (ν k):ℝ) := fun k => by
    have hh := hs k
    exact_mod_cast (show 0 < n (ν k) by omega)
  have hmx : Tendsto (fun k => (m k:ℝ)/(2:ℝ)^(ν k)) atTop (𝓝 (alpha*x)) := by
    apply (hmN.mul (hnx.comp hν.tendsto_atTop)).congr'
    exact Eventually.of_forall (fun k => by
      change (m k:ℝ)/(n (ν k):ℝ)*((n (ν k):ℝ)/(2:ℝ)^(ν k))=(m k:ℝ)/(2:ℝ)^(ν k)
      field_simp [(hnpos k).ne'])
  have hrx : Tendsto (fun k => (r k:ℝ)/(2:ℝ)^(ν k)) atTop (𝓝 ((1-alpha)*x)) := by
    apply (hrN.mul (hnx.comp hν.tendsto_atTop)).congr'
    exact Eventually.of_forall (fun k => by
      change (r k:ℝ)/(n (ν k):ℝ)*((n (ν k):ℝ)/(2:ℝ)^(ν k))=(r k:ℝ)/(2:ℝ)^(ν k)
      field_simp [(hnpos k).ne'])
  have hmPhi := periodic_phase_scaled_tendsto Phi Phi_periodic Phi_continuous m ν (alpha*x) (mul_pos hα hx) hmat hmx
  have hPhiq := hmPhi.rpow_const (Or.inr q_pos.le)
  have hPhi1 : Tendsto (fun k => (Phi (phase (m k)))^q) atTop (𝓝 1) := by
    apply hU.congr'
    exact Eventually.of_forall (fun k => U_phase_power (m k) (hs k).1)
  have hPhiqEq := tendsto_nhds_unique hPhiq hPhi1
  have hPhiEq : Phi (Real.logb 2 (alpha*x))=1 := by
    have hh := congrArg (fun z : ℝ => z^p) hPhiqEq
    change ((Phi (Real.logb 2 (alpha*x)))^q)^p=(1:ℝ)^p at hh
    simpa only [rpow_q_p _ (Phi_pos _).le,Real.one_rpow] using hh
  have hCrl := C_scaled_tendsto r ν ((1-alpha)*x) (mul_pos hrα hx) hrat hrx
  have hCr := C_tendsto_of_deficit r hrat hEr
  have hPsiEq := tendsto_nhds_unique hCrl hCr
  rw [Real.logb_mul hα.ne' hx.ne',hxlog,add_comm] at hPhiEq
  rw [Real.logb_mul hrα.ne' hx.ne',hxlog,add_comm] at hPsiEq
  exact ⟨hPhiEq,hPsiEq⟩

theorem Phi_contact_integer (t : ℝ) (ht : Phi t=1) : ∃ z : ℤ, t=(z:ℝ) := by
  have hfract : Int.fract t=0 := by
    by_contra h
    have hpos : 0 < Int.fract t := lt_of_le_of_ne (Int.fract_nonneg t) (Ne.symm h)
    have hh := Phi_lt_one (Int.fract t) ⟨hpos,Int.fract_lt_one t⟩
    rw [periodic_fract Phi Phi_periodic t,ht] at hh
    exact (lt_irrefl 1 hh)
  refine ⟨Int.floor t,?_⟩
  change t-(Int.floor t:ℝ)=0 at hfract
  linarith

theorem Psi_ne_cstar (t : ℝ) : Psi t ≠ cstar := by
  intro ht
  have h0 := phase_contact t ht
  have h1 := phase_contact (t+Real.logb 2 (1-alpha)) h0.2
  exact D8.two_contact_contradiction alpha t (t+Real.logb 2 (1-alpha))
    contact_fraction_bounds.1 contact_fraction_bounds.2
    (Phi_contact_integer _ h0.1) (Phi_contact_integer _ h1.1) ⟨0,by simp⟩

theorem theorem_D_8 : Targets.theorem_D_8 := by
  have hpoint : ∀ t, cstar < Psi t := by
    intro t
    have hge : cstar ≤ Psi t := by
      rw [Psi_eq_mantissa]
      exact (obsMantissa_bounds _ (two_rpow_mem _ ⟨Int.fract_nonneg t,(Int.fract_lt_one t).le⟩)).1
    exact lt_of_le_of_ne hge (Ne.symm (Psi_ne_cstar t))
  refine ⟨hpoint,?_⟩
  obtain ⟨a,ha,b,hb,hea,heb,hbound⟩ := Psi_extrema
  rw [← hea]
  exact hpoint a

theorem theorem_D_6 : Targets.theorem_D_6 := by
  refine ⟨Psi 0,?_,theorem_D_8.1 0⟩
  have h := OBSPhase_ray Psi Psi_OBSPhase 1 (by norm_num)
  simpa [phase] using h

theorem theorem_6_5 : Targets.theorem_6_5 := by
  obtain ⟨a,ha,b,hb,hea,heb,hbound⟩ := Psi_extrema
  refine ⟨theorem_D_8.2,?_,?_⟩
  · rw [← hea,← heb]
    have hle := (hbound a).2
    apply lt_of_le_of_ne hle
    intro he
    have hc : ∀ t, Psi t=Psi a := by
      intro t
      have hh := hbound t
      rw [← he] at hh
      exact le_antisymm hh.2 hh.1
    have hstar := lemma_D_7 (Psi a) hc
    have hh := theorem_D_8.1 a
    rw [hstar] at hh
    exact lt_irrefl _ hh
  · rw [← heb]
    exact proposition_D_9 b

end
end GD
