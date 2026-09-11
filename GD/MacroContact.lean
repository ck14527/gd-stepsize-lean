import GD.DeficitLimits

namespace GD
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 1200000

theorem pivot_deficit_terms (s m : ℕ) (hm : 1 ≤ m) (hms : m < s)
    (hp : W s=A (U m) (W (s-m))) :
    (0 ≤ Bsup*((m:ℝ)-(U m)^q) ∧ Bsup*((m:ℝ)-(U m)^q) ≤ deficit s) ∧
    (0 ≤ deficit (s-m) ∧ deficit (s-m) ≤ deficit s) ∧
    (0 ≤ sigma (U m) (W (s-m)) ∧ sigma (U m) (W (s-m)) ≤ deficit s) := by
  have h := proposition_D_3.2 s m hm hms hp
  exact ⟨⟨h.2.1,by linarith [h.1,h.2.2.1,h.2.2.2]⟩,
    ⟨h.2.2.1,by linarith [h.1,h.2.1,h.2.2.2]⟩,
    ⟨h.2.2.2,by linarith [h.1,h.2.1,h.2.2.1]⟩⟩

theorem normalized_sigma (s m : ℕ) (hm : 1 ≤ m) (hms : m < s) :
    sigma (U m/(s:ℝ)^p) (W (s-m)/(s:ℝ)^p)=sigma (U m) (W (s-m))/(s:ℝ) := by
  have hs0 : 0 < (s:ℝ) := by exact_mod_cast (show 0 < s by omega)
  have h := sigma_hom ((s:ℝ)^p)⁻¹ (U m) (W (s-m)) (by positivity) (U_nonneg _) (W_pos _ (by omega)).le
  simp only [← div_eq_inv_mul] at h
  rw [h,Real.inv_rpow (Real.rpow_nonneg hs0.le _),rpow_p_q _ hs0.le,div_eq_inv_mul]

theorem macro_contact_limit (s m : ℕ → ℕ) (β : ℝ) (hβ : 0 < β)
    (hm : ∀ k, 1 ≤ m k) (hms : ∀ k, m k < s k)
    (hp : ∀ k, W (s k)=A (U (m k)) (W (s k-m k)))
    (hE : Tendsto (fun k => deficit (s k)/(s k:ℝ)) atTop (𝓝 0))
    (hfrac : Tendsto (fun k => (m k:ℝ)/(s k:ℝ)) atTop (𝓝 β)) :
    β=alpha ∧
    Tendsto (fun k => (U (m k))^q/(m k:ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun k => deficit (s k-m k)/(s k-m k:ℕ)) atTop (𝓝 0) := by
  have hs0 : ∀ k, 0 < (s k:ℝ) := fun k => by exact_mod_cast (show 0 < s k by have := hm k; have := hms k; omega)
  have hm0 : ∀ k, 0 < (m k:ℝ) := fun k => by exact_mod_cast (show 0 < m k by have := hm k; omega)
  have hr0 : ∀ k, 0 < ((s k-m k:ℕ):ℝ) := fun k => by exact_mod_cast (show 0 < s k-m k by have := hms k; omega)
  have hterms := fun k => pivot_deficit_terms (s k) (m k) (hm k) (hms k) (hp k)
  have hpre : Tendsto (fun k => Bsup*((m k:ℝ)-(U (m k))^q)/(s k:ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun k => div_nonneg (hterms k).1.1 (hs0 k).le)
      (fun k => div_le_div_of_nonneg_right (hterms k).1.2 (hs0 k).le) hE
  have hrem : Tendsto (fun k => deficit (s k-m k)/(s k:ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun k => div_nonneg (hterms k).2.1.1 (hs0 k).le)
      (fun k => div_le_div_of_nonneg_right (hterms k).2.1.2 (hs0 k).le) hE
  have hslack : Tendsto (fun k => sigma (U (m k)) (W (s k-m k))/(s k:ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun k => div_nonneg (hterms k).2.2.1 (hs0 k).le)
      (fun k => div_le_div_of_nonneg_right (hterms k).2.2.2 (hs0 k).le) hE
  have hUq : Tendsto (fun k => (U (m k))^q/(s k:ℝ)) atTop (𝓝 β) := by
    have h := hfrac.sub (hpre.div_const Bsup)
    simp only [zero_div,sub_zero] at h
    apply h.congr'
    exact Eventually.of_forall (fun k => by
      change (m k:ℝ)/(s k:ℝ)-(Bsup*((m k:ℝ)-(U (m k))^q)/(s k:ℝ))/Bsup=(U (m k))^q/(s k:ℝ)
      field_simp [Bsup_pos.ne',(hs0 k).ne']
      <;> ring)
  have hr : Tendsto (fun k => ((s k-m k:ℕ):ℝ)/(s k:ℝ)) atTop (𝓝 (1-β)) := by
    apply ((tendsto_const_nhds (x:=(1:ℝ))).sub hfrac).congr'
    exact Eventually.of_forall (fun k => by change 1-(m k:ℝ)/(s k:ℝ)=((s k-m k:ℕ):ℝ)/(s k:ℝ); rw [Nat.cast_sub (hms k).le,sub_div,div_self (hs0 k).ne'])
  have hWq : Tendsto (fun k => (W (s k-m k))^q/(s k:ℝ)) atTop (𝓝 (Bsup*(1-β))) := by
    have h := (hr.const_mul Bsup).sub hrem
    simp only [sub_zero] at h
    apply h.congr'
    exact Eventually.of_forall (fun k => by change Bsup*(((s k-m k:ℕ):ℝ)/(s k:ℝ))-deficit (s k-m k)/(s k:ℝ)=(W (s k-m k))^q/(s k:ℝ); unfold deficit; ring)
  have hU := power_scaled_tendsto (fun k => U (m k)) (fun k => (s k:ℝ)) β (fun k => U_nonneg _) hs0 hUq
  have hW := power_scaled_tendsto (fun k => W (s k-m k)) (fun k => (s k:ℝ)) (Bsup*(1-β))
    (fun k => (W_pos _ (by have := hms k; omega)).le) hs0 hWq
  have hsig : Tendsto (fun k => sigma (U (m k)/(s k:ℝ)^p) (W (s k-m k)/(s k:ℝ)^p)) atTop
      (𝓝 (sigma (β^p) ((Bsup*(1-β))^p))) :=
    sigma_continuous.continuousAt.tendsto.comp (hU.prodMk_nhds hW)
  have hsig0 : Tendsto (fun k => sigma (U (m k)/(s k:ℝ)^p) (W (s k-m k)/(s k:ℝ)^p)) atTop (𝓝 0) := by
    simpa only [normalized_sigma _ _ (hm _) (hms _)] using hslack
  have hβle : β ≤ 1 := le_of_tendsto' hfrac (fun k => (div_le_one (hs0 k)).mpr (by exact_mod_cast (hms k).le))
  have hα := support_contact_fraction β ⟨hβ,hβle⟩ (tendsto_nhds_unique hsig hsig0)
  refine ⟨hα,?_,?_⟩
  · have h := hUq.div hfrac hβ.ne'
    rw [div_self hβ.ne'] at h
    apply h.congr'
    exact Eventually.of_forall (fun k => div_div_div_cancel_right₀ (hs0 k).ne' _ _)
  · have hβ1 : β < 1 := hα ▸ lemma_D_5.2.2.2.2.2
    have h := hrem.div hr (sub_pos.mpr hβ1).ne'
    rw [zero_div] at h
    apply h.congr'
    exact Eventually.of_forall (fun k => div_div_div_cancel_right₀ (hs0 k).ne' _ _)

end
end GD
