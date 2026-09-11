import GD.MacroContact

namespace GD
noncomputable section
open Set Filter
open scoped Topology

/-- Low deficit yields a macroscopic contact along a subsequence. The actual
continuation is s-m, where s is the surviving spine size, not the initial n-m. -/
theorem deficit_concentration (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hE : Tendsto (fun k => deficit (n k)/(n k:ℝ)) atTop (𝓝 0)) :
    ∃ ν s m : ℕ → ℕ, StrictMono ν ∧
      (∀ k, 1 ≤ m k ∧ m k < s k ∧ s k ≤ n (ν k)) ∧
      Tendsto (fun k => (m k:ℝ)/(n (ν k):ℝ)) atTop (𝓝 alpha) ∧
      Tendsto (fun k => ((s k-m k:ℕ):ℝ)/(n (ν k):ℝ)) atTop (𝓝 (1-alpha)) ∧
      Tendsto (fun k => (U (m k))^q/(m k:ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun k => deficit (s k-m k)/((s k-m k:ℕ):ℝ)) atTop (𝓝 0) := by
  obtain ⟨ε,c0,hε,hc0,hsmall⟩ := small_pivot_constants
  have hevent := (hn.eventually (eventually_ge_atTop 2)).and
    (hE.eventually (gt_mem_nhds (show (0:ℝ) < c0/2 by positivity)))
  obtain ⟨K,hK⟩ := eventually_atTop.mp hevent
  let n0 := fun k : ℕ => n (K+k)
  have hn0 : Tendsto n0 atTop atTop := by simpa only [Nat.add_comm] using hn.comp (tendsto_add_atTop_nat K)
  have hE0 : Tendsto (fun k => deficit (n0 k)/(n0 k:ℝ)) atTop (𝓝 0) :=
    by simpa only [Nat.add_comm] using hE.comp (tendsto_add_atTop_nat K)
  have hall : ∀ k : ℕ, ∃ s m : ℕ, 1 ≤ m ∧ m < s ∧ s ≤ n0 k ∧ ε < (m:ℝ)/(s:ℝ) ∧
      W s=A (U m) (W (s-m)) ∧ c0*((n0 k:ℝ)-(s:ℝ))+deficit s ≤ deficit (n0 k) := by
    intro k
    have hk := hK (K+k) (by omega)
    exact low_deficit_first_macro ε c0 hc0 hsmall (n0 k) hk.1 hk.2
  choose s m hm hms hsN hmacro hp hbound using hall
  have hnpos : ∀ k, 0 < (n0 k:ℝ) := fun k => by exact_mod_cast (show 0 < n0 k by have := hm k; have := hms k; have := hsN k; omega)
  have hspos : ∀ k, 0 < (s k:ℝ) := fun k => by exact_mod_cast (show 0 < s k by have := hm k; have := hms k; omega)
  have hEs : ∀ k, 0 ≤ deficit (s k) := fun k => deficit_nonneg _ (by have := hm k; have := hms k; omega)
  have hdrop : ∀ k, 0 ≤ (n0 k:ℝ)-(s k:ℝ) := fun k => sub_nonneg.mpr (by exact_mod_cast hsN k)
  have hdropbound : ∀ k, (n0 k:ℝ)-(s k:ℝ) ≤ deficit (n0 k)/c0 := by
    intro k
    apply (le_div_iff₀ hc0).mpr
    have h := hbound k
    nlinarith [hEs k]
  have hdropzero : Tendsto (fun k => ((n0 k:ℝ)-(s k:ℝ))/(n0 k:ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => div_nonneg (hdrop k) (hnpos k).le)
      (g:=fun k => (deficit (n0 k)/(n0 k:ℝ))/c0)
    · intro k
      have h := div_le_div_of_nonneg_right (hdropbound k) (hnpos k).le
      simpa only [div_right_comm] using h
    · simpa using hE0.div_const c0
  have hsratio : Tendsto (fun k => (s k:ℝ)/(n0 k:ℝ)) atTop (𝓝 1) := by
    have h := hdropzero.const_sub 1
    simp only [sub_zero] at h
    apply h.congr'
    exact Eventually.of_forall (fun k => by change 1-((n0 k:ℝ)-(s k:ℝ))/(n0 k:ℝ)=(s k:ℝ)/(n0 k:ℝ); rw [sub_div,div_self (hnpos k).ne']; ring)
  have hEsN : Tendsto (fun k => deficit (s k)/(n0 k:ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => div_nonneg (hEs k) (hnpos k).le) (g:=fun k => deficit (n0 k)/(n0 k:ℝ))
    · intro k
      apply div_le_div_of_nonneg_right _ (hnpos k).le
      have h := hbound k
      nlinarith [mul_nonneg hc0.le (hdrop k)]
    · exact hE0
  have hEss : Tendsto (fun k => deficit (s k)/(s k:ℝ)) atTop (𝓝 0) := by
    have h := hEsN.div hsratio (by norm_num : (1:ℝ) ≠ 0)
    rw [zero_div] at h
    apply h.congr'
    exact Eventually.of_forall (fun k => div_div_div_cancel_right₀ (hnpos k).ne' _ _)
  have hcompact : ∀ k, (m k:ℝ)/(s k:ℝ) ∈ Icc ε 1 := by
    intro k
    exact ⟨(hmacro k).le,(div_le_one (hspos k)).mpr (by exact_mod_cast (hms k).le)⟩
  obtain ⟨β,hβ,ν,hν,hfrac⟩ := isCompact_Icc.tendsto_subseq hcompact
  have hβ0 : 0 < β := hε.1.trans_le hβ.1
  have hcontact := macro_contact_limit (s ∘ ν) (m ∘ ν) β hβ0
    (fun k => hm (ν k)) (fun k => hms (ν k)) (fun k => hp (ν k)) (hEss.comp hν.tendsto_atTop) hfrac
  have hα : β=alpha := hcontact.1
  have hmN : Tendsto (fun k => (m (ν k):ℝ)/(n0 (ν k):ℝ)) atTop (𝓝 alpha) := by
    have h := hfrac.mul (hsratio.comp hν.tendsto_atTop)
    rw [mul_one,hα] at h
    apply h.congr'
    exact Eventually.of_forall (fun k => by change (m (ν k):ℝ)/(s (ν k):ℝ)*((s (ν k):ℝ)/(n0 (ν k):ℝ))=(m (ν k):ℝ)/(n0 (ν k):ℝ); field_simp [(hspos (ν k)).ne',(hnpos (ν k)).ne'])
  have hrN : Tendsto (fun k => ((s (ν k)-m (ν k):ℕ):ℝ)/(n0 (ν k):ℝ)) atTop (𝓝 (1-alpha)) := by
    apply ((hsratio.comp hν.tendsto_atTop).sub hmN).congr'
    exact Eventually.of_forall (fun k => by change (s (ν k):ℝ)/(n0 (ν k):ℝ)-(m (ν k):ℝ)/(n0 (ν k):ℝ)=((s (ν k)-m (ν k):ℕ):ℝ)/(n0 (ν k):ℝ); rw [Nat.cast_sub (hms (ν k)).le,sub_div])
  refine ⟨fun k => K+ν k,s ∘ ν,m ∘ ν,?_,?_,hmN,hrN,hcontact.2.1,hcontact.2.2⟩
  · exact fun i j hij => Nat.add_lt_add_left (hν hij) K
  · exact fun k => ⟨hm (ν k),hms (ν k),hsN (ν k)⟩

end
end GD
