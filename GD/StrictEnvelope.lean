import GD.DeficitBounds

namespace GD
noncomputable section
open Set Filter
open scoped Topology

def tentGap : ℝ := 3-(U 3)^q

theorem tentGap_pos : 0 < tentGap := by
  have h := silver_power_nonnegative (U 1) (U 2) (U_nonneg 1) (U_nonneg 2)
  have hu : U 3=K (U 1) (U 2) := by simpa using U_odd 1
  have hu2 : (U 2)^q=2 := by simpa using U_dyadic_q 1
  rw [← hu,U_one,Real.one_rpow,hu2] at h
  have hne : (U 3)^q ≠ 1+2 := by
    intro he
    rcases h.2.mp he with he | he
    · have hs := U_strictMono (by norm_num : 1 < 2)
      rw [U_one] at hs
      linarith
    · have hp := U_pos (by norm_num : 0 < 2)
      simp only [one_mul] at he
      exact hp.ne' he
  unfold tentGap
  have hlt := lt_of_le_of_ne h.1 hne
  linarith

theorem U_q_even (n : ℕ) : (U (2*n))^q=2*(U n)^q := by
  rw [U_even,Real.mul_rpow rho_pos.le (U_nonneg n),rho_rpow_q]

theorem U_q_odd_le (n : ℕ) : (U (2*n+1))^q ≤ (U n)^q+(U (n+1))^q := by
  rw [U_odd]
  exact (silver_power_nonnegative _ _ (U_nonneg n) (U_nonneg (n+1))).1

def natTent (k n : ℕ) : ℕ := min (n-2^k) (2^(k+1)-n)

theorem natTent_double (k n : ℕ) : natTent (k+1) (2*n)=2*natTent k n := by
  unfold natTent
  rw [show (2:ℕ)^(k+1)=2*2^k by ring,show (2:ℕ)^(k+1+1)=2*(2*2^k) by ring]
  omega

theorem natTent_odd (k n : ℕ) (hk : 1 ≤ k) (hn : 2^k ≤ n) (hn' : n+1 ≤ 2^(k+1)) :
    natTent (k+1) (2*n+1)=natTent k n+natTent k (n+1) := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hp : (2:ℕ)^(l+1)=2*2^l := by ring
  have hp2 : (2:ℕ)^(l+1+1)=4*2^l := by ring
  have hp3 : (2:ℕ)^(l+1+1+1)=8*2^l := by ring
  unfold natTent
  rw [hp,hp2,hp3]
  rw [hp] at hn
  rw [hp2] at hn'
  omega

theorem U_tent_bound (k n : ℕ) (hk : 1 ≤ k) (hn : 2^k ≤ n) (hn' : n ≤ 2^(k+1)) :
    (U n)^q ≤ (n:ℝ)-tentGap*(natTent k n:ℝ) := by
  induction k, hk using Nat.le_induction generalizing n with
  | base =>
    norm_num at hn hn'
    interval_cases n
    · have h := U_dyadic_q 1
      norm_num [natTent] at h ⊢
      exact h.le
    · simp [natTent,tentGap]
    · have h := U_dyadic_q 2
      norm_num [natTent] at h ⊢
      exact h.le
  | succ k hk ih =>
    let m := n/2
    have hp : (2:ℕ)^(k+1)=2*2^k := by ring
    have hp2 : (2:ℕ)^(k+1+1)=2*2^(k+1) := by ring
    by_cases he : n%2=0
    · have hnval : n=2*m := by dsimp [m]; omega
      have hm : 2^k ≤ m := by rw [hp] at hn; dsimp [m]; omega
      have hm' : m ≤ 2^(k+1) := by rw [hp2] at hn'; dsimp [m]; omega
      have hi := ih m hm hm'
      rw [hnval,U_q_even,natTent_double]
      push_cast
      nlinarith
    · have hnval : n=2*m+1 := by dsimp [m]; omega
      have hm : 2^k ≤ m := by rw [hp] at hn; dsimp [m]; omega
      have hm' : m+1 ≤ 2^(k+1) := by rw [hp2] at hn'; dsimp [m]; omega
      have hi := ih m hm (by omega)
      have hi' := ih (m+1) (by omega) hm'
      have hq := U_q_odd_le m
      rw [hnval,natTent_odd k m hk hm hm']
      push_cast at hi' ⊢
      linarith

theorem natTent_cast (k n : ℕ) (hn : 2^k ≤ n) (hn' : n ≤ 2^(k+1)) :
    (natTent k n:ℝ)=min ((n:ℝ)-(2:ℝ)^k) ((2:ℝ)^(k+1)-(n:ℝ)) := by
  simp only [natTent,Nat.cast_min,Nat.cast_sub hn,Nat.cast_sub hn',Nat.cast_pow,Nat.cast_ofNat]

theorem F_grid_tent (k n : ℕ) (hk : 1 ≤ k) (hn : 2^k ≤ n) (hn' : n ≤ 2^(k+1)) :
    (F ((n:ℝ)/(2:ℝ)^k))^q ≤ (n:ℝ)/(2:ℝ)^k-
      tentGap*min ((n:ℝ)/(2:ℝ)^k-1) (2-(n:ℝ)/(2:ℝ)^k) := by
  have hp : 0 < (2:ℝ)^k := by positivity
  have h := U_tent_bound k n hk hn hn'
  rw [F_grid k n hn hn',Real.div_rpow (U_nonneg n) (pow_nonneg rho_pos.le k),
    ← Real.rpow_pow_comm rho_pos.le,rho_rpow_q]
  have hb := (div_le_div_of_nonneg_right h hp.le)
  rw [natTent_cast k n hn hn',pow_succ] at hb
  have he : min ((n:ℝ)-(2:ℝ)^k) ((2:ℝ)^k*2-(n:ℝ))/(2:ℝ)^k=
      min ((n:ℝ)/(2:ℝ)^k-1) (2-(n:ℝ)/(2:ℝ)^k) := by
    rw [← min_div_div_right hp.le]
    congr 1 <;> field_simp <;> ring
  rw [sub_div,mul_div_assoc,he] at hb
  exact hb

theorem F_tent_bound (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
    (F x)^q ≤ x-tentGap*min (x-1) (2-x) := by
  let a := fun k : ℕ => (cellIndex (k+1) x:ℝ)/(2:ℝ)^(k+1)
  have ha : Tendsto a atTop (𝓝[Icc (1:ℝ) 2] x) :=
    (cell_point_tendsto x hx).comp (tendsto_add_atTop_nat 1)
  have hax : Tendsto a atTop (𝓝 x) := tendsto_nhds_of_tendsto_nhdsWithin ha
  have hF := ((F_continuousOn x hx).tendsto.comp ha).rpow_const (Or.inr q_pos.le)
  have hg := hax.sub ((hax.sub_const 1).min ((tendsto_const_nhds (x:=(2:ℝ))).sub hax) |>.const_mul tentGap)
  apply le_of_tendsto_of_tendsto' hF hg
  intro k
  have hc := cell_bounds (k+1) x hx
  exact F_grid_tent (k+1) _ (by omega) hc.1 (by omega)

theorem F_lt_power (x : ℝ) (hx : x ∈ Ioo (1:ℝ) 2) : F x < x^p := by
  have hg := F_tent_bound x ⟨hx.1.le,hx.2.le⟩
  have hmin : 0 < min (x-1) (2-x) := lt_min (by linarith [hx.1]) (by linarith [hx.2])
  have hq : (F x)^q < x := by nlinarith [mul_pos tentGap_pos hmin]
  have hf : 0 ≤ F x := by
    have hr := F_range
    have hm : F x ∈ Icc (1:ℝ) rho := by rw [← hr]; exact ⟨x,⟨hx.1.le,hx.2.le⟩,rfl⟩
    linarith [hm.1]
  have hp := Real.rpow_lt_rpow (Real.rpow_nonneg hf _) hq p_pos
  rwa [← Real.rpow_mul hf,mul_comm q p,p_mul_q,Real.rpow_one] at hp

theorem Phi_lt_one (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : Phi t < 1 := by
  have hf : Int.fract t=t := Int.fract_eq_self.mpr ⟨ht.1.le,ht.2⟩
  have hx0 : 0 < (2:ℝ)^t := Real.rpow_pos_of_pos (by norm_num) _
  have hx : (2:ℝ)^t ∈ Ioo (1:ℝ) 2 := by
    constructor
    · exact Real.one_lt_rpow (by norm_num) ht.1
    · have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) ht.2
      simpa using h
  have h := mul_lt_mul_of_pos_left (F_lt_power _ hx) (Real.rpow_pos_of_pos rho_pos (-t))
  have he : rho^(-t)*((2:ℝ)^t)^p=1 := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),mul_comm t p,
      Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),two_rpow_p,← Real.rpow_add rho_pos]
    simp
  simpa only [Phi,hf,he] using h

/-- Lemma D.4; the explicit tent deficit also supplies quantitative strictness. -/
theorem lemma_D_4 : Targets.lemma_D_4 := ⟨F_lt_power,Phi_lt_one⟩

end
end GD
