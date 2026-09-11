import GD.SilverPower

namespace GD
noncomputable section

theorem U_dyadic_q (k : ℕ) : (U (2^k))^q=(2^k:ℕ) := by
  have hu : U (2^k)=rho^k := by simpa using U_dyadic k 1
  rw [hu,← Real.rpow_pow_comm rho_pos.le,rho_rpow_q]
  norm_cast

theorem U_power_q (N : ℕ) (hN : 1 ≤ N) :
    (U N)^q ≤ (N:ℝ) ∧ ((U N)^q=(N:ℝ) ↔ ∃ k : ℕ, N=2^k) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hn : N=1
    · subst N
      simp only [U_one,Real.one_rpow,Nat.cast_one,le_refl,true_and]
      exact ⟨fun _ => ⟨0,by norm_num⟩,fun _ => trivial⟩
    have hn2 : 2 ≤ N := by omega
    let a := N/2
    let b := (N+1)/2
    have ha : 1 ≤ a := by dsimp [a]; omega
    have hb : 1 ≤ b := by dsimp [b]; omega
    have haN : a < N := by dsimp [a]; omega
    have hbN : b < N := by dsimp [b]; omega
    have hab : a+b=N := by dsimp [a,b]; omega
    have hcast : (a:ℝ)+(b:ℝ)=(N:ℝ) := by exact_mod_cast hab
    have hia := ih a haN ha
    have hib := ih b hbN hb
    have hrec : U N=K (U a) (U b) := corollary_4_2.2.2 N hn2
    have hK := silver_power_nonnegative (U a) (U b) (U_nonneg a) (U_nonneg b)
    rw [← hrec] at hK
    have hup : (U N)^q ≤ (N:ℝ) := by linarith [hK.1,hia.1,hib.1]
    refine ⟨hup,?_,?_⟩
    · intro he
      have heK : (U N)^q=(U a)^q+(U b)^q := by linarith [hK.1,hia.1,hib.1]
      have heab : a=b := by
        rcases hK.2.mp heK with h | h
        · exact U_strictMono.injective h
        · have hp := mul_pos (U_pos (by omega : 0 < a)) (U_pos (by omega : 0 < b))
          exact False.elim (hp.ne' h)
      have hea : (U a)^q=(a:ℝ) := by rw [← heab] at hib hcast heK; linarith
      obtain ⟨k,hk⟩ := hia.2.mp hea
      refine ⟨k+1,?_⟩
      rw [← hab,← heab,hk,pow_succ]
      omega
    · rintro ⟨k,rfl⟩
      exact U_dyadic_q k

/-- Proposition 5.2, including necessity and sufficiency of the dyadic case. -/
theorem proposition_5_2 : Targets.proposition_5_2 := by
  intro N hN
  have h := U_power_q N hN
  have hu := U_nonneg N
  have hleft : ((U N)^q)^p=U N := by
    rw [← Real.rpow_mul hu,mul_comm q p,p_mul_q,Real.rpow_one]
  have hright : ((N:ℝ)^p)^q=(N:ℝ) := by
    rw [← Real.rpow_mul (Nat.cast_nonneg N),p_mul_q,Real.rpow_one]
  constructor
  · have hp := Real.rpow_le_rpow (Real.rpow_nonneg hu _) h.1 p_pos.le
    rwa [hleft] at hp
  · constructor
    · intro he
      apply h.2.mp
      rw [he,hright]
    · intro he
      have hp := congrArg (fun x : ℝ => x^p) (h.2.mpr he)
      dsimp only at hp
      rwa [hleft] at hp

end
end GD
