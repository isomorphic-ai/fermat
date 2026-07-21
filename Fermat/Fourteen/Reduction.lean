import Fermat.Fourteen.Dirichlet

/-!
# Reduction of FLT for exponent 14 to Dirichlet's two cases

This file is the outer shell of Dirichlet's direct proof.  It reduces a
primitive counterexample to either the first case (none of the three entries
is divisible by `7`) or to the generalized equation used in the infinite
descent.  No result for exponent `7` is used.
-/

namespace Fermat.Fourteen.Dirichlet

/-- The remaining first-case obligation in a form independent of the later
power-extraction implementation. -/
def FirstCaseImpossible : Prop :=
  ∀ ⦃t u v : ℤ⦄, t * u * v ≠ 0 → IsCoprime t u → IsCoprime t v →
    t ^ 14 = u ^ 14 + v ^ 14 →
    ¬(7 : ℤ) ∣ t → ¬(7 : ℤ) ∣ u → ¬(7 : ℤ) ∣ v → False

private theorem zmod_seven_sum_fourteen_eq_zero :
    ∀ a b : ZMod 7, a ^ 14 + b ^ 14 = 0 → a = 0 ∧ b = 0 := by
  decide

/-- In a primitive solution, the term on the right cannot be divisible by
`7`.  This is the elementary `-1` nonresidue calculation modulo `7`. -/
theorem not_seven_dvd_right {t u v : ℤ} (huv : IsCoprime u v)
    (heq : t ^ 14 = u ^ 14 + v ^ 14) : ¬(7 : ℤ) ∣ t := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro ht
  have ht' : (t : ZMod 7) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd t 7).2 ht
  have heq' : (u : ZMod 7) ^ 14 + (v : ZMod 7) ^ 14 = 0 := by
    have := congrArg (fun z : ℤ ↦ (z : ZMod 7)) heq
    simpa [ht'] using this.symm
  obtain ⟨hu, hv⟩ := zmod_seven_sum_fourteen_eq_zero (u : ZMod 7) (v : ZMod 7) heq'
  have h7u : (7 : ℤ) ∣ u := (ZMod.intCast_zmod_eq_zero_iff_dvd u 7).1 hu
  have h7v : (7 : ℤ) ∣ v := (ZMod.intCast_zmod_eq_zero_iff_dvd v 7).1 hv
  have : IsUnit (7 : ℤ) := huv.isUnit_of_dvd' h7u h7v
  norm_num [Int.isUnit_iff] at this

/-- Pairwise coprimality follows from primitivity and the Fermat equation. -/
private theorem pairwise_isCoprime_of_gcd_eq_one {a b c : ℤ}
    (hgcd : Finset.gcd {a, b, c} id = 1)
    (heq : a ^ 14 + b ^ 14 = c ^ 14) :
    IsCoprime a b ∧ IsCoprime a c ∧ IsCoprime b c := by
  have common_prime_absurd (p : ℤ) (hp : Prime p)
      (hpa : p ∣ a) (hpb : p ∣ b) (hpc : p ∣ c) : False := by
    apply hp.not_dvd_one
    rw [← hgcd]
    refine Finset.dvd_gcd (fun q hq ↦ ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact hpa
    · exact hpb
    · exact hpc
  have hab : IsCoprime a b := by
    refine isCoprime_of_prime_dvd ?_ (fun p hp hpa hpb ↦ ?_)
    · rintro ⟨rfl, rfl⟩
      have hc : c = 0 := (pow_eq_zero_iff (by norm_num)).1 heq.symm
      subst c
      norm_num at hgcd
    · have hpc : p ∣ c := hp.dvd_of_dvd_pow (heq ▸ dvd_add (dvd_pow hpa (by norm_num))
          (dvd_pow hpb (by norm_num)))
      exact common_prime_absurd p hp hpa hpb hpc
  have hac : IsCoprime a c := by
    refine isCoprime_of_prime_dvd ?_ (fun p hp hpa hpc ↦ ?_)
    · rintro ⟨rfl, rfl⟩
      simp at heq
      subst b
      norm_num at hgcd
    · have hpb14 : p ∣ b ^ 14 := by
        rw [show b ^ 14 = c ^ 14 - a ^ 14 by omega]
        exact dvd_sub (dvd_pow hpc (by norm_num)) (dvd_pow hpa (by norm_num))
      exact common_prime_absurd p hp hpa (hp.dvd_of_dvd_pow hpb14) hpc
  have hbc : IsCoprime b c := by
    refine isCoprime_of_prime_dvd ?_ (fun p hp hpb hpc ↦ ?_)
    · rintro ⟨rfl, rfl⟩
      simp at heq
      subst a
      norm_num at hgcd
    · have hpa14 : p ∣ a ^ 14 := by
        rw [show a ^ 14 = c ^ 14 - b ^ 14 by omega]
        exact dvd_sub (dvd_pow hpc (by norm_num)) (dvd_pow hpb (by norm_num))
      exact common_prime_absurd p hp (hp.dvd_of_dvd_pow hpa14) hpb hpc
  exact ⟨hab, hac, hbc⟩

/-- Dirichlet's two obligations imply FLT for exponent `14`, without invoking
the theorem for exponent `7`. -/
theorem holdsAt_fourteen_of_dirichlet
    (hfirst : FirstCaseImpossible) (hdesc : Descends) : Fermat.HoldsAt 14 := by
  change FermatLastTheoremFor 14
  rw [fermatLastTheoremFor_iff_int]
  refine fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
    (fun a b c ha hb hc hgcd heq ↦ ?_)
  obtain ⟨hab, hac, hbc⟩ := pairwise_isCoprime_of_gcd_eq_one hgcd heq
  have hnonzero : c * a * b ≠ 0 := by positivity
  have h7c : ¬(7 : ℤ) ∣ c := not_seven_dvd_right hab heq.symm
  by_cases h7a : (7 : ℤ) ∣ a
  · obtain ⟨w, hw⟩ := descentEquation_zero_thirteen
      (t := c) (u := b) (v := a) (by positivity) hbc.symm (by omega) h7a
    exact no_descentEquation_of_descends hdesc c b w 0 13 hw
  by_cases h7b : (7 : ℤ) ∣ b
  · obtain ⟨w, hw⟩ := descentEquation_zero_thirteen
      (t := c) (u := a) (v := b) (by positivity) hac.symm heq.symm h7b
    exact no_descentEquation_of_descends hdesc c a w 0 13 hw
  exact hfirst hnonzero hac.symm hbc.symm heq.symm h7c h7a h7b

end Fermat.Fourteen.Dirichlet
