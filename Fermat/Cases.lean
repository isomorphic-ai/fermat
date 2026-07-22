import Fermat.SophieGermain

/-!
# Assembling the first and second cases

This module packages the elementary final assembly shared by the irregular
prime exponents.  Sophie Germain's auxiliary-prime theorem forces every
primitive solution into the second case; any independently proved exclusion
of that second case then yields Fermat's Last Theorem at the exponent.
-/

namespace Fermat

open Finset

/-- A primitive nonzero Fermat solution over the integers is pairwise
coprime. -/
theorem pairwiseCoprime_of_primitive_solution {p : ℕ} (hp : p ≠ 0)
    {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hfermat : a ^ p + b ^ p = c ^ p) :
    IsCoprime a b ∧ IsCoprime b c ∧ IsCoprime a c := by
  have commonPrime_isUnit {r : ℤ} (hra : r ∣ a) (hrb : r ∣ b) (hrc : r ∣ c) :
      IsUnit r := by
    rw [isUnit_iff_dvd_one, ← hgcd, Finset.dvd_gcd_iff]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hra
    · exact hrb
    · exact hrc
  constructor
  · apply isCoprime_of_prime_dvd (fun h ↦ ha h.1)
    intro r hr hra hrb
    have hrcpow : r ∣ c ^ p := by
      rw [← hfermat]
      exact dvd_add (dvd_pow hra hp) (dvd_pow hrb hp)
    exact hr.not_unit (commonPrime_isUnit hra hrb (hr.dvd_of_dvd_pow hrcpow))
  constructor
  · apply isCoprime_of_prime_dvd (fun h ↦ hb h.1)
    intro r hr hrb hrc
    have hrapow : r ∣ a ^ p := by
      have hsub := dvd_sub (dvd_pow hrc hp) (dvd_pow hrb hp)
      rw [← hfermat, add_sub_cancel_right] at hsub
      exact hsub
    exact hr.not_unit (commonPrime_isUnit (hr.dvd_of_dvd_pow hrapow) hrb hrc)
  · apply isCoprime_of_prime_dvd (fun h ↦ ha h.1)
    intro r hr hra hrc
    have hrbpow : r ∣ b ^ p := by
      have hsub := dvd_sub (dvd_pow hrc hp) (dvd_pow hra hp)
      rw [← hfermat, add_sub_cancel_left] at hsub
      exact hsub
    exact hr.not_unit (commonPrime_isUnit hra (hr.dvd_of_dvd_pow hrbpow) hrc)

/-- The form of a second-case theorem needed by the final FLT assembly. -/
def SecondCaseExcluded (p : ℕ) : Prop :=
  ∀ {a b c : ℤ}, a ≠ 0 → b ≠ 0 → c ≠ 0 →
    ({a, b, c} : Finset ℤ).gcd id = 1 →
    (p : ℤ) ∣ a * b * c → a ^ p + b ^ p ≠ c ^ p

/-- Sophie Germain's residue conditions, together with an exclusion of the
second case, prove FLT at the prime exponent `p`. -/
theorem holdsAt_of_auxiliaryPrime_of_secondCaseExcluded {p q : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hq : q.Prime)
    (hNC : SophieGermain.NoConsecutivePowers p q)
    (hNP : SophieGermain.ExponentNotPower p q)
    (hsecond : SecondCaseExcluded p) : HoldsAt p := by
  change FermatLastTheoremFor p
  rw [fermatLastTheoremFor_iff_int]
  refine fermatLastTheoremWith_of_fermatLastTheoremWith_coprime ?_
  intro a b c ha hb hc hgcd hfermat
  obtain ⟨hab, hbc, hac⟩ :=
    pairwiseCoprime_of_primitive_solution hp.ne_zero ha hb hc hgcd hfermat
  have hcase := SophieGermain.firstCase_of_pairwise_coprime
    hp hodd hq hNC hNP hab hbc hac hfermat
  apply hsecond ha hb hc hgcd
  rcases hcase with ha' | hb' | hc'
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ha' b) c
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hb' a) c
  · exact dvd_mul_of_dvd_right hc' (a * b)
  exact hfermat

end Fermat
