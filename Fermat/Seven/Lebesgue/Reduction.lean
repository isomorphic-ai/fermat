import Fermat.Basic

/-!
# Reduction of FLT for exponent seven to Lebesgue's ternary theorem

Lebesgue proves the signed statement that a primitive solution of

`x ^ 7 + y ^ 7 + z ^ 7 = 0`

has a zero entry.  This file records the outer reduction from that statement
to the project's standard `Fermat.HoldsAt 7` API.
-/

namespace Fermat.Seven.Lebesgue

/-- The exact ternary obligation proved by Lebesgue's Theorem II. -/
def TernaryOnlyTrivial : Prop :=
  ∀ {x y z : ℤ}, IsCoprime x y → IsCoprime x z → IsCoprime y z →
    x ^ 7 + y ^ 7 + z ^ 7 = 0 → x * y * z = 0

/-- Pairwise coprimality follows from primitivity and the Fermat equation. -/
private theorem pairwise_isCoprime_of_gcd_eq_one {a b c : ℤ}
    (hgcd : Finset.gcd {a, b, c} id = 1)
    (heq : a ^ 7 + b ^ 7 = c ^ 7) :
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
    · have hpc : p ∣ c := hp.dvd_of_dvd_pow (heq ▸ dvd_add
          (dvd_pow hpa (by norm_num)) (dvd_pow hpb (by norm_num)))
      exact common_prime_absurd p hp hpa hpb hpc
  have hac : IsCoprime a c := by
    refine isCoprime_of_prime_dvd ?_ (fun p hp hpa hpc ↦ ?_)
    · rintro ⟨rfl, rfl⟩
      simp at heq
      subst b
      norm_num at hgcd
    · have hpb7 : p ∣ b ^ 7 := by
        rw [show b ^ 7 = c ^ 7 - a ^ 7 by omega]
        exact dvd_sub (dvd_pow hpc (by norm_num)) (dvd_pow hpa (by norm_num))
      exact common_prime_absurd p hp hpa (hp.dvd_of_dvd_pow hpb7) hpc
  have hbc : IsCoprime b c := by
    refine isCoprime_of_prime_dvd ?_ (fun p hp hpb hpc ↦ ?_)
    · rintro ⟨rfl, rfl⟩
      simp at heq
      subst a
      norm_num at hgcd
    · have hpa7 : p ∣ a ^ 7 := by
        rw [show a ^ 7 = c ^ 7 - b ^ 7 by omega]
        exact dvd_sub (dvd_pow hpc (by norm_num)) (dvd_pow hpb (by norm_num))
      exact common_prime_absurd p hp (hp.dvd_of_dvd_pow hpa7) hpb hpc
  exact ⟨hab, hac, hbc⟩

/-- Lebesgue's signed ternary theorem implies Fermat's Last Theorem for
exponent seven. -/
theorem holdsAt_seven_of_ternaryOnlyTrivial
    (hternary : TernaryOnlyTrivial) : Fermat.HoldsAt 7 := by
  change FermatLastTheoremFor 7
  rw [fermatLastTheoremFor_iff_int]
  refine fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
    (fun a b c ha hb hc hgcd heq ↦ ?_)
  obtain ⟨hab, hac, hbc⟩ := pairwise_isCoprime_of_gcd_eq_one hgcd heq
  have hsigned : a ^ 7 + b ^ 7 + (-c) ^ 7 = 0 := by
    rw [(show Odd 7 by norm_num).neg_pow]
    omega
  have hzero := hternary hab hac.neg_right hbc.neg_right hsigned
  have hnonzero : a * b * (-c) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero ha hb) (neg_ne_zero.mpr hc)
  exact hnonzero hzero

end Fermat.Seven.Lebesgue
