import Fermat.Regular.Faulhaber
import FltRegular.FltRegular
import KummerCriterion.BernoulliFast.PrimesUpTo100

/-!
# Kummer's criterion for direct Faulhaber certificates

`BernoulliNumeratorRegular p` is the numerical condition checked by the
finite power-sum certificates in `Fermat.Regular.Faulhaber`.  The external
`KummerCriterion` development proves that, for an odd prime, this condition
is equivalent to regularity of the cyclotomic class number.

This module aligns the two equivalent index conventions and then composes
the result with the kernel-checked Lamé--Kummer descent `flt_regular`.
-/

namespace Fermat.Regular.Faulhaber

/-- The finite-index predicate used by the direct Faulhaber certificates is
exactly Kummer's class-group regularity condition for an odd prime. -/
theorem bernoulliNumeratorRegular_iff_isRegularPrime
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2) :
    BernoulliNumeratorRegular p ↔ IsRegularPrime p := by
  constructor
  · intro hregular
    apply (KummerCriterion (p := p) hp_odd).mpr
    intro k hk hupper
    apply hregular (2 * k)
    simp only [regularIndices, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hupper⟩, even_two_mul k⟩
  · intro hregular k hk
    have hk' : 2 ≤ k ∧ k ≤ p - 3 ∧ Even k := by
      simpa [regularIndices, and_assoc] using hk
    rcases hk'.2.2 with ⟨j, rfl⟩
    have hj := (KummerCriterion (p := p) hp_odd).mp hregular j
      (by omega) (by omega)
    simpa [two_mul] using hj

/-- A direct Bernoulli-numerator certificate proves cyclotomic regularity. -/
theorem isRegularPrime_of_bernoulliNumeratorRegular
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hregular : BernoulliNumeratorRegular p) :
    IsRegularPrime p :=
  (bernoulliNumeratorRegular_iff_isRegularPrime hp_odd).mp hregular

/-- The complete checked bridge from direct Faulhaber data to Fermat's Last
Theorem at an odd prime exponent. -/
theorem holdsAt_of_bernoulliNumeratorRegular
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hregular : BernoulliNumeratorRegular p) :
    Fermat.HoldsAt p :=
  flt_regular
    (isRegularPrime_of_bernoulliNumeratorRegular hp_odd hregular)
    hp_odd

end Fermat.Regular.Faulhaber
