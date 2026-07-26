import Fermat.Regular.Faulhaber
import FltRegular.FltRegular
import KummerCriterion.CyclotomicUnits.UnitsReflection

/-!
# Kummer's criterion for direct Faulhaber certificates

`BernoulliNumeratorRegular p` is the numerical condition checked by the
finite power-sum certificates in `Fermat.Regular.Faulhaber`.  The external
`KummerCriterion` development proves that, for an odd prime, this condition
is equivalent to coprimality of the exponent and the cyclotomic class
number.

The patched `flt-regular` core intentionally no longer exports
`IsRegularPrime` or consumes a class-number premise.  This module therefore
states the historical criterion against a local, explicit class-number
predicate.  Its FLT compatibility endpoint retains the checked Faulhaber
certificate at existing call sites and applies the now-generic descent.
-/

namespace Fermat.Regular.Faulhaber

open NumberField

/-- The historical cyclotomic class-number regularity condition, retained
independently of the patched `flt-regular` public API. -/
noncomputable def CyclotomicClassNumberRegular (p : ℕ) : Prop :=
  p.Coprime <| Fintype.card <| ClassGroup (𝓞 <| CyclotomicField p ℚ)

/-- Kummer's criterion stated against the local historical class-number
predicate. -/
theorem cyclotomicClassNumberRegular_iff_bernoulliCriterion
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2) :
    CyclotomicClassNumberRegular p ↔
      ∀ k, 1 ≤ k → 2 * k ≤ p - 3 →
        ¬(p : ℤ) ∣ (bernoulli (2 * k)).num := by
  letI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  letI : IsCMField (CyclotomicField p ℚ) :=
    KummerCriterion.isCMField_of_cyclotomic (p := p) (hp_odd := hp_odd)
      (K := CyclotomicField p ℚ)
  have hiff : (p : ℕ) ∣ KummerCriterion.h (CyclotomicField p ℚ) ↔
      ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧
        (p : ℤ) ∣ (bernoulli (2 * k)).num :=
    KummerCriterion.dvd_h_iff_exists_dvd_bernoulli_units
      (p := p) (K := CyclotomicField p ℚ) hp_odd
  rw [CyclotomicClassNumberRegular, hp.out.coprime_iff_not_dvd]
  change ¬(p : ℕ) ∣ KummerCriterion.h (CyclotomicField p ℚ) ↔ _
  rw [hiff]
  push Not
  rfl

/-- The finite-index predicate used by the direct Faulhaber certificates is
exactly the historical cyclotomic class-number condition for an odd prime. -/
theorem bernoulliNumeratorRegular_iff_cyclotomicClassNumberRegular
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2) :
    BernoulliNumeratorRegular p ↔ CyclotomicClassNumberRegular p := by
  constructor
  · intro hregular
    apply (cyclotomicClassNumberRegular_iff_bernoulliCriterion hp_odd).mpr
    intro k hk hupper
    apply hregular (2 * k)
    simp only [regularIndices, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hupper⟩, even_two_mul k⟩
  · intro hregular k hk
    have hk' : 2 ≤ k ∧ k ≤ p - 3 ∧ Even k := by
      simpa [regularIndices, and_assoc] using hk
    rcases hk'.2.2 with ⟨j, rfl⟩
    have hj :=
      (cyclotomicClassNumberRegular_iff_bernoulliCriterion hp_odd).mp
        hregular j (by omega) (by omega)
    simpa [two_mul] using hj

/-- A direct Bernoulli-numerator certificate proves the historical
cyclotomic class-number condition. -/
theorem cyclotomicClassNumberRegular_of_bernoulliNumeratorRegular
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hregular : BernoulliNumeratorRegular p) :
    CyclotomicClassNumberRegular p :=
  (bernoulliNumeratorRegular_iff_cyclotomicClassNumberRegular hp_odd).mp
    hregular

/-- The patched descent no longer consumes class-number regularity.  This
compatibility endpoint keeps the checked Faulhaber certificate in its
historical call sites while applying the now-generic descent. -/
theorem holdsAt_of_bernoulliNumeratorRegular
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (_hregular : BernoulliNumeratorRegular p) :
    Fermat.HoldsAt p :=
  flt_regular hp_odd

end Fermat.Regular.Faulhaber
