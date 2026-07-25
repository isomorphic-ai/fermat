import Fermat.GenericIrregular.SecondCase
import Fermat.Cases

/-!
# The generic fixed-exponent irregular-prime theorem

This module is the final assembly layer for one irregular prime exponent.
It deliberately records finite mathematical input rather than any theorem
shaped like the desired conclusion:

* `SophieGermainCertificate` contains an auxiliary prime and the two finite
  residue conditions;
* `FixedIrregularCertificate` contains the lower bound on the exponent, that
  Sophie--Germain data, and the honest generic second-case certificate.

In particular, neither certificate stores `Fermat.HoldsAt`,
`Fermat.SecondCaseExcluded`, Vandiver's Lemma II, or a first-case conclusion.
The theorem below constructs those intermediate conclusions internally.
-/

namespace Fermat.GenericIrregular.FixedExponent

open Fermat.GenericIrregular.SecondCase

noncomputable section

/- The canonical cyclotomic field is available at every prime exponent. -/
local instance primeNeZero (p : ℕ) [Fact p.Prime] : NeZero p :=
  ⟨(Fact.out : p.Prime).ne_zero⟩

local instance primeNeZeroRat (p : ℕ) [Fact p.Prime] :
    NeZero (p : ℚ) :=
  ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩

local instance cyclotomicExtension (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
  CyclotomicField.isCyclotomicExtension p ℚ

/-- The direct finite Sophie--Germain input at exponent `p`.

The traditional relation `q = 2kp + 1` is a useful way to find these data,
but the final theorem needs only primality and the two residue conditions
which that search establishes. -/
structure SophieGermainCertificate (p : ℕ) where
  auxiliaryPrime : ℕ
  auxiliaryPrime_isPrime : auxiliaryPrime.Prime
  noConsecutivePowers :
    Fermat.SophieGermain.NoConsecutivePowers p auxiliaryPrime
  exponentNotPower :
    Fermat.SophieGermain.ExponentNotPower p auxiliaryPrime

/-- All honest input needed to prove FLT at one fixed irregular prime.

The second-case field is specialized to the canonical cyclotomic field.
Its CM-field instance is justified by the earlier field
`exponent_atLeastFive`; no CM hypothesis is smuggled in for exponent `2`. -/
structure FixedIrregularCertificate (p N : ℕ) [Fact p.Prime] where
  exponent_atLeastFive : 5 ≤ p
  sophieGermain : SophieGermainCertificate p
  secondCase :
    @FixedSecondCaseCertificate
      (CyclotomicField p ℚ) p N
      _ _ _
      (IsCyclotomicExtension.IsCMField (p := p) (CyclotomicField p ℚ)
        (by omega))
      _

/-- A finite fixed-exponent certificate proves Fermat's Last Theorem at
that exponent.

The proof chooses a primitive root in the canonical cyclotomic field,
assembles the historical second-case exclusion from the certificate, and
then invokes Sophie Germain's elementary first/second-case assembly. -/
theorem holdsAt_of_certificate {p N : ℕ} [Fact p.Prime]
    (certificate : FixedIrregularCertificate p N) :
    Fermat.HoldsAt p := by
  have hp5 : 5 ≤ p := certificate.exponent_atLeastFive
  letI : NumberField.IsCMField (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.IsCMField (p := p) (CyclotomicField p ℚ)
      (by omega)
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField p ℚ)
      (Set.mem_singleton p) (Fact.out : p.Prime).ne_zero
  have hsecond : Fermat.SecondCaseExcluded p :=
    secondCaseExcluded_of_certificate
      hp5 hζ certificate.secondCase
  have hp2 : p ≠ 2 := by
    omega
  exact
    Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
      (Fact.out : p.Prime)
      ((Fact.out : p.Prime).odd_of_ne_two hp2)
      certificate.sophieGermain.auxiliaryPrime_isPrime
      certificate.sophieGermain.noConsecutivePowers
      certificate.sophieGermain.exponentNotPower
      hsecond

end

end Fermat.GenericIrregular.FixedExponent
