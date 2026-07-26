import Fermat.GenericIrregular.SecondCase
import Fermat.Cases

/-!
# The generic fixed-exponent irregular-prime theorem

This module is the final assembly layer for one irregular prime exponent.
It deliberately records finite Case-II input rather than any theorem shaped
like the desired conclusion:

* `SophieGermainCertificate` remains available for explicit historical
  auxiliary-prime regressions;
* `FixedIrregularCertificate` contains only the lower bound on the exponent
  and the honest generic second-case certificate.

In particular, neither certificate stores `Fermat.HoldsAt`,
`Fermat.SecondCaseExcluded`, Vandiver's Lemma II, or a first-case conclusion.
The theorem below constructs the second-case conclusion internally and uses
the generic proof-producing Sophie--Germain search for Case I.
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

/-- An explicit finite Sophie--Germain regression bundle at exponent `p`.

The traditional relation `q = 2kp + 1` is a useful way to find these data,
and the concrete historical developments retain these checked witnesses.
The generic final theorem no longer requires this structure: it uses the
proof-producing auxiliary-prime search directly. -/
structure SophieGermainCertificate (p : ℕ) where
  auxiliaryPrime : ℕ
  auxiliaryPrime_isPrime : auxiliaryPrime.Prime
  noConsecutivePowers :
    Fermat.SophieGermain.NoConsecutivePowers p auxiliaryPrime
  exponentNotPower :
    Fermat.SophieGermain.ExponentNotPower p auxiliaryPrime

/-- The honest Case-II input needed to prove FLT at one fixed irregular
prime. Case I is supplied uniformly by the proof-producing auxiliary-prime
search, so no per-prime Sophie--Germain field remains here.

The second-case field is specialized to the canonical cyclotomic field.
Its CM-field instance is justified by the earlier field
`exponent_atLeastFive`; no CM hypothesis is smuggled in for exponent `2`. -/
structure FixedIrregularCertificate (p N : ℕ) [Fact p.Prime] where
  exponent_atLeastFive : 5 ≤ p
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
then invokes the generic proof-producing Sophie--Germain search for
Case I. -/
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
  exact
    Fermat.holdsAt_of_sophieGermainSearch_of_secondCaseExcluded
      hsecond

end

end Fermat.GenericIrregular.FixedExponent
