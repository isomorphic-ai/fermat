import Fermat.GenericIrregular.FixedExponent
import Fermat.KummerIso.SecondCase

/-!
# Fixed-exponent FLT through the Kummer correction

This is the final assembly for an existing
`GenericIrregular.FixedExponent.FixedIrregularCertificate`.

The second case is reconstructed by `KummerIso.SecondCase`, so its unit step
passes through the normalized correction automorphism. The generic
proof-producing Sophie--Germain search then excludes the first case and
joins the two cases into `Fermat.HoldsAt p`.

This theorem does not delegate to
`GenericIrregular.FixedExponent.holdsAt_of_certificate`.
-/

namespace Fermat.KummerIso.FixedExponent

open Fermat.GenericIrregular.FixedExponent

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

/-- An existing honest fixed-irregular certificate proves FLT through the
new correction-based second-case assembly.

The certificate type is reused unchanged.  In particular, it stores neither
a second-case conclusion nor `Fermat.HoldsAt p`. -/
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
    Fermat.KummerIso.SecondCase.secondCaseExcluded_of_certificate
      hp5 hζ certificate.secondCase
  exact
    Fermat.holdsAt_of_sophieGermainSearch_of_secondCaseExcluded
      hsecond

end

end Fermat.KummerIso.FixedExponent
