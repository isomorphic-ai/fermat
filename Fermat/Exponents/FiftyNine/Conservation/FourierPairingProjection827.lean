/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Fourier projection of the oriented 827 pairing sum

Pairing an arbitrary scalar vector with a pure inverse-character wave only
sees the corresponding Fourier component.  This is a statement about the
complete orbit sum: it does not assert a generally false pointwise equality
between the raw vector and its projected component.

The explicit residue maps and the canonical place orbit have opposite
orientations.  The `inverseReindex` definitions and lemmas below retain that
inverse visibly.  In particular, inversion swaps the raw Fourier coefficient
from `eta` to `eta⁻¹`; no symmetry between those coefficients is assumed.
-/
import Fermat.Experiments.Conservation.PrimeFourierPairingCompression
import Fermat.Exponents.FiftyNine.Conservation.SplitPrimeFourier827

open scoped BigOperators

noncomputable section

namespace Fermat.FiftyNine.Conservation.FourierPairingProjection827

open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

universe uDelta

variable {Delta : Type uDelta} [CommGroup Delta]

section Finite

variable [Fintype Delta]

/-- Pairing against a pure inverse-character wave sees exactly the
corresponding Fourier component of an arbitrary primal vector. -/
theorem sum_mul_pureInverse_eq_sum_characterComponent_mul
    (hcard : Fintype.card Delta = 58)
    (eta : Delta →* (ZMod 59)ˣ)
    (primal reflected : Delta → ZMod 59)
    (hreflected : IsPureCharacter eta⁻¹ reflected) :
    (∑ x : Delta, primal x * reflected x) =
      ∑ x : Delta, characterComponent primal eta x * reflected x :=
  Fermat.Conservation.PrimeFourierPairingCompression.sum_mul_pureInverse_eq_sum_characterComponent_mul
      (p := 59) hcard eta primal reflected hreflected

/-- The oriented raw orbit: canonical place index `x` reads the explicit
residue map indexed by `x⁻¹`. -/
def inverseReindex (v : Delta → ZMod 59) : Delta → ZMod 59 :=
  Fermat.Conservation.PrimeFourierPairingCompression.inverseReindex
    (p := 59) v

/-- Inverting the place index swaps the coefficient selected from the raw
vector.  Thus the honest place-oriented primal wave uses the raw
`eta⁻¹`-coefficient, not the raw `eta`-coefficient. -/
theorem fourierCoefficient_inverseReindex
    (raw : Delta → ZMod 59) (eta : Delta →* (ZMod 59)ˣ) :
    fourierCoefficient (inverseReindex raw) eta =
      fourierCoefficient raw eta⁻¹ :=
  Fermat.Conservation.PrimeFourierPairingCompression.fourierCoefficient_inverseReindex
    (p := 59) raw eta

/-- Full-orbit compression may start from the honest unprojected residue
vector.  Pairing with a pure inverse wave automatically selects the one
complementary Fourier mode; no pointwise raw/component identification is
assumed. -/
theorem sum_inverseReindex_mul_pureInverse_eq_neg_selectedComponent
    (hcard : Fintype.card Delta = 58)
    (eta : Delta →* (ZMod 59)ˣ)
    (raw reflected : Delta → ZMod 59)
    (selected : Delta)
    (hreflected : IsPureCharacter eta⁻¹ reflected) :
    (∑ x : Delta, inverseReindex raw x * reflected x) =
      -(characterComponent (inverseReindex raw) eta selected *
          reflected selected) :=
  Fermat.Conservation.PrimeFourierPairingCompression.sum_inverseReindex_mul_pureInverse_eq_neg_selectedComponent
      (p := 59) hcard eta raw reflected selected hreflected

end Finite

end Fermat.FiftyNine.Conservation.FourierPairingProjection827
