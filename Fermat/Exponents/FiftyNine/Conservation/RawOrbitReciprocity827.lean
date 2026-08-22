/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Raw-orbit reciprocity and Fourier projection at 827

An actual local tame symbol is a pointwise product of an unprojected primal
residue vector and the reflected localization vector.  Fourier projection
therefore belongs under the complete reciprocity sum, not in a pointwise
comparison.  This module proves that honest sum-level adapter and retains the
inverse place orientation explicitly.

The scalar theorem takes the reciprocity equation itself as its sole
arithmetic input.  It does not manufacture a global pairing or a local value.
-/
import Fermat.Experiments.Conservation.PrimeFourierPairingCompression
import Fermat.Experiments.Conservation.PrimeFullOrbitReciprocity
import Fermat.Exponents.FiftyNine.Conservation.FullOrbitReciprocity827
import Fermat.Exponents.FiftyNine.Conservation.FourierPairingProjection827

open scoped BigOperators

noncomputable section

namespace Fermat.FiftyNine.Conservation.RawOrbitReciprocity827

open Fermat.Conservation
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.TatePairing
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827
open Fermat.FiftyNine.Conservation.FourierPairingProjection827
open Fermat.FiftyNine.Conservation.FullOrbitReciprocity827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

universe uPlace uDelta uChi uDual

variable {Delta : Type uDelta} [CommGroup Delta] [Fintype Delta]
  {omega chi : InvolutiveBase.Character (PadicInt 59) Delta}
  {Place : Type uPlace} {SelmerChi : Type uChi}
  {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra 59 Delta) DOmegaSelmerChiStar]
  {pairing : PlaceIndexedLocalPairing 59 Delta omega chi Place
    SelmerChi DOmegaSelmerChiStar}

/-- Global reciprocity may consume honest raw local products. Fourier
projection occurs under the complete finite sum; no pointwise equality
between a raw residue and its selected character component is assumed. -/
theorem GlobalReciprocityLaw.pairAt_eq_selectedComponent_of_rawOrbit
    (hcard : Fintype.card Delta = 58)
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished : Place) (auxiliaryPlace : Delta → Place)
    (hinjective : Function.Injective auxiliaryPlace)
    (hdisjoint : ∀ index, auxiliaryPlace index ≠ distinguished)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (houtside : ∀ v, v ≠ distinguished →
      v ∉ Set.range auxiliaryPlace → pairing.pairAt v x y = 0)
    (eta : Delta →* (ZMod 59)ˣ)
    (raw reflected : Delta → ZMod 59)
    (selected : Delta)
    (hreflected : IsPureCharacter eta⁻¹ reflected)
    (hcomparison : ∀ index,
      pairing.pairAt (auxiliaryPlace index) x y =
        raw index * reflected index) :
    pairing.pairAt distinguished x y =
      characterComponent raw eta selected * reflected selected :=
  Fermat.Conservation.PrimeFullOrbitReciprocity.GlobalReciprocityLaw.pairAt_eq_selectedComponent_of_rawOrbit
    (p := 59) hcard reciprocity distinguished auxiliaryPlace hinjective
      hdisjoint x y houtside eta raw reflected selected hreflected hcomparison

/-- The scalar form consumed by a family of explicit tame symbols. The sole
arithmetic input is the retained reciprocity equation itself. -/
theorem wild_eq_selectedComponent_of_raw_reciprocity
    (hcard : Fintype.card Delta = 58)
    (eta : Delta →* (ZMod 59)ˣ)
    (raw reflected : Delta → ZMod 59)
    (selected : Delta)
    (hreflected : IsPureCharacter eta⁻¹ reflected)
    (wild : ZMod 59)
    (reciprocity : wild + ∑ index : Delta,
      raw index * reflected index = 0) :
    wild = characterComponent raw eta selected * reflected selected :=
  Fermat.Conservation.PrimeFourierPairingCompression.wild_eq_selectedComponent_of_raw_reciprocity
      (p := 59) hcard eta raw reflected selected hreflected wild reciprocity

/-- The explicit inverse-oriented specialization. Canonical place index
`index` reads raw residue index `index⁻¹`. -/
theorem GlobalReciprocityLaw.pairAt_eq_inverseOrientedComponent_of_rawOrbit
    (hcard : Fintype.card Delta = 58)
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished : Place) (auxiliaryPlace : Delta → Place)
    (hinjective : Function.Injective auxiliaryPlace)
    (hdisjoint : ∀ index, auxiliaryPlace index ≠ distinguished)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (houtside : ∀ v, v ≠ distinguished →
      v ∉ Set.range auxiliaryPlace → pairing.pairAt v x y = 0)
    (eta : Delta →* (ZMod 59)ˣ)
    (raw reflected : Delta → ZMod 59)
    (selected : Delta)
    (hreflected : IsPureCharacter eta⁻¹ reflected)
    (hcomparison : ∀ index,
      pairing.pairAt (auxiliaryPlace index) x y =
        inverseReindex raw index * reflected index) :
    pairing.pairAt distinguished x y =
      characterComponent (inverseReindex raw) eta selected *
        reflected selected :=
  Fermat.Conservation.PrimeFullOrbitReciprocity.GlobalReciprocityLaw.pairAt_eq_inverseOrientedComponent_of_rawOrbit
    (p := 59) hcard reciprocity distinguished auxiliaryPlace hinjective
      hdisjoint x y houtside eta raw reflected selected hreflected hcomparison

end Fermat.FiftyNine.Conservation.RawOrbitReciprocity827
