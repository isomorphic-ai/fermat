/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Full-orbit reciprocity at the 827 support

Global reciprocity must retain the complete 58-place auxiliary orbit.  This
file proves the finite-support bookkeeping needed to do so and combines it
with complementary Fourier-wave compression.  If the actual local readings
on that orbit are the pointwise products of complementary pure-character
waves, the distinguished wild reading is their selected product.

The local comparison is an explicit hypothesis.  No Kummer class, local
Tate value, silence law, or reflected lift is manufactured here.
-/
import Fermat.Experiments.Conservation.TatePairing
import Fermat.Experiments.Conservation.PrimeFullOrbitReciprocity
import Fermat.Exponents.FiftyNine.Conservation.ComplementaryWaveCompression827
import Fermat.Exponents.FiftyNine.Conservation.PrimalOrbitResidue827

open scoped BigOperators

noncomputable section

namespace Fermat.FiftyNine.Conservation.FullOrbitReciprocity827

open Fermat.Conservation
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.TatePairing
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827
open Fermat.FiftyNine.Conservation.PrimalOrbitResidue827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

universe uPlace uDelta uChi uDual

variable {Delta : Type uDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt 59) Delta}
  {Place : Type uPlace} {SelmerChi : Type uChi}
  {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra 59 Delta) DOmegaSelmerChiStar]

/-- The local-reading vector along an indexed auxiliary orbit. -/
def orbitReading
    (pairing : PlaceIndexedLocalPairing 59 Delta omega chi Place
      SelmerChi DOmegaSelmerChiStar)
    {Index : Type*} (auxiliaryPlace : Index → Place)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) : Index → ZMod 59 :=
  Fermat.Conservation.PrimeFullOrbitReciprocity.orbitReading
    pairing auxiliaryPlace x y

namespace GlobalReciprocityLaw

variable {pairing : PlaceIndexedLocalPairing 59 Delta omega chi Place
  SelmerChi DOmegaSelmerChiStar}

/-- If all away readings lie on one injectively indexed finite orbit,
reciprocity balances the distinguished reading against their full sum. -/
theorem pairAt_eq_neg_sum_orbitReading
    {Index : Type*} [Fintype Index]
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished : Place) (auxiliaryPlace : Index → Place)
    (hinjective : Function.Injective auxiliaryPlace)
    (hdisjoint : ∀ index, auxiliaryPlace index ≠ distinguished)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (houtside : ∀ v, v ≠ distinguished →
      v ∉ Set.range auxiliaryPlace → pairing.pairAt v x y = 0) :
    pairing.pairAt distinguished x y =
      -∑ index : Index, orbitReading pairing auxiliaryPlace x y index :=
  Fermat.Conservation.PrimeFullOrbitReciprocity.GlobalReciprocityLaw.pairAt_eq_neg_sum_orbitReading
    (p := 59) reciprocity distinguished auxiliaryPlace hinjective hdisjoint
      x y houtside

/-- On a 58-place auxiliary orbit, complementary character phases turn the
global reciprocity balance into the selected local product.  The comparison
between actual local readings and the displayed products remains explicit. -/
theorem pairAt_eq_selectedProduct_of_complementaryOrbit
    {Index : Type*} [CommGroup Index] [Fintype Index]
    (hcard : Fintype.card Index = 58)
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished : Place) (auxiliaryPlace : Index → Place)
    (hinjective : Function.Injective auxiliaryPlace)
    (hdisjoint : ∀ index, auxiliaryPlace index ≠ distinguished)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (houtside : ∀ v, v ≠ distinguished →
      v ∉ Set.range auxiliaryPlace → pairing.pairAt v x y = 0)
    (mode : Index →* (ZMod 59)ˣ)
    (primal reflected : Index → ZMod 59)
    (selected : Index)
    (hprimal : IsPureCharacter mode primal)
    (hreflected : IsPureCharacter mode⁻¹ reflected)
    (hcomparison : ∀ index,
      pairing.pairAt (auxiliaryPlace index) x y =
        primal index * reflected index) :
    pairing.pairAt distinguished x y =
      primal selected * reflected selected :=
  Fermat.Conservation.PrimeFullOrbitReciprocity.GlobalReciprocityLaw.pairAt_eq_selectedProduct_of_complementaryOrbit
    (p := 59) hcard reciprocity distinguished auxiliaryPlace hinjective
      hdisjoint x y houtside mode primal reflected selected hprimal hreflected
      hcomparison

/-! ## The canonically seated reflected wave -/

universe uK

section CyclotomicReflected

variable {K : Type uK} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  {Place : Type uPlace} {SelmerChi : Type uChi}
  {DOmegaSelmerChiStar : Type uDual}
  {omega chi : InvolutiveBase.Character
    (PadicInt 59) GaloisIndex59}
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra 59 GaloisIndex59) SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra 59 GaloisIndex59)
    DOmegaSelmerChiStar]
  {pairing : PlaceIndexedLocalPairing 59 GaloisIndex59 omega chi Place
    SelmerChi DOmegaSelmerChiStar}

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2000 in
/-- The full-orbit reciprocity theorem with the reflected wave supplied by
the actual canonical q-relaxed localization.  Only the complementary primal
wave and its comparison with the local Tate readings remain explicit. -/
theorem pairAt_eq_selectedProduct_of_cyclotomicReflectedOrbit
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished : Place)
    (auxiliaryPlace : GaloisIndex59 → Place)
    (hinjective : Function.Injective auxiliaryPlace)
    (hdisjoint : ∀ index, auxiliaryPlace index ≠ distinguished)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (houtside : ∀ v, v ≠ distinguished →
      v ∉ Set.range auxiliaryPlace → pairing.pairAt v x y = 0)
    (selectedPlace : Place827 K)
    (source : QRelaxedSelmerCarrier827 K)
    (primal : GaloisIndex59 → ZMod 59)
    (selectedIndex : GaloisIndex59)
    (hprimal : IsPureCharacter
      (reducedCharacter59
        (InvolutiveBase.reflectedCharacter omega chi)) primal)
    (hcomparison : ∀ index,
      pairing.pairAt (auxiliaryPlace index) x y =
        primal index *
          projectedLocalizationVector827
            (cyclotomicQRelaxedSelmerRepresentation827 K)
            omega chi selectedPlace source index) :
    pairing.pairAt distinguished x y =
      primal selectedIndex *
        projectedLocalizationVector827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          omega chi selectedPlace source selectedIndex := by
  let reflected : GaloisIndex59 → ZMod 59 :=
    projectedLocalizationVector827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi selectedPlace source
  have hsumComparison :
      (∑ index : GaloisIndex59,
          orbitReading pairing auxiliaryPlace x y index) =
        ∑ index : GaloisIndex59, primal index * reflected index := by
    apply Finset.sum_congr rfl
    intro index _
    simpa only [orbitReading,
      Fermat.Conservation.PrimeFullOrbitReciprocity.orbitReading,
      reflected] using hcomparison index
  have hcompression :
      (∑ index : GaloisIndex59, primal index * reflected index) =
        -(primal selectedIndex * reflected selectedIndex) := by
    exact cyclotomic_projectedLocalization_product_sum_eq_neg_selected
      omega chi selectedPlace source primal selectedIndex hprimal
  calc
    pairing.pairAt distinguished x y =
        -∑ index : GaloisIndex59,
          orbitReading pairing auxiliaryPlace x y index :=
      pairAt_eq_neg_sum_orbitReading reciprocity distinguished
        auxiliaryPlace hinjective hdisjoint x y houtside
    _ = -∑ index : GaloisIndex59,
        primal index * reflected index := congrArg Neg.neg hsumComparison
    _ = -(-(primal selectedIndex * reflected selectedIndex)) :=
      congrArg Neg.neg hcompression
    _ = primal selectedIndex * reflected selectedIndex := neg_neg _
    _ = primal selectedIndex *
        projectedLocalizationVector827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          omega chi selectedPlace source selectedIndex := rfl

set_option maxRecDepth 2000 in
/-- Full-orbit reciprocity with both Fourier waves now constructed: the
primal wave is the reflected-character component of the actual first
generated circular unit's 58-place residue vector, and the reflected wave is
the canonical q-relaxed localization.  The only local arithmetic seam left
in this theorem is the explicit comparison with the Tate readings. -/
theorem pairAt_eq_selectedCircularUnitProduct_of_cyclotomicReflectedOrbit
    {zeta : K} (hZeta : IsPrimitiveRoot zeta 59)
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished : Place)
    (auxiliaryPlace : GaloisIndex59 → Place)
    (hinjective : Function.Injective auxiliaryPlace)
    (hdisjoint : ∀ index, auxiliaryPlace index ≠ distinguished)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (houtside : ∀ v, v ≠ distinguished →
      v ∉ Set.range auxiliaryPlace → pairing.pairAt v x y = 0)
    (selectedPlace : Place827 K)
    (source : QRelaxedSelmerCarrier827 K)
    (selectedIndex : GaloisIndex59)
    (hcomparison : ∀ index,
      pairing.pairAt (auxiliaryPlace index) x y =
        complementaryPrimalUnitWave827 hZeta omega chi index *
          projectedLocalizationVector827
            (cyclotomicQRelaxedSelmerRepresentation827 K)
            omega chi selectedPlace source index) :
    pairing.pairAt distinguished x y =
      complementaryPrimalUnitWave827 hZeta omega chi selectedIndex *
        projectedLocalizationVector827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          omega chi selectedPlace source selectedIndex :=
  pairAt_eq_selectedProduct_of_cyclotomicReflectedOrbit
    reciprocity distinguished auxiliaryPlace hinjective hdisjoint x y
      houtside selectedPlace source
      (complementaryPrimalUnitWave827 hZeta omega chi) selectedIndex
      (complementaryPrimalUnitWave827_isPureCharacter hZeta omega chi)
      hcomparison

end CyclotomicReflected

end GlobalReciprocityLaw

end Fermat.FiftyNine.Conservation.FullOrbitReciprocity827
