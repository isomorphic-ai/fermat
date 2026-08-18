/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Prime-generic full-orbit reciprocity compression

For every prime `p`, this file retains a complete finite auxiliary orbit
inside an honest place-indexed global reciprocity law.  Reciprocity first
identifies the distinguished reading with the negative full orbit sum.
Complementary pure character waves then compress that sum to one selected
product, while an arbitrary raw primal wave is retained through exactly its
selected Fourier component.  Inverse reindexing records the opposite place
orientation explicitly.

The representation group carried by the local pairing and the group indexing
the auxiliary orbit are intentionally separate.  No local pairing, global
reciprocity law, support-silence theorem, comparison with local values, or
cyclotomic orbit is constructed here; all such arithmetic data remain
explicit inputs.  Fourier projection occurs only under the complete orbit
sum, never through a pointwise identification of a raw vector with one of its
character components.
-/
import Fermat.Conservation.PrimeFourierPairingCompression
import Fermat.Conservation.TatePairing

open scoped BigOperators

noncomputable section

namespace Fermat.Conservation.PrimeFullOrbitReciprocity

open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.PrimeFourierPairingCompression
open Fermat.Conservation.PrimeResidueFourier
open Fermat.Conservation.TatePairing

universe uPlace uDelta uIndex uChi uDual

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt p) Delta}
  {Place : Type uPlace} {SelmerChi : Type uChi}
  {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra p Delta) SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra p Delta) DOmegaSelmerChiStar]

/-- The local-reading vector along an indexed auxiliary orbit.  Its index
type is independent of the representation group of the pairing. -/
def orbitReading
    (pairing : PlaceIndexedLocalPairing p Delta omega chi Place
      SelmerChi DOmegaSelmerChiStar)
    {Index : Type uIndex} (auxiliaryPlace : Index → Place)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) : Index → ZMod p :=
  fun index ↦ pairing.pairAt (auxiliaryPlace index) x y

namespace GlobalReciprocityLaw

variable {pairing : PlaceIndexedLocalPairing p Delta omega chi Place
  SelmerChi DOmegaSelmerChiStar}

/-- If all away readings lie on one injectively indexed finite orbit,
reciprocity balances the distinguished reading against its complete sum. -/
theorem pairAt_eq_neg_sum_orbitReading
    {Index : Type uIndex} [Fintype Index]
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished : Place) (auxiliaryPlace : Index → Place)
    (hinjective : Function.Injective auxiliaryPlace)
    (hdisjoint : ∀ index, auxiliaryPlace index ≠ distinguished)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (houtside : ∀ v, v ≠ distinguished →
      v ∉ Set.range auxiliaryPlace → pairing.pairAt v x y = 0) :
    pairing.pairAt distinguished x y =
      -∑ index : Index, orbitReading pairing auxiliaryPlace x y index := by
  classical
  let places : Finset Place := Finset.univ.image auxiliaryPlace
  have hdistinguished : distinguished ∉ places := by
    intro hmem
    obtain ⟨index, _, hindex⟩ := Finset.mem_image.mp hmem
    exact hdisjoint index hindex
  have houtsidePlaces : ∀ v, v ≠ distinguished → v ∉ places →
      pairing.pairAt v x y = 0 := by
    intro v hvd hvplaces
    apply houtside v hvd
    rintro ⟨index, rfl⟩
    exact hvplaces (Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩)
  have htotal : pairing.readingTotalOn places x y =
      ∑ index : Index, orbitReading pairing auxiliaryPlace x y index := by
    unfold PlaceIndexedLocalPairing.readingTotalOn
    rw [Finset.sum_image hinjective.injOn]
    rfl
  calc
    pairing.pairAt distinguished x y =
        -pairing.readingTotalOn places x y :=
      reciprocity.pairAt_eq_neg_readingTotalOn distinguished places
        hdistinguished x y houtsidePlaces
    _ = -∑ index : Index,
        orbitReading pairing auxiliaryPlace x y index := congrArg Neg.neg htotal

/-- Complementary pure-character waves turn the complete reciprocity balance
on an orbit of cardinality `p - 1` into their product at any selected index.
The comparison with actual local readings remains an explicit premise. -/
theorem pairAt_eq_selectedProduct_of_complementaryOrbit
    {Index : Type uIndex} [CommGroup Index] [Fintype Index]
    (hcard : Fintype.card Index = p - 1)
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished : Place) (auxiliaryPlace : Index → Place)
    (hinjective : Function.Injective auxiliaryPlace)
    (hdisjoint : ∀ index, auxiliaryPlace index ≠ distinguished)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (houtside : ∀ v, v ≠ distinguished →
      v ∉ Set.range auxiliaryPlace → pairing.pairAt v x y = 0)
    (mode : Index →* (ZMod p)ˣ)
    (primal reflected : Index → ZMod p)
    (selected : Index)
    (hprimal : IsPureCharacter mode primal)
    (hreflected : IsPureCharacter mode⁻¹ reflected)
    (hcomparison : ∀ index,
      pairing.pairAt (auxiliaryPlace index) x y =
        primal index * reflected index) :
    pairing.pairAt distinguished x y =
      primal selected * reflected selected := by
  calc
    pairing.pairAt distinguished x y =
        -∑ index : Index,
          orbitReading pairing auxiliaryPlace x y index :=
      pairAt_eq_neg_sum_orbitReading reciprocity distinguished
        auxiliaryPlace hinjective hdisjoint x y houtside
    _ = -∑ index : Index, primal index * reflected index := by
      congr 1
      apply Finset.sum_congr rfl
      intro index _
      exact hcomparison index
    _ = -(-(primal selected * reflected selected)) := by
      rw [sum_pointwiseProduct_eq_neg_selected hcard mode
        primal reflected selected hprimal hreflected]
    _ = primal selected * reflected selected := neg_neg _

/-- A complete raw orbit comparison may be Fourier-projected under the sum:
pairing with a pure inverse-character wave retains precisely the selected
component of the raw primal vector. -/
theorem pairAt_eq_selectedComponent_of_rawOrbit
    {Index : Type uIndex} [CommGroup Index] [Fintype Index]
    (hcard : Fintype.card Index = p - 1)
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished : Place) (auxiliaryPlace : Index → Place)
    (hinjective : Function.Injective auxiliaryPlace)
    (hdisjoint : ∀ index, auxiliaryPlace index ≠ distinguished)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (houtside : ∀ v, v ≠ distinguished →
      v ∉ Set.range auxiliaryPlace → pairing.pairAt v x y = 0)
    (eta : Index →* (ZMod p)ˣ)
    (raw reflected : Index → ZMod p)
    (selected : Index)
    (hreflected : IsPureCharacter eta⁻¹ reflected)
    (hcomparison : ∀ index,
      pairing.pairAt (auxiliaryPlace index) x y =
        raw index * reflected index) :
    pairing.pairAt distinguished x y =
      characterComponent raw eta selected * reflected selected := by
  have horbit :
      (∑ index : Index,
          orbitReading pairing auxiliaryPlace x y index) =
        ∑ index : Index, raw index * reflected index := by
    apply Finset.sum_congr rfl
    intro index _
    exact hcomparison index
  have hprojection :
      (∑ index : Index, raw index * reflected index) =
        -(characterComponent raw eta selected * reflected selected) :=
    sum_mul_pureInverse_eq_neg_selectedComponent
      hcard eta raw reflected selected hreflected
  calc
    pairing.pairAt distinguished x y =
        -∑ index : Index,
          orbitReading pairing auxiliaryPlace x y index :=
      pairAt_eq_neg_sum_orbitReading reciprocity distinguished
        auxiliaryPlace hinjective hdisjoint x y houtside
    _ = -∑ index : Index, raw index * reflected index :=
      congrArg Neg.neg horbit
    _ = -(-(characterComponent raw eta selected * reflected selected)) :=
      congrArg Neg.neg hprojection
    _ = characterComponent raw eta selected * reflected selected := neg_neg _

/-- The explicit inverse-oriented specialization: orbit index `index` reads
raw coordinate `index⁻¹`, and the selected component is taken only after that
reindexing. -/
theorem pairAt_eq_inverseOrientedComponent_of_rawOrbit
    {Index : Type uIndex} [CommGroup Index] [Fintype Index]
    (hcard : Fintype.card Index = p - 1)
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished : Place) (auxiliaryPlace : Index → Place)
    (hinjective : Function.Injective auxiliaryPlace)
    (hdisjoint : ∀ index, auxiliaryPlace index ≠ distinguished)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (houtside : ∀ v, v ≠ distinguished →
      v ∉ Set.range auxiliaryPlace → pairing.pairAt v x y = 0)
    (eta : Index →* (ZMod p)ˣ)
    (raw reflected : Index → ZMod p)
    (selected : Index)
    (hreflected : IsPureCharacter eta⁻¹ reflected)
    (hcomparison : ∀ index,
      pairing.pairAt (auxiliaryPlace index) x y =
        inverseReindex raw index * reflected index) :
    pairing.pairAt distinguished x y =
      characterComponent (inverseReindex raw) eta selected *
        reflected selected :=
  pairAt_eq_selectedComponent_of_rawOrbit hcard reciprocity distinguished
    auxiliaryPlace hinjective hdisjoint x y houtside eta
    (inverseReindex raw) reflected selected hreflected hcomparison

end GlobalReciprocityLaw

end Fermat.Conservation.PrimeFullOrbitReciprocity
