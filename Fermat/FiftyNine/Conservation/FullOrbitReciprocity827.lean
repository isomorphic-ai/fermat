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
import Fermat.Conservation.TatePairing
import Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827

open scoped BigOperators

noncomputable section

namespace Fermat.FiftyNine.Conservation.FullOrbitReciprocity827

open Fermat.Conservation
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.TatePairing
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827

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
  fun index ↦ pairing.pairAt (auxiliaryPlace index) x y

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
      -∑ index : Index, orbitReading pairing auxiliaryPlace x y index := by
  classical
  let entries := pairing.readings x y
  have hsupport : entries.support ⊆
      insert distinguished (Finset.univ.image auxiliaryPlace) := by
    intro v hv
    rw [Finset.mem_insert]
    by_cases hvd : v = distinguished
    · exact Or.inl hvd
    · refine Or.inr ?_
      by_contra hnot
      have hrange : v ∉ Set.range auxiliaryPlace := by
        rintro ⟨index, rfl⟩
        exact hnot (Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩)
      exact (Finsupp.mem_support_iff.mp hv) (houtside v hvd hrange)
  have hdistinguished :
      distinguished ∉ Finset.univ.image auxiliaryPlace := by
    intro hmem
    obtain ⟨index, _, hindex⟩ := Finset.mem_image.mp hmem
    exact hdisjoint index hindex
  have hsum_support :
      entries.support.sum (fun v ↦ entries v) = 0 :=
    reciprocity.sum_eq_zero x y
  have hsum_insert :
      (insert distinguished (Finset.univ.image auxiliaryPlace)).sum
          (fun v ↦ entries v) = 0 := by
    calc
      (insert distinguished (Finset.univ.image auxiliaryPlace)).sum
          (fun v ↦ entries v) =
          entries.support.sum (fun v ↦ entries v) := by
        symm
        apply Finset.sum_subset hsupport
        intro v _hv hnot
        by_contra hne
        exact hnot (Finsupp.mem_support_iff.mpr hne)
      _ = 0 := hsum_support
  rw [Finset.sum_insert hdistinguished] at hsum_insert
  have hbalanced : pairing.pairAt distinguished x y +
      ∑ index : Index, orbitReading pairing auxiliaryPlace x y index = 0 := by
    rw [Finset.sum_image hinjective.injOn] at hsum_insert
    simpa [PlaceIndexedLocalPairing.pairAt, orbitReading, entries] using hsum_insert
  exact eq_neg_of_add_eq_zero_left hbalanced

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

end GlobalReciprocityLaw

end Fermat.FiftyNine.Conservation.FullOrbitReciprocity827
