/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Compression of complementary Fourier waves on the 827 orbit

This file isolates the finite Fourier algebra needed by a future global
reciprocity adapter.  If two `ZMod 59`-valued waves occupy inverse character
modes, their pointwise product is constant.  On the 58-element regular orbit
over 827, the sum of that product is therefore `58` times any selected value,
which is its negation in `ZMod 59`.

The statements concern functions on the orbit only.  In particular, they do
not identify either wave with a Kummer class or their product with a local
Tate pairing.
-/
import Fermat.Conservation.PrimeFourierPairingCompression
import Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827

open scoped BigOperators

noncomputable section

namespace Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

universe uDelta

variable {Delta : Type uDelta} [CommGroup Delta]

/-! ## Generic complementary-character algebra -/

/-- Inverse character modes have a constant pointwise product, equal to the
product of their scalar components. -/
theorem pointwiseProduct_complementaryCharacters
    (chi : Delta →* (ZMod 59)ˣ) (leftComponent rightComponent : ZMod 59)
    (position : Delta) :
    (leftComponent • characterFunction chi) position *
        (rightComponent • characterFunction chi⁻¹) position =
      leftComponent * rightComponent :=
  Fermat.Conservation.PrimeFourierPairingCompression.pointwiseProduct_complementaryCharacters
      (p := 59) chi leftComponent rightComponent position

/-- Consequently, the pointwise product of two complementary pure-character
waves can be read at any chosen position. -/
theorem pointwiseProduct_eq_selected_of_complementaryPureCharacters
    (chi : Delta →* (ZMod 59)ˣ) (left right : Delta → ZMod 59)
    (selected position : Delta)
    (hleft : IsPureCharacter chi left)
    (hright : IsPureCharacter chi⁻¹ right) :
    left position * right position = left selected * right selected :=
  Fermat.Conservation.PrimeFourierPairingCompression.pointwiseProduct_eq_selected_of_complementaryPureCharacters
      (p := 59) chi left right selected position hleft hright

section Finite

variable [Fintype Delta]

/-- Summing the pointwise product over a finite orbit multiplies its value at
one selected position by the orbit cardinality. -/
theorem sum_pointwiseProduct_eq_card_mul_selected
    (chi : Delta →* (ZMod 59)ˣ) (left right : Delta → ZMod 59)
    (selected : Delta)
    (hleft : IsPureCharacter chi left)
    (hright : IsPureCharacter chi⁻¹ right) :
    (∑ position : Delta, left position * right position) =
      (Fintype.card Delta : ZMod 59) * (left selected * right selected) :=
  Fermat.Conservation.PrimeFourierPairingCompression.sum_pointwiseProduct_eq_card_mul_selected
      (p := 59) chi left right selected hleft hright

/-- On any 58-element orbit, complementary waves compress to 58 times their
product at the selected position. -/
theorem sum_pointwiseProduct_eq_fiftyEight_mul_selected
    (hcard : Fintype.card Delta = 58)
    (chi : Delta →* (ZMod 59)ˣ) (left right : Delta → ZMod 59)
    (selected : Delta)
    (hleft : IsPureCharacter chi left)
    (hright : IsPureCharacter chi⁻¹ right) :
    (∑ position : Delta, left position * right position) =
      (58 : ZMod 59) * (left selected * right selected) :=
  Fermat.Conservation.PrimeFourierPairingCompression.sum_pointwiseProduct_eq_pred_mul_selected
      (p := 59) hcard chi left right selected hleft hright

/-- Since `58 = -1` in `ZMod 59`, full-orbit compression is negation. -/
theorem sum_pointwiseProduct_eq_neg_selected
    (hcard : Fintype.card Delta = 58)
    (chi : Delta →* (ZMod 59)ˣ) (left right : Delta → ZMod 59)
    (selected : Delta)
    (hleft : IsPureCharacter chi left)
    (hright : IsPureCharacter chi⁻¹ right) :
    (∑ position : Delta, left position * right position) =
      -(left selected * right selected) :=
  Fermat.Conservation.PrimeFourierPairingCompression.sum_pointwiseProduct_eq_neg_selected
      (p := 59) hcard chi left right selected hleft hright

end Finite

/-! ## The actual 58-place Galois index orbit -/

/-- The reusable compression theorem specialized to the regular 58-place
index orbit above 827. -/
theorem galoisIndex59_sum_pointwiseProduct_eq_neg_selected
    (chi : GaloisIndex59 →* (ZMod 59)ˣ)
    (left right : GaloisIndex59 → ZMod 59)
    (selected : GaloisIndex59)
    (hleft : IsPureCharacter chi left)
    (hright : IsPureCharacter chi⁻¹ right) :
    (∑ sigma : GaloisIndex59, left sigma * right sigma) =
      -(left selected * right selected) :=
  sum_pointwiseProduct_eq_neg_selected galoisIndex59_card
    chi left right selected hleft hright

/-! ## Canonically seated reflected localization -/

universe uK

section CyclotomicLocalization

variable {K : Type uK} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- The canonical projected 827-localization is the inverse wave in the
full-orbit compression formula.  The complementary primal wave is deliberately
an explicit input: this theorem neither constructs it nor identifies the
pointwise products with local Tate pairings. -/
theorem cyclotomic_projectedLocalization_product_sum_eq_neg_selected
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (selectedPlace : Place827 K)
    (source : QRelaxedSelmerCarrier827 K)
    (primal : GaloisIndex59 → ZMod 59)
    (selectedIndex : GaloisIndex59)
    (hprimal : IsPureCharacter
      (reducedCharacter59
        (InvolutiveBase.reflectedCharacter omega chi)) primal) :
    (∑ sigma : GaloisIndex59,
        primal sigma *
          projectedLocalizationVector827
            (cyclotomicQRelaxedSelmerRepresentation827 K)
            omega chi selectedPlace source sigma) =
      -(primal selectedIndex *
          projectedLocalizationVector827
            (cyclotomicQRelaxedSelmerRepresentation827 K)
            omega chi selectedPlace source selectedIndex) := by
  let reflectedCharacter :=
    reducedCharacter59 (InvolutiveBase.reflectedCharacter omega chi)
  have hreflected : IsPureCharacter reflectedCharacter⁻¹
      (projectedLocalizationVector827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        omega chi selectedPlace source) :=
    projectedLocalization_isPureCharacter
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi selectedPlace
      (cyclotomicQLocalizationEquivariance827 K omega chi selectedPlace)
      source
  exact galoisIndex59_sum_pointwiseProduct_eq_neg_selected
    reflectedCharacter primal
    (projectedLocalizationVector827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi selectedPlace source)
    selectedIndex hprimal hreflected

end CyclotomicLocalization

end Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827
