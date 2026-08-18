/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Prime-generic compression of complementary Fourier waves

For every prime `p`, inverse character modes have constant pointwise product.
On a finite group of cardinality `p - 1`, summing that product therefore
multiplies a selected value by `p - 1`, hence negates it in `ZMod p`.

Pairing an arbitrary vector with a pure inverse-character wave sees only the
corresponding Fourier component.  The inverse-reindexing lemmas retain the
orientation change explicitly, and the final scalar theorem turns an honest
raw reciprocity equation into the selected Fourier reading.

This is purely finite Fourier algebra.  It does not construct a Kummer class,
a local pairing, a reciprocity law, or a cyclotomic support orbit.
-/
import Fermat.Conservation.PrimeResidueFourier

open scoped BigOperators

noncomputable section

namespace Fermat.Conservation.PrimeFourierPairingCompression

open Fermat.Conservation.PrimeResidueFourier

universe uDelta

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]

private theorem cast_pred_eq_neg_one :
    ((p - 1 : ℕ) : ZMod p) = -1 := by
  rw [Nat.cast_sub (Fact.out : Nat.Prime p).one_le, ZMod.natCast_self]
  simp

private theorem cast_pred_ne_zero :
    ((p - 1 : ℕ) : ZMod p) ≠ 0 := by
  rw [cast_pred_eq_neg_one (p := p)]
  exact neg_ne_zero.mpr one_ne_zero

/-! ## Complementary-character algebra -/

/-- Inverse character modes have a constant pointwise product, equal to the
product of their scalar components. -/
theorem pointwiseProduct_complementaryCharacters
    (chi : Delta →* (ZMod p)ˣ) (leftComponent rightComponent : ZMod p)
    (position : Delta) :
    (leftComponent • characterFunction chi) position *
        (rightComponent • characterFunction chi⁻¹) position =
      leftComponent * rightComponent := by
  simp only [Pi.smul_apply, smul_eq_mul, characterFunction,
    MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have hchi : (chi position : ZMod p) ≠ 0 := Units.ne_zero _
  field_simp

/-- The pointwise product of complementary pure-character waves can be read
at any selected position. -/
theorem pointwiseProduct_eq_selected_of_complementaryPureCharacters
    (chi : Delta →* (ZMod p)ˣ) (left right : Delta → ZMod p)
    (selected position : Delta)
    (hleft : IsPureCharacter chi left)
    (hright : IsPureCharacter chi⁻¹ right) :
    left position * right position = left selected * right selected := by
  rcases hleft with ⟨leftComponent, rfl⟩
  rcases hright with ⟨rightComponent, rfl⟩
  rw [pointwiseProduct_complementaryCharacters,
    pointwiseProduct_complementaryCharacters]

section Finite

variable [Fintype Delta]

/-- Summing a constant complementary product multiplies its selected value by
the cardinality of the indexing group. -/
theorem sum_pointwiseProduct_eq_card_mul_selected
    (chi : Delta →* (ZMod p)ˣ) (left right : Delta → ZMod p)
    (selected : Delta)
    (hleft : IsPureCharacter chi left)
    (hright : IsPureCharacter chi⁻¹ right) :
    (∑ position : Delta, left position * right position) =
      (Fintype.card Delta : ZMod p) * (left selected * right selected) := by
  rw [Finset.sum_congr rfl (fun position _ ↦
    pointwiseProduct_eq_selected_of_complementaryPureCharacters
      chi left right selected position hleft hright)]
  simp

/-- On a group of cardinality `p - 1`, complementary waves compress to
`p - 1` times their product at the selected position. -/
theorem sum_pointwiseProduct_eq_pred_mul_selected
    (hcard : Fintype.card Delta = p - 1)
    (chi : Delta →* (ZMod p)ˣ) (left right : Delta → ZMod p)
    (selected : Delta)
    (hleft : IsPureCharacter chi left)
    (hright : IsPureCharacter chi⁻¹ right) :
    (∑ position : Delta, left position * right position) =
      ((p - 1 : ℕ) : ZMod p) * (left selected * right selected) := by
  calc
    (∑ position : Delta, left position * right position) =
        (Fintype.card Delta : ZMod p) *
          (left selected * right selected) :=
      sum_pointwiseProduct_eq_card_mul_selected
        chi left right selected hleft hright
    _ = ((p - 1 : ℕ) : ZMod p) *
          (left selected * right selected) := by rw [hcard]

/-- Since `p - 1 = -1` in `ZMod p`, full-orbit compression is negation. -/
theorem sum_pointwiseProduct_eq_neg_selected
    (hcard : Fintype.card Delta = p - 1)
    (chi : Delta →* (ZMod p)ˣ) (left right : Delta → ZMod p)
    (selected : Delta)
    (hleft : IsPureCharacter chi left)
    (hright : IsPureCharacter chi⁻¹ right) :
    (∑ position : Delta, left position * right position) =
      -(left selected * right selected) := by
  rw [sum_pointwiseProduct_eq_pred_mul_selected
    hcard chi left right selected hleft hright]
  rw [cast_pred_eq_neg_one (p := p), neg_one_mul]

/-! ## Fourier projection under a complete pairing sum -/

/-- Pairing against a pure inverse-character wave sees exactly the
corresponding Fourier component of an arbitrary vector. -/
theorem sum_mul_pureInverse_eq_sum_characterComponent_mul
    (hcard : Fintype.card Delta = p - 1)
    (eta : Delta →* (ZMod p)ˣ)
    (primal reflected : Delta → ZMod p)
    (hreflected : IsPureCharacter eta⁻¹ reflected) :
    (∑ x : Delta, primal x * reflected x) =
      ∑ x : Delta, characterComponent primal eta x * reflected x := by
  rcases hreflected with ⟨component, rfl⟩
  have hpred : ((p - 1 : ℕ) : ZMod p) ≠ 0 :=
    cast_pred_ne_zero (p := p)
  have hcoef :
      ((p - 1 : ℕ) : ZMod p) * fourierCoefficient primal eta =
        ∑ x : Delta, ((eta x : ZMod p))⁻¹ * primal x := by
    unfold fourierCoefficient
    rw [← mul_assoc, mul_inv_cancel₀ hpred, one_mul]
  have hright :
      (∑ x : Delta,
          characterComponent primal eta x *
            (component • characterFunction eta⁻¹) x) =
        ((p - 1 : ℕ) : ZMod p) *
          (fourierCoefficient primal eta * component) := by
    calc
      (∑ x : Delta,
          characterComponent primal eta x *
            (component • characterFunction eta⁻¹) x) =
          ∑ _x : Delta, fourierCoefficient primal eta * component := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [Pi.smul_apply, smul_eq_mul, characterFunction,
          MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
        have heta : (eta x : ZMod p) ≠ 0 := Units.ne_zero _
        field_simp
      _ = (Fintype.card Delta : ZMod p) *
          (fourierCoefficient primal eta * component) := by simp
      _ = ((p - 1 : ℕ) : ZMod p) *
          (fourierCoefficient primal eta * component) := by rw [hcard]
  rw [hright]
  calc
    (∑ x : Delta,
        primal x * (component • characterFunction eta⁻¹) x) =
        component * ∑ x : Delta, ((eta x : ZMod p))⁻¹ * primal x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp only [Pi.smul_apply, smul_eq_mul, characterFunction,
        MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
      ring
    _ = component *
        (((p - 1 : ℕ) : ZMod p) * fourierCoefficient primal eta) := by
      rw [hcoef]
    _ = ((p - 1 : ℕ) : ZMod p) *
        (fourierCoefficient primal eta * component) := by ring

/-- Full-orbit compression of an arbitrary vector against a pure inverse wave
is the negated product of its selected Fourier component and that wave. -/
theorem sum_mul_pureInverse_eq_neg_selectedComponent
    (hcard : Fintype.card Delta = p - 1)
    (eta : Delta →* (ZMod p)ˣ)
    (primal reflected : Delta → ZMod p)
    (selected : Delta)
    (hreflected : IsPureCharacter eta⁻¹ reflected) :
    (∑ x : Delta, primal x * reflected x) =
      -(characterComponent primal eta selected * reflected selected) := by
  calc
    (∑ x : Delta, primal x * reflected x) =
        ∑ x : Delta,
          characterComponent primal eta x * reflected x :=
      sum_mul_pureInverse_eq_sum_characterComponent_mul
        hcard eta primal reflected hreflected
    _ = -(characterComponent primal eta selected * reflected selected) :=
      sum_pointwiseProduct_eq_neg_selected hcard eta
        (characterComponent primal eta) reflected selected
        ⟨fourierCoefficient primal eta, rfl⟩ hreflected

/-! ## Explicit inverse orientation -/

/-- Reindex a raw vector by inversion in the group. -/
def inverseReindex (v : Delta → ZMod p) : Delta → ZMod p :=
  fun x ↦ v x⁻¹

/-- Inverting the index swaps the Fourier coefficient selected from the raw
vector from `eta` to `eta⁻¹`. -/
theorem fourierCoefficient_inverseReindex
    (raw : Delta → ZMod p) (eta : Delta →* (ZMod p)ˣ) :
    fourierCoefficient (inverseReindex raw) eta =
      fourierCoefficient raw eta⁻¹ := by
  unfold fourierCoefficient inverseReindex
  congr 1
  apply Fintype.sum_equiv (Equiv.inv Delta)
  intro x
  change (eta x : ZMod p)⁻¹ * raw x⁻¹ =
    (eta⁻¹ x⁻¹ : ZMod p)⁻¹ * raw x⁻¹
  rw [MonoidHom.inv_apply, map_inv]
  simp only [inv_inv]

/-- The inverse-oriented raw vector obeys the same selected-component
compression law. -/
theorem sum_inverseReindex_mul_pureInverse_eq_neg_selectedComponent
    (hcard : Fintype.card Delta = p - 1)
    (eta : Delta →* (ZMod p)ˣ)
    (raw reflected : Delta → ZMod p)
    (selected : Delta)
    (hreflected : IsPureCharacter eta⁻¹ reflected) :
    (∑ x : Delta, inverseReindex raw x * reflected x) =
      -(characterComponent (inverseReindex raw) eta selected *
          reflected selected) :=
  sum_mul_pureInverse_eq_neg_selectedComponent hcard eta
    (inverseReindex raw) reflected selected hreflected

/-! ## Scalar reciprocity adapter -/

/-- An honest raw reciprocity equation, together with a pure inverse meter,
identifies the distinguished scalar with the selected Fourier reading. -/
theorem wild_eq_selectedComponent_of_raw_reciprocity
    (hcard : Fintype.card Delta = p - 1)
    (eta : Delta →* (ZMod p)ˣ)
    (raw reflected : Delta → ZMod p)
    (selected : Delta)
    (hreflected : IsPureCharacter eta⁻¹ reflected)
    (wild : ZMod p)
    (reciprocity : wild + ∑ index : Delta,
      raw index * reflected index = 0) :
    wild = characterComponent raw eta selected * reflected selected := by
  have hprojection :
      (∑ index : Delta, raw index * reflected index) =
        -(characterComponent raw eta selected * reflected selected) :=
    sum_mul_pureInverse_eq_neg_selectedComponent
      hcard eta raw reflected selected hreflected
  rw [hprojection] at reciprocity
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using reciprocity)

end Finite

end Fermat.Conservation.PrimeFourierPairingCompression
