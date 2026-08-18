/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Pure Fourier silence for the global-unit shape at 827

This file isolates the finite Fourier half of the W5 global-unit obligation.
It assumes only that a raw residue wave is the sum of a conjugation-even
component and the primitive-root mode.  Inverting the place index sends that
root mode from exponent `1` to exponent `57`; both the even component and
mode `57` have zero Fourier coefficient in the canonical odd mode `43`.

The inverse orientation and all three numerical indices are retained in the
public theorem statements.  This file does not assert the arithmetic input
that every global unit admits the displayed decomposition.
-/
import Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
import Fermat.FiftyNine.Conservation.FourierPairingProjection827

open scoped BigOperators
open Module

noncomputable section

namespace Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827

open Fermat.FiftyNine.Conservation.FourierPairingProjection827
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

private theorem fourierCoefficient_characterFunction_eq_zero_of_ne
    (psi eta : GaloisIndex59 →* (ZMod 59)ˣ) (hne : psi ≠ eta) :
    fourierCoefficient (characterFunction psi) eta = 0 := by
  rw [← characterBasis_repr_eq_fourierCoefficient galoisIndex59_card]
  rw [← characterBasis_apply galoisIndex59_card psi, Basis.repr_self]
  simp [hne]

private theorem fourierCoefficient_add
    (v w : GaloisIndex59 → ZMod 59)
    (eta : GaloisIndex59 →* (ZMod 59)ˣ) :
    fourierCoefficient (v + w) eta =
      fourierCoefficient v eta + fourierCoefficient w eta := by
  unfold fourierCoefficient
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem fourierCoefficient_const_mul
    (component : ZMod 59) (v : GaloisIndex59 → ZMod 59)
    (eta : GaloisIndex59 →* (ZMod 59)ˣ) :
    fourierCoefficient (fun sigma ↦ component * v sigma) eta =
      component * fourierCoefficient v eta := by
  unfold fourierCoefficient
  conv_lhs =>
    enter [2, 2, sigma]
    rw [show ((eta sigma : ZMod 59))⁻¹ * (component * v sigma) =
      component * (((eta sigma : ZMod 59))⁻¹ * v sigma) by ring]
  rw [← Finset.mul_sum]
  ring

private theorem fourierCoefficient_eq_zero_of_negOne_invariant
    (v : GaloisIndex59 → ZMod 59)
    (hv : ∀ sigma, v ((-1 : GaloisIndex59) * sigma) = v sigma)
    (eta : GaloisIndex59 →* (ZMod 59)ˣ)
    (heta : (eta (-1) : ZMod 59) = -1) :
    fourierCoefficient v eta = 0 := by
  set_option maxRecDepth 10000 in
  let term : GaloisIndex59 → ZMod 59 :=
    fun sigma ↦ ((eta sigma : ZMod 59))⁻¹ * v sigma
  have hterm (sigma : GaloisIndex59) :
      term sigma = -term ((-1 : GaloisIndex59) * sigma) := by
    dsimp [term]
    rw [map_mul, hv, Units.val_mul, heta]
    rw [neg_one_mul, inv_neg]
    ring
  have hsum : (∑ sigma : GaloisIndex59, term sigma) =
      -∑ sigma : GaloisIndex59, term sigma := by
    calc
      (∑ sigma : GaloisIndex59, term sigma) =
          ∑ sigma : GaloisIndex59, -term ((-1 : GaloisIndex59) * sigma) := by
            apply Finset.sum_congr rfl
            intro sigma _
            exact hterm sigma
      _ = ∑ sigma : GaloisIndex59, -term sigma := by
            apply Fintype.sum_equiv (Equiv.mulLeft (-1 : GaloisIndex59))
            intro sigma
            rfl
      _ = -∑ sigma : GaloisIndex59, term sigma := by
            simp only [Finset.sum_neg_distrib]
  have htwo : (2 : ZMod 59) ≠ 0 := by decide
  have hsumZero : (∑ sigma : GaloisIndex59, term sigma) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left htwo
    calc
      (2 : ZMod 59) * ∑ sigma : GaloisIndex59, term sigma =
          (∑ sigma : GaloisIndex59, term sigma) +
            ∑ sigma : GaloisIndex59, term sigma := by ring
      _ = (∑ sigma : GaloisIndex59, term sigma) +
            -∑ sigma : GaloisIndex59, term sigma :=
          congrArg (fun x ↦ (∑ sigma : GaloisIndex59, term sigma) + x) hsum
      _ = 0 := add_neg_cancel _
  unfold fourierCoefficient
  change (58 : ZMod 59)⁻¹ * ∑ sigma : GaloisIndex59, term sigma = 0
  rw [hsumZero, mul_zero]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- In the residue orientation, inversion sends the primitive root mode
`1` to the explicitly frozen place-oriented mode `57`. -/
theorem inverseReindex_powerCharacter59_one_eq_fiftySeven :
    inverseReindex (characterFunction (powerCharacter59 1)) =
      characterFunction (powerCharacter59 57) := by
  decide +kernel +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The canonical readout mode `43` is odd under complex conjugation. -/
theorem powerCharacter59_fortyThree_negOne :
    (powerCharacter59 43 (-1) : ZMod 59) = -1 := by
  decide +kernel +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The inverted primitive-root mode `57` is not the readout mode `43`. -/
theorem powerCharacter59_fiftySeven_ne_fortyThree :
    powerCharacter59 57 ≠ powerCharacter59 43 := by
  decide +kernel +revert

/-- Inverse reindexing preserves conjugation symmetry. -/
theorem inverseReindex_negOne_invariant
    (evenPart : GaloisIndex59 → ZMod 59)
    (heven : ∀ sigma,
      evenPart ((-1 : GaloisIndex59) * sigma) = evenPart sigma) :
    ∀ sigma, inverseReindex evenPart ((-1 : GaloisIndex59) * sigma) =
      inverseReindex evenPart sigma := by
  intro sigma
  unfold FourierPairingProjection827.inverseReindex
    Fermat.Conservation.PrimeFourierPairingCompression.inverseReindex
  have hinv : ((-1 : GaloisIndex59) * sigma)⁻¹ =
      (-1 : GaloisIndex59) * sigma⁻¹ := by
    rw [mul_inv_rev]
    simp only [inv_neg, inv_one]
    ac_rfl
  rw [hinv, heven]

/-- The complete orientation audit for an even component plus a raw
primitive-root component.  The inverse on the sigma index is retained on the
left; on the right it visibly turns raw mode `1` into place mode `57`. -/
theorem inverseReindex_even_add_primitiveRootMode_eq
    (evenPart : GaloisIndex59 → ZMod 59) (rootComponent : ZMod 59) :
    inverseReindex
        (fun sigma ↦ evenPart sigma + rootComponent *
          (powerCharacter59 1 sigma : ZMod 59)) =
      fun sigma ↦ inverseReindex evenPart sigma + rootComponent *
        (powerCharacter59 57 sigma : ZMod 59) := by
  funext sigma
  change evenPart sigma⁻¹ + rootComponent *
      (powerCharacter59 1 sigma⁻¹ : ZMod 59) =
    evenPart sigma⁻¹ + rootComponent *
      (powerCharacter59 57 sigma : ZMod 59)
  have hmode := congrFun inverseReindex_powerCharacter59_one_eq_fiftySeven sigma
  change (powerCharacter59 1 sigma⁻¹ : ZMod 59) =
      (powerCharacter59 57 sigma : ZMod 59) at hmode
  rw [hmode]

/-- The pure Fourier half of the W5 global-unit obligation.  If a raw
residue wave is the sum of a conjugation-even component and the primitive
root mode, then its explicitly inverse-oriented place wave has zero
coefficient in the canonical reflected readout mode `43`.

This theorem proves only the finite Fourier consequence.  It does not claim
that every global unit has the displayed decomposition. -/
theorem inverseEvenPrimitive_powerFortyThree_fourier_eq_zero
    (evenPart : GaloisIndex59 → ZMod 59) (rootComponent : ZMod 59)
    (heven : ∀ sigma,
      evenPart ((-1 : GaloisIndex59) * sigma) = evenPart sigma) :
    fourierCoefficient
      (inverseReindex
        (fun sigma ↦ evenPart sigma + rootComponent *
          (powerCharacter59 1 sigma : ZMod 59)))
      (powerCharacter59 43) = 0 := by
  rw [inverseReindex_even_add_primitiveRootMode_eq]
  have hevenInv := inverseReindex_negOne_invariant evenPart heven
  have hevenZero :
      fourierCoefficient (inverseReindex evenPart) (powerCharacter59 43) = 0 :=
    fourierCoefficient_eq_zero_of_negOne_invariant
      (inverseReindex evenPart) hevenInv (powerCharacter59 43)
        powerCharacter59_fortyThree_negOne
  have hrootZero :
      fourierCoefficient (characterFunction (powerCharacter59 57))
        (powerCharacter59 43) = 0 :=
    fourierCoefficient_characterFunction_eq_zero_of_ne
      (powerCharacter59 57) (powerCharacter59 43)
        powerCharacter59_fiftySeven_ne_fortyThree
  change fourierCoefficient
      (inverseReindex evenPart +
        fun sigma ↦ rootComponent *
          characterFunction (powerCharacter59 57) sigma)
      (powerCharacter59 43) = 0
  rw [fourierCoefficient_add, fourierCoefficient_const_mul,
    hevenZero, hrootZero]
  ring

end Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827
