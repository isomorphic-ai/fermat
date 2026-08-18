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
import Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827

open scoped BigOperators

noncomputable section

namespace Fermat.FiftyNine.Conservation.FourierPairingProjection827

open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827

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
      ∑ x : Delta, characterComponent primal eta x * reflected x := by
  rcases hreflected with ⟨component, rfl⟩
  have h58 : (58 : ZMod 59) ≠ 0 := by decide +kernel +revert
  have hcoef :
      (58 : ZMod 59) * fourierCoefficient primal eta =
        ∑ x : Delta, ((eta x : ZMod 59))⁻¹ * primal x := by
    unfold fourierCoefficient
    rw [← mul_assoc, mul_inv_cancel₀ h58, one_mul]
  have hright :
      (∑ x : Delta,
          characterComponent primal eta x *
            (component • characterFunction eta⁻¹) x) =
        (58 : ZMod 59) * (fourierCoefficient primal eta * component) := by
    calc
      (∑ x : Delta,
          characterComponent primal eta x *
            (component • characterFunction eta⁻¹) x) =
          ∑ _x : Delta, fourierCoefficient primal eta * component := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [characterComponent_apply, Pi.smul_apply, smul_eq_mul,
          characterFunction, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
        have heta : (eta x : ZMod 59) ≠ 0 := Units.ne_zero _
        field_simp
      _ = (Fintype.card Delta : ZMod 59) *
          (fourierCoefficient primal eta * component) := by simp
      _ = (58 : ZMod 59) *
          (fourierCoefficient primal eta * component) := by
        rw [hcard]
        norm_num
  rw [hright]
  calc
    (∑ x : Delta,
        primal x * (component • characterFunction eta⁻¹) x) =
        component * ∑ x : Delta, ((eta x : ZMod 59))⁻¹ * primal x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp only [Pi.smul_apply, smul_eq_mul, characterFunction,
        MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
      ring
    _ = component * ((58 : ZMod 59) * fourierCoefficient primal eta) := by
      rw [hcoef]
    _ = (58 : ZMod 59) * (fourierCoefficient primal eta * component) := by
      ring

/-- The oriented raw orbit: canonical place index `x` reads the explicit
residue map indexed by `x⁻¹`. -/
def inverseReindex (v : Delta → ZMod 59) : Delta → ZMod 59 :=
  fun x ↦ v x⁻¹

/-- Inverting the place index swaps the coefficient selected from the raw
vector.  Thus the honest place-oriented primal wave uses the raw
`eta⁻¹`-coefficient, not the raw `eta`-coefficient. -/
theorem fourierCoefficient_inverseReindex
    (raw : Delta → ZMod 59) (eta : Delta →* (ZMod 59)ˣ) :
    fourierCoefficient (inverseReindex raw) eta =
      fourierCoefficient raw eta⁻¹ := by
  unfold fourierCoefficient inverseReindex
  congr 1
  apply Fintype.sum_equiv (Equiv.inv Delta)
  intro x
  change (↑(eta x) : ZMod 59)⁻¹ * raw x⁻¹ =
    (↑(eta⁻¹ x⁻¹) : ZMod 59)⁻¹ * raw x⁻¹
  rw [MonoidHom.inv_apply, map_inv]
  simp only [inv_inv]

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
          reflected selected) := by
  calc
    (∑ x : Delta, inverseReindex raw x * reflected x) =
        ∑ x : Delta,
          characterComponent (inverseReindex raw) eta x * reflected x :=
      sum_mul_pureInverse_eq_sum_characterComponent_mul
        hcard eta (inverseReindex raw) reflected hreflected
    _ = -(characterComponent (inverseReindex raw) eta selected *
          reflected selected) :=
      sum_pointwiseProduct_eq_neg_selected hcard eta
        (characterComponent (inverseReindex raw) eta) reflected selected
        ⟨fourierCoefficient (inverseReindex raw) eta, rfl⟩ hreflected

end Finite

end Fermat.FiftyNine.Conservation.FourierPairingProjection827
