/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Arbitrary global-unit silence in the canonical 827 Fourier mode

The arithmetic decomposition writes the raw residue wave of every actual
global ring unit as an explicit conjugation-even half-sum plus one
primitive-root mode.  The pure Fourier theorem then kills its explicitly
inverse-reindexed coefficient in the canonical odd mode `43`.  This is the
raw wave consumed by the tame context.  The already symmetrized
`fullOrbitUnitReading827` follows as a shorter corollary.

This file does not identify residue products with local Tate pairings and
makes no Poitou--Tate or Kummer--Artin comparison claim.
-/
import Fermat.FiftyNine.Conservation.ArbitraryUnitOrbitDecomposition827
import Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827

noncomputable section

namespace Fermat.FiftyNine.Conservation.ArbitraryUnitFourierSilence827

open Fermat.FiftyNine.Conservation.ArbitraryUnitOrbitDecomposition827
open Fermat.FiftyNine.Conservation.FourierPairingProjection827
open Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.PrimalOrbitResidue827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

private abbrev canonicalZeta59_isPrimitive :
    IsPrimitiveRoot (IsCyclotomicExtension.zeta 59 ℚ K) 59 :=
  IsCyclotomicExtension.zeta_spec 59 ℚ K

/-- The explicit conjugation-even half-sum extracted from an arbitrary raw
global-unit residue wave. -/
noncomputable def rawGlobalUnitEvenPart827
    (u : (NumberField.RingOfIntegers K)ˣ) :
    GaloisIndex59 → ZMod 59 :=
  fun sigma ↦ (2 : ZMod 59)⁻¹ *
    (rawGlobalUnitOrbitWave827 u sigma +
      rawGlobalUnitOrbitWave827 u
        (sigma * (-1 : GaloisIndex59)))

/-- The half-sum is fixed by left multiplication by `-1`.  The arithmetic
decomposition uses a right action; only commutativity reconciles the two. -/
theorem rawGlobalUnitEvenPart827_negOne_even
    (u : (NumberField.RingOfIntegers K)ˣ) (sigma : GaloisIndex59) :
    rawGlobalUnitEvenPart827 u ((-1 : GaloisIndex59) * sigma) =
      rawGlobalUnitEvenPart827 u sigma := by
  unfold rawGlobalUnitEvenPart827
  have hfirst : (-1 : GaloisIndex59) * sigma =
      sigma * (-1 : GaloisIndex59) := mul_comm _ _
  have hsecond : (sigma * (-1 : GaloisIndex59)) *
      (-1 : GaloisIndex59) = sigma := by simp
  rw [hfirst, hsecond]
  ring

/-- Every arbitrary raw global-unit wave is its explicit conjugation-even
half-sum plus one scalar multiple of raw power-character mode `1`. -/
theorem exists_rawGlobalUnitOrbitWave827_eq_even_add_primitiveRootMode
    (u : (NumberField.RingOfIntegers K)ˣ) :
    ∃ rootComponent : ZMod 59,
      rawGlobalUnitOrbitWave827 u =
        fun sigma ↦ rawGlobalUnitEvenPart827 u sigma +
          rootComponent * (powerCharacter59 1 sigma : ZMod 59) := by
  obtain ⟨j, hj⟩ :=
    exists_rawGlobalUnitOrbitWave827_rootMode_decomposition (K := K) u
  let c : ZMod 59 := ((2 * 7 * (j * 2) : ℕ) : ZMod 59)
  refine ⟨(2 : ZMod 59)⁻¹ * c, ?_⟩
  funext sigma
  have hdecomp : rawGlobalUnitOrbitWave827 u sigma =
      c * (sigma : ZMod 59) +
        rawGlobalUnitOrbitWave827 u
          (sigma * (-1 : GaloisIndex59)) := by
    exact hj sigma
  unfold rawGlobalUnitEvenPart827
  rw [powerCharacter59_apply]
  rw [show (1 : ZMod 58).val = 1 by decide, pow_one]
  change rawGlobalUnitOrbitWave827 u sigma =
    (2 : ZMod 59)⁻¹ *
        (rawGlobalUnitOrbitWave827 u sigma +
          rawGlobalUnitOrbitWave827 u
            (sigma * (-1 : GaloisIndex59))) +
      (2 : ZMod 59)⁻¹ * c * (sigma : ZMod 59)
  rw [hdecomp]
  have htwo : (2 : ZMod 59) ≠ 0 := by decide
  field_simp
  ring

/-- The actual raw global-unit residue wave seen by the tame context has
zero inverse-oriented Fourier coefficient in fixed mode `43`. -/
theorem inverseReindex_rawGlobalUnitOrbitWave827_powerFortyThree_eq_zero
    (u : (NumberField.RingOfIntegers K)ˣ) :
    fourierCoefficient
      (inverseReindex (rawGlobalUnitOrbitWave827 u))
      (powerCharacter59 43) = 0 := by
  obtain ⟨rootComponent, hdecomp⟩ :=
    exists_rawGlobalUnitOrbitWave827_eq_even_add_primitiveRootMode
      (K := K) u
  rw [hdecomp]
  exact inverseEvenPrimitive_powerFortyThree_fourier_eq_zero
    (rawGlobalUnitEvenPart827 u) rootComponent
      (rawGlobalUnitEvenPart827_negOne_even u)

/-- Equivalently, the mode-`43` projection of the inverse-oriented raw tame
wave is identically zero. -/
theorem inverseReindex_rawGlobalUnitOrbitWave827_powerFortyThree_characterComponent_eq_zero
    (u : (NumberField.RingOfIntegers K)ˣ) :
    characterComponent
      (inverseReindex (rawGlobalUnitOrbitWave827 u))
      (powerCharacter59 43) = 0 := by
  funext sigma
  rw [characterComponent_apply,
    inverseReindex_rawGlobalUnitOrbitWave827_powerFortyThree_eq_zero]
  simp

/-- Every corrected global-unit residue wave has zero inverse-oriented
Fourier coefficient in the fixed canonical mode `43`.  The arithmetic
evenness theorem is stated with right multiplication by `-1`; the only
orientation reconciliation below is commutativity of `GaloisIndex59`. -/
theorem inverseReindex_fullOrbitUnitReading827_powerFortyThree_eq_zero
    (u : (NumberField.RingOfIntegers K)ˣ) :
    fourierCoefficient
      (inverseReindex
        (fullOrbitUnitReading827
          (canonicalZeta59_isPrimitive (K := K)) u))
      (powerCharacter59 43) = 0 := by
  have heven : ∀ sigma : GaloisIndex59,
      fullOrbitUnitReading827 (canonicalZeta59_isPrimitive (K := K)) u
          ((-1 : GaloisIndex59) * sigma) =
        fullOrbitUnitReading827 (canonicalZeta59_isPrimitive (K := K)) u
          sigma := by
    intro sigma
    rw [mul_comm]
    exact fullOrbitUnitReading827_negOne_even u sigma
  simpa using
    (inverseEvenPrimitive_powerFortyThree_fourier_eq_zero
      (fullOrbitUnitReading827
        (canonicalZeta59_isPrimitive (K := K)) u) 0 heven)

/-- Equivalently, the complete mode-`43` Fourier projection of every
inverse-oriented corrected global-unit wave is the zero wave. -/
theorem inverseReindex_fullOrbitUnitReading827_powerFortyThree_characterComponent_eq_zero
    (u : (NumberField.RingOfIntegers K)ˣ) :
    characterComponent
      (inverseReindex
        (fullOrbitUnitReading827
          (canonicalZeta59_isPrimitive (K := K)) u))
      (powerCharacter59 43) = 0 := by
  funext sigma
  rw [characterComponent_apply,
    inverseReindex_fullOrbitUnitReading827_powerFortyThree_eq_zero]
  simp

end Fermat.FiftyNine.Conservation.ArbitraryUnitFourierSilence827
