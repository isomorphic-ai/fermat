/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Arbitrary global-unit residue waves above 827

This file isolates the arithmetic half of odd-mode silence.  For an
arbitrary global ring unit it defines the uncorrected residue-log wave on
all 58 explicit roots above 827.  Complex conjugation is proved to act by
the actual `sigma ↦ sigma * (-1)` root permutation.  The CM unit theorem
then shows that the entire odd difference of the raw wave is one explicit
linear cyclotomic-root mode.

The capacity certificate's existing `realNorm` correction symmetrizes that
raw wave.  Consequently its corrected `fullOrbitUnitReading827` is
pointwise fixed by `-1`.  No Fourier coefficient is evaluated here; odd
Fourier-mode vanishing is a separate finite harmonic-analysis consequence.
-/
import Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827
import Fermat.FiftyNine.Conservation.ExplicitResiduePlaceOrbit827
import Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.ArbitraryUnitOrbitDecomposition827

open Fermat.FiftyNine.Conservation.CapacityCertificate
open Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827
open Fermat.FiftyNine.Conservation.Credit
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.PrimalOrbitResidue827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

private abbrev canonicalZeta59 : K :=
  IsCyclotomicExtension.zeta 59 ℚ K

private abbrev canonicalZeta59_isPrimitive :
    IsPrimitiveRoot (canonicalZeta59 (K := K)) 59 :=
  IsCyclotomicExtension.zeta_spec 59 ℚ K

/-- The uncorrected residue-log wave of an actual global ring unit on all
58 explicit residue roots above 827. -/
noncomputable def rawGlobalUnitOrbitWave827
    (u : (NumberField.RingOfIntegers K)ˣ) :
    GaloisIndex59 → ZMod 59 :=
  fun sigma ↦
    CapacityCertificate.residueLog <| Additive.ofMul <|
      Units.map
        (orbitReductionHom827
          (canonicalZeta59_isPrimitive (K := K)) sigma).toMonoidHom u

/-- Reduction after CM conjugation is reduction at the root indexed by
`sigma * (-1)`. -/
theorem orbitReductionHom827_unitsComplexConj
    (u : (NumberField.RingOfIntegers K)ˣ)
    (sigma : GaloisIndex59) :
    Units.map
        (orbitReductionHom827
          (canonicalZeta59_isPrimitive (K := K)) sigma).toMonoidHom
        (NumberField.IsCMField.unitsComplexConj K u) =
      Units.map
        (orbitReductionHom827
          (canonicalZeta59_isPrimitive (K := K))
          (sigma * (-1 : GaloisIndex59))).toMonoidHom u := by
  apply Units.ext
  change orbitReductionHom827
      (canonicalZeta59_isPrimitive (K := K)) sigma
        ((NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv
          (u : NumberField.RingOfIntegers K)) =
    orbitReductionHom827
      (canonicalZeta59_isPrimitive (K := K))
        (sigma * (-1 : GaloisIndex59))
          (u : NumberField.RingOfIntegers K)
  rw [ringOfIntegersComplexConj_eq_cyclotomic_negOne59 (K := K)]
  change ((orbitReductionHom827
      (canonicalZeta59_isPrimitive (K := K)) sigma).comp
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := 59) K (-1 : GaloisIndex59)).toRingHom)
        (u : NumberField.RingOfIntegers K) = _
  rw [Fermat.FiftyNine.Conservation.OrbitPlace827.orbitReductionHom827_comp_cyclotomicRingEquiv]

/-- The uncorrected wave sees CM conjugation as translation by `-1` on
the explicit root orbit. -/
theorem rawGlobalUnitOrbitWave827_unitsComplexConj
    (u : (NumberField.RingOfIntegers K)ˣ)
    (sigma : GaloisIndex59) :
    rawGlobalUnitOrbitWave827
        (NumberField.IsCMField.unitsComplexConj K u) sigma =
      rawGlobalUnitOrbitWave827 u
        (sigma * (-1 : GaloisIndex59)) := by
  unfold rawGlobalUnitOrbitWave827
  rw [orbitReductionHom827_unitsComplexConj]

/-- A power of the canonical global cyclotomic root reduces to the
corresponding power of the explicit root indexed by `sigma`. -/
theorem orbitReductionHom827_canonicalRoot_pow
    (m : ℕ) (sigma : GaloisIndex59) :
    Units.map
        (orbitReductionHom827
          (canonicalZeta59_isPrimitive (K := K)) sigma).toMonoidHom
        ((canonicalZeta59_isPrimitive (K := K)).unit' ^ m) =
      CapacityCertificate.attestationRootUnit ^
        ((sigma : ZMod 59).val * m) := by
  apply Units.ext
  simp only [Units.coe_map, Units.val_pow_eq_pow_val, map_pow]
  change (orbitReductionHom827
      (canonicalZeta59_isPrimitive (K := K)) sigma
        (canonicalZeta59_isPrimitive (K := K)).toInteger) ^ m =
    Credit.attestationRoot ^ ((sigma : ZMod 59).val * m)
  rw [orbitReductionHom827_zeta]
  simp only [orbitRoot827]
  rw [pow_mul]

/-- Before Fourier projection, the residue logarithm of a cyclotomic-root
power is visibly the linear root mode `sigma ↦ c * sigma`. -/
theorem rawGlobalUnitOrbitWave827_canonicalRoot_pow
    (m : ℕ) (sigma : GaloisIndex59) :
    rawGlobalUnitOrbitWave827
        ((canonicalZeta59_isPrimitive (K := K)).unit' ^ m) sigma =
      (((2 * 7 * m : ℕ) : ZMod 59) * (sigma : ZMod 59)) := by
  rw [rawGlobalUnitOrbitWave827,
    orbitReductionHom827_canonicalRoot_pow]
  let rootPower : (ZMod Credit.attestationPrime)ˣ :=
    CapacityCertificate.attestationRootUnit ^
      ((sigma : ZMod 59).val * m)
  have hsymbol :
      ((rootPower : ZMod Credit.attestationPrime) ^ (2 * 7)) =
        Credit.attestationRoot ^
          (((sigma : ZMod 59).val * m) * (2 * 7)) := by
    dsimp [rootPower]
    simp only [CapacityCertificate.attestationRootUnit,
      Units.val_mk0]
    simp only [← pow_mul, Nat.mul_assoc]
  rw [PrimalFourierNonvanishing827.residueLog_eq_of_symbol
    rootPower _ hsymbol]
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
  ring

/-- The raw orbit wave is additive in the multiplicative group of global
units. -/
theorem rawGlobalUnitOrbitWave827_mul
    (u v : (NumberField.RingOfIntegers K)ˣ)
    (sigma : GaloisIndex59) :
    rawGlobalUnitOrbitWave827 (u * v) sigma =
      rawGlobalUnitOrbitWave827 u sigma +
        rawGlobalUnitOrbitWave827 v sigma := by
  unfold rawGlobalUnitOrbitWave827
  rw [map_mul]
  change CapacityCertificate.residueLog
      (Additive.ofMul
        (Units.map
          (orbitReductionHom827
            (canonicalZeta59_isPrimitive (K := K)) sigma).toMonoidHom u) +
       Additive.ofMul
        (Units.map
          (orbitReductionHom827
            (canonicalZeta59_isPrimitive (K := K)) sigma).toMonoidHom v)) = _
  rw [map_add]

/-- The complete arithmetic decomposition of an arbitrary global-unit
wave.  Its failure to be fixed by conjugation is one explicit linear
cyclotomic-root mode; the remaining term is the `-1` translate of the same
unit wave. -/
theorem exists_rawGlobalUnitOrbitWave827_rootMode_decomposition
    (u : (NumberField.RingOfIntegers K)ˣ) :
    ∃ j : ℕ, ∀ sigma : GaloisIndex59,
      rawGlobalUnitOrbitWave827 u sigma =
        (((2 * 7 * (j * 2) : ℕ) : ZMod 59) *
            (sigma : ZMod 59)) +
          rawGlobalUnitOrbitWave827 u
            (sigma * (-1 : GaloisIndex59)) := by
  obtain ⟨j, hj⟩ := unit_inv_conj_is_root_of_unity
    (hζ := canonicalZeta59_isPrimitive (K := K)) u (by norm_num)
  refine ⟨j, fun sigma ↦ ?_⟩
  have hu : u =
      ((canonicalZeta59_isPrimitive (K := K)).unit' ^ j) ^ 2 *
        NumberField.IsCMField.unitsComplexConj K u := by
    calc
      u = (u * (NumberField.IsCMField.unitsComplexConj K u)⁻¹) *
          NumberField.IsCMField.unitsComplexConj K u := by simp
      _ = ((canonicalZeta59_isPrimitive (K := K)).unit' ^ j) ^ 2 *
          NumberField.IsCMField.unitsComplexConj K u := by rw [hj]
  calc
    rawGlobalUnitOrbitWave827 u sigma =
        rawGlobalUnitOrbitWave827
          (((canonicalZeta59_isPrimitive (K := K)).unit' ^ j) ^ 2 *
            NumberField.IsCMField.unitsComplexConj K u) sigma := by
      rw [← hu]
    _ = rawGlobalUnitOrbitWave827
          (((canonicalZeta59_isPrimitive (K := K)).unit' ^ j) ^ 2) sigma +
        rawGlobalUnitOrbitWave827
          (NumberField.IsCMField.unitsComplexConj K u) sigma :=
      rawGlobalUnitOrbitWave827_mul _ _ _
    _ = rawGlobalUnitOrbitWave827
          ((canonicalZeta59_isPrimitive (K := K)).unit' ^ (j * 2)) sigma +
        rawGlobalUnitOrbitWave827
          (NumberField.IsCMField.unitsComplexConj K u) sigma := by
      rw [pow_mul]
    _ = (((2 * 7 * (j * 2) : ℕ) : ZMod 59) *
            (sigma : ZMod 59)) +
          rawGlobalUnitOrbitWave827 u
            (sigma * (-1 : GaloisIndex59)) := by
      rw [rawGlobalUnitOrbitWave827_canonicalRoot_pow,
        rawGlobalUnitOrbitWave827_unitsComplexConj]

/-- Equivalently, the odd difference of an arbitrary raw unit wave is a
single explicit root mode. -/
theorem exists_rawGlobalUnitOrbitWave827_oddDifference_eq_rootMode
    (u : (NumberField.RingOfIntegers K)ˣ) :
    ∃ j : ℕ, ∀ sigma : GaloisIndex59,
      rawGlobalUnitOrbitWave827 u sigma -
          rawGlobalUnitOrbitWave827 u
            (sigma * (-1 : GaloisIndex59)) =
        ((2 * 7 * (j * 2) : ℕ) : ZMod 59) *
          (sigma : ZMod 59) := by
  obtain ⟨j, hj⟩ :=
    exists_rawGlobalUnitOrbitWave827_rootMode_decomposition (K := K) u
  refine ⟨j, fun sigma ↦ ?_⟩
  rw [hj]
  ring

/-- The repository's corrected full-orbit unit reading is exactly the
half-sum of the raw wave and its CM-conjugate translate. -/
theorem fullOrbitUnitReading827_eq_half_raw_add_negOneTranslate
    (u : (NumberField.RingOfIntegers K)ˣ)
    (sigma : GaloisIndex59) :
    fullOrbitUnitReading827
        (canonicalZeta59_isPrimitive (K := K)) u sigma =
      (2 : ZMod 59)⁻¹ *
        (rawGlobalUnitOrbitWave827 u sigma +
          rawGlobalUnitOrbitWave827 u
            (sigma * (-1 : GaloisIndex59))) := by
  change (2 : ZMod 59)⁻¹ *
      rawGlobalUnitOrbitWave827
        (u * NumberField.IsCMField.unitsComplexConj K u) sigma = _
  rw [rawGlobalUnitOrbitWave827_mul,
    rawGlobalUnitOrbitWave827_unitsComplexConj]

/-- Consequently the actual corrected orbit wave of every global unit is
fixed by the `-1` action.  This is the entire arithmetic input needed by a
separate pure-Fourier odd-mode vanishing theorem. -/
theorem fullOrbitUnitReading827_negOne_even
    (u : (NumberField.RingOfIntegers K)ˣ)
    (sigma : GaloisIndex59) :
    fullOrbitUnitReading827
        (canonicalZeta59_isPrimitive (K := K)) u
          (sigma * (-1 : GaloisIndex59)) =
      fullOrbitUnitReading827
        (canonicalZeta59_isPrimitive (K := K)) u sigma := by
  rw [fullOrbitUnitReading827_eq_half_raw_add_negOneTranslate,
    fullOrbitUnitReading827_eq_half_raw_add_negOneTranslate]
  simp only [mul_neg, mul_one, neg_neg]
  ring

end Fermat.FiftyNine.Conservation.ArbitraryUnitOrbitDecomposition827
