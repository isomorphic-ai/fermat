/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Unique global class descent of the 827 Kummer--Frobenius reading

The signed mode-44 Fourier reading of the 58 genuine residue-Frobenius
exponents kills every global-unit Selmer class.  Hence it is not merely a
representative-level local expression: it descends uniquely through the
actual 59-torsion ideal class group.

This module states that result directly in Frobenius language and proves
preimage independence.  It is the class-level Kummer--Frobenius part of W5.
It does not construct a ray-class Artin map, identify a Hilbert class field,
or assert that the descended character is nonzero or faithful.
-/
import Fermat.Exponents.FiftyNine.Conservation.KummerFrobeniusRead827

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.GlobalClassKummerFrobeniusReadout827

open Fermat.Conservation.CommonActionStage
open CanonicalFullOrbitLocalPairing827
open CanonicalModeFortyFourClassFactorization827
open CyclotomicSelmerClassNaturality59
open DetectorWitness827
open FermatFactorClassGaugeSeating59
open KummerFrobeniusRead827
open PrimalFourierNonvanishing827
open SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

/-- The genuine residue-Frobenius Fourier reading descends through the
global strict-Selmer class gauge in one and only one way. -/
theorem existsUnique_classKummerFrobeniusReadout827 :
    ∃! readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59,
      ∀ x : StrictCarrier59 K,
        readout (fermatFactorClassGaugeMap59 (K := K) x) =
          -fourierCoefficient
            (strictOrbitFrobeniusExponentWave827 K x)
            (powerCharacter59 44) := by
  refine ⟨canonicalModeFortyFourClassReadout827 K, ?_, ?_⟩
  · intro x
    exact canonicalModeFortyFourClassReadout827_eq_frobeniusFourier K x
  · intro other hother
    apply LinearMap.ext
    intro c
    obtain ⟨x, rfl⟩ :=
      fermatFactorClassGaugeMap59_surjective (K := K) c
    exact (hother x).trans
      (canonicalModeFortyFourClassReadout827_eq_frobeniusFourier K x).symm

/-- The canonical class readout is characterized exactly by the genuine
Frobenius-wave formula on all strict Selmer inputs. -/
theorem classReadout_eq_canonical_iff_frobeniusFourier
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59) :
    readout = canonicalModeFortyFourClassReadout827 K ↔
      ∀ x : StrictCarrier59 K,
        readout (fermatFactorClassGaugeMap59 (K := K) x) =
          -fourierCoefficient
            (strictOrbitFrobeniusExponentWave827 K x)
            (powerCharacter59 44) := by
  constructor
  · rintro rfl x
    exact canonicalModeFortyFourClassReadout827_eq_frobeniusFourier K x
  · intro h
    exact (existsUnique_classKummerFrobeniusReadout827 K).unique h
      (canonicalModeFortyFourClassReadout827_eq_frobeniusFourier K)

/-- The Frobenius Fourier reading depends only on the ideal class of a
strict Selmer input.  This is the literal representative-independence law
behind the global class descent. -/
theorem frobeniusFourier_eq_of_classGauge_eq
    (x x' : StrictCarrier59 K)
    (hclass : fermatFactorClassGaugeMap59 (K := K) x =
      fermatFactorClassGaugeMap59 (K := K) x') :
    fourierCoefficient
        (strictOrbitFrobeniusExponentWave827 K x)
        (powerCharacter59 44) =
      fourierCoefficient
        (strictOrbitFrobeniusExponentWave827 K x')
        (powerCharacter59 44) := by
  have hread := congrArg (canonicalModeFortyFourClassReadout827 K) hclass
  rw [canonicalModeFortyFourClassReadout827_eq_frobeniusFourier,
    canonicalModeFortyFourClassReadout827_eq_frobeniusFourier] at hread
  exact neg_injective hread

/-- Vanishing of the global ideal class is exactly the statement that its
Frobenius Fourier reading agrees with the reading of a genuine global unit
preimage, namely zero. -/
theorem frobeniusFourier_eq_zero_of_classGauge_eq_zero
    (x : StrictCarrier59 K)
    (hclass : fermatFactorClassGaugeMap59 (K := K) x = 0) :
    fourierCoefficient
        (strictOrbitFrobeniusExponentWave827 K x)
        (powerCharacter59 44) = 0 := by
  have hread := congrArg (canonicalModeFortyFourClassReadout827 K) hclass
  rw [canonicalModeFortyFourClassReadout827_eq_frobeniusFourier,
    map_zero] at hread
  exact neg_eq_zero.mp hread

/-! ## Axiom audit -/

/--
info: 'Fermat.FiftyNine.Conservation.GlobalClassKummerFrobeniusReadout827.existsUnique_classKummerFrobeniusReadout827' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms existsUnique_classKummerFrobeniusReadout827

/--
info: 'Fermat.FiftyNine.Conservation.GlobalClassKummerFrobeniusReadout827.frobeniusFourier_eq_of_classGauge_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms frobeniusFourier_eq_of_classGauge_eq

end Fermat.FiftyNine.Conservation.GlobalClassKummerFrobeniusReadout827
