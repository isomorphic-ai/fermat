/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Cyclotomic naturality of the strict 59-Selmer class map

This file is the thin `p = 59` compatibility adapter for the prime-generic
class-group action and strict Selmer class naturality.  Every class action,
torsion representation, intertwiner, and character projector below is a
transparent specialization of
`Fermat.Conservation.PrimeCyclotomicSelmerClassNaturality`.

Only the final plus/minus statements remain specific to the hypothetical
Fermat state: they identify the generic projected class map on the two
solution-dependent Selmer sources constructed in `FermatFactorSelmerSource59`.
-/
import Fermat.Experiments.Conservation.PrimeCyclotomicSelmerClassNaturality
import Fermat.Exponents.FiftyNine.Conservation.FermatFactorSelmerSource59

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.InvolutiveBase
open Fermat.Conservation.PrimeCyclotomicSelmerClassNaturality
open Fermat.Conservation.SelmerEigenspace
open CanonicalIrregularMode827
open CyclotomicSelmerAction59
open DetectorWitness827
open FermatFactorSelmerSource59
open SplitPrimeFourier827
open StateFactorPair
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-! ## Transparent specialization of the class-group action -/

/-- Transport of fractional ideals by the canonical cyclotomic automorphism
at `p = 59`. -/
noncomputable abbrev cyclotomicFractionalIdealEquiv59
    (sigma : GaloisIndex59) :
    FractionalIdeal (NumberField.RingOfIntegers K)⁰ K ≃+*
      FractionalIdeal (NumberField.RingOfIntegers K)⁰ K :=
  cyclotomicFractionalIdealEquiv 59 K sigma

/-- The induced action on nonzero fractional ideals at `p = 59`. -/
noncomputable abbrev cyclotomicFractionalIdealUnitMulEquiv59
    (sigma : GaloisIndex59) :
    (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ ≃*
      (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ :=
  cyclotomicFractionalIdealUnitMulEquiv 59 K sigma

/-- The induced class-group equivalence at `p = 59`. -/
noncomputable abbrev cyclotomicClassGroupMulEquiv59
    (sigma : GaloisIndex59) :
    ClassGroup (NumberField.RingOfIntegers K) ≃*
      ClassGroup (NumberField.RingOfIntegers K) :=
  cyclotomicClassGroupMulEquiv 59 K sigma

/-- Computation of the specialized class action on a represented fractional
ideal. -/
theorem cyclotomicClassGroupMulEquiv59_mk
    (sigma : GaloisIndex59)
    (I : (FractionalIdeal
      (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    cyclotomicClassGroupMulEquiv59 K sigma (ClassGroup.mk K I) =
      ClassGroup.mk K
        (cyclotomicFractionalIdealUnitMulEquiv59 K sigma I) :=
  cyclotomicClassGroupMulEquiv_mk 59 K sigma I

/-- The specialized class action at the identity is the identity. -/
@[simp]
theorem cyclotomicClassGroupMulEquiv59_one_apply
    (c : ClassGroup (NumberField.RingOfIntegers K)) :
    cyclotomicClassGroupMulEquiv59 K 1 c = c :=
  cyclotomicClassGroupMulEquiv_one_apply 59 K c

/-- Multiplication of cyclotomic indices is composition of the specialized
class actions. -/
theorem cyclotomicClassGroupMulEquiv59_mul_apply
    (sigma tau : GaloisIndex59)
    (c : ClassGroup (NumberField.RingOfIntegers K)) :
    cyclotomicClassGroupMulEquiv59 K (sigma * tau) c =
      cyclotomicClassGroupMulEquiv59 K sigma
        (cyclotomicClassGroupMulEquiv59 K tau c) :=
  cyclotomicClassGroupMulEquiv_mul_apply 59 K sigma tau c

/-- The genuine cyclotomic representation on the additive class group at
`p = 59`. -/
noncomputable abbrev cyclotomicAdditiveClassGroupRepresentation59 :
    Representation ℤ GaloisIndex59
      (Additive (ClassGroup (NumberField.RingOfIntegers K))) :=
  cyclotomicAdditiveClassGroupRepresentation 59 K

/-! ## Transparent specialization of strict-class naturality -/

/-- The fraction-field automorphism induced from the ring of integers is the
canonical cyclotomic field automorphism at `p = 59`. -/
theorem cyclotomicFractionEquiv59_eq (sigma : GaloisIndex59) :
    IsFractionRing.ringEquivOfRingEquiv
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := 59) K sigma) =
      (KummerCriterion.cyclotomicSigmaOfUnit
        (p := 59) K sigma).toRingEquiv :=
  cyclotomicFractionEquiv_eq 59 K sigma

/-- Specialized transport of principal fractional ideals. -/
theorem cyclotomicFractionalIdealEquiv59_toPrincipalIdeal
    (sigma : GaloisIndex59) (x : Kˣ) :
    cyclotomicFractionalIdealUnitMulEquiv59 K sigma
        (toPrincipalIdeal (NumberField.RingOfIntegers K) K x) =
      toPrincipalIdeal (NumberField.RingOfIntegers K) K
        (cyclotomicUnitEquiv59 K sigma x) :=
  cyclotomicFractionalIdealEquiv_toPrincipalIdeal 59 K sigma x

/-- The strict 59-Selmer ideal-class map intertwines the canonical
cyclotomic actions. -/
theorem strictSelmerIdealClass59_cyclotomic
    (sigma : GaloisIndex59)
    (q : SelmerCarrier (NumberField.RingOfIntegers K) K 59) :
    strictSelmerIdealClass59 (K := K)
        (cyclotomicStrictSelmerRepresentation59 K sigma q) =
      cyclotomicAdditiveClassGroupRepresentation59 K sigma
        (strictSelmerIdealClass59 (K := K) q) :=
  strictSelmerIdealClass_cyclotomic 59 K sigma q

/-! ## Transparent specialization of the torsion representation -/

/-- The actual 59-torsion subgroup of the class group. -/
abbrev ClassTorsion59 :=
  ClassTorsion 59 K

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

local instance instClassTorsion59ModulePadicInt :
    Module (PadicInt 59) (ClassTorsion59 K) :=
  Module.compHom (ClassTorsion59 K) PadicInt.toZMod

/-- Restriction of one class-group automorphism to 59-torsion. -/
noncomputable abbrev cyclotomicClassTorsionAddHom59
    (sigma : GaloisIndex59) :
    ClassTorsion59 K →+ ClassTorsion59 K :=
  cyclotomicClassTorsionAddHom 59 K sigma

/-- The restricted action as an integral 59-adic linear map. -/
noncomputable abbrev cyclotomicClassTorsionLinearMap59
    (sigma : GaloisIndex59) :
    ClassTorsion59 K →ₗ[PadicInt 59] ClassTorsion59 K :=
  cyclotomicClassTorsionLinearMap 59 K sigma

/-- The canonical cyclotomic representation on class-group 59-torsion. -/
noncomputable abbrev cyclotomicClassTorsionRepresentation59 :
    Representation (PadicInt 59) GaloisIndex59 (ClassTorsion59 K) :=
  cyclotomicClassTorsionRepresentation 59 K

/-- The strict Selmer class map with its genuine 59-torsion codomain. -/
noncomputable abbrev strictSelmerClassLinearMap59 :
    SelmerCarrier (NumberField.RingOfIntegers K) K 59 →ₗ[PadicInt 59]
      ClassTorsion59 K :=
  strictSelmerClassLinearMap 59 K

omit [IsCyclotomicExtension {59} ℚ K] in
/-- Forgetting the torsion proof recovers the full ideal-class map. -/
@[simp]
theorem strictSelmerClassLinearMap59_value
    (q : SelmerCarrier (NumberField.RingOfIntegers K) K 59) :
    (strictSelmerClassLinearMap59 K q :
      Additive (ClassGroup (NumberField.RingOfIntegers K))) =
      strictSelmerIdealClass59 (K := K) q :=
  strictSelmerClassLinearMap_value 59 K q

/-- The restricted 59-class map as an intertwiner of the specialized
cyclotomic representations. -/
noncomputable abbrev strictSelmerClassIntertwiner59 :
    Representation.IntertwiningMap
      (cyclotomicStrictSelmerRepresentation59 K)
      (cyclotomicClassTorsionRepresentation59 K) :=
  strictSelmerClassIntertwiner 59 K

/-- The character-idempotent action on class-group 59-torsion. -/
noncomputable abbrev cyclotomicClassProjector59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (eta : Character (PadicInt 59) GaloisIndex59) :
    ClassTorsion59 K →ₗ[PadicInt 59] ClassTorsion59 K :=
  cyclotomicClassProjector 59 K eta

/-- Strong projector naturality for the specialized strict Selmer class
map. -/
theorem strictSelmerClassLinearMap59_characterProjector
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (eta : Character (PadicInt 59) GaloisIndex59)
    (q : SelmerCarrier (NumberField.RingOfIntegers K) K 59) :
    strictSelmerClassLinearMap59 K
        ((characterProjectorAt
          (cyclotomicStrictSelmerRepresentation59 K) eta q).1) =
      cyclotomicClassProjector59 K eta
        (strictSelmerClassLinearMap59 K q) :=
  strictSelmerClassLinearMap_characterProjector 59 K eta q

/-! ## The genuinely 59-specific Fermat-state endpoints -/

variable {K}
  {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

/-- The projected plus Fermat factor has exactly the chi=15 projection of
the allocated plus root class as its class-group obstruction. -/
theorem fermatPlusPrimalMode59_classProjection
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    strictSelmerClassLinearMap59 K (fermatPlusPrimalMode59 pair).1 =
      cyclotomicClassProjector59 K irregularCharacter59
        (allocatedRootClassPTorsion pair.ledger 0) := by
  rw [fermatPlusPrimalMode59,
    strictSelmerClassLinearMap59_characterProjector]
  apply congrArg (cyclotomicClassProjector59 K irregularCharacter59)
  apply Subtype.ext
  exact fermatPlusStrictSelmer59_idealClass pair

/-- The analogous exact identification for the projected minus Fermat
factor. -/
theorem fermatMinusPrimalMode59_classProjection
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    strictSelmerClassLinearMap59 K (fermatMinusPrimalMode59 pair).1 =
      cyclotomicClassProjector59 K irregularCharacter59
        (allocatedRootClassPTorsion pair.ledger 1) := by
  rw [fermatMinusPrimalMode59,
    strictSelmerClassLinearMap59_characterProjector]
  apply congrArg (cyclotomicClassProjector59 K irregularCharacter59)
  apply Subtype.ext
  exact fermatMinusStrictSelmer59_idealClass pair

end Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59
