/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Equation-(8) coefficient units in the actual class kernel

The literal equation-(8) factorization supplies concrete global units whose
classes map to the plus and minus Fermat Selmer sources.  Cyclotomic
naturality lets us project those units before including them in the strict
Selmer group.  The class-map naturality theorem then identifies the resulting
obstruction, while the statewise Takagi theorem proves it is zero.

Thus the two projected coefficient units are not merely existential unit
lifts: their images are the actual irregular Fermat modes and lie in the
kernel of the genuine 59-torsion ideal-class map.
-/
import Fermat.Exponents.FiftyNine.Conservation.CyclotomicUnitSelmerNaturality59
import Fermat.Exponents.FiftyNine.Conservation.FermatFactorClassProjection59

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.FermatStateUnitClassKernel59

open Fermat.Conservation.IdealPowerSelmer
open Fermat.Conservation.SelmerEigenspace
open CanonicalIrregularMode827
open CyclotomicSelmerAction59
open CyclotomicSelmerClassNaturality59
open CyclotomicUnitSelmerNaturality59
open FermatFactorClassProjection59
open FermatFactorSelmerGauge59
open FermatFactorSelmerSource59
open FermatState
open NormalizationCorrectionProjection59
open SplitPrimeFourier827
open StateFactorPair
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}

/-- The concrete plus equation-(8) coefficient unit, projected in the
chi-15 seat on the unit side, includes to a strict Selmer class with zero
actual ideal-class obstruction. -/
theorem exists_explicitProjectedUnitLift_classSilent_fermatPlus59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (rho : NumberField.RingOfIntegers K)
        (epsilon : (NumberField.RingOfIntegers K)ˣ),
      pair.plusIdeal = Ideal.span {rho} ∧
      normalizedPlusFactor hZeta S hz = epsilon * rho ^ 59 ∧
      strictSelmerClassLinearMap59 K
          (unitInclusionLinearMap59 K
            (cyclotomicUnitProjector59 K irregularCharacter59
              (Additive.ofMul (QuotientGroup.mk epsilon)))) = 0 := by
  obtain ⟨rho, epsilon, hideal, hequation, hmode⟩ :=
    exists_explicitUnitProjector_fermatPlusPrimalMode59 pair
  refine ⟨rho, epsilon, hideal, hequation, ?_⟩
  rw [hmode]
  exact fermatPlusPrimalMode59_classProjection_eq_zero_takagi pair

/-- The analogous minus equation-(8) coefficient unit has zero obstruction
after projection in the same genuine character seat. -/
theorem exists_explicitProjectedUnitLift_classSilent_fermatMinus59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (rho : NumberField.RingOfIntegers K)
        (epsilon : (NumberField.RingOfIntegers K)ˣ),
      pair.minusIdeal = Ideal.span {rho} ∧
      normalizedMinusFactor hZeta S hz = epsilon * rho ^ 59 ∧
      strictSelmerClassLinearMap59 K
          (unitInclusionLinearMap59 K
            (cyclotomicUnitProjector59 K irregularCharacter59
              (Additive.ofMul (QuotientGroup.mk epsilon)))) = 0 := by
  obtain ⟨rho, epsilon, hideal, hequation, hmode⟩ :=
    exists_explicitUnitProjector_fermatMinusPrimalMode59 pair
  refine ⟨rho, epsilon, hideal, hequation, ?_⟩
  rw [hmode]
  exact fermatMinusPrimalMode59_classProjection_eq_zero_takagi pair

/-! ## One explicit unit representative of the projected difference -/

/-- The two equation-(8) coefficient units combine to one explicit global
unit representative of the actual projected plus-minus Selmer difference.
That representative is twice the plus mode and has zero obstruction under
the genuine `59`-torsion ideal-class map. -/
theorem exists_explicitProjectedUnitDifference_classSilent59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (rhoPlus : NumberField.RingOfIntegers K)
        (epsilonPlus : (NumberField.RingOfIntegers K)ˣ)
        (rhoMinus : NumberField.RingOfIntegers K)
        (epsilonMinus : (NumberField.RingOfIntegers K)ˣ),
      pair.plusIdeal = Ideal.span {rhoPlus} ∧
      normalizedPlusFactor hZeta S hz = epsilonPlus * rhoPlus ^ 59 ∧
      pair.minusIdeal = Ideal.span {rhoMinus} ∧
      normalizedMinusFactor hZeta S hz = epsilonMinus * rhoMinus ^ 59 ∧
      let uPlus := cyclotomicUnitProjector59 K irregularCharacter59
        (Additive.ofMul (QuotientGroup.mk epsilonPlus))
      let uMinus := cyclotomicUnitProjector59 K irregularCharacter59
        (Additive.ofMul (QuotientGroup.mk epsilonMinus))
      unitInclusionLinearMap59 K (uPlus - uMinus) =
          ((characterProjectorAt
            (cyclotomicStrictSelmerRepresentation59 K)
            irregularCharacter59
            (fermatFactorSelmerDifference59 pair)).1) ∧
      unitInclusionLinearMap59 K (uPlus - uMinus) =
          (2 : PadicInt 59) • (fermatPlusPrimalMode59 pair).1 ∧
      strictSelmerClassLinearMap59 K
          (unitInclusionLinearMap59 K (uPlus - uMinus)) = 0 := by
  obtain ⟨rhoPlus, epsilonPlus, hplusIdeal, hplus, hplusMode⟩ :=
    exists_explicitUnitProjector_fermatPlusPrimalMode59 pair
  obtain ⟨rhoMinus, epsilonMinus, hminusIdeal, hminus, hminusMode⟩ :=
    exists_explicitUnitProjector_fermatMinusPrimalMode59 pair
  let uPlus := cyclotomicUnitProjector59 K irregularCharacter59
    (Additive.ofMul (QuotientGroup.mk epsilonPlus))
  let uMinus := cyclotomicUnitProjector59 K irregularCharacter59
    (Additive.ofMul (QuotientGroup.mk epsilonMinus))
  have hactual :
      unitInclusionLinearMap59 K (uPlus - uMinus) =
        ((characterProjectorAt
          (cyclotomicStrictSelmerRepresentation59 K)
          irregularCharacter59
          (fermatFactorSelmerDifference59 pair)).1) := by
    dsimp only [uPlus, uMinus]
    rw [map_sub, hplusMode, hminusMode]
    rw [fermatFactorSelmerDifference59, map_sub]
    rfl
  have htwo :
      unitInclusionLinearMap59 K (uPlus - uMinus) =
        (2 : PadicInt 59) • (fermatPlusPrimalMode59 pair).1 := by
    dsimp only [uPlus, uMinus]
    rw [map_sub, hplusMode, hminusMode]
    have hneg := congrArg Subtype.val
      (fermatMinusPrimalMode59_eq_neg_plus pair)
    rw [hneg]
    change (fermatPlusPrimalMode59 pair).1 -
      (-(fermatPlusPrimalMode59 pair).1) = _
    rw [sub_neg_eq_add]
    exact (two_smul (PadicInt 59) (fermatPlusPrimalMode59 pair).1).symm
  have hsilent :
      strictSelmerClassLinearMap59 K
        (unitInclusionLinearMap59 K (uPlus - uMinus)) = 0 := by
    rw [hactual]
    exact fermatFactorSelmerDifference59_projected_class_eq_zero_takagi pair
  refine ⟨rhoPlus, epsilonPlus, rhoMinus, epsilonMinus,
    hplusIdeal, hplus, hminusIdeal, hminus, hactual, htwo, hsilent⟩

end Fermat.FiftyNine.Conservation.FermatStateUnitClassKernel59
