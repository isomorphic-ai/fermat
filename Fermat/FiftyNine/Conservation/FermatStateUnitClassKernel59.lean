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
import Fermat.FiftyNine.Conservation.CyclotomicUnitSelmerNaturality59
import Fermat.FiftyNine.Conservation.FermatFactorClassProjection59

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

namespace Fermat.FiftyNine.Conservation.FermatStateUnitClassKernel59

open Fermat.Conservation.IdealPowerSelmer
open Fermat.Conservation.SelmerEigenspace
open CanonicalIrregularMode827
open CyclotomicSelmerAction59
open CyclotomicSelmerClassNaturality59
open CyclotomicUnitSelmerNaturality59
open FermatFactorClassProjection59
open FermatFactorSelmerSource59
open FermatState
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

end Fermat.FiftyNine.Conservation.FermatStateUnitClassKernel59
