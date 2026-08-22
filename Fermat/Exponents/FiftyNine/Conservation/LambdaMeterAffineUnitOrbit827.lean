/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The affine lambda obstruction is one unit-orbit equation

The meter-parametric affine cokernel criterion retains exactly one honest
normalization freedom: multiplication of the prescribed wild meter by a
nonzero scalar.  This file exposes that statement literally in the W1
lambda cokernel.

A normalized meter lift exists precisely when the normalized `827` coset
lies in the unit orbit of the meter's cokernel class.  This is only a
re-expression of the already proved affine lift criterion.  It chooses no
scale or lift and asserts no Poitou--Tate exactness or arithmetic
nonvanishing theorem.
-/
import Fermat.Experiments.Conservation.GuardDependsOn
import Fermat.Experiments.Conservation.OneDimensionalUnitProportionality
import Fermat.Exponents.FiftyNine.Conservation.LambdaMeterAffineCokernel827

open scoped NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Fermat.FiftyNine.Conservation.LambdaMeterAffineUnitOrbit827

open Fermat.Conservation
open CanonicalIrregularMode827
open ContinuousKummerTateLocalization59
open CyclotomicSelmerAction59
open DetectorWitness827
open ExplicitTameOrbitReciprocity827
open LambdaMeterAffineCokernel827
open LambdaMeterPointedPoitouTate827
open LambdaOrbitAffineCokernel827
open LambdaOrbitLocalizationFiber827
open PointedTateIncidence
open SplitPrimeFourier827
open UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-! ## The meter's linear cokernel class -/

/-- The image of a proposed lambda meter in the exact cokernel which
measures changes invisible on the complete `827` orbit. -/
noncomputable def lambdaMeterCokernelClass827
    (meter : LambdaRootsContinuousH1 K) :
    W1LambdaCokernel827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 :=
  w1LambdaCokernelProjection827 (K := K)
    canonicalTeichmullerCharacter59 irregularCharacter59 meter

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The fixed-scale affine obstruction is exactly the difference between
the scaled meter class and the normalized full-orbit class. -/
theorem scaledLambdaMeterObstructionClass827_eq_smul_sub_normalized
    (meter : LambdaRootsContinuousH1 K) (scale : ZMod 59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    scaledLambdaMeterObstructionClass827 (K := K) meter scale y₀ =
      scale • lambdaMeterCokernelClass827 (K := K) meter -
        normalizedW3LambdaCoset827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y₀ := by
  rw [scaledLambdaMeterObstructionClass827_eq_meter_sub_normalized]
  exact congrArg
    (fun z => z - normalizedW3LambdaCoset827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 y₀)
    ((w1LambdaCokernelProjection827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59).map_smul
        scale meter)

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Vanishing of the affine obstruction is the literal equality of the
two retained cokernel classes at the prescribed scale. -/
theorem scaledLambdaMeterObstructionClass827_eq_zero_iff_smul_eq_normalized
    (meter : LambdaRootsContinuousH1 K) (scale : ZMod 59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    scaledLambdaMeterObstructionClass827 (K := K) meter scale y₀ = 0 ↔
      scale • lambdaMeterCokernelClass827 (K := K) meter =
        normalizedW3LambdaCoset827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y₀ := by
  rw [scaledLambdaMeterObstructionClass827_eq_smul_sub_normalized]
  exact sub_eq_zero

/-! ## Exact lift criteria in unit-orbit form -/

/-- At one prescribed unit scale, a normalized global meter lift exists
exactly when that scale carries the meter class to the normalized `827`
class in the W1 cokernel. -/
theorem exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff_smul
    (meter : LambdaRootsContinuousH1 K) (scale : (ZMod 59)ˣ)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    (∃ lift : NormalizedOrbitScaledLambdaMeterLift827 (K := K) meter,
        lift.wildScale = scale) ↔
      (scale : ZMod 59) • lambdaMeterCokernelClass827 (K := K) meter =
        normalizedW3LambdaCoset827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y₀ := by
  rw [exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff,
    scaledLambdaMeterObstructionClass827_eq_zero_iff_smul_eq_normalized]

/-- Allowing the unique honest normalization freedom, the actual lift
fiber is nonempty exactly when the normalized `827` class belongs to the
unit orbit of the meter class. -/
theorem nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_unitOrbit
    (meter : LambdaRootsContinuousH1 K)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    Nonempty (NormalizedOrbitScaledLambdaMeterLift827 (K := K) meter) ↔
      ∃ scale : (ZMod 59)ˣ,
        (scale : ZMod 59) • lambdaMeterCokernelClass827 (K := K) meter =
          normalizedW3LambdaCoset827 (K := K)
            canonicalTeichmullerCharacter59 irregularCharacter59 y₀ := by
  rw [nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_exists_scale]
  apply exists_congr
  intro scale
  exact
      scaledLambdaMeterObstructionClass827_eq_zero_iff_smul_eq_normalized
        meter (scale : ZMod 59) y₀

/-! ## One-dimensional cokernel discharge -/

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- In a one-dimensional W1 lambda cokernel, nonzero meter and normalized
`827` classes determine a unique unit normalization carrying the former to
the latter. -/
theorem existsUnique_unit_smul_lambdaMeterCokernelClass827_eq_normalized
    (meter : LambdaRootsContinuousH1 K)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)))
    (hfinrank : Module.finrank (ZMod 59)
      (W1LambdaCokernel827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59) = 1)
    (hmeter : lambdaMeterCokernelClass827 (K := K) meter ≠ 0)
    (hnormalized : normalizedW3LambdaCoset827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 y₀ ≠ 0) :
    ∃! scale : (ZMod 59)ˣ,
      (scale : ZMod 59) • lambdaMeterCokernelClass827 (K := K) meter =
        normalizedW3LambdaCoset827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y₀ := by
  obtain ⟨scale, hscale, hscale_unique⟩ :=
    existsUnique_unit_smul_of_mem_finrank_one
      (⊤ : Submodule (ZMod 59)
        (W1LambdaCokernel827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59))
      (normalizedW3LambdaCoset827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y₀)
      (lambdaMeterCokernelClass827 (K := K) meter)
      (by simp) (by simp) (by simpa using hfinrank)
      hnormalized hmeter
  refine ⟨scale, hscale.symm, ?_⟩
  intro other hother
  exact hscale_unique other hother.symm

/-- The note's one-dimensional-line criterion therefore discharges the
entire affine globalization obstruction and produces a nonempty lift fiber.
The point and the unique scale remain under existential packaging. -/
theorem nonempty_normalizedOrbitScaledLambdaMeterLift827_of_finrank_one
    (meter : LambdaRootsContinuousH1 K)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)))
    (hfinrank : Module.finrank (ZMod 59)
      (W1LambdaCokernel827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59) = 1)
    (hmeter : lambdaMeterCokernelClass827 (K := K) meter ≠ 0)
    (hnormalized : normalizedW3LambdaCoset827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 y₀ ≠ 0) :
    Nonempty (NormalizedOrbitScaledLambdaMeterLift827 (K := K) meter) := by
  apply
    (nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_unitOrbit
      meter y₀).2
  obtain ⟨scale, hscale, _⟩ :=
    existsUnique_unit_smul_lambdaMeterCokernelClass827_eq_normalized
      meter y₀ hfinrank hmeter hnormalized
  exact ⟨scale, hscale⟩

/-! ## Kernel-trust and route-separation audit -/

/--
info: 'Fermat.FiftyNine.Conservation.LambdaMeterAffineUnitOrbit827.nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_unitOrbit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_unitOrbit

/--
info: 'Fermat.FiftyNine.Conservation.LambdaMeterAffineUnitOrbit827.nonempty_normalizedOrbitScaledLambdaMeterLift827_of_finrank_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  nonempty_normalizedOrbitScaledLambdaMeterLift827_of_finrank_one

#guard_depends_on
  scaledLambdaMeterObstructionClass827_eq_smul_sub_normalized,
  LambdaMeterAffineCokernel827.scaledLambdaMeterObstructionClass827_eq_meter_sub_normalized

#guard_depends_on
  exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff_smul,
  LambdaMeterAffineCokernel827.exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff

#guard_depends_on
  nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_unitOrbit,
  LambdaMeterAffineCokernel827.nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_exists_scale

#guard_depends_on
  existsUnique_unit_smul_lambdaMeterCokernelClass827_eq_normalized,
  Fermat.Conservation.existsUnique_unit_smul_of_mem_finrank_one

#guard_depends_on
  nonempty_normalizedOrbitScaledLambdaMeterLift827_of_finrank_one,
  existsUnique_unit_smul_lambdaMeterCokernelClass827_eq_normalized

#guard_depends_on
  nonempty_normalizedOrbitScaledLambdaMeterLift827_of_finrank_one,
  nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_unitOrbit

/- The unit-orbit criterion consumes neither the former full reverse-PT
inclusion nor its conditional lift constructor. -/
#guard_not_depends_on
  nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_unitOrbit,
  LambdaMeterPointedPoitouTate827.lambdaMeterPointedLocalization827_range_eq_ker_iff_kernel_lifts

#guard_not_depends_on
  nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_unitOrbit,
  LambdaMeterPointedPoitouTate827.nonempty_scaledLambdaMeterLift827_of_pt_and_unitComparison

end Fermat.FiftyNine.Conservation.LambdaMeterAffineUnitOrbit827
