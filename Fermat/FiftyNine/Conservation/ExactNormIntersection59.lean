/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Exact norm intersection at the critical unit layer

The critical norm-image theorem gives the difficult inclusion: a norm from
the twisted-lambda Kummer extension which lies in `U_59` already lies in
`U_60`.  The converse is formal once the independently proved Hensel theorem
is used: every element of `U_60` is a 59th power in the base field, and a
base-field 59th power is the norm of the same element embedded in the
degree-59 extension.

Consequently the intersection of the actual unit norm image with `U_59` is
exactly `U_60`.  This is stronger than the quotient-level statement that the
critical norm image is trivial and retains the full subgroup equality for
later statewise use.
-/
import Fermat.FiftyNine.Conservation.CriticalUnitPowerSurjectivity59
import Fermat.FiftyNine.Conservation.NormImageBridge59

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.ExactNormIntersection59

open Fermat.FiftyNine.Conservation.CriticalUnitPowerSurjectivity59
open Fermat.FiftyNine.Conservation.CriticalUnitQuotient59
open Fermat.FiftyNine.Conservation.EisensteinIntegrality59
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.NormImageBridge59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

noncomputable local instance : FiniteDimensional (F59 K) (E59 K) :=
  (twistedLambdaPowerBasis59 K).finite

/-- Every depth-60 principal unit is an actual norm from the twisted-lambda
Kummer extension. -/
theorem mem_twistedLambdaNormUnits59_range_of_mem_U60
    (u : (F59 K)ˣ) (hu : u ∈ U60 K) :
    u ∈ (twistedLambdaNormUnits59 K).range := by
  obtain ⟨x, hx⟩ := exists_fieldUnit_pow59_eq_of_mem_U60 K u hu
  let xE : (E59 K)ˣ := Units.map
    (algebraMap (F59 K) (E59 K)).toMonoidHom x
  refine ⟨xE, ?_⟩
  apply Units.ext
  change Algebra.norm (F59 K) (algebraMap (F59 K) (E59 K) (x : F59 K)) =
    (u : F59 K)
  rw [Algebra.norm_algebraMap]
  have hfinrank : Module.finrank (F59 K) (E59 K) = 59 := by
    calc
      Module.finrank (F59 K) (E59 K) =
          (twistedLambdaPowerBasis59 K).dim :=
        (twistedLambdaPowerBasis59 K).finrank
      _ = 59 := twistedLambdaPowerBasis59_dim K
  rw [hfinrank]
  exact congrArg Units.val hx

/-- The exact critical filtration law: actual unit norms meet `U_59` in
precisely `U_60`. -/
theorem twistedLambdaNormUnits59_range_inf_U59_eq_U60 :
    (twistedLambdaNormUnits59 K).range ⊓ U59 K = U60 K := by
  apply le_antisymm
  · intro u hu
    obtain ⟨beta, hbeta⟩ := hu.1
    rw [← hbeta]
    exact twistedLambdaNormUnits59_mem_U60_of_mem_U59 K beta (by
      rw [hbeta]
      exact hu.2)
  · intro u hu
    exact ⟨mem_twistedLambdaNormUnits59_range_of_mem_U60 K u hu,
      U60_le_U59 K hu⟩

/-- Pointwise form of the exact intersection law for a unit already known
to lie at critical depth.  This is the convenient statewise interface: at
depth 59, being a norm is exactly the same as having one further digit of
lambda-adic depth. -/
theorem mem_twistedLambdaNormUnits59_range_iff_mem_U60_of_mem_U59
    (u : (F59 K)ˣ) (hu59 : u ∈ U59 K) :
    u ∈ (twistedLambdaNormUnits59 K).range ↔ u ∈ U60 K := by
  constructor
  · intro hnorm
    obtain ⟨beta, hbeta⟩ := hnorm
    rw [← hbeta]
    exact twistedLambdaNormUnits59_mem_U60_of_mem_U59 K beta (by
      rw [hbeta]
      exact hu59)
  · exact mem_twistedLambdaNormUnits59_range_of_mem_U60 K u

/-- Contrapositive statewise form: a critical-depth unit whose next-depth
coefficient is nonzero cannot be an extension norm. -/
theorem not_mem_twistedLambdaNormUnits59_range_iff_not_mem_U60_of_mem_U59
    (u : (F59 K)ˣ) (hu59 : u ∈ U59 K) :
    u ∉ (twistedLambdaNormUnits59 K).range ↔ u ∉ U60 K :=
  not_congr
    (mem_twistedLambdaNormUnits59_range_iff_mem_U60_of_mem_U59 K u hu59)

end Fermat.FiftyNine.Conservation.ExactNormIntersection59
