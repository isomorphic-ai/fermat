/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Five exact triangular residual rounds at 59

This module iterates the genuine residual factorization through the depths
`0 -> 2 -> 6 -> 14 -> 30 -> 62`. It retains the five extracted
extension-field factors and packages the product of their actual field norms
as one concrete unit in `U60`.
-/
import Fermat.Exponents.FiftyNine.Conservation.TriangularResidualStep59
import Fermat.Exponents.FiftyNine.Conservation.TriangularTerminalResidual59
import Mathlib.Tactic

open scoped NumberField WithZero BigOperators

noncomputable section

set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.FiveStepResidual59

open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
open Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59
open Fermat.FiftyNine.Conservation.EisensteinIntegrality59
open Fermat.FiftyNine.Conservation.CriticalUnitQuotient59
open Fermat.FiftyNine.Conservation.TriangularSpectralDepth59
open Fermat.FiftyNine.Conservation.TriangularResidualNormalization59
open Fermat.FiftyNine.Conservation.TriangularResidualStep59
open Fermat.FiftyNine.Conservation.TriangularTerminalResidual59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

local instance : NontriviallyNormedField (F59 K) :=
  lambdaField59NontriviallyNormedField K

noncomputable local instance : FiniteDimensional (F59 K) (E59 K) :=
  (twistedLambdaPowerBasis59 K).finite

/-- The extension-field product of the five bases extracted along the
depth chain `0 -> 2 -> 6 -> 14 -> 30 -> 62`. -/
def fiveStepBase59
    (y0 y1 y2 y3 y4 : E59 K) : E59 K :=
  triangularBase59 K y0 * triangularBase59 K y1 *
    triangularBase59 K y2 * triangularBase59 K y3 *
      triangularBase59 K y4

/-- Five actual triangular residual rounds, retaining the exact
extension-field decomposition and the product of the five concrete field
norm units in `U60`. -/
theorem exists_fiveStep_residual_chain_with_normUnit
    (y0 : E59 K) (hy0 : HasCoordinateDepth59 K y0 0) :
    ∃ (y1 y2 y3 y4 y5 : E59 K) (u : (F59 K)ˣ),
      HasCoordinateDepth59 K y1 2 ∧
      HasCoordinateDepth59 K y2 6 ∧
      HasCoordinateDepth59 K y3 14 ∧
      HasCoordinateDepth59 K y4 30 ∧
      HasCoordinateDepth59 K y5 62 ∧
      residualElement59 K y0 =
        fiveStepBase59 K y0 y1 y2 y3 y4 * residualElement59 K y5 ∧
      (u : F59 K) =
        Algebra.norm (F59 K) (fiveStepBase59 K y0 y1 y2 y3 y4) ∧
      u ∈ U60 K := by
  obtain ⟨y1, u0, h01, hy1, hu0, hu0mem⟩ :=
    exists_residual_step_with_normUnit K y0 0 hy0
  have hy1' : HasCoordinateDepth59 K y1 2 := by
    simpa [nextDepth59] using hy1
  obtain ⟨y2, u1, h12, hy2, hu1, hu1mem⟩ :=
    exists_residual_step_with_normUnit K y1 2 hy1'
  have hy2' : HasCoordinateDepth59 K y2 6 := by
    simpa [nextDepth59] using hy2
  obtain ⟨y3, u2, h23, hy3, hu2, hu2mem⟩ :=
    exists_residual_step_with_normUnit K y2 6 hy2'
  have hy3' : HasCoordinateDepth59 K y3 14 := by
    simpa [nextDepth59] using hy3
  obtain ⟨y4, u3, h34, hy4, hu3, hu3mem⟩ :=
    exists_residual_step_with_normUnit K y3 14 hy3'
  have hy4' : HasCoordinateDepth59 K y4 30 := by
    simpa [nextDepth59] using hy4
  obtain ⟨y5, u4, h45, hy5, hu4, hu4mem⟩ :=
    exists_residual_step_with_normUnit K y4 30 hy4'
  have hy5' : HasCoordinateDepth59 K y5 62 := by
    simpa [nextDepth59] using hy5
  let u : (F59 K)ˣ := u0 * u1 * u2 * u3 * u4
  refine ⟨y1, y2, y3, y4, y5, u,
    hy1', hy2', hy3', hy4', hy5', ?_, ?_, ?_⟩
  · rw [h01, h12, h23, h34, h45]
    simp only [fiveStepBase59]
    ring
  · dsimp [u]
    change
      (u0 : F59 K) * (u1 : F59 K) * (u2 : F59 K) *
          (u3 : F59 K) * (u4 : F59 K) = _
    rw [fiveStepBase59, map_mul, map_mul, map_mul, map_mul,
      ← hu0, ← hu1, ← hu2, ← hu3, ← hu4]
  · dsimp [u]
    exact (U60 K).mul_mem
      ((U60 K).mul_mem
        ((U60 K).mul_mem ((U60 K).mul_mem hu0mem hu1mem) hu2mem) hu3mem)
      hu4mem

/-- The complete five-round endpoint. Starting from coordinate depth zero,
the actual norm of the original residual is represented by a concrete unit
in `U60`; the proof retains the five extracted bases and closes the terminal
factor using its depth-62 norm estimate. -/
theorem exists_residualElement59_normUnit_mem_U60_of_depth_zero
    (y0 : E59 K) (hy0 : HasCoordinateDepth59 K y0 0) :
    ∃ u : (F59 K)ˣ,
      (u : F59 K) = Algebra.norm (F59 K) (residualElement59 K y0) ∧
      u ∈ U60 K := by
  obtain ⟨y1, y2, y3, y4, y5, baseUnit,
      hy1, hy2, hy3, hy4, hy5, hfactor, hbaseEq, hbaseMem⟩ :=
    exists_fiveStep_residual_chain_with_normUnit K y0 hy0
  have hterminalDepth :
      Valued.v
          (Algebra.norm (F59 K) (residualElement59 K y5) - 1) ≤
        WithZero.exp (-60 : ℤ) :=
    norm_residualElement59_mem_U60_of_depth K y5 62 hy5 (by norm_num)
  have hterminalLt :
      Valued.v
          (Algebra.norm (F59 K) (residualElement59 K y5) - 1) < 1 :=
    hterminalDepth.trans_lt (by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num)
  have hterminalVal :
      Valued.v (Algebra.norm (F59 K) (residualElement59 K y5)) = 1 := by
    have hone :=
      (Valued.v : Valuation (F59 K) ℤᵐ⁰).map_one_add_of_lt hterminalLt
    simpa only [add_sub_cancel] using hone
  have hterminalNe :
      Algebra.norm (F59 K) (residualElement59 K y5) ≠ 0 := by
    apply (Valuation.ne_zero_iff
      (Valued.v : Valuation (F59 K) ℤᵐ⁰)).mp
    rw [hterminalVal]
    exact one_ne_zero
  let terminalUnit : (F59 K)ˣ :=
    Units.mk0 (Algebra.norm (F59 K) (residualElement59 K y5)) hterminalNe
  have hterminalMem : terminalUnit ∈ U60 K := by
    rw [mem_lambdaOneUnits]
    exact hterminalDepth
  let totalUnit : (F59 K)ˣ := baseUnit * terminalUnit
  refine ⟨totalUnit, ?_, (U60 K).mul_mem hbaseMem hterminalMem⟩
  dsimp [totalUnit, terminalUnit]
  change
    (baseUnit : F59 K) *
        Algebra.norm (F59 K) (residualElement59 K y5) =
      Algebra.norm (F59 K) (residualElement59 K y0)
  rw [hbaseEq, hfactor, map_mul]

end Fermat.FiftyNine.Conservation.FiveStepResidual59
