import Fermat.Ladder.Basic
import Fermat.OneHundredFiftySeven.FoldCertificates
import Fermat.OneHundredFiftySeven.SecondCase

/-!
# Conditional seven-fold ladder trace for exponent 157

The first six folds are exponent-specific kernel-checked data.  Fold six
eliminates the first case and records the package's finite loop of exactly
two circular-unit probes.  The run exits only at fold seven, where the
explicit `TwoComponentSecondCaseBridge` excludes the second case.

Until the shared historical bridge is formalized, the trace is a function of
that exact proposition.  Thus this file exposes the measured response without
claiming an unconditional FLT theorem prematurely.
-/

namespace Fermat.Ladder.OneHundredFiftySeven

open Fermat.OneHundredFiftySeven
open Fermat.OneHundredFiftySeven.FoldCertificates

def awarenessClaim : Prop :=
  Nat.Prime 79 ∧ Nat.Prime 157 ∧ Nat.Prime 1571 ∧ Nat.Prime 7537 ∧
    156 = 3 * 52 ∧ 156 = 4 * 39 ∧ 156 = 12 * 13 ∧ 158 = 2 * 79

theorem awarenessClaim_checked : awarenessClaim :=
  ⟨prime_79, OneHundredFiftySeven.prime_157,
    OneHundredFiftySeven.prime_1571, prime_7537,
    leftNeighbor_decompositions.1,
    leftNeighbor_decompositions.2.1,
    leftNeighbor_decompositions.2.2,
    rightNeighbor_decomposition⟩

def structureClaim : Prop :=
  (5 : ZMod 157) ^ 156 = 1 ∧
    (5 : ZMod 157) ^ 78 ≠ 1 ∧
    (5 : ZMod 157) ^ 52 ≠ 1 ∧
    (5 : ZMod 157) ^ 12 ≠ 1

theorem structureClaim_checked : structureClaim := generator_five_power_tests

def sharpeningClaim : Prop :=
  (2 : ZMod 157) ^ 52 = 1 ∧
    (2 : ZMod 157) ^ 26 = -1 ∧
    (4 : ZMod 157) ^ 26 = 1 ∧
    (4 : ZMod 157) ^ 13 = -1

theorem sharpeningClaim_checked : sharpeningClaim :=
  ⟨two_crease_power_tests.1, two_crease_power_tests.2.1,
    square_sheet_power_tests.1, square_sheet_power_tests.2⟩

def presenceClaim : Prop :=
  (∀ t : ℤ, 4 * phi314 t = a157 t ^ 2 - 157 * b157 t ^ 2) ∧
    (∀ t : ℤ, b157 t = b13 t * q72 t)

theorem presenceClaim_checked : presenceClaim :=
  ⟨quadratic_fold, b157_eq_b13_mul_q72⟩

def alignmentClaim : Prop :=
  74 ^ 2 + 74 * 11 - 39 * 11 ^ 2 = 1571 ∧
    ((23 : ZMod 1571) - 19 * 640 + 640 ^ 2 = 0)

theorem alignmentClaim_checked : alignmentClaim :=
  ⟨quadratic_branch_norm, cubic_branch_values.1⟩

/-- Fold six carries the two Sophie-Germain residue conditions and records
that the real-class re-probe loop used exactly two samples. -/
def agencyClaim : Prop :=
  Fermat.SophieGermain.NoConsecutivePowers 157 1571 ∧
    Fermat.SophieGermain.ExponentNotPower 157 1571 ∧
    probeLoop.count = 2

theorem agencyClaim_checked : agencyClaim :=
  ⟨noConsecutivePowers_157_1571, exponentNotPower_157_1571,
    probeLoop.count_eq_two⟩

/-- Fold seven is exactly the remaining primary-singular second-case
endpoint; no finite certificate is promoted into it by definition. -/
def flexibilityClaim : Prop := TwoComponentSecondCaseBridge

def trace (hsecond : TwoComponentSecondCaseBridge) : CaseTrace 157 where
  awareness_substrate := ⟨awarenessClaim, awarenessClaim_checked⟩
  structure_algebra := ⟨structureClaim, structureClaim_checked⟩
  sharpening_analysis := ⟨sharpeningClaim, sharpeningClaim_checked⟩
  presence_geometry := ⟨presenceClaim, presenceClaim_checked⟩
  alignment_logic := ⟨alignmentClaim, alignmentClaim_checked⟩
  agency_arithmetic := ⟨agencyClaim, agencyClaim_checked⟩
  flexibility_potential := ⟨flexibilityClaim, hsecond⟩
  conclude := by
    intro _ _ _ _ _ _ hsecond'
    exact .contradicted
      (holdsAt_oneHundredFiftySeven_of_twoComponentSecondCaseBridge hsecond')

def run (hsecond : TwoComponentSecondCaseBridge) : Checked 157 where
  folds := sevenFolds 157
  trace := trace hsecond

def measured (hsecond : TwoComponentSecondCaseBridge) : Measured 157 :=
  Measured.atFold (run hsecond) ⟨6, by decide⟩

/-- The package reaches the seventh fold: fold six closes the first case,
and fold seven is the first fold that can close both cases. -/
def exitDepth : ℕ := 7

theorem exitDepth_eq_measured (hsecond : TwoComponentSecondCaseBridge) :
    (measured hsecond).exitDepth = exitDepth := rfl

theorem exitDepth_le_seven : exitDepth ≤ 7 := by
  norm_num [exitDepth]

theorem exitDepth_first_sufficient (hsecond : TwoComponentSecondCaseBridge) :
    (measured hsecond).exitDepth = exitDepth ∧
      (measured hsecond).schedule.decision
          (measured hsecond).schedule.exitIndex =
        .exit (measured hsecond).schedule.outcome ∧
      ∀ i, i < (measured hsecond).schedule.exitIndex →
        (measured hsecond).schedule.decision i = .continue :=
  ⟨rfl, (measured hsecond).schedule.at_exit,
    (measured hsecond).schedule.before_exit⟩

end Fermat.Ladder.OneHundredFiftySeven
