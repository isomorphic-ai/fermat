import Fermat.Classical
import Fermat.Ladder.Basic

/-! # Seven-fold ladder trace for exponent three -/

namespace Fermat.Ladder.Three

open Finset

def awarenessClaim : Prop :=
  Nat.Prime 3 ∧ Odd 3

theorem awarenessClaim_checked : awarenessClaim := by
  norm_num [awarenessClaim]

def structureClaim : Prop :=
  ∀ a b : ℤ,
    a ^ 3 + b ^ 3 = (a + b) * (a ^ 2 - a * b + b ^ 2)

theorem structureClaim_checked : structureClaim := by
  intro a b
  ring

/-- Mathlib's Eisenstein-integer multiplicity descent is the sharpening
certificate that settles exponent three. -/
def sharpeningClaim : Prop :=
  Fermat.HoldsAt 3

theorem sharpeningClaim_checked : sharpeningClaim :=
  Fermat.holdsAt_three

def presenceClaim : Prop :=
  ∀ a b : ℤ,
    4 * (a ^ 2 - a * b + b ^ 2) = (2 * a - b) ^ 2 + 3 * b ^ 2

theorem presenceClaim_checked : presenceClaim := by
  intro a b
  ring

def alignmentClaim : Prop :=
  Fermat.HoldsAt 3 ↔ FermatLastTheoremWith ℤ 3

theorem alignmentClaim_checked : alignmentClaim :=
  fermatLastTheoremFor_iff_int

def agencyClaim : Prop :=
  ∑ i ∈ range 3, i ^ 3 = 9

theorem agencyClaim_checked : agencyClaim := by
  norm_num [agencyClaim, sum_range_succ]

def flexibilityClaim : Prop :=
  ¬ Nonempty (SolutionWitness 3)

theorem flexibilityClaim_checked : flexibilityClaim := by
  rintro ⟨witness⟩
  exact (Fermat.holdsAt_three witness.x witness.y witness.z
    witness.x_ne_zero witness.y_ne_zero witness.z_ne_zero) witness.equation

def trace : CaseTrace 3 where
  awareness_substrate := ⟨awarenessClaim, awarenessClaim_checked⟩
  structure_algebra := ⟨structureClaim, structureClaim_checked⟩
  sharpening_analysis := ⟨sharpeningClaim, sharpeningClaim_checked⟩
  presence_geometry := ⟨presenceClaim, presenceClaim_checked⟩
  alignment_logic := ⟨alignmentClaim, alignmentClaim_checked⟩
  agency_arithmetic := ⟨agencyClaim, agencyClaim_checked⟩
  flexibility_potential := ⟨flexibilityClaim, flexibilityClaim_checked⟩
  conclude := by
    intro _ _ hDescent _ _ _ _
    exact .contradicted hDescent

def run : Checked 3 where
  folds := sevenFolds 3
  trace := trace

def measured : Measured 3 :=
  Measured.atFold run ⟨2, by decide⟩

def exitDepth : ℕ := 3

theorem exitDepth_eq_measured : measured.exitDepth = exitDepth := rfl

theorem exitDepth_le_seven : exitDepth ≤ 7 := by
  norm_num [exitDepth]

theorem exitDepth_first_sufficient :
    measured.exitDepth = exitDepth ∧
      measured.schedule.decision measured.schedule.exitIndex =
        .exit measured.schedule.outcome ∧
      ∀ i, i < measured.schedule.exitIndex →
        measured.schedule.decision i = .continue :=
  ⟨rfl, measured.schedule.at_exit, measured.schedule.before_exit⟩

end Fermat.Ladder.Three
