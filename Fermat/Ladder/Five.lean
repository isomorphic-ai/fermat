import Fermat.Five.Dirichlet
import Fermat.Ladder.Basic

/-!
# Seven-fold ladder trace for exponent five

The first distinguishing instrument is fold five: Dirichlet's completed
two-branch historical descent.  Arithmetic and potential remain checked as
coverage after that exit.
-/

namespace Fermat.Ladder.Five

def awarenessClaim : Prop :=
  Nat.Prime 5 ∧ Odd 5

theorem awarenessClaim_checked : awarenessClaim := by
  norm_num [awarenessClaim]

def structureClaim : Prop :=
  ∀ a b : ℤ,
    a ^ 5 + b ^ 5 =
      (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4)

theorem structureClaim_checked : structureClaim := by
  intro a b
  ring

def sharpeningClaim : Prop :=
  HasDerivAt (fun x : ℝ ↦ x ^ 5) 5 1

theorem sharpeningClaim_checked : sharpeningClaim := by
  simpa [sharpeningClaim] using hasDerivAt_pow 5 (1 : ℝ)

/-- The real-quadratic norm identity behind the fifth-power cofactor. -/
def presenceClaim : Prop :=
  ∀ a b : ℤ,
    (2 * a ^ 2 - a * b + 2 * b ^ 2) ^ 2 - 5 * (a * b) ^ 2 =
      4 * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4)

theorem presenceClaim_checked : presenceClaim := by
  intro a b
  ring

/-- Dirichlet's completed 1828 proof is the first settling certificate. -/
def alignmentClaim : Prop :=
  Fermat.HoldsAt 5

theorem alignmentClaim_checked : alignmentClaim :=
  Fermat.Five.Dirichlet.holdsAt_five_dirichlet

def agencyClaim : Prop :=
  Fermat.Five.Dirichlet.FifthEquationImpossible

theorem agencyClaim_checked : agencyClaim :=
  Fermat.Five.Dirichlet.fifthEquationImpossible

def flexibilityClaim : Prop :=
  ¬ Nonempty (SolutionWitness 5)

theorem flexibilityClaim_checked : flexibilityClaim := by
  rintro ⟨witness⟩
  exact (Fermat.Five.Dirichlet.holdsAt_five_dirichlet
    witness.x witness.y witness.z witness.x_ne_zero witness.y_ne_zero
    witness.z_ne_zero) witness.equation

def trace : CaseTrace 5 where
  awareness_substrate := ⟨awarenessClaim, awarenessClaim_checked⟩
  structure_algebra := ⟨structureClaim, structureClaim_checked⟩
  sharpening_analysis := ⟨sharpeningClaim, sharpeningClaim_checked⟩
  presence_geometry := ⟨presenceClaim, presenceClaim_checked⟩
  alignment_logic := ⟨alignmentClaim, alignmentClaim_checked⟩
  agency_arithmetic := ⟨agencyClaim, agencyClaim_checked⟩
  flexibility_potential := ⟨flexibilityClaim, flexibilityClaim_checked⟩
  conclude := by
    intro _ _ _ _ hDirichlet _ _
    exact .contradicted hDirichlet

def run : Checked 5 where
  folds := sevenFolds 5
  trace := trace

def measured : Measured 5 :=
  Measured.atFold run ⟨4, by decide⟩

def exitDepth : ℕ := 5

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

end Fermat.Ladder.Five
