import Fermat.Five.Dirichlet
import Fermat.Ladder.Basic

/-!
# Seven-fold ladder trace for exponent ten

The solved divisor `5 ∣ 10` is visible at the substrate fold.  Thus the
method exits at depth one, while the remaining folds retain exact
tenth-power structure as checked coverage.
-/

namespace Fermat.Ladder.Ten

/-- The substrate exposes Dirichlet's solved exponent-five divisor. -/
def awarenessClaim : Prop :=
  Fermat.HoldsAt 5 ∧ 5 ∣ 10

theorem awarenessClaim_checked : awarenessClaim :=
  ⟨Fermat.Five.Dirichlet.holdsAt_five_dirichlet, by norm_num⟩

theorem holdsAt_of_awarenessClaim (h : awarenessClaim) : Fermat.HoldsAt 10 :=
  h.1.mono_of_dvd h.2

def structureClaim : Prop :=
  ∀ a b : ℤ,
    a ^ 10 - b ^ 10 = (a ^ 5 - b ^ 5) * (a ^ 5 + b ^ 5)

theorem structureClaim_checked : structureClaim := by
  intro a b
  ring

def sharpeningClaim : Prop :=
  HasDerivAt (fun x : ℝ ↦ x ^ 10) 10 1

theorem sharpeningClaim_checked : sharpeningClaim := by
  simpa [sharpeningClaim] using hasDerivAt_pow 10 (1 : ℝ)

/-- The fifth-power coordinates form the difference-of-squares geometry. -/
def presenceClaim : Prop :=
  ∀ a b : ℤ,
    (a ^ 5 + b ^ 5) ^ 2 - (a ^ 5 - b ^ 5) ^ 2 = 4 * a ^ 5 * b ^ 5

theorem presenceClaim_checked : presenceClaim := by
  intro a b
  ring

def alignmentClaim : Prop :=
  Fermat.HoldsAt 10 ↔ FermatLastTheoremWith ℤ 10

theorem alignmentClaim_checked : alignmentClaim :=
  fermatLastTheoremFor_iff_int

/-- Tenth powers are squares of fifth powers, the explicit exponent map. -/
def agencyClaim : Prop :=
  ∀ x : ℕ, x ^ 10 = (x ^ 5) ^ 2

theorem agencyClaim_checked : agencyClaim := by
  intro x
  ring

def flexibilityClaim : Prop :=
  ¬ Nonempty (SolutionWitness 10)

theorem flexibilityClaim_checked : flexibilityClaim := by
  rintro ⟨witness⟩
  exact (holdsAt_of_awarenessClaim awarenessClaim_checked
    witness.x witness.y witness.z witness.x_ne_zero witness.y_ne_zero
    witness.z_ne_zero) witness.equation

def trace : CaseTrace 10 where
  awareness_substrate := ⟨awarenessClaim, awarenessClaim_checked⟩
  structure_algebra := ⟨structureClaim, structureClaim_checked⟩
  sharpening_analysis := ⟨sharpeningClaim, sharpeningClaim_checked⟩
  presence_geometry := ⟨presenceClaim, presenceClaim_checked⟩
  alignment_logic := ⟨alignmentClaim, alignmentClaim_checked⟩
  agency_arithmetic := ⟨agencyClaim, agencyClaim_checked⟩
  flexibility_potential := ⟨flexibilityClaim, flexibilityClaim_checked⟩
  conclude := by
    intro hDivisor _ _ _ _ _ _
    exact .contradicted (holdsAt_of_awarenessClaim hDivisor)

def run : Checked 10 where
  folds := sevenFolds 10
  trace := trace

def measured : Measured 10 :=
  Measured.atFold run ⟨0, by decide⟩

/-- The first distinguishing instrument is the substrate fold. -/
def exitDepth : ℕ := 1

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

end Fermat.Ladder.Ten
