import Fermat.Fourteen.DescentConstruction
import Fermat.Ladder.Basic
import Fermat.Seven.Lebesgue.TheoremTwo

/-!
# Seven-fold ladder trace for exponent fourteen

The response exits at substrate depth one through the already checked OLD
exponent-seven descent and `7 ∣ 14`.  Dirichlet's independent 1832 proof is
nevertheless retained in the later folds: its factorization, first case,
strict descent construction, and final endpoint are all checked here.
-/

namespace Fermat.Ladder.Fourteen

/-- The substrate exposes Lebesgue's old exponent-seven theorem and the
divisibility map into exponent fourteen. -/
def awarenessClaim : Prop :=
  Fermat.HoldsAt 7 ∧ 7 ∣ 14

theorem awarenessClaim_checked : awarenessClaim :=
  ⟨Fermat.Seven.Lebesgue.holdsAt_seven_lebesgue, by norm_num⟩

theorem holdsAt_of_awarenessClaim (h : awarenessClaim) : Fermat.HoldsAt 14 :=
  h.1.mono_of_dvd h.2

def structureClaim : Prop :=
  ∀ a b : ℤ,
    a ^ 14 - b ^ 14 = (a ^ 7 - b ^ 7) * (a ^ 7 + b ^ 7)

theorem structureClaim_checked : structureClaim := by
  intro a b
  ring

def sharpeningClaim : Prop :=
  HasDerivAt (fun x : ℝ ↦ x ^ 14) 14 1

theorem sharpeningClaim_checked : sharpeningClaim := by
  simpa [sharpeningClaim] using hasDerivAt_pow 14 (1 : ℝ)

/-- Equation (3) of Dirichlet's direct proof. -/
def presenceClaim : Prop :=
  ∀ t u : ℤ,
    t ^ 14 - u ^ 14 =
      Fermat.Fourteen.Dirichlet.phi t u *
        ((Fermat.Fourteen.Dirichlet.phi t u ^ 3) ^ 2 +
          7 * Fermat.Fourteen.Dirichlet.psi t u ^ 2)

theorem presenceClaim_checked : presenceClaim :=
  Fermat.Fourteen.Dirichlet.factorization

/-- Dirichlet's signed quadratic extraction closes the direct first case. -/
def alignmentClaim : Prop :=
  Fermat.Fourteen.Dirichlet.FirstCaseImpossible

theorem alignmentClaim_checked : alignmentClaim :=
  Fermat.Fourteen.Dirichlet.firstCaseImpossible

/-- The explicit construction lowers Dirichlet's old descent height. -/
def agencyClaim : Prop :=
  Fermat.Fourteen.Dirichlet.Descends

theorem agencyClaim_checked : agencyClaim :=
  Fermat.Fourteen.Dirichlet.descends

/-- The complete OLD/slow route, independent of exponent seven. -/
def flexibilityClaim : Prop :=
  Fermat.HoldsAt 14

theorem flexibilityClaim_checked : flexibilityClaim :=
  Fermat.Fourteen.Dirichlet.holdsAt_fourteen_dirichlet

def trace : CaseTrace 14 where
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

def run : Checked 14 where
  folds := sevenFolds 14
  trace := trace

def measured : Measured 14 :=
  Measured.atFold run ⟨0, by decide⟩

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

end Fermat.Ladder.Fourteen
