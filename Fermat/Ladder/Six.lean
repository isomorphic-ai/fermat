import Fermat.Classical
import Fermat.Ladder.Basic

/-!
# Seven-fold ladder trace for exponent six

The solved divisor `3 ∣ 6` is already visible at the substrate fold, so the
method exits at depth one while retaining all seven checked folds.
-/

namespace Fermat.Ladder.Six

/-- The substrate exposes both a solved divisor and its divisibility map. -/
def awarenessClaim : Prop :=
  Fermat.HoldsAt 3 ∧ 3 ∣ 6

theorem awarenessClaim_checked : awarenessClaim :=
  ⟨Fermat.holdsAt_three, by norm_num⟩

theorem holdsAt_of_awarenessClaim (h : awarenessClaim) : Fermat.HoldsAt 6 :=
  h.1.mono_of_dvd h.2

def structureClaim : Prop :=
  ∀ a b : ℤ,
    a ^ 6 - b ^ 6 =
      (a - b) * (a + b) * (a ^ 2 + a * b + b ^ 2) * (a ^ 2 - a * b + b ^ 2)

theorem structureClaim_checked : structureClaim := by
  intro a b
  ring

def sharpeningClaim : Prop :=
  HasDerivAt (fun x : ℝ ↦ x ^ 6) 6 1

theorem sharpeningClaim_checked : sharpeningClaim := by
  simpa [sharpeningClaim] using hasDerivAt_pow 6 (1 : ℝ)

/-- The product of the two Eisenstein quadratic norms. -/
def presenceClaim : Prop :=
  ∀ a b : ℤ,
    (a ^ 2 + a * b + b ^ 2) * (a ^ 2 - a * b + b ^ 2) =
      a ^ 4 + a ^ 2 * b ^ 2 + b ^ 4

theorem presenceClaim_checked : presenceClaim := by
  intro a b
  ring

def alignmentClaim : Prop :=
  Fermat.HoldsAt 6 ↔ FermatLastTheoremWith ℤ 6

theorem alignmentClaim_checked : alignmentClaim :=
  fermatLastTheoremFor_iff_int

def agencyClaim : Prop :=
  ∀ x : ℕ, x ^ 6 = (x ^ 3) ^ 2

theorem agencyClaim_checked : agencyClaim := by
  intro x
  ring

def flexibilityClaim : Prop :=
  ¬ Nonempty (SolutionWitness 6)

theorem flexibilityClaim_checked : flexibilityClaim := by
  rintro ⟨witness⟩
  exact (holdsAt_of_awarenessClaim awarenessClaim_checked
    witness.x witness.y witness.z witness.x_ne_zero witness.y_ne_zero
    witness.z_ne_zero) witness.equation

def trace : CaseTrace 6 where
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

def run : Checked 6 where
  folds := sevenFolds 6
  trace := trace

def measured : Measured 6 :=
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

end Fermat.Ladder.Six
