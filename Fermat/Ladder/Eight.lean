import Fermat.Classical
import Fermat.Ladder.Basic

/-!
# Seven-fold ladder trace for exponent eight

The solved divisor `4 ∣ 8` closes the method at the substrate fold.  The
Pythagorean geometry behind exponent four remains visible later in the trace.
-/

namespace Fermat.Ladder.Eight

def awarenessClaim : Prop :=
  Fermat.HoldsAt 4 ∧ 4 ∣ 8

theorem awarenessClaim_checked : awarenessClaim :=
  ⟨Fermat.holdsAt_four, by norm_num⟩

theorem holdsAt_of_awarenessClaim (h : awarenessClaim) : Fermat.HoldsAt 8 :=
  h.1.mono_of_dvd h.2

def structureClaim : Prop :=
  ∀ a b : ℤ,
    a ^ 8 - b ^ 8 =
      (a - b) * (a + b) * (a ^ 2 + b ^ 2) * (a ^ 4 + b ^ 4)

theorem structureClaim_checked : structureClaim := by
  intro a b
  ring

def sharpeningClaim : Prop :=
  HasDerivAt (fun x : ℝ ↦ x ^ 8) 8 1

theorem sharpeningClaim_checked : sharpeningClaim := by
  simpa [sharpeningClaim] using hasDerivAt_pow 8 (1 : ℝ)

/-- The Pythagorean parametrization identity used by the exponent-four
descent. -/
def presenceClaim : Prop :=
  ∀ a b : ℤ,
    (a ^ 2 - b ^ 2) ^ 2 + (2 * a * b) ^ 2 = (a ^ 2 + b ^ 2) ^ 2

theorem presenceClaim_checked : presenceClaim := by
  intro a b
  ring

def alignmentClaim : Prop :=
  Fermat.HoldsAt 8 ↔ FermatLastTheoremWith ℤ 8

theorem alignmentClaim_checked : alignmentClaim :=
  fermatLastTheoremFor_iff_int

def agencyClaim : Prop :=
  ∀ x : ℕ, x ^ 8 = (x ^ 4) ^ 2

theorem agencyClaim_checked : agencyClaim := by
  intro x
  ring

def flexibilityClaim : Prop :=
  ¬ Nonempty (SolutionWitness 8)

theorem flexibilityClaim_checked : flexibilityClaim := by
  rintro ⟨witness⟩
  exact (holdsAt_of_awarenessClaim awarenessClaim_checked
    witness.x witness.y witness.z witness.x_ne_zero witness.y_ne_zero
    witness.z_ne_zero) witness.equation

def trace : CaseTrace 8 where
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

def run : Checked 8 where
  folds := sevenFolds 8
  trace := trace

def measured : Measured 8 :=
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

end Fermat.Ladder.Eight
