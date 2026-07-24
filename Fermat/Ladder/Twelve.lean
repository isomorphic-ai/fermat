import Fermat.Classical
import Fermat.Ladder.Basic

/-!
# Seven-fold ladder trace for exponent twelve

As predicted by the response curve, this composite exits at depth one: the
substrate already exposes the solved divisor `3 ∣ 12`.
-/

namespace Fermat.Ladder.Twelve

def awarenessClaim : Prop :=
  Fermat.HoldsAt 3 ∧ 3 ∣ 12

theorem awarenessClaim_checked : awarenessClaim :=
  ⟨Fermat.holdsAt_three, by norm_num⟩

theorem holdsAt_of_awarenessClaim (h : awarenessClaim) : Fermat.HoldsAt 12 :=
  h.1.mono_of_dvd h.2

def structureClaim : Prop :=
  ∀ a b : ℤ,
    a ^ 12 - b ^ 12 =
      (a ^ 4 - b ^ 4) * (a ^ 8 + a ^ 4 * b ^ 4 + b ^ 8)

theorem structureClaim_checked : structureClaim := by
  intro a b
  ring

def sharpeningClaim : Prop :=
  HasDerivAt (fun x : ℝ ↦ x ^ 12) 12 1

theorem sharpeningClaim_checked : sharpeningClaim := by
  simpa [sharpeningClaim] using hasDerivAt_pow 12 (1 : ℝ)

/-- The two quartic quadratic norms multiply to the cubic cofactor. -/
def presenceClaim : Prop :=
  ∀ a b : ℤ,
    (a ^ 4 + a ^ 2 * b ^ 2 + b ^ 4) *
        (a ^ 4 - a ^ 2 * b ^ 2 + b ^ 4) =
      a ^ 8 + a ^ 4 * b ^ 4 + b ^ 8

theorem presenceClaim_checked : presenceClaim := by
  intro a b
  ring

def alignmentClaim : Prop :=
  Fermat.HoldsAt 12 ↔ FermatLastTheoremWith ℤ 12

theorem alignmentClaim_checked : alignmentClaim :=
  fermatLastTheoremFor_iff_int

/-- Twelfth powers are cubes of fourth powers, the explicit map to the
solved exponent-three equation. -/
def agencyClaim : Prop :=
  ∀ x : ℕ, x ^ 12 = (x ^ 4) ^ 3

theorem agencyClaim_checked : agencyClaim := by
  intro x
  ring

def flexibilityClaim : Prop :=
  ¬ Nonempty (SolutionWitness 12)

theorem flexibilityClaim_checked : flexibilityClaim := by
  rintro ⟨witness⟩
  exact (holdsAt_of_awarenessClaim awarenessClaim_checked
    witness.x witness.y witness.z witness.x_ne_zero witness.y_ne_zero
    witness.z_ne_zero) witness.equation

def trace : CaseTrace 12 where
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

def run : Checked 12 where
  folds := sevenFolds 12
  trace := trace

def measured : Measured 12 :=
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

end Fermat.Ladder.Twelve
