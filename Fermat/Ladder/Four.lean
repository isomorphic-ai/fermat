import Fermat.Classical
import Fermat.Ladder.Basic

/-! # Seven-fold ladder trace for exponent four -/

namespace Fermat.Ladder.Four

/-- The visible divisor `2` does not close exponent four, because exponent
two passes rather than being contradicted. -/
def awarenessClaim : Prop :=
  2 ∣ 4 ∧ ¬ Fermat.HoldsAt 2

theorem awarenessClaim_checked : awarenessClaim := by
  exact ⟨by norm_num, not_fermatLastTheoremFor_two⟩

def structureClaim : Prop :=
  ∀ a b : ℤ,
    a ^ 4 - b ^ 4 = (a - b) * (a + b) * (a ^ 2 + b ^ 2)

theorem structureClaim_checked : structureClaim := by
  intro a b
  ring

def sharpeningClaim : Prop :=
  HasDerivAt (fun x : ℝ ↦ x ^ 4) 4 1

theorem sharpeningClaim_checked : sharpeningClaim := by
  simpa [sharpeningClaim] using hasDerivAt_pow 4 (1 : ℝ)

/-- The right-triangle infinite-descent endpoint formalized by Mathlib. -/
def presenceClaim : Prop :=
  ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → a ^ 4 + b ^ 4 ≠ c ^ 2

theorem presenceClaim_checked : presenceClaim := by
  exact fun a b c ↦ not_fermat_42

theorem holdsAt_of_presenceClaim (h : presenceClaim) : Fermat.HoldsAt 4 := by
  change FermatLastTheoremFor 4
  rw [fermatLastTheoremFor_iff_int]
  intro a b c ha hb _ hEquation
  apply h a b (c ^ 2) ha hb
  calc
    a ^ 4 + b ^ 4 = c ^ 4 := hEquation
    _ = (c ^ 2) ^ 2 := by ring

def alignmentClaim : Prop :=
  Fermat.HoldsAt 4 ↔ FermatLastTheoremWith ℤ 4

theorem alignmentClaim_checked : alignmentClaim :=
  fermatLastTheoremFor_iff_int

def agencyClaim : Prop :=
  Fermat.HoldsAt 4

theorem agencyClaim_checked : agencyClaim :=
  Fermat.holdsAt_four

def flexibilityClaim : Prop :=
  ¬ Nonempty (SolutionWitness 4)

theorem flexibilityClaim_checked : flexibilityClaim := by
  rintro ⟨witness⟩
  exact (Fermat.holdsAt_four witness.x witness.y witness.z
    witness.x_ne_zero witness.y_ne_zero witness.z_ne_zero) witness.equation

def trace : CaseTrace 4 where
  awareness_substrate := ⟨awarenessClaim, awarenessClaim_checked⟩
  structure_algebra := ⟨structureClaim, structureClaim_checked⟩
  sharpening_analysis := ⟨sharpeningClaim, sharpeningClaim_checked⟩
  presence_geometry := ⟨presenceClaim, presenceClaim_checked⟩
  alignment_logic := ⟨alignmentClaim, alignmentClaim_checked⟩
  agency_arithmetic := ⟨agencyClaim, agencyClaim_checked⟩
  flexibility_potential := ⟨flexibilityClaim, flexibilityClaim_checked⟩
  conclude := by
    intro _ _ _ hGeometry _ _ _
    exact .contradicted (holdsAt_of_presenceClaim hGeometry)

def run : Checked 4 where
  folds := sevenFolds 4
  trace := trace

def measured : Measured 4 :=
  Measured.atFold run ⟨3, by decide⟩

def exitDepth : ℕ := 4

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

end Fermat.Ladder.Four
