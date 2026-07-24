import Fermat.Classical
import Fermat.Ladder.Basic

/-!
# Seven-fold ladder trace for exponent nine

The solved divisor `3 ∣ 9` is visible at fold one.  The later folds retain
the cubic factorization and Eisenstein norm geometry specific to exponent
nine.
-/

namespace Fermat.Ladder.Nine

def awarenessClaim : Prop :=
  Fermat.HoldsAt 3 ∧ 3 ∣ 9

theorem awarenessClaim_checked : awarenessClaim :=
  ⟨Fermat.holdsAt_three, by norm_num⟩

theorem holdsAt_of_awarenessClaim (h : awarenessClaim) : Fermat.HoldsAt 9 :=
  h.1.mono_of_dvd h.2

def structureClaim : Prop :=
  ∀ a b : ℤ,
    a ^ 9 + b ^ 9 =
      (a ^ 3 + b ^ 3) * (a ^ 6 - a ^ 3 * b ^ 3 + b ^ 6)

theorem structureClaim_checked : structureClaim := by
  intro a b
  ring

def sharpeningClaim : Prop :=
  HasDerivAt (fun x : ℝ ↦ x ^ 9) 9 1

theorem sharpeningClaim_checked : sharpeningClaim := by
  simpa [sharpeningClaim] using hasDerivAt_pow 9 (1 : ℝ)

/-- The Eisenstein norm identity after the cubic substitution. -/
def presenceClaim : Prop :=
  ∀ a b : ℤ,
    4 * (a ^ 6 - a ^ 3 * b ^ 3 + b ^ 6) =
      (2 * a ^ 3 - b ^ 3) ^ 2 + 3 * b ^ 6

theorem presenceClaim_checked : presenceClaim := by
  intro a b
  ring

def alignmentClaim : Prop :=
  Fermat.HoldsAt 9 ↔ FermatLastTheoremWith ℤ 9

theorem alignmentClaim_checked : alignmentClaim :=
  fermatLastTheoremFor_iff_int

def agencyClaim : Prop :=
  ∀ x : ℕ, x ^ 9 = (x ^ 3) ^ 3

theorem agencyClaim_checked : agencyClaim := by
  intro x
  ring

def flexibilityClaim : Prop :=
  ¬ Nonempty (SolutionWitness 9)

theorem flexibilityClaim_checked : flexibilityClaim := by
  rintro ⟨witness⟩
  exact (holdsAt_of_awarenessClaim awarenessClaim_checked
    witness.x witness.y witness.z witness.x_ne_zero witness.y_ne_zero
    witness.z_ne_zero) witness.equation

def trace : CaseTrace 9 where
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

def run : Checked 9 where
  folds := sevenFolds 9
  trace := trace

def measured : Measured 9 :=
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

end Fermat.Ladder.Nine
