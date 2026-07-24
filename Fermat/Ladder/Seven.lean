import Fermat.Ladder.Basic
import Fermat.Seven.LameArithmetic
import Fermat.Seven.Lebesgue.TheoremTwo

/-!
# Seven-fold ladder trace for exponent seven

The first distinguishing instrument is arithmetic fold six: Lebesgue's
corrected 1840 descent, assembled through the source-faithful OLD package.
-/

namespace Fermat.Ladder.Seven

def awarenessClaim : Prop :=
  Nat.Prime 7 ∧ Odd 7

theorem awarenessClaim_checked : awarenessClaim := by
  norm_num [awarenessClaim]

/-- Lamé's exact binomial cofactor entrance. -/
def structureClaim : Prop :=
  ∀ d y : ℕ,
    (d + y) ^ 7 = y ^ 7 + d * Fermat.Seven.Lame.X d y

theorem structureClaim_checked : structureClaim := by
  intro d y
  exact Fermat.Seven.Lame.add_seventhPower_factorization d y

def sharpeningClaim : Prop :=
  HasDerivAt (fun x : ℝ ↦ x ^ 7) 7 1

theorem sharpeningClaim_checked : sharpeningClaim := by
  simpa [sharpeningClaim] using hasDerivAt_pow 7 (1 : ℝ)

/-- Lebesgue's symmetric seventh-power configuration from p. 278. -/
def presenceClaim : Prop :=
  ∀ x y z : ℤ,
    Fermat.Seven.Lebesgue.s x y z ^ 7 =
      x ^ 7 + y ^ 7 + z ^ 7 +
        7 * Fermat.Seven.Lebesgue.v x y z * Fermat.Seven.Lebesgue.t x y z

theorem presenceClaim_checked : presenceClaim := by
  exact Fermat.Seven.Lebesgue.seventh_power_identity

def alignmentClaim : Prop :=
  Fermat.HoldsAt 7 ↔ FermatLastTheoremWith ℤ 7

theorem alignmentClaim_checked : alignmentClaim :=
  fermatLastTheoremFor_iff_int

/-- Lebesgue's corrected Theorem II is the first settling certificate. -/
def agencyClaim : Prop :=
  Fermat.HoldsAt 7

theorem agencyClaim_checked : agencyClaim :=
  Fermat.Seven.Lebesgue.holdsAt_seven_lebesgue

def flexibilityClaim : Prop :=
  ¬ Nonempty (SolutionWitness 7)

theorem flexibilityClaim_checked : flexibilityClaim := by
  rintro ⟨witness⟩
  exact (Fermat.Seven.Lebesgue.holdsAt_seven_lebesgue
    witness.x witness.y witness.z witness.x_ne_zero witness.y_ne_zero
    witness.z_ne_zero) witness.equation

def trace : CaseTrace 7 where
  awareness_substrate := ⟨awarenessClaim, awarenessClaim_checked⟩
  structure_algebra := ⟨structureClaim, structureClaim_checked⟩
  sharpening_analysis := ⟨sharpeningClaim, sharpeningClaim_checked⟩
  presence_geometry := ⟨presenceClaim, presenceClaim_checked⟩
  alignment_logic := ⟨alignmentClaim, alignmentClaim_checked⟩
  agency_arithmetic := ⟨agencyClaim, agencyClaim_checked⟩
  flexibility_potential := ⟨flexibilityClaim, flexibilityClaim_checked⟩
  conclude := by
    intro _ _ _ _ _ hLebesgue _
    exact .contradicted hLebesgue

def run : Checked 7 where
  folds := sevenFolds 7
  trace := trace

def measured : Measured 7 :=
  Measured.atFold run ⟨5, by decide⟩

def exitDepth : ℕ := 6

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

end Fermat.Ladder.Seven
