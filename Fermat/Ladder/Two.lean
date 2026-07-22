import Fermat.Ladder.Basic

/-! # Seven-fold ladder trace for exponent two -/

namespace Fermat.Ladder.Two

def awarenessClaim : Prop :=
  (3 : ℕ) ≠ 0 ∧ (4 : ℕ) ≠ 0 ∧ (5 : ℕ) ≠ 0

theorem awarenessClaim_checked : awarenessClaim := by
  norm_num [awarenessClaim]

/-- The algebraic `3–4–5` identity is the first distinguishing instrument. -/
def structureClaim : Prop :=
  (3 : ℕ) ^ 2 + 4 ^ 2 = 5 ^ 2

theorem structureClaim_checked : structureClaim := by
  norm_num [structureClaim]

def sharpeningClaim : Prop :=
  HasDerivAt (fun x : ℝ ↦ x ^ 2) 2 1

theorem sharpeningClaim_checked : sharpeningClaim := by
  simpa [sharpeningClaim] using hasDerivAt_pow 2 (1 : ℝ)

def presenceClaim : Prop :=
  ∀ m n : ℤ,
    (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2

theorem presenceClaim_checked : presenceClaim := by
  intro m n
  ring

def alignmentClaim : Prop :=
  Fermat.HoldsAt 2 ↔ FermatLastTheoremWith ℤ 2

theorem alignmentClaim_checked : alignmentClaim :=
  fermatLastTheoremFor_iff_int

def agencyClaim : Prop :=
  (9 : ℕ) + 16 = 25

theorem agencyClaim_checked : agencyClaim := by
  norm_num [agencyClaim]

def flexibilityClaim : Prop :=
  ∀ k : ℕ, (3 * k) ^ 2 + (4 * k) ^ 2 = (5 * k) ^ 2

theorem flexibilityClaim_checked : flexibilityClaim := by
  intro k
  ring

def trace : CaseTrace 2 where
  awareness_substrate := ⟨awarenessClaim, awarenessClaim_checked⟩
  structure_algebra := ⟨structureClaim, structureClaim_checked⟩
  sharpening_analysis := ⟨sharpeningClaim, sharpeningClaim_checked⟩
  presence_geometry := ⟨presenceClaim, presenceClaim_checked⟩
  alignment_logic := ⟨alignmentClaim, alignmentClaim_checked⟩
  agency_arithmetic := ⟨agencyClaim, agencyClaim_checked⟩
  flexibility_potential := ⟨flexibilityClaim, flexibilityClaim_checked⟩
  conclude := by
    intro _ hEquation _ _ _ _ _
    exact .pass
      { x := 3
        y := 4
        z := 5
        x_ne_zero := by norm_num
        y_ne_zero := by norm_num
        z_ne_zero := by norm_num
        equation := hEquation }

def run : Checked 2 where
  folds := sevenFolds 2
  trace := trace

def measured : Measured 2 :=
  Measured.atFold run ⟨1, by decide⟩

def exitDepth : ℕ := 2

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

end Fermat.Ladder.Two
