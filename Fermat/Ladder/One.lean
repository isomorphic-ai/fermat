import Fermat.Ladder.Basic

/-! # Seven-fold ladder trace for exponent one -/

namespace Fermat.Ladder.One

open Finset

def awarenessClaim : Prop :=
  (1 : ℕ) ^ 1 + 1 ^ 1 = 2 ^ 1

theorem awarenessClaim_checked : awarenessClaim := by
  norm_num [awarenessClaim]

def structureClaim : Prop :=
  ∀ a b : ℤ, a ^ 1 + b ^ 1 = a + b

theorem structureClaim_checked : structureClaim := by
  simp [structureClaim]

def sharpeningClaim : Prop :=
  HasDerivAt (fun x : ℝ ↦ x ^ 1) 1 1

theorem sharpeningClaim_checked : sharpeningClaim := by
  simpa [sharpeningClaim] using hasDerivAt_pow 1 (1 : ℝ)

def presenceClaim : Prop :=
  dist (1 : ℝ) 2 = 1

theorem presenceClaim_checked : presenceClaim := by
  norm_num [presenceClaim, Real.dist_eq]

def alignmentClaim : Prop :=
  ∀ a b c : ℕ, a ^ 1 + b ^ 1 = c ^ 1 ↔ a + b = c

theorem alignmentClaim_checked : alignmentClaim := by
  simp [alignmentClaim]

def agencyClaim : Prop :=
  (2 : ℕ) ^ 1 = 2

theorem agencyClaim_checked : agencyClaim := by
  norm_num [agencyClaim]

def flexibilityClaim : Prop :=
  Fintype.card (Finset (Fin 1)) = 2

theorem flexibilityClaim_checked : flexibilityClaim := by
  simp [flexibilityClaim]

def trace : CaseTrace 1 where
  awareness_substrate := ⟨awarenessClaim, awarenessClaim_checked⟩
  structure_algebra := ⟨structureClaim, structureClaim_checked⟩
  sharpening_analysis := ⟨sharpeningClaim, sharpeningClaim_checked⟩
  presence_geometry := ⟨presenceClaim, presenceClaim_checked⟩
  alignment_logic := ⟨alignmentClaim, alignmentClaim_checked⟩
  agency_arithmetic := ⟨agencyClaim, agencyClaim_checked⟩
  flexibility_potential := ⟨flexibilityClaim, flexibilityClaim_checked⟩
  conclude := by
    intro hEquation _ _ _ _ _ _
    exact .pass
      { x := 1
        y := 1
        z := 2
        x_ne_zero := by norm_num
        y_ne_zero := by norm_num
        z_ne_zero := by norm_num
        equation := hEquation }

def run : Checked 1 where
  folds := sevenFolds 1
  trace := trace

def measured : Measured 1 :=
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

end Fermat.Ladder.One
