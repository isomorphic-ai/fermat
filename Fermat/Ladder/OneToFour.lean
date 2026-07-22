import Fermat.Classical
import Fermat.Ladder.Basic

/-!
# Seven-fold ladder traces for exponents one through four

All four exponents retain checked coverage through fold seven.  Their
methodological exits form the initial diagonal ramp: the concrete substrate
witness at `1`, the Pythagorean algebraic identity at `2`, the sharpened
Eisenstein descent at `3`, and the geometric right-triangle descent at `4`.
-/

namespace Fermat.Ladder

open Finset

namespace One

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

end One

namespace Two

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

end Two

namespace Three

def awarenessClaim : Prop :=
  Nat.Prime 3 ∧ Odd 3

theorem awarenessClaim_checked : awarenessClaim := by
  norm_num [awarenessClaim]

def structureClaim : Prop :=
  ∀ a b : ℤ,
    a ^ 3 + b ^ 3 = (a + b) * (a ^ 2 - a * b + b ^ 2)

theorem structureClaim_checked : structureClaim := by
  intro a b
  ring

/-- Mathlib's Eisenstein-integer multiplicity descent is the sharpening
certificate that settles exponent three. -/
def sharpeningClaim : Prop :=
  Fermat.HoldsAt 3

theorem sharpeningClaim_checked : sharpeningClaim :=
  Fermat.holdsAt_three

def presenceClaim : Prop :=
  ∀ a b : ℤ,
    4 * (a ^ 2 - a * b + b ^ 2) = (2 * a - b) ^ 2 + 3 * b ^ 2

theorem presenceClaim_checked : presenceClaim := by
  intro a b
  ring

def alignmentClaim : Prop :=
  Fermat.HoldsAt 3 ↔ FermatLastTheoremWith ℤ 3

theorem alignmentClaim_checked : alignmentClaim :=
  fermatLastTheoremFor_iff_int

def agencyClaim : Prop :=
  ∑ i ∈ range 3, i ^ 3 = 9

theorem agencyClaim_checked : agencyClaim := by
  norm_num [agencyClaim, sum_range_succ]

def flexibilityClaim : Prop :=
  ¬ Nonempty (SolutionWitness 3)

theorem flexibilityClaim_checked : flexibilityClaim := by
  rintro ⟨witness⟩
  exact (Fermat.holdsAt_three witness.x witness.y witness.z
    witness.x_ne_zero witness.y_ne_zero witness.z_ne_zero) witness.equation

def trace : CaseTrace 3 where
  awareness_substrate := ⟨awarenessClaim, awarenessClaim_checked⟩
  structure_algebra := ⟨structureClaim, structureClaim_checked⟩
  sharpening_analysis := ⟨sharpeningClaim, sharpeningClaim_checked⟩
  presence_geometry := ⟨presenceClaim, presenceClaim_checked⟩
  alignment_logic := ⟨alignmentClaim, alignmentClaim_checked⟩
  agency_arithmetic := ⟨agencyClaim, agencyClaim_checked⟩
  flexibility_potential := ⟨flexibilityClaim, flexibilityClaim_checked⟩
  conclude := by
    intro _ _ hDescent _ _ _ _
    exact .contradicted hDescent

def run : Checked 3 where
  folds := sevenFolds 3
  trace := trace

def measured : Measured 3 :=
  Measured.atFold run ⟨2, by decide⟩

def exitDepth : ℕ := 3

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

end Three

namespace Four

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

end Four

end Fermat.Ladder
