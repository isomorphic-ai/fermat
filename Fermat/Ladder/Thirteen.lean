import Fermat.Ladder.Basic
import Fermat.Thirteen.SevenFold

/-!
# Seven-fold ladder trace for exponent thirteen

The class-number-one / regular-prime branch first settles the exponent at
arithmetic fold six.  The five-index direct Faulhaber computation remains
checked at fold seven as an independent decompressed alternative.
-/

namespace Fermat.Ladder.Thirteen

open Fermat.Regular.Faulhaber

local instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

def awarenessClaim : Prop :=
  Fermat.HoldsAt 12 ∧ Fermat.HoldsAt 14

theorem awarenessClaim_checked : awarenessClaim :=
  ⟨Fermat.Thirteen.SevenFold.holdsAt_twelve,
    Fermat.Thirteen.SevenFold.holdsAt_fourteen⟩

/-- The exact odd-power cofactor around the exponent-thirteen circle. -/
def structureClaim : Prop :=
  ∀ x y : ℤ,
    x ^ 13 + y ^ 13 =
      (x + y) * Fermat.Thirteen.SevenFold.phi26 x y

theorem structureClaim_checked : structureClaim := by
  intro x y
  norm_num [Fermat.Thirteen.SevenFold.phi26, Finset.sum_range_succ]
  ring

def sharpeningClaim : Prop :=
  HasDerivAt (fun x : ℝ ↦ x ^ 13) 13 1

theorem sharpeningClaim_checked : sharpeningClaim := by
  simpa [sharpeningClaim] using hasDerivAt_pow 13 (1 : ℝ)

/-- The exact norm identity in the real quadratic-period crease. -/
def presenceClaim : Prop :=
  ∀ x y : ℤ,
    Fermat.Thirteen.SevenFold.quadraticA x y ^ 2 -
        13 * Fermat.Thirteen.SevenFold.quadraticB x y ^ 2 =
      4 * Fermat.Thirteen.SevenFold.phi26 x y

theorem presenceClaim_checked : presenceClaim :=
  Fermat.Thirteen.SevenFold.quadratic_fold

def alignmentClaim : Prop :=
  Fermat.HoldsAt 13 ↔ FermatLastTheoremWith ℤ 13

theorem alignmentClaim_checked : alignmentClaim :=
  fermatLastTheoremFor_iff_int

/-- Class-number regularity, together with the formal Lamé–Kummer bridge.
This is the first settling certificate. -/
def agencyClaim : Prop :=
  IsRegularPrime 13 ∧ (IsRegularPrime 13 → Fermat.HoldsAt 13)

theorem agencyClaim_checked : agencyClaim := by
  refine ⟨Fermat.Thirteen.SevenFold.classNumber_branch, ?_⟩
  intro hregular
  exact @flt_regular 13 ⟨Nat.prime_thirteen⟩ hregular (by omega)

/-- The five low Bernoulli indices are checked directly by finite
Faulhaber power sums, independently of the class-number branch. -/
def flexibilityClaim : Prop :=
  BernoulliNumeratorRegular 13

theorem flexibilityClaim_checked : flexibilityClaim :=
  Fermat.Thirteen.SevenFold.bernoulliNumeratorRegular_thirteen

def trace : CaseTrace 13 where
  awareness_substrate := ⟨awarenessClaim, awarenessClaim_checked⟩
  structure_algebra := ⟨structureClaim, structureClaim_checked⟩
  sharpening_analysis := ⟨sharpeningClaim, sharpeningClaim_checked⟩
  presence_geometry := ⟨presenceClaim, presenceClaim_checked⟩
  alignment_logic := ⟨alignmentClaim, alignmentClaim_checked⟩
  agency_arithmetic := ⟨agencyClaim, agencyClaim_checked⟩
  flexibility_potential := ⟨flexibilityClaim, flexibilityClaim_checked⟩
  conclude := by
    intro _ _ _ _ _ hRegular _
    exact .contradicted (hRegular.2 hRegular.1)

def run : Checked 13 where
  folds := sevenFolds 13
  trace := trace

def measured : Measured 13 :=
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

end Fermat.Ladder.Thirteen
