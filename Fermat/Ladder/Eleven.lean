import Fermat.Eleven.SevenFold
import Fermat.Ladder.Basic

/-!
# Seven-fold ladder trace for exponent eleven

The class-number-one / regular-prime branch first settles the exponent at
arithmetic fold six.  The direct finite Faulhaber certificate remains
checked at fold seven as an independent decompressed alternative.
-/

namespace Fermat.Ladder.Eleven

open Fermat.Regular.Faulhaber

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- Both neighboring composite exponents are already closed. -/
def awarenessClaim : Prop :=
  Fermat.HoldsAt 10 ∧ Fermat.HoldsAt 12

theorem awarenessClaim_checked : awarenessClaim :=
  ⟨Fermat.Eleven.SevenFold.holdsAt_ten,
    Fermat.Eleven.SevenFold.holdsAt_twelve⟩

/-- The exact odd-power cofactor around the exponent-eleven circle. -/
def structureClaim : Prop :=
  ∀ x y : ℤ,
    x ^ 11 + y ^ 11 =
      (x + y) * Fermat.Eleven.SevenFold.phi22 x y

theorem structureClaim_checked : structureClaim := by
  intro x y
  norm_num [Fermat.Eleven.SevenFold.phi22, Finset.sum_range_succ]
  ring

def sharpeningClaim : Prop :=
  HasDerivAt (fun x : ℝ ↦ x ^ 11) 11 1

theorem sharpeningClaim_checked : sharpeningClaim := by
  simpa [sharpeningClaim] using hasDerivAt_pow 11 (1 : ℝ)

/-- The exact norm identity in the quadratic-period crease. -/
def presenceClaim : Prop :=
  ∀ x y : ℤ,
    Fermat.Eleven.SevenFold.quadraticA x y ^ 2 +
        11 * Fermat.Eleven.SevenFold.quadraticB x y ^ 2 =
      4 * Fermat.Eleven.SevenFold.phi22 x y

theorem presenceClaim_checked : presenceClaim :=
  Fermat.Eleven.SevenFold.quadratic_fold

def alignmentClaim : Prop :=
  Fermat.HoldsAt 11 ↔ FermatLastTheoremWith ℤ 11

theorem alignmentClaim_checked : alignmentClaim :=
  fermatLastTheoremFor_iff_int

/-- Class-number regularity, together with the formal Lamé–Kummer bridge.
This is the first settling certificate. -/
def agencyClaim : Prop :=
  IsRegularPrime 11 ∧ (IsRegularPrime 11 → Fermat.HoldsAt 11)

theorem agencyClaim_checked : agencyClaim := by
  refine ⟨Fermat.Eleven.SevenFold.classNumber_branch, ?_⟩
  intro hregular
  exact @flt_regular 11 ⟨Nat.prime_eleven⟩ hregular (by omega)

/-- The four low Bernoulli indices are checked directly by finite
Faulhaber power sums, independently of the class-number branch. -/
def flexibilityClaim : Prop :=
  BernoulliNumeratorRegular 11

theorem flexibilityClaim_checked : flexibilityClaim :=
  Fermat.Eleven.SevenFold.bernoulliNumeratorRegular_eleven

def trace : CaseTrace 11 where
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

def run : Checked 11 where
  folds := sevenFolds 11
  trace := trace

def measured : Measured 11 :=
  Measured.atFold run ⟨5, by decide⟩

/-- The regular-prime arithmetic branch first settles the ladder. -/
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

end Fermat.Ladder.Eleven
