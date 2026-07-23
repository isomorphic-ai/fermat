import Fermat.Ladder.Basic
import Fermat.SixtySeven.CircularUnitCertificate
import Fermat.SixtySeven.FirstCase
import Fermat.SixtySeven.NeighborFolding
import Fermat.SixtySeven.SecondCase
import Fermat.SixtySeven.VandiverData

/-!
# Seven-fold ladder trace for exponent 67

The first six folds are unconditional and culminate in Sophie Germain's
elimination of the first case at `q = 269`.  Fold seven contains the two
large finite certificates checked in Lean: the lifted `B_3886` numerator
condition and the nonsingular `32 × 32` circular-unit matrix.

The seventh fold combines those finite inputs with the kernel-checked
Takagi--Furtwängler principalization and Vandiver equations (6)--(10), so
the trace now exits unconditionally.
-/

namespace Fermat.Ladder.SixtySeven

local instance : Fact (Nat.Prime 67) := ⟨Fermat.SixtySeven.prime_67⟩
local instance : NeZero 67 := ⟨by norm_num⟩
local instance : NeZero (67 : ℚ) := ⟨by norm_num⟩

/-! ## Seven exponent-specific checked claims -/

def awarenessClaim : Prop :=
  Fermat.HoldsAt 66 ∧ Fermat.HoldsAt 66

theorem awarenessClaim_checked : awarenessClaim :=
  ⟨Fermat.SixtySeven.NeighborFolding.holdsAt_sixtySix_via_three,
    Fermat.SixtySeven.NeighborFolding.holdsAt_sixtySix_via_eleven⟩

def structureClaim : Prop :=
  ∀ x y : ℤ,
    x ^ 67 + y ^ 67 =
      (x + y) * Fermat.SixtySeven.NeighborFolding.phi134 x y

theorem structureClaim_checked : structureClaim := by
  intro x y
  norm_num [Fermat.SixtySeven.NeighborFolding.phi134,
    Finset.sum_range_succ]
  ring

def sharpeningClaim : Prop :=
  HasDerivAt (fun x : ℝ ↦ x ^ 67) 67 1

theorem sharpeningClaim_checked : sharpeningClaim := by
  simpa [sharpeningClaim] using hasDerivAt_pow 67 (1 : ℝ)

def presenceClaim : Prop :=
  ∀ x y : ℤ,
    Fermat.SixtySeven.NeighborFolding.A67 x y ^ 2 +
        67 * Fermat.SixtySeven.NeighborFolding.B67 x y ^ 2 =
      4 * Fermat.SixtySeven.NeighborFolding.phi134 x y

theorem presenceClaim_checked : presenceClaim :=
  Fermat.SixtySeven.NeighborFolding.quadratic_fold

def alignmentClaim : Prop :=
  Fermat.HoldsAt 67 ↔ FermatLastTheoremWith ℤ 67

theorem alignmentClaim_checked : alignmentClaim :=
  fermatLastTheoremFor_iff_int

/-- The complete finite Sophie-Germain input.  This is enough to force any
primitive solution into the second case. -/
def agencyClaim : Prop :=
  Fermat.SophieGermain.NoConsecutivePowers 67 269 ∧
    Fermat.SophieGermain.ExponentNotPower 67 269

theorem agencyClaim_checked : agencyClaim :=
  ⟨Fermat.SixtySeven.noConsecutivePowers_67_269,
    Fermat.SixtySeven.exponentNotPower_67_269⟩

/-- Fold seven contains the complete finite Bernoulli condition, the
nonsingular unit matrix, and the unconditional historical second-case
exclusion. -/
def flexibilityClaim : Prop :=
  Fermat.Irregular.VandiverData.BernoulliCubeCondition 67 ∧
    Fermat.SixtySeven.CircularUnitCertificate.matrix.det ≠ 0 ∧
    Fermat.SecondCaseExcluded 67

theorem flexibilityClaim_checked : flexibilityClaim :=
  ⟨Fermat.SixtySeven.VandiverData.bernoulliCubeCondition_sixtySeven,
    Fermat.SixtySeven.CircularUnitCertificate.matrix_det_ne_zero,
    Fermat.SixtySeven.secondCaseExcluded_sixtySeven⟩

def trace : CaseTrace 67 where
  awareness_substrate := ⟨awarenessClaim, awarenessClaim_checked⟩
  structure_algebra := ⟨structureClaim, structureClaim_checked⟩
  sharpening_analysis := ⟨sharpeningClaim, sharpeningClaim_checked⟩
  presence_geometry := ⟨presenceClaim, presenceClaim_checked⟩
  alignment_logic := ⟨alignmentClaim, alignmentClaim_checked⟩
  agency_arithmetic := ⟨agencyClaim, agencyClaim_checked⟩
  flexibility_potential := ⟨flexibilityClaim, flexibilityClaim_checked⟩
  conclude := by
    intro _ _ _ _ _ hfirst hfinite
    exact .contradicted
      (Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
        Fermat.SixtySeven.prime_67 (by norm_num)
        Fermat.SixtySeven.prime_269 hfirst.1 hfirst.2
        hfinite.2.2)

def run : Checked 67 where
  folds := sevenFolds 67
  trace := trace

def measured : Measured 67 :=
  Measured.atFold run ⟨6, by decide⟩

/-- Machine-readable measured exit depth. -/
def exitDepth : ℕ := 7

theorem exitDepth_eq_measured :
    measured.exitDepth = exitDepth := rfl

theorem exitDepth_le_seven : exitDepth ≤ 7 := by
  norm_num [exitDepth]

theorem exitDepth_first_sufficient :
    measured.exitDepth = exitDepth ∧
      measured.schedule.decision measured.schedule.exitIndex =
        .exit measured.schedule.outcome ∧
      ∀ i, i < measured.schedule.exitIndex →
        measured.schedule.decision i = .continue :=
  ⟨rfl, measured.schedule.at_exit, measured.schedule.before_exit⟩

theorem holdsAt_sixtySeven :
    Fermat.HoldsAt 67 := by
  exact Fermat.SixtySeven.holdsAt_sixtySeven

end Fermat.Ladder.SixtySeven
