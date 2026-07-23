import Fermat.Ladder.Basic
import Fermat.ThirtySeven.CircularUnitCertificate
import Fermat.ThirtySeven.FirstCase
import Fermat.ThirtySeven.NeighborFolding
import Fermat.ThirtySeven.VandiverData
import Fermat.ThirtySeven.VandiverHistoricalAssembly37

/-!
# Seven-fold ladder trace for exponent 37

The first six folds retain the finite and decompressed structure of the
uploaded exponent-`37` proof: the auxiliary prime, quadratic and cubic
neighbor folds, and the two Sophie--Germain residue conditions.  Fold seven
reuses the kernel-checked Bernoulli, circular-unit, and historical
Takagi--Furtwängler/Vandiver proof.

The measured run is additionally packaged as `proofBacked`, tying its
contradicted outcome to `Fermat.ThirtySeven.holdsAt_thirtySeven`.
-/

namespace Fermat.Ladder.ThirtySeven

open Fermat.ThirtySeven
open Fermat.ThirtySeven.NeighborFolding

def awarenessClaim : Prop :=
  Nat.Prime 37 ∧ Nat.Prime 149 ∧ 149 = 4 * 37 + 1

theorem awarenessClaim_checked : awarenessClaim := by
  norm_num [awarenessClaim]

/-- The direct `36 → 18` quadratic-period fold. -/
def structureClaim : Prop :=
  ∀ x y : ℤ, A37 x y ^ 2 - 37 * B37 x y ^ 2 = 4 * phi74 x y

theorem structureClaim_checked : structureClaim :=
  quadratic_fold

/-- The older exponent-`13` coordinate occurs literally in the quadratic
coordinate at exponent `37`. -/
def sharpeningClaim : Prop :=
  ∀ x y : ℤ, B37 x y = B13 x y * Q12 x y

theorem sharpeningClaim_checked : sharpeningClaim :=
  B37_eq_B13_mul_Q12

/-- The independent index-three Gaussian-period norm fold. -/
def presenceClaim : Prop :=
  ∀ x y : ℤ,
    cubicNorm (cubicP0 x y) (cubicP1 x y) (cubicP2 x y) = phi74 x y

theorem presenceClaim_checked : presenceClaim :=
  cubic_fold

/-- The cubic coordinate exposes the older exponent-`11` and exponent-`7`
factors in one exact identity. -/
def alignmentClaim : Prop :=
  ∀ x y : ℤ,
    cubicP1Quotient x y + phi22 x y = 2 * R4 x y * psi7 x y

theorem alignmentClaim_checked : alignmentClaim :=
  cubicP1_contains_eleven_and_seven

/-- The auxiliary prime `149` eliminates the first case. -/
def agencyClaim : Prop :=
  Fermat.SophieGermain.NoConsecutivePowers 37 149 ∧
    Fermat.SophieGermain.ExponentNotPower 37 149

theorem agencyClaim_checked : agencyClaim :=
  ⟨noConsecutivePowers_37_149, exponentNotPower_37_149⟩

/-- Fold seven carries the unique irregular Bernoulli channel, the
nonsingular `17 × 17` circular-unit matrix, and the completed historical
second-case proof. -/
def flexibilityClaim : Prop :=
  Fermat.Irregular.VandiverData.BernoulliCubeCondition 37 ∧
    Fermat.ThirtySeven.CircularUnitCertificate.matrix.det ≠ 0 ∧
    Fermat.SecondCaseExcluded 37

theorem flexibilityClaim_checked : flexibilityClaim :=
  ⟨Fermat.ThirtySeven.VandiverData.bernoulliCubeCondition_thirtySeven_via_kummer,
    Fermat.ThirtySeven.CircularUnitCertificate.matrix_det_ne_zero,
    Fermat.ThirtySeven.secondCaseExcluded_thirtySeven⟩

def trace : CaseTrace 37 where
  awareness_substrate := ⟨awarenessClaim, awarenessClaim_checked⟩
  structure_algebra := ⟨structureClaim, structureClaim_checked⟩
  sharpening_analysis := ⟨sharpeningClaim, sharpeningClaim_checked⟩
  presence_geometry := ⟨presenceClaim, presenceClaim_checked⟩
  alignment_logic := ⟨alignmentClaim, alignmentClaim_checked⟩
  agency_arithmetic := ⟨agencyClaim, agencyClaim_checked⟩
  flexibility_potential := ⟨flexibilityClaim, flexibilityClaim_checked⟩
  conclude := by
    intro _ _ _ _ _ hfirst hhistorical
    exact .contradicted
      (Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
        (by norm_num) (by norm_num) (by norm_num)
        hfirst.1 hfirst.2 hhistorical.2.2)

def run : Checked 37 where
  folds := sevenFolds 37
  trace := trace

def measured : Measured 37 :=
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

/-- Public reuse of the completed fixed-exponent theorem. -/
theorem holdsAt_thirtySeven : Fermat.HoldsAt 37 :=
  Fermat.ThirtySeven.holdsAt_thirtySeven

/-- The measured ladder verdict and the campaign theorem are the same
kernel-checked contradiction payload. -/
def proofBacked : ProofBacked 37 where
  measured := measured
  holds := holdsAt_thirtySeven
  outcome_eq := by
    change Outcome.contradicted _ = Outcome.contradicted _
    rfl

end Fermat.Ladder.ThirtySeven
