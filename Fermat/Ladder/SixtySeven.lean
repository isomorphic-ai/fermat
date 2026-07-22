import Fermat.Cases
import Fermat.Irregular.VandiverHistoricalDescent
import Fermat.Ladder.Basic
import Fermat.SixtySeven.CircularUnitCertificate
import Fermat.SixtySeven.FirstCase
import Fermat.SixtySeven.NeighborFolding
import Fermat.SixtySeven.VandiverData

/-!
# Seven-fold ladder trace for exponent 67

The first six folds are unconditional and culminate in Sophie Germain's
elimination of the first case at `q = 269`.  Fold seven contains the two
large finite certificates checked in Lean: the lifted `B_3886` numerator
condition and the nonsingular `32 × 32` circular-unit matrix.

The complete verdict is parameterized by one explicitly named historical
bridge collecting Vandiver's three remaining source boundaries; no
class-number or singular-primary implication is smuggled in as a finite
computation.
-/

namespace Fermat.Ladder.SixtySeven

open Fermat.Irregular.VandiverHistoricalDescent

local instance : Fact (Nat.Prime 67) := ⟨Fermat.SixtySeven.prime_67⟩
local instance : NeZero 67 := ⟨by norm_num⟩
local instance : NeZero (67 : ℚ) := ⟨by norm_num⟩

/-! ## The exact remaining historical boundary -/

abbrev CyclotomicField67 := CyclotomicField 67 ℚ

local instance : IsCyclotomicExtension {67} ℚ CyclotomicField67 :=
  CyclotomicField.isCyclotomicExtension 67 ℚ

/-- The exact source boundaries in Vandiver's historical proof: passage
from a rational second-case solution to equation (6), the construction in
equations (7b)--(10b), and Vandiver's Lemma 2.  The well-founded descent
after those inputs is already checked generically. -/
structure HistoricalSecondCaseBridge where
  zeta : CyclotomicField67
  primitive : IsPrimitiveRoot zeta 67
  admissible : HistoricalAdmissibility primitive
  starts : SecondCaseStartsHistoricalDescent primitive admissible
  reduces : EquationsSevenToTenReduction primitive admissible
  lemmaTwo :
    Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo CyclotomicField67 67

theorem secondCaseExcluded_of_historicalBridge
    (hbridge : HistoricalSecondCaseBridge)
    (hBernoulli :
      Fermat.Irregular.VandiverData.BernoulliCubeCondition 67) :
    Fermat.SecondCaseExcluded 67 := by
  exact secondCaseExcluded_of_vandiver_lemmaTwo
    (K := CyclotomicField67) (p := 67)
    (by norm_num) (by norm_num)
    hbridge.primitive hbridge.admissible hbridge.starts hbridge.reduces
    hbridge.lemmaTwo hBernoulli

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

/-- The unconditional finite core at fold seven.  The matrix statement is
deliberately nonsingularity, not the absent conclusion `67 ∤ h⁺`. -/
def flexibilityClaim : Prop :=
  Fermat.Irregular.VandiverData.BernoulliCubeCondition 67 ∧
    Fermat.SixtySeven.CircularUnitCertificate.matrix.det ≠ 0

theorem flexibilityClaim_checked : flexibilityClaim :=
  ⟨Fermat.SixtySeven.VandiverData.bernoulliCubeCondition_sixtySeven,
    Fermat.SixtySeven.CircularUnitCertificate.matrix_det_ne_zero⟩

def trace (hbridge : HistoricalSecondCaseBridge) : CaseTrace 67 where
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
        (secondCaseExcluded_of_historicalBridge hbridge hfinite.1))

def run (hbridge : HistoricalSecondCaseBridge) : Checked 67 where
  folds := sevenFolds 67
  trace := trace hbridge

def measured (hbridge : HistoricalSecondCaseBridge) : Measured 67 :=
  Measured.atFold (run hbridge) ⟨6, by decide⟩

/-- Machine-readable measured exit depth. -/
def exitDepth : ℕ := 7

theorem exitDepth_eq_measured (hbridge : HistoricalSecondCaseBridge) :
    (measured hbridge).exitDepth = exitDepth := rfl

theorem exitDepth_le_seven : exitDepth ≤ 7 := by
  norm_num [exitDepth]

theorem exitDepth_first_sufficient (hbridge : HistoricalSecondCaseBridge) :
    (measured hbridge).exitDepth = exitDepth ∧
      (measured hbridge).schedule.decision
          (measured hbridge).schedule.exitIndex =
        .exit (measured hbridge).schedule.outcome ∧
      ∀ i, i < (measured hbridge).schedule.exitIndex →
        (measured hbridge).schedule.decision i = .continue :=
  ⟨rfl, (measured hbridge).schedule.at_exit,
    (measured hbridge).schedule.before_exit⟩

theorem holdsAt_sixtySeven (hbridge : HistoricalSecondCaseBridge) :
    Fermat.HoldsAt 67 := by
  exact Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    Fermat.SixtySeven.prime_67 (by norm_num)
    Fermat.SixtySeven.prime_269
    Fermat.SixtySeven.noConsecutivePowers_67_269
    Fermat.SixtySeven.exponentNotPower_67_269
    (secondCaseExcluded_of_historicalBridge hbridge
      Fermat.SixtySeven.VandiverData.bernoulliCubeCondition_sixtySeven)

end Fermat.Ladder.SixtySeven
