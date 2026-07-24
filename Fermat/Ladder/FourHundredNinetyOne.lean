import Fermat.FourHundredNinetyOne.CircularUnitCertificate
import Fermat.FourHundredNinetyOne.FirstCase
import Fermat.FourHundredNinetyOne.SecondCase
import Fermat.FourHundredNinetyOne.VandiverData
import Fermat.Ladder.Basic

/-!
# Seven-fold ladder trace for exponent 491

The first six folds retain the finite structure of the uploaded three-loop
package: the auxiliary-prime relation, the order-two residue sheet, the three
candidate irregular channels `292`, `336`, and `338`, their lifted Bernoulli
certificates, and the complete Sophie--Germain first-case obstruction.

Fold seven combines the Bernoulli condition, the nonsingular `244 × 244`
circular-unit matrix, and the completed Takagi--Furtwängler/Vandiver
descent. Its contradiction payload reuses the
already-proved fixed-exponent theorem.
-/

namespace Fermat.Ladder.FourHundredNinetyOne

def awarenessClaim : Prop :=
  Nat.Prime 491 ∧ Nat.Prime 983 ∧ 983 = 2 * 491 + 1

theorem awarenessClaim_checked : awarenessClaim :=
  ⟨Fermat.FourHundredNinetyOne.prime_491,
    Fermat.FourHundredNinetyOne.prime_983,
    Fermat.FourHundredNinetyOne.auxiliaryPrimeRelation⟩

/-- Every nonzero `491`st power modulo the auxiliary prime lies on the
order-two residue sheet. -/
def structureClaim : Prop :=
  ∀ {x : ZMod 983}, x ≠ 0 →
    x ^ 491 = 1 ∨ x ^ 491 = -1

theorem structureClaim_checked : structureClaim :=
  Fermat.FourHundredNinetyOne.pow_491_eq_one_or_neg_one

/-- The compact Voronoi scan leaves only the three candidate irregular
channels. -/
def sharpeningClaim : Prop :=
  Fermat.FourHundredNinetyOne.HighBernoulli.CompleteIrregularScan

theorem sharpeningClaim_checked : sharpeningClaim :=
  Fermat.FourHundredNinetyOne.IrregularScan.completeIrregularScan

/-- All three lifted irregular channels have valuation strictly below
three. -/
def presenceClaim : Prop :=
  ¬(491 : ℤ) ^ 3 ∣ (bernoulli 143372).num ∧
    ¬(491 : ℤ) ^ 3 ∣ (bernoulli 164976).num ∧
    ¬(491 : ℤ) ^ 3 ∣ (bernoulli 165958).num

theorem presenceClaim_checked : presenceClaim :=
  ⟨Fermat.FourHundredNinetyOne.HighBernoulli.bernoulli_143372_numerator_not_dvd_cube,
    Fermat.FourHundredNinetyOne.HighBernoulli.bernoulli_164976_numerator_not_dvd_cube,
    Fermat.FourHundredNinetyOne.HighBernoulli.bernoulli_165958_numerator_not_dvd_cube⟩

def alignmentClaim : Prop :=
  Fermat.HoldsAt 491 ↔ FermatLastTheoremWith ℤ 491

theorem alignmentClaim_checked : alignmentClaim :=
  fermatLastTheoremFor_iff_int

/-- The auxiliary prime `983` eliminates the first case. -/
def agencyClaim : Prop :=
  Fermat.SophieGermain.NoConsecutivePowers 491 983 ∧
    Fermat.SophieGermain.ExponentNotPower 491 983

theorem agencyClaim_checked : agencyClaim :=
  ⟨Fermat.FourHundredNinetyOne.noConsecutivePowers_491_983,
    Fermat.FourHundredNinetyOne.exponentNotPower_491_983⟩

/-- Fold seven contains the complete finite Bernoulli condition, the
nonsingular circular-unit matrix, and the unconditional historical
second-case exclusion. -/
def flexibilityClaim : Prop :=
  Fermat.Irregular.VandiverData.BernoulliCubeCondition 491 ∧
    Fermat.FourHundredNinetyOne.CircularUnitMatrix.matrix.det ≠ 0 ∧
    Fermat.SecondCaseExcluded 491

theorem flexibilityClaim_checked : flexibilityClaim :=
  ⟨Fermat.FourHundredNinetyOne.VandiverData.bernoulliCubeCondition_fourHundredNinetyOne,
    Fermat.FourHundredNinetyOne.CircularUnitCertificate.matrix_det_ne_zero,
    Fermat.FourHundredNinetyOne.secondCaseExcluded_fourHundredNinetyOne⟩

def trace : CaseTrace 491 where
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
        Fermat.FourHundredNinetyOne.prime_491 (by norm_num)
        Fermat.FourHundredNinetyOne.prime_983
        hfirst.1 hfirst.2 hfinite.2.2)

def run : Checked 491 where
  folds := sevenFolds 491
  trace := trace

/-- Public reuse of the completed fixed-exponent theorem. -/
theorem holdsAt_fourHundredNinetyOne :
    Fermat.HoldsAt 491 :=
  Fermat.FourHundredNinetyOne.holdsAt_fourHundredNinetyOne

/-- Any ladder outcome at an exponent already known to satisfy FLT must be
the contradiction outcome; a pass witness would violate that theorem. -/
private theorem outcome_eq_contradicted_of_holds
    (outcome : Outcome 491) (holds : Fermat.HoldsAt 491) :
    outcome = .contradicted holds := by
  cases outcome with
  | pass witness =>
      exact (holds witness.x witness.y witness.z
        witness.x_ne_zero witness.y_ne_zero witness.z_ne_zero
        witness.equation).elim
  | contradicted _ =>
      rfl

/-- Store the known contradiction as the executable schedule outcome.
The erased coherence proof ties it back to the full causal trace without
forcing evaluation of that large trace when consumers inspect the depth. -/
def measured : Measured 491 where
  run := run
  schedule :=
    ExitSchedule.atFold ⟨6, by decide⟩
      (.contradicted holdsAt_fourHundredNinetyOne)
  outcome_coherent :=
    (outcome_eq_contradicted_of_holds run.outcome
      holdsAt_fourHundredNinetyOne).symm

/-- The first full FLT exit occurs at fold seven: fold six excludes only
the first case, while fold seven closes the historical second case. -/
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

/-- The measured ladder verdict is explicitly backed by the completed
historical proof at exponent `491`. -/
def proofBacked : ProofBacked 491 where
  measured := measured
  holds := holdsAt_fourHundredNinetyOne
  outcome_eq :=
    outcome_eq_contradicted_of_holds measured.run.outcome
      holdsAt_fourHundredNinetyOne

end Fermat.Ladder.FourHundredNinetyOne
