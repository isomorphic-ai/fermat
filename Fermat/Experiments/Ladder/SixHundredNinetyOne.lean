import Fermat.Exponents.SixHundredNinetyOne.CircularUnitCertificate
import Fermat.Exponents.SixHundredNinetyOne.FirstCase
import Fermat.Exponents.SixHundredNinetyOne.SecondCase
import Fermat.Exponents.SixHundredNinetyOne.VandiverData
import Fermat.Experiments.Ladder.Basic

/-!
# Seven-fold ladder trace for exponent 691

The first six folds retain the finite structure of the uploaded paired
four-digit folding package: the auxiliary-prime relation, the
sixteenth-root residue sheet, the two candidate irregular channels `12`
and `200`, their lifted Bernoulli certificates, and the complete
Sophie--Germain first-case obstruction.

Fold seven combines the Bernoulli condition, the nonsingular `344 × 344`
circular-unit matrix, and the completed Takagi--Furtwängler/Vandiver
descent. Its contradiction payload reuses the already-proved
fixed-exponent theorem.
-/

namespace Fermat.Ladder.SixHundredNinetyOne

set_option exponentiation.threshold 700

def awarenessClaim : Prop :=
  Nat.Prime 691 ∧ Nat.Prime 11057 ∧ 11057 = 16 * 691 + 1

theorem awarenessClaim_checked : awarenessClaim :=
  ⟨Fermat.SixHundredNinetyOne.prime_691,
    Fermat.SixHundredNinetyOne.prime_11057,
    Fermat.SixHundredNinetyOne.auxiliaryPrimeRelation⟩

/-- Every nonzero `691`st power modulo the auxiliary prime lies on the
sixteenth-root residue sheet. -/
def structureClaim : Prop :=
  ∀ {x : ZMod 11057}, x ≠ 0 →
    (x ^ 691) ^ 16 = 1

theorem structureClaim_checked : structureClaim :=
  Fermat.SixHundredNinetyOne.pow_691_pow_sixteen_eq_one

/-- The compact Voronoi scan leaves only the two candidate irregular
channels. -/
def sharpeningClaim : Prop :=
  Fermat.SixHundredNinetyOne.HighBernoulli.CompleteIrregularScan

theorem sharpeningClaim_checked : sharpeningClaim :=
  Fermat.SixHundredNinetyOne.IrregularScan.completeIrregularScan

/-- Both lifted irregular channels have valuation strictly below three. -/
def presenceClaim : Prop :=
  ¬(691 : ℤ) ^ 3 ∣ (bernoulli 8292).num ∧
    ¬(691 : ℤ) ^ 3 ∣ (bernoulli 138200).num

theorem presenceClaim_checked : presenceClaim :=
  ⟨Fermat.SixHundredNinetyOne.HighBernoulli.bernoulli_8292_numerator_not_dvd_cube,
    Fermat.SixHundredNinetyOne.HighBernoulli.bernoulli_138200_numerator_not_dvd_cube⟩

def alignmentClaim : Prop :=
  Fermat.HoldsAt 691 ↔ FermatLastTheoremWith ℤ 691

theorem alignmentClaim_checked : alignmentClaim :=
  fermatLastTheoremFor_iff_int

/-- The auxiliary prime `11057` eliminates the first case. -/
def agencyClaim : Prop :=
  Fermat.SophieGermain.NoConsecutivePowers 691 11057 ∧
    Fermat.SophieGermain.ExponentNotPower 691 11057

theorem agencyClaim_checked : agencyClaim :=
  ⟨Fermat.SixHundredNinetyOne.noConsecutivePowers_691_11057,
    Fermat.SixHundredNinetyOne.exponentNotPower_691_11057⟩

/-- Fold seven contains the complete finite Bernoulli condition, the
nonsingular circular-unit matrix, and the unconditional historical
second-case exclusion. -/
def flexibilityClaim : Prop :=
  Fermat.Irregular.VandiverData.BernoulliCubeCondition 691 ∧
    Fermat.SixHundredNinetyOne.CircularUnitMatrix.matrix.det ≠ 0 ∧
    Fermat.SecondCaseExcluded 691

theorem flexibilityClaim_checked : flexibilityClaim :=
  ⟨Fermat.SixHundredNinetyOne.VandiverData.bernoulliCubeCondition_sixHundredNinetyOne,
    Fermat.SixHundredNinetyOne.CircularUnitCertificate.matrix_det_ne_zero,
    Fermat.SixHundredNinetyOne.secondCaseExcluded_sixHundredNinetyOne⟩

def trace : CaseTrace 691 where
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
        Fermat.SixHundredNinetyOne.prime_691 (by norm_num)
        Fermat.SixHundredNinetyOne.prime_11057
        hfirst.1 hfirst.2 hfinite.2.2)

def run : Checked 691 where
  folds := sevenFolds 691
  trace := trace

/-- Public reuse of the completed fixed-exponent theorem. -/
theorem holdsAt_sixHundredNinetyOne :
    Fermat.HoldsAt 691 :=
  Fermat.SixHundredNinetyOne.holdsAt_sixHundredNinetyOne

/-- Any ladder outcome at an exponent already known to satisfy FLT must be
the contradiction outcome; a pass witness would violate that theorem. -/
private theorem outcome_eq_contradicted_of_holds
    (outcome : Outcome 691) (holds : Fermat.HoldsAt 691) :
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
def measured : Measured 691 where
  run := run
  schedule :=
    ExitSchedule.atFold ⟨6, by decide⟩
      (.contradicted holdsAt_sixHundredNinetyOne)
  outcome_coherent :=
    (outcome_eq_contradicted_of_holds run.outcome
      holdsAt_sixHundredNinetyOne).symm

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
historical proof at exponent `691`. -/
def proofBacked : ProofBacked 691 where
  measured := measured
  holds := holdsAt_sixHundredNinetyOne
  outcome_eq :=
    outcome_eq_contradicted_of_holds measured.run.outcome
      holdsAt_sixHundredNinetyOne

end Fermat.Ladder.SixHundredNinetyOne
