import Fermat.Ladder.Basic
import Fermat.FiveHundredEightySeven.CircularUnitCertificate
import Fermat.FiveHundredEightySeven.FirstCase
import Fermat.FiveHundredEightySeven.SecondCase
import Fermat.FiveHundredEightySeven.VandiverData

/-!
# Seven-fold ladder trace for exponent 587

The first six folds retain the finite structure of the uploaded safe-prime
package: the auxiliary-prime relation, the order-fourteen residue sheet,
the exact irregular channels `90` and `92`, their lifted Bernoulli
certificates, and the complete Sophie--Germain first-case obstruction.

Fold seven combines the Bernoulli condition, the nonsingular `292 × 292`
circular-unit matrix, and the completed historical
Takagi--Furtwängler/Vandiver descent.  Its contradiction payload reuses the
already-proved fixed-exponent theorem.
-/

namespace Fermat.Ladder.FiveHundredEightySeven

def awarenessClaim : Prop :=
  Nat.Prime 587 ∧ Nat.Prime 8219 ∧ 8219 = 14 * 587 + 1

theorem awarenessClaim_checked : awarenessClaim :=
  ⟨Fermat.FiveHundredEightySeven.prime_587,
    Fermat.FiveHundredEightySeven.prime_8219,
    Fermat.FiveHundredEightySeven.auxiliaryPrimeRelation⟩

/-- Every nonzero `587`th power modulo the auxiliary prime lies on the
order-fourteen residue sheet. -/
def structureClaim : Prop :=
  ∀ {x : ZMod 8219}, x ≠ 0 → (x ^ 587) ^ 14 = 1

theorem structureClaim_checked : structureClaim :=
  Fermat.FiveHundredEightySeven.pow_587_pow_fourteen_eq_one

/-- The compact Voronoi scan leaves exactly the two historical irregular
channels. -/
def sharpeningClaim : Prop :=
  Fermat.FiveHundredEightySeven.IrregularScan.irregularIndices 587 =
    {90, 92}

theorem sharpeningClaim_checked : sharpeningClaim :=
  Fermat.FiveHundredEightySeven.IrregularScan.irregularIndices_587

/-- Both lifted irregular channels have valuation strictly below three. -/
def presenceClaim : Prop :=
  ¬(587 : ℤ) ^ 3 ∣ (bernoulli 52830).num ∧
    ¬(587 : ℤ) ^ 3 ∣ (bernoulli 54004).num

theorem presenceClaim_checked : presenceClaim :=
  ⟨Fermat.FiveHundredEightySeven.HighBernoulli.bernoulli_52830_numerator_not_dvd_cube,
    Fermat.FiveHundredEightySeven.HighBernoulli.bernoulli_54004_numerator_not_dvd_cube⟩

def alignmentClaim : Prop :=
  Fermat.HoldsAt 587 ↔ FermatLastTheoremWith ℤ 587

theorem alignmentClaim_checked : alignmentClaim :=
  fermatLastTheoremFor_iff_int

/-- The auxiliary prime `8219` eliminates the first case. -/
def agencyClaim : Prop :=
  Fermat.SophieGermain.NoConsecutivePowers 587 8219 ∧
    Fermat.SophieGermain.ExponentNotPower 587 8219

theorem agencyClaim_checked : agencyClaim :=
  ⟨Fermat.FiveHundredEightySeven.noConsecutivePowers_587_8219,
    Fermat.FiveHundredEightySeven.exponentNotPower_587_8219⟩

/-- Fold seven contains the complete finite Bernoulli condition, the
nonsingular circular-unit matrix, and the unconditional historical
second-case exclusion. -/
def flexibilityClaim : Prop :=
  Fermat.Irregular.VandiverData.BernoulliCubeCondition 587 ∧
    Fermat.FiveHundredEightySeven.CircularUnitMatrix.matrix.det ≠ 0 ∧
    Fermat.SecondCaseExcluded 587

theorem flexibilityClaim_checked : flexibilityClaim :=
  ⟨Fermat.FiveHundredEightySeven.VandiverData.bernoulliCubeCondition_fiveHundredEightySeven,
    Fermat.FiveHundredEightySeven.CircularUnitCertificate.matrix_det_ne_zero,
    Fermat.FiveHundredEightySeven.secondCaseExcluded_fiveHundredEightySeven⟩

def trace : CaseTrace 587 where
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
        Fermat.FiveHundredEightySeven.prime_587 (by norm_num)
        Fermat.FiveHundredEightySeven.prime_8219
        hfirst.1 hfirst.2 hfinite.2.2)

def run : Checked 587 where
  folds := sevenFolds 587
  trace := trace

def measured : Measured 587 :=
  Measured.atFold run ⟨6, by decide⟩

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

/-- Public reuse of the completed fixed-exponent theorem. -/
theorem holdsAt_fiveHundredEightySeven :
    Fermat.HoldsAt 587 :=
  Fermat.FiveHundredEightySeven.holdsAt_fiveHundredEightySeven

/-- The measured ladder verdict is explicitly backed by the completed
historical proof at exponent `587`. -/
def proofBacked : ProofBacked 587 where
  measured := measured
  holds := holdsAt_fiveHundredEightySeven
  outcome_eq := by
    change Outcome.contradicted _ = Outcome.contradicted _
    rfl

end Fermat.Ladder.FiveHundredEightySeven
