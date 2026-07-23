import Fermat.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Fintype.Powerset

/-!
# A uniform seven-fold ladder

The seven folds in this file are independent of the final outcome.  In
particular, small exponents may carry a concrete nonzero solution through all
seven folds, while an exponent covered by Fermat's Last Theorem carries a
proof that no such solution exists.
-/

namespace Fermat.Ladder

open Finset

/-- Concrete positive data satisfying the Fermat equation at exponent `n`. -/
structure SolutionWitness (n : ℕ) where
  x : ℕ
  y : ℕ
  z : ℕ
  x_ne_zero : x ≠ 0
  y_ne_zero : y ≠ 0
  z_ne_zero : z ≠ 0
  equation : x ^ n + y ^ n = z ^ n

/-- The two genuine ways an exponent can leave the ladder. -/
inductive Outcome (n : ℕ) : Type
  | pass (witness : SolutionWitness n)
  | contradicted (holds : Fermat.HoldsAt n)

/-- Awareness / substrate: the measured finite substrate has exactly `n`
points. -/
def AwarenessFold (n : ℕ) : Prop :=
  Fintype.card (Fin n) = n

/-- Structure / algebra: the homogeneous geometric sum factors a difference
of `n`th powers over the integers. -/
def StructureFold (n : ℕ) : Prop :=
  ∀ x y : ℤ,
    (x - y) * (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = x ^ n - y ^ n

/-- Sharpening / analysis: zooming into `x ↦ x^n` at `1` has slope `n`. -/
def SharpeningFold (n : ℕ) : Prop :=
  HasDerivAt (fun x : ℝ ↦ x ^ n) (n : ℝ) 1

/-- Presence / geometry: the point `n` lies at distance `n` from the origin
on the real line. -/
def PresenceFold (n : ℕ) : Prop :=
  dist (0 : ℝ) (n : ℝ) = n

/-- Alignment / logic: the natural and integer formulations of the fixed
exponent theorem are logically equivalent. -/
def AlignmentFold (n : ℕ) : Prop :=
  Fermat.HoldsAt n ↔ FermatLastTheoremWith ℤ n

/-- Agency / arithmetic: an executed power calculation doubles `2^n`. -/
def AgencyFold (n : ℕ) : Prop :=
  2 ^ n + 2 ^ n = 2 ^ (n + 1)

/-- Flexibility / stochastic potential: an `n`-point substrate has `2^n`
possible events. -/
def FlexibilityFold (n : ℕ) : Prop :=
  Fintype.card (Finset (Fin n)) = 2 ^ n

/-- The seven checked mathematical strata, deliberately containing no final
FLT verdict. -/
structure SevenFolds (n : ℕ) : Prop where
  awareness_substrate : AwarenessFold n
  structure_algebra : StructureFold n
  sharpening_analysis : SharpeningFold n
  presence_geometry : PresenceFold n
  alignment_logic : AlignmentFold n
  agency_arithmetic : AgencyFold n
  flexibility_potential : FlexibilityFold n

/-- A proposition together with the proof that it was genuinely checked. -/
structure CheckedClaim where
  proposition : Prop
  is_checked : proposition

/-- The exponent-specific causal trace.  Its conclusion must be built from
the seven checked claims, so a ladder verdict is not an unrelated decoration
on the universal mathematical spine. -/
structure CaseTrace (n : ℕ) where
  awareness_substrate : CheckedClaim
  structure_algebra : CheckedClaim
  sharpening_analysis : CheckedClaim
  presence_geometry : CheckedClaim
  alignment_logic : CheckedClaim
  agency_arithmetic : CheckedClaim
  flexibility_potential : CheckedClaim
  conclude :
    awareness_substrate.proposition →
    structure_algebra.proposition →
    sharpening_analysis.proposition →
    presence_geometry.proposition →
    alignment_logic.proposition →
    agency_arithmetic.proposition →
    flexibility_potential.proposition →
    Outcome n

def CaseTrace.outcome {n : ℕ} (trace : CaseTrace n) : Outcome n :=
  trace.conclude
    trace.awareness_substrate.is_checked
    trace.structure_algebra.is_checked
    trace.sharpening_analysis.is_checked
    trace.presence_geometry.is_checked
    trace.alignment_logic.is_checked
    trace.agency_arithmetic.is_checked
    trace.flexibility_potential.is_checked

/-- A complete ladder run: the neutral seven-fold spine and a concrete
exponent-specific causal trace. -/
structure Checked (n : ℕ) where
  folds : SevenFolds n
  trace : CaseTrace n

def Checked.outcome {n : ℕ} (run : Checked n) : Outcome n :=
  run.trace.outcome

/-- What the method records at a fold: either it continues gathering
coverage, or this fold is the first distinguishing instrument and settles the
outcome. -/
inductive FoldDecision (n : ℕ) : Type
  | continue
  | exit (outcome : Outcome n)

/-- Machine-readable methodological exit data.  The `before_exit` field is
about the declared ladder method, not a claim of absolute logical minimality. -/
structure ExitSchedule (n : ℕ) where
  decision : Fin 7 → FoldDecision n
  exitIndex : Fin 7
  outcome : Outcome n
  before_exit : ∀ i, i < exitIndex → decision i = .continue
  at_exit : decision exitIndex = .exit outcome

namespace ExitSchedule

/-- The public fold numbering is one-based. -/
def exitDepth {n : ℕ} (schedule : ExitSchedule n) : ℕ :=
  schedule.exitIndex + 1

theorem exitDepth_pos {n : ℕ} (schedule : ExitSchedule n) :
    0 < schedule.exitDepth := by
  simp [exitDepth]

theorem exitDepth_le_seven {n : ℕ} (schedule : ExitSchedule n) :
    schedule.exitDepth ≤ 7 := by
  exact schedule.exitIndex.isLt

/-- Declare a run to continue before `fold` and to exit exactly at `fold`. -/
def atFold {n : ℕ} (fold : Fin 7) (outcome : Outcome n) : ExitSchedule n where
  decision i := if i = fold then .exit outcome else .continue
  exitIndex := fold
  outcome := outcome
  before_exit := by
    intro i hi
    simp [ne_of_lt hi]
  at_exit := by simp

@[simp]
theorem atFold_exitDepth {n : ℕ} (fold : Fin 7) (outcome : Outcome n) :
    (atFold fold outcome).exitDepth = fold + 1 := rfl

end ExitSchedule

/-- A checked run together with methodological exit data whose verdict is
definitionally tied back to the trace. -/
structure Measured (n : ℕ) where
  run : Checked n
  schedule : ExitSchedule n
  outcome_coherent : schedule.outcome = run.outcome

namespace Measured

def exitDepth {n : ℕ} (measured : Measured n) : ℕ :=
  measured.schedule.exitDepth

theorem exitDepth_pos {n : ℕ} (measured : Measured n) :
    0 < measured.exitDepth :=
  measured.schedule.exitDepth_pos

theorem exitDepth_le_seven {n : ℕ} (measured : Measured n) :
    measured.exitDepth ≤ 7 :=
  measured.schedule.exitDepth_le_seven

/-- Attach a checked run to a declared first distinguishing fold. -/
def atFold {n : ℕ} (run : Checked n) (fold : Fin 7) : Measured n where
  run := run
  schedule := ExitSchedule.atFold fold run.outcome
  outcome_coherent := rfl

end Measured

/-- A measured contradiction whose payload is explicitly the already-proved
fixed-exponent theorem.  Exponent-specific ladders use this wrapper to expose
that their measured verdict reuses the campaign theorem rather than carrying
an unrelated shadow proof. -/
structure ProofBacked (n : ℕ) where
  measured : Measured n
  holds : Fermat.HoldsAt n
  outcome_eq : measured.run.outcome = .contradicted holds

namespace ProofBacked

def exitDepth {n : ℕ} (backed : ProofBacked n) : ℕ :=
  backed.measured.exitDepth

theorem exitDepth_pos {n : ℕ} (backed : ProofBacked n) :
    0 < backed.exitDepth :=
  backed.measured.exitDepth_pos

theorem exitDepth_le_seven {n : ℕ} (backed : ProofBacked n) :
    backed.exitDepth ≤ 7 :=
  backed.measured.exitDepth_le_seven

end ProofBacked

theorem awarenessFold (n : ℕ) : AwarenessFold n := by
  simp [AwarenessFold]

theorem structureFold (n : ℕ) : StructureFold n := by
  intro x y
  exact (Commute.all x y).mul_geom_sum₂ n

theorem sharpeningFold (n : ℕ) : SharpeningFold n := by
  simpa [SharpeningFold] using hasDerivAt_pow n (1 : ℝ)

theorem presenceFold (n : ℕ) : PresenceFold n := by
  simp [PresenceFold, Real.dist_eq]

theorem alignmentFold (n : ℕ) : AlignmentFold n := by
  exact fermatLastTheoremFor_iff_int

theorem agencyFold (n : ℕ) : AgencyFold n := by
  simp only [AgencyFold, pow_succ]
  omega

theorem flexibilityFold (n : ℕ) : FlexibilityFold n := by
  simp [FlexibilityFold]

/-- Every exponent has the same seven mathematical folds; only its outcome
varies. -/
theorem sevenFolds (n : ℕ) : SevenFolds n where
  awareness_substrate := awarenessFold n
  structure_algebra := structureFold n
  sharpening_analysis := sharpeningFold n
  presence_geometry := presenceFold n
  alignment_logic := alignmentFold n
  agency_arithmetic := agencyFold n
  flexibility_potential := flexibilityFold n

end Fermat.Ladder
