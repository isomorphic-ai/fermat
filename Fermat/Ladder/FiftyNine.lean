import Fermat.FiftyNine.ArithmeticCertificate
import Fermat.FiftyNine.CircularUnitCertificate
import Fermat.FiftyNine.Folding
import Fermat.FiftyNine.SecondCase
import Fermat.Ladder.Basic

/-!
# Seven-fold ladder trace for exponent 59

The first six folds are unconditional exponent-specific certificates from
the uploaded safe-prime package.  Fold six reaches the complete
Sophie--Germain first-case theorem but cannot settle FLT because `59` is
irregular.  Fold seven exits only after receiving the explicitly named
`OneComponentSecondCaseBridge`; no hidden assumption is placed in an
earlier fold.
-/

namespace Fermat.Ladder.FiftyNine

open Fermat.FiftyNine
open Fermat.FiftyNine.Folding

/-- Neighbor substrate: the right neighbor is already closed in three
ways, while the left neighbor is functorially reduced to exponent `29`. -/
def awarenessClaim : Prop :=
  Fermat.HoldsAt 60 ∧
    (Fermat.HoldsAt 29 → Fermat.HoldsAt 58) ∧
    (59 = 2 * 29 + 1 ∧ 29 = 2 * 14 + 1 ∧ 14 = 2 * 7)

theorem awarenessClaim_checked : awarenessClaim :=
  ⟨holdsAt_sixty_via_three, holdsAt_fiftyEight_of_twentyNine,
    safePrimeLadder⟩

/-- The full `C58` circle and its order-`29` square subgroup. -/
def structureClaim : Prop :=
  orderOf (2 : ZMod 59) = 58 ∧ orderOf (4 : ZMod 59) = 29

theorem structureClaim_checked : structureClaim :=
  ⟨two_order_mod_59, four_order_mod_59⟩

/-- The `g = 2` crease: even discrete logarithms are powers of `4`. -/
def sharpeningClaim : Prop :=
  ∀ j : ℕ, (2 : ZMod 59) ^ (2 * j) = 4 ^ j

theorem sharpeningClaim_checked : sharpeningClaim := by
  intro j
  rw [pow_mul]
  norm_num

/-- The quadratic-period sheet is measured by the norm form of
`ℤ[(1 + sqrt(-59))/2]`. -/
def presenceClaim : Prop :=
  ∀ a b : ℤ, (2 * a + b) ^ 2 + 59 * b ^ 2 = 4 * quadraticNorm a b

theorem presenceClaim_checked : presenceClaim :=
  quadraticNorm_discriminant

/-- The old exponent-`11` coordinate occurs literally in the new
degree-`28` square-root coordinate. -/
def alignmentClaim : Prop :=
  ∀ x y : ℤ, B59 x y = B11 x y * Q24 x y

theorem alignmentClaim_checked : alignmentClaim :=
  B59_eq_B11_mul_Q24

/-- The successful `14`-channel at `827` completes the first-case branch.
This is substantial progress, but it is not yet the full FLT verdict. -/
def agencyClaim : Prop :=
  ∀ {x y z : ℤ},
    IsCoprime x y → IsCoprime y z → IsCoprime x z →
    x ^ 59 + y ^ 59 = z ^ 59 →
      (59 : ℤ) ∣ x ∨ (59 : ℤ) ∣ y ∨ (59 : ℤ) ∣ z

theorem agencyClaim_checked : agencyClaim := by
  intro x y z hxy hyz hxz hfermat
  exact firstCase_of_pairwise_coprime hxy hyz hxz hfermat

/-- Fold seven contains the complete finite Bernoulli condition and the
nonsingular unit matrix.  Only the named global singular-primary bridge is
supplied as a parameter. -/
def flexibilityClaim : Prop :=
  Fermat.Irregular.VandiverData.BernoulliCubeCondition 59 ∧
    Fermat.FiftyNine.CircularUnitCertificate.matrix.det ≠ 0 ∧
    OneComponentSecondCaseBridge

def trace (hsecond : OneComponentSecondCaseBridge) : CaseTrace 59 where
  awareness_substrate := ⟨awarenessClaim, awarenessClaim_checked⟩
  structure_algebra := ⟨structureClaim, structureClaim_checked⟩
  sharpening_analysis := ⟨sharpeningClaim, sharpeningClaim_checked⟩
  presence_geometry := ⟨presenceClaim, presenceClaim_checked⟩
  alignment_logic := ⟨alignmentClaim, alignmentClaim_checked⟩
  agency_arithmetic := ⟨agencyClaim, agencyClaim_checked⟩
  flexibility_potential := ⟨flexibilityClaim,
    Fermat.FiftyNine.ArithmeticCertificate.bernoulliCubeCondition_fiftyNine,
    Fermat.FiftyNine.CircularUnitCertificate.matrix_det_ne_zero,
    hsecond⟩
  conclude := by
    intro _ _ _ _ _ _ hfoldSeven
    exact .contradicted
      (holdsAt_fiftyNine_of_oneComponentSecondCaseBridge hfoldSeven.2.2)

def run (hsecond : OneComponentSecondCaseBridge) : Checked 59 where
  folds := sevenFolds 59
  trace := trace hsecond

def measured (hsecond : OneComponentSecondCaseBridge) : Measured 59 :=
  Measured.atFold (run hsecond) ⟨6, by decide⟩

/-- The package traverses the entire seven-fold battery.  Its first honest
FLT exit is the singular-primary second-case bridge at fold seven. -/
def exitDepth : ℕ := 7

theorem exitDepth_eq_measured (hsecond : OneComponentSecondCaseBridge) :
    (measured hsecond).exitDepth = exitDepth := rfl

theorem exitDepth_le_seven : exitDepth ≤ 7 := by
  norm_num [exitDepth]

theorem exitDepth_first_sufficient (hsecond : OneComponentSecondCaseBridge) :
    (measured hsecond).exitDepth = exitDepth ∧
      (measured hsecond).schedule.decision
          (measured hsecond).schedule.exitIndex =
        .exit (measured hsecond).schedule.outcome ∧
      ∀ i, i < (measured hsecond).schedule.exitIndex →
        (measured hsecond).schedule.decision i = .continue :=
  ⟨rfl, (measured hsecond).schedule.at_exit,
    (measured hsecond).schedule.before_exit⟩

end Fermat.Ladder.FiftyNine
