import Fermat.Ladder.Eight
import Fermat.Ladder.Eleven
import Fermat.Ladder.Five
import Fermat.Ladder.Four
import Fermat.Ladder.Fourteen
import Fermat.Ladder.Nine
import Fermat.Ladder.One
import Fermat.Ladder.Seven
import Fermat.Ladder.Six
import Fermat.Ladder.Ten
import Fermat.Ladder.Thirteen
import Fermat.Ladder.Three
import Fermat.Ladder.Twelve
import Fermat.Ladder.Two

/-!
# The measured seven-fold response curve

Each point carries its checked ladder run as well as its public, one-based
exit depth.  Thus `responseData` is not a detached table: every coordinate
is tied by `depth_coherent` to the schedule of the corresponding exponent.

The first five points form the diagonal ramp.  Exponents `7`, `11`, and `13`
form the arithmetic plateau at depth six, while exponents having a solved
proper divisor leave at the substrate fold.  Exponent four is the instructive
composite exception: its only prime divisor is exponent two, which passes the
ladder instead of being contradicted.
-/

namespace Fermat.Ladder.Response

open Matrix

/-- One kernel-checked sample of the ladder's response function. -/
structure Point where
  exponent : ℕ
  measured : Measured exponent
  exitDepth : ℕ
  depth_coherent : measured.exitDepth = exitDepth

/-- Package a measured run and its case-local machine-readable depth. -/
def mkPoint {n : ℕ} (measured : Measured n) (exitDepth : ℕ)
    (depth_coherent : measured.exitDepth = exitDepth) : Point where
  exponent := n
  measured := measured
  exitDepth := exitDepth
  depth_coherent := depth_coherent

namespace Point

theorem exitDepth_pos (point : Point) : 0 < point.exitDepth := by
  rw [← point.depth_coherent]
  exact point.measured.exitDepth_pos

theorem exitDepth_le_seven (point : Point) : point.exitDepth ≤ 7 := by
  rw [← point.depth_coherent]
  exact point.measured.exitDepth_le_seven

end Point

def one : Point :=
  mkPoint One.measured One.exitDepth One.exitDepth_eq_measured

def two : Point :=
  mkPoint Two.measured Two.exitDepth Two.exitDepth_eq_measured

def three : Point :=
  mkPoint Three.measured Three.exitDepth Three.exitDepth_eq_measured

def four : Point :=
  mkPoint Four.measured Four.exitDepth Four.exitDepth_eq_measured

def five : Point :=
  mkPoint Five.measured Five.exitDepth Five.exitDepth_eq_measured

def six : Point :=
  mkPoint Six.measured Six.exitDepth Six.exitDepth_eq_measured

def seven : Point :=
  mkPoint Seven.measured Seven.exitDepth Seven.exitDepth_eq_measured

def eight : Point :=
  mkPoint Eight.measured Eight.exitDepth Eight.exitDepth_eq_measured

def nine : Point :=
  mkPoint Nine.measured Nine.exitDepth Nine.exitDepth_eq_measured

def ten : Point :=
  mkPoint Ten.measured Ten.exitDepth Ten.exitDepth_eq_measured

def eleven : Point :=
  mkPoint Eleven.measured Eleven.exitDepth Eleven.exitDepth_eq_measured

def twelve : Point :=
  mkPoint Twelve.measured Twelve.exitDepth Twelve.exitDepth_eq_measured

def thirteen : Point :=
  mkPoint Thirteen.measured Thirteen.exitDepth Thirteen.exitDepth_eq_measured

def fourteen : Point :=
  mkPoint Fourteen.measured Fourteen.exitDepth Fourteen.exitDepth_eq_measured

/-- The fourteen checked samples, in exponent order. -/
def responseCurve : List Point :=
  [one, two, three, four, five, six, seven, eight, nine, ten, eleven,
    twelve, thirteen, fourteen]

/-- Forget the proof payload while retaining the empirical coordinates. -/
def coordinates (points : List Point) : List (ℕ × ℕ) :=
  points.map fun point ↦ (point.exponent, point.exitDepth)

/-- The generator-search-friendly projection of `responseCurve`. -/
def responseData : List (ℕ × ℕ) :=
  coordinates responseCurve

/-- The battery response as an actual finite function.  Index `0` records
exponent `1`, and in general index `i` records exponent `i + 1`. -/
def exitDepthFunction : Fin 14 → ℕ :=
  ![One.exitDepth, Two.exitDepth, Three.exitDepth, Four.exitDepth,
    Five.exitDepth, Six.exitDepth, Seven.exitDepth, Eight.exitDepth,
    Nine.exitDepth, Ten.exitDepth, Eleven.exitDepth, Twelve.exitDepth,
    Thirteen.exitDepth, Fourteen.exitDepth]

theorem exitDepthFunction_values : List.ofFn exitDepthFunction =
    [1, 2, 3, 4, 5, 1, 6, 1, 1, 1, 6, 1, 6, 1] :=
  rfl

/-- The functional and proof-carrying presentations have identical depth
coordinates. -/
theorem responseData_depths :
    responseData.map Prod.snd = List.ofFn exitDepthFunction :=
  rfl

theorem responseCurve_length : responseCurve.length = 14 := rfl

/-- The exact first measured law of the seven-fold battery. -/
theorem responseData_eq : responseData =
    [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 1), (7, 6),
      (8, 1), (9, 1), (10, 1), (11, 6), (12, 1), (13, 6), (14, 1)] :=
  rfl

/-- Samples whose solved proper divisor is already visible at the substrate
fold. -/
def solvedDivisorPoints : List Point :=
  [six, eight, nine, ten, twelve, fourteen]

/-- The post-ramp prime samples that settle at executed arithmetic. -/
def arithmeticPlateauPoints : List Point :=
  [seven, eleven, thirteen]

/-- The response decomposes into its diagonal ramp, substrate exits, and
depth-six arithmetic plateau. -/
theorem response_shape :
    responseData.take 5 = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5)] ∧
      coordinates solvedDivisorPoints =
        [(6, 1), (8, 1), (9, 1), (10, 1), (12, 1), (14, 1)] ∧
      coordinates arithmeticPlateauPoints = [(7, 6), (11, 6), (13, 6)] :=
  ⟨rfl, rfl, rfl⟩

/-- Four does not inherit a contradiction at the substrate layer because
its divisor `2` is a passing exponent. -/
theorem four_is_the_composite_exception :
    Four.exitDepth = 4 ∧ 2 ∣ 4 ∧ ¬ Fermat.HoldsAt 2 :=
  ⟨rfl, by norm_num, not_fermatLastTheoremFor_two⟩

end Fermat.Ladder.Response
