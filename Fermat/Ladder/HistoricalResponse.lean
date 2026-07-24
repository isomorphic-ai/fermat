import Fermat.Ladder.FiftyNine
import Fermat.Ladder.FiveHundredEightySeven
import Fermat.Ladder.OneHundredFiftySeven
import Fermat.Ladder.SixtySeven
import Fermat.Ladder.ThirtySeven

/-!
# Proof-backed historical ladder samples

This module is the reusable finite-data interface for the completed
historical campaigns at exponents `37`, `59`, `67`, `157`, and `587`.

Unlike a detached table, every point carries:

* its exponent-specific measured seven-fold run;
* its machine-readable exit depth;
* the already-proved `Fermat.HoldsAt n` theorem; and
* a kernel-checked equality identifying the run's outcome with that theorem.

Generator-search and empirical-response code can therefore consume
`responseData`, while proof-oriented code can retain the dependent
`ProofBacked` payload.
-/

namespace Fermat.Ladder.HistoricalResponse

/-- One completed historical campaign, including both its measured response
and the fixed-exponent theorem reused by that response. -/
structure Point where
  exponent : ℕ
  backed : ProofBacked exponent
  exitDepth : ℕ
  depth_coherent : backed.exitDepth = exitDepth

/-- Package an exponent-specific proof-backed run and its public depth. -/
def mkPoint {n : ℕ} (backed : ProofBacked n) (exitDepth : ℕ)
    (depth_coherent : backed.exitDepth = exitDepth) : Point where
  exponent := n
  backed := backed
  exitDepth := exitDepth
  depth_coherent := depth_coherent

namespace Point

theorem exitDepth_pos (point : Point) : 0 < point.exitDepth := by
  rw [← point.depth_coherent]
  exact point.backed.exitDepth_pos

theorem exitDepth_le_seven (point : Point) : point.exitDepth ≤ 7 := by
  rw [← point.depth_coherent]
  exact point.backed.exitDepth_le_seven

/-- Recover the campaign theorem directly from a response point. -/
def holds (point : Point) : Fermat.HoldsAt point.exponent :=
  point.backed.holds

/-- The point's checked run ends with precisely its stored campaign theorem. -/
theorem outcome_eq (point : Point) :
    point.backed.measured.run.outcome = .contradicted point.holds :=
  point.backed.outcome_eq

end Point

def thirtySeven : Point :=
  mkPoint ThirtySeven.proofBacked ThirtySeven.exitDepth
    ThirtySeven.exitDepth_eq_measured

def fiftyNine : Point :=
  mkPoint FiftyNine.proofBacked FiftyNine.exitDepth
    FiftyNine.exitDepth_eq_measured

def sixtySeven : Point :=
  mkPoint SixtySeven.proofBacked SixtySeven.exitDepth
    SixtySeven.exitDepth_eq_measured

def oneHundredFiftySeven : Point :=
  mkPoint OneHundredFiftySeven.proofBacked
    OneHundredFiftySeven.exitDepth
    OneHundredFiftySeven.exitDepth_eq_measured

def fiveHundredEightySeven : Point :=
  mkPoint FiveHundredEightySeven.proofBacked
    FiveHundredEightySeven.exitDepth
    FiveHundredEightySeven.exitDepth_eq_measured

/-- The proof-carrying historical response curve, in exponent order. -/
def responseCurve : List Point :=
  [thirtySeven, fiftyNine, sixtySeven, oneHundredFiftySeven,
    fiveHundredEightySeven]

/-- Forget proof payloads while retaining empirical coordinates. -/
def coordinates (points : List Point) : List (ℕ × ℕ) :=
  points.map fun point ↦ (point.exponent, point.exitDepth)

/-- Generator-search-friendly projection of the proof-backed curve. -/
def responseData : List (ℕ × ℕ) :=
  coordinates responseCurve

theorem responseCurve_length : responseCurve.length = 5 := rfl

theorem responseData_eq :
    responseData = [(37, 7), (59, 7), (67, 7), (157, 7), (587, 7)] :=
  rfl

/-- All five completed irregular-prime campaigns traverse the full battery. -/
theorem all_exit_at_seven :
    responseData.map Prod.snd = [7, 7, 7, 7, 7] :=
  rfl

/-- Public aggregate of the five fixed-exponent theorems, recovered from
the proof-backed ladder points rather than reproved inside `Ladder/`. -/
theorem campaignProofs :
    Fermat.HoldsAt 37 ∧ Fermat.HoldsAt 59 ∧
      Fermat.HoldsAt 67 ∧ Fermat.HoldsAt 157 ∧ Fermat.HoldsAt 587 :=
  ⟨thirtySeven.holds, fiftyNine.holds, sixtySeven.holds,
    oneHundredFiftySeven.holds, fiveHundredEightySeven.holds⟩

end Fermat.Ladder.HistoricalResponse
