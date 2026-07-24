import Fermat.Ladder.Eleven
import Fermat.Ladder.Thirteen

/-!
# Proof-backed Faulhaber ladder alternatives

The primary response curve records the first sufficient route at exponents
`11` and `13`, namely their depth-six class-number-one certificates.  This
module records the independent direct-Faulhaber alternatives.  Each point
carries the depth-seven run and the `Fermat.HoldsAt` theorem obtained from
its fold-seven Bernoulli data through Kummer's criterion.
-/

namespace Fermat.Ladder.FaulhaberResponse

structure Point where
  exponent : ℕ
  backed : ProofBacked exponent
  exitDepth : ℕ
  depth_coherent : backed.exitDepth = exitDepth

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

def holds (point : Point) : Fermat.HoldsAt point.exponent :=
  point.backed.holds

theorem outcome_eq (point : Point) :
    point.backed.measured.run.outcome = .contradicted point.holds :=
  point.backed.outcome_eq

end Point

def eleven : Point :=
  mkPoint Eleven.Faulhaber.proofBacked Eleven.Faulhaber.exitDepth
    Eleven.Faulhaber.exitDepth_eq_measured

def thirteen : Point :=
  mkPoint Thirteen.Faulhaber.proofBacked Thirteen.Faulhaber.exitDepth
    Thirteen.Faulhaber.exitDepth_eq_measured

def responseCurve : List Point :=
  [eleven, thirteen]

def coordinates (points : List Point) : List (ℕ × ℕ) :=
  points.map fun point ↦ (point.exponent, point.exitDepth)

def responseData : List (ℕ × ℕ) :=
  coordinates responseCurve

theorem responseCurve_length : responseCurve.length = 2 := rfl

theorem responseData_eq :
    responseData = [(11, 7), (13, 7)] :=
  rfl

theorem both_exit_at_seven :
    responseData.map Prod.snd = [7, 7] :=
  rfl

theorem alternativeProofs :
    Fermat.HoldsAt 11 ∧ Fermat.HoldsAt 13 :=
  ⟨eleven.holds, thirteen.holds⟩

end Fermat.Ladder.FaulhaberResponse
