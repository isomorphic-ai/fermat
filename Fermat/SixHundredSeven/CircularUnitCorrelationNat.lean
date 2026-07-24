import Fermat.Irregular.CyclicNatCorrelation
import Fermat.SixHundredSeven.CircularUnitMatrix

/-!
# Natural cyclic-correlation evaluator at exponent 607

The 303 phase and inverse representatives are evaluated by the generic
tail-recursive natural-number loop. The structural theorem below transports
the result back to the abstract correlation over `ZMod 607`; concrete
certificate modules therefore normalize only bounded natural arithmetic.
-/

namespace Fermat.SixHundredSeven.CircularUnitCertificate

open scoped BigOperators

open Fermat.Irregular.CyclicNatCorrelation
open Fermat.SixHundredSeven.CircularUnitCyclic
open Fermat.SixHundredSeven.CircularUnitMatrix

/-- Tail-recursive natural representative of one complete correlation. -/
def natCorrelation (d : Cyc) : ℕ :=
  evaluate 607 303 symbolPhaseData correlationInverseData d.val

/-- Casting the natural evaluator recovers the original cyclic
correlation. -/
theorem natCorrelation_cast (d : Cyc) :
    (natCorrelation d : ZMod 607) =
      ∑ u : Cyc, symbolPhase u * correlationInverse (u + d) := by
  simpa only [natCorrelation, arrayFunction, symbolPhase,
    correlationInverse] using
    cast_evaluate_eq_cyclicCorrelation
      607 303 symbolPhaseData correlationInverseData d

/-- Lift a checked natural correlation value to the abstract field-valued
correlation used by the reduced-difference-matrix theorem. -/
theorem phaseCorrelation_of_nat {d : Cyc}
    (h : natCorrelation d = if d = 0 then 1 else 0) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  rw [← natCorrelation_cast]
  by_cases hd : d = 0
  · rw [if_pos hd] at h ⊢
    simpa only [Nat.cast_one] using
      congrArg (fun n : ℕ ↦ (n : ZMod 607)) h
  · rw [if_neg hd] at h ⊢
    simpa only [Nat.cast_zero] using
      congrArg (fun n : ℕ ↦ (n : ZMod 607)) h

/-- Tail-recursively check a consecutive block of cyclic shifts. -/
def verifyNatCorrelationRange (offset size : ℕ) : Bool :=
  verifyRange
    (fun shift ↦ natCorrelation ((shift : ℕ) : Cyc))
    (fun shift ↦ if (((shift : ℕ) : Cyc) = 0) then 1 else 0)
    offset size

/-- Extract one natural correlation equality from a successful range
verification. -/
theorem natCorrelation_of_verifyRange {offset size : ℕ}
    (h : verifyNatCorrelationRange offset size = true) (i : Fin size) :
    let d : Cyc := ((offset + i.val : ℕ) : Cyc)
    natCorrelation d = if d = 0 then 1 else 0 := by
  exact verifyRange_get
    (fun shift ↦ natCorrelation ((shift : ℕ) : Cyc))
    (fun shift ↦ if (((shift : ℕ) : Cyc) = 0) then 1 else 0)
    offset size h i

end Fermat.SixHundredSeven.CircularUnitCertificate
