import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk43
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk44
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk45

/-!
# Cyclic-correlation data at exponent 1381: residues 485--494

This module kernel-checks its shifts as separate tail-recursive natural
computations. Keeping each decision in its own declaration lets Lean
release normalization state before checking the next shift.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate

noncomputable section

open Fermat.OneThousandThreeHundredEightyOne.CircularUnitCyclic
open Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem nat_phase_correlation_485 :
    natCorrelation (485 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_486 :
    natCorrelation (486 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_487 :
    natCorrelation (487 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_488 :
    natCorrelation (488 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_489 :
    natCorrelation (489 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_490 :
    natCorrelation (490 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_491 :
    natCorrelation (491 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_492 :
    natCorrelation (492 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_493 :
    natCorrelation (493 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_494 :
    natCorrelation (494 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk46 (i : Fin 10) :
    let d : Cyc := ((485 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_485
  · exact phaseCorrelation_of_nat nat_phase_correlation_486
  · exact phaseCorrelation_of_nat nat_phase_correlation_487
  · exact phaseCorrelation_of_nat nat_phase_correlation_488
  · exact phaseCorrelation_of_nat nat_phase_correlation_489
  · exact phaseCorrelation_of_nat nat_phase_correlation_490
  · exact phaseCorrelation_of_nat nat_phase_correlation_491
  · exact phaseCorrelation_of_nat nat_phase_correlation_492
  · exact phaseCorrelation_of_nat nat_phase_correlation_493
  · exact phaseCorrelation_of_nat nat_phase_correlation_494

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
