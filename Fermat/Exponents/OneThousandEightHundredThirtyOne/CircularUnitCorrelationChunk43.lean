import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk40
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk41
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk42

/-!
# Cyclic-correlation data at exponent 1831: residues 455--464

This module kernel-checks its shifts as separate tail-recursive natural
computations. Keeping each decision in its own declaration lets Lean
release normalization state before checking the next shift.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate

noncomputable section

open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem nat_phase_correlation_455 :
    natCorrelation (455 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_456 :
    natCorrelation (456 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_457 :
    natCorrelation (457 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_458 :
    natCorrelation (458 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_459 :
    natCorrelation (459 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_460 :
    natCorrelation (460 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_461 :
    natCorrelation (461 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_462 :
    natCorrelation (462 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_463 :
    natCorrelation (463 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_464 :
    natCorrelation (464 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk43 (i : Fin 10) :
    let d : Cyc := ((455 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_455
  · exact phaseCorrelation_of_nat nat_phase_correlation_456
  · exact phaseCorrelation_of_nat nat_phase_correlation_457
  · exact phaseCorrelation_of_nat nat_phase_correlation_458
  · exact phaseCorrelation_of_nat nat_phase_correlation_459
  · exact phaseCorrelation_of_nat nat_phase_correlation_460
  · exact phaseCorrelation_of_nat nat_phase_correlation_461
  · exact phaseCorrelation_of_nat nat_phase_correlation_462
  · exact phaseCorrelation_of_nat nat_phase_correlation_463
  · exact phaseCorrelation_of_nat nat_phase_correlation_464

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
