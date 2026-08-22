import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk43
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk44
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk45

/-!
# Cyclic-correlation data at exponent 1831: residues 505--514

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

private theorem nat_phase_correlation_505 :
    natCorrelation (505 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_506 :
    natCorrelation (506 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_507 :
    natCorrelation (507 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_508 :
    natCorrelation (508 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_509 :
    natCorrelation (509 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_510 :
    natCorrelation (510 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_511 :
    natCorrelation (511 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_512 :
    natCorrelation (512 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_513 :
    natCorrelation (513 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_514 :
    natCorrelation (514 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk48 (i : Fin 10) :
    let d : Cyc := ((505 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_505
  · exact phaseCorrelation_of_nat nat_phase_correlation_506
  · exact phaseCorrelation_of_nat nat_phase_correlation_507
  · exact phaseCorrelation_of_nat nat_phase_correlation_508
  · exact phaseCorrelation_of_nat nat_phase_correlation_509
  · exact phaseCorrelation_of_nat nat_phase_correlation_510
  · exact phaseCorrelation_of_nat nat_phase_correlation_511
  · exact phaseCorrelation_of_nat nat_phase_correlation_512
  · exact phaseCorrelation_of_nat nat_phase_correlation_513
  · exact phaseCorrelation_of_nat nat_phase_correlation_514

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
