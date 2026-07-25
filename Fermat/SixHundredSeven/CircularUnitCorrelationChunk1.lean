import Fermat.SixHundredSeven.CircularUnitCorrelationChunk0

/-!
# Cyclic-correlation data at exponent 607: residues 5--9

This module kernel-checks five or fewer shifts as separate tail-recursive
natural computations. Keeping each decision in its own declaration lets
Lean release normalization state before checking the next shift.
-/

namespace Fermat.SixHundredSeven.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredSeven.CircularUnitCyclic
open Fermat.SixHundredSeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option cbv.warning false
set_option cbv.maxSteps 10000000

private theorem nat_phase_correlation_5 :
    natCorrelation (5 : Cyc) = 0 := by
  decide_cbv

private theorem nat_phase_correlation_6 :
    natCorrelation (6 : Cyc) = 0 := by
  decide_cbv

private theorem nat_phase_correlation_7 :
    natCorrelation (7 : Cyc) = 0 := by
  decide_cbv

private theorem nat_phase_correlation_8 :
    natCorrelation (8 : Cyc) = 0 := by
  decide_cbv

private theorem nat_phase_correlation_9 :
    natCorrelation (9 : Cyc) = 0 := by
  decide_cbv

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk1 (i : Fin 5) :
    let d : Cyc := ((5 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_5
  · exact phaseCorrelation_of_nat nat_phase_correlation_6
  · exact phaseCorrelation_of_nat nat_phase_correlation_7
  · exact phaseCorrelation_of_nat nat_phase_correlation_8
  · exact phaseCorrelation_of_nat nat_phase_correlation_9

end

end Fermat.SixHundredSeven.CircularUnitCertificate
