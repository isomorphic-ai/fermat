import Fermat.SixHundredSeven.CircularUnitCorrelationChunk4

/-!
# Cyclic-correlation data at exponent 607: residues 35--39

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

private theorem nat_phase_correlation_35 :
    natCorrelation (35 : Cyc) = 0 := by
  decide_cbv

private theorem nat_phase_correlation_36 :
    natCorrelation (36 : Cyc) = 0 := by
  decide_cbv

private theorem nat_phase_correlation_37 :
    natCorrelation (37 : Cyc) = 0 := by
  decide_cbv

private theorem nat_phase_correlation_38 :
    natCorrelation (38 : Cyc) = 0 := by
  decide_cbv

private theorem nat_phase_correlation_39 :
    natCorrelation (39 : Cyc) = 0 := by
  decide_cbv

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk7 (i : Fin 5) :
    let d : Cyc := ((35 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_35
  · exact phaseCorrelation_of_nat nat_phase_correlation_36
  · exact phaseCorrelation_of_nat nat_phase_correlation_37
  · exact phaseCorrelation_of_nat nat_phase_correlation_38
  · exact phaseCorrelation_of_nat nat_phase_correlation_39

end

end Fermat.SixHundredSeven.CircularUnitCertificate
