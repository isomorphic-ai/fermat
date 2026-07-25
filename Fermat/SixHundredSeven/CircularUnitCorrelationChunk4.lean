import Fermat.SixHundredSeven.CircularUnitCorrelationChunk3

/-!
# Cyclic-correlation data at exponent 607: residues 20--24

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

private theorem nat_phase_correlation_20 :
    natCorrelation (20 : Cyc) = 0 := by
  decide_cbv

private theorem nat_phase_correlation_21 :
    natCorrelation (21 : Cyc) = 0 := by
  decide_cbv

private theorem nat_phase_correlation_22 :
    natCorrelation (22 : Cyc) = 0 := by
  decide_cbv

private theorem nat_phase_correlation_23 :
    natCorrelation (23 : Cyc) = 0 := by
  decide_cbv

private theorem nat_phase_correlation_24 :
    natCorrelation (24 : Cyc) = 0 := by
  decide_cbv

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk4 (i : Fin 5) :
    let d : Cyc := ((20 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_20
  · exact phaseCorrelation_of_nat nat_phase_correlation_21
  · exact phaseCorrelation_of_nat nat_phase_correlation_22
  · exact phaseCorrelation_of_nat nat_phase_correlation_23
  · exact phaseCorrelation_of_nat nat_phase_correlation_24

end

end Fermat.SixHundredSeven.CircularUnitCertificate
