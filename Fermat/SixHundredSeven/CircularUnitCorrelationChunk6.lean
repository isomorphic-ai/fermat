import Fermat.SixHundredSeven.CircularUnitCorrelationChunk0

/-!
# Cyclic-correlation data at exponent 607: residues 30--34

This module kernel-checks five or fewer shifts as separate tail-recursive
natural computations. The modules are arranged in restartable dependency
tiers of width ten.
-/

namespace Fermat.SixHundredSeven.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredSeven.CircularUnitCyclic
open Fermat.SixHundredSeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem nat_phase_correlation_30 :
    natCorrelation (30 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_31 :
    natCorrelation (31 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_32 :
    natCorrelation (32 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_33 :
    natCorrelation (33 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_34 :
    natCorrelation (34 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk6 (i : Fin 5) :
    let d : Cyc := ((30 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_30
  · exact phaseCorrelation_of_nat nat_phase_correlation_31
  · exact phaseCorrelation_of_nat nat_phase_correlation_32
  · exact phaseCorrelation_of_nat nat_phase_correlation_33
  · exact phaseCorrelation_of_nat nat_phase_correlation_34

end

end Fermat.SixHundredSeven.CircularUnitCertificate
