import Fermat.SixHundredSeven.CircularUnitCorrelationChunk0

/-!
# Cyclic-correlation data at exponent 607: residues 50--54

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

private theorem nat_phase_correlation_50 :
    natCorrelation (50 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_51 :
    natCorrelation (51 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_52 :
    natCorrelation (52 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_53 :
    natCorrelation (53 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_54 :
    natCorrelation (54 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk10 (i : Fin 5) :
    let d : Cyc := ((50 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_50
  · exact phaseCorrelation_of_nat nat_phase_correlation_51
  · exact phaseCorrelation_of_nat nat_phase_correlation_52
  · exact phaseCorrelation_of_nat nat_phase_correlation_53
  · exact phaseCorrelation_of_nat nat_phase_correlation_54

end

end Fermat.SixHundredSeven.CircularUnitCertificate
