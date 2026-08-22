import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk0

/-!
# Cyclic-correlation data at exponent 607: residues 10--14

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

private theorem nat_phase_correlation_10 :
    natCorrelation (10 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_11 :
    natCorrelation (11 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_12 :
    natCorrelation (12 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_13 :
    natCorrelation (13 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_14 :
    natCorrelation (14 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk2 (i : Fin 5) :
    let d : Cyc := ((10 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_10
  · exact phaseCorrelation_of_nat nat_phase_correlation_11
  · exact phaseCorrelation_of_nat nat_phase_correlation_12
  · exact phaseCorrelation_of_nat nat_phase_correlation_13
  · exact phaseCorrelation_of_nat nat_phase_correlation_14

end

end Fermat.SixHundredSeven.CircularUnitCertificate
