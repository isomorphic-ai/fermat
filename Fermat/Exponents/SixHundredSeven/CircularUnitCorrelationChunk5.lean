import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk0

/-!
# Cyclic-correlation data at exponent 607: residues 25--29

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

private theorem nat_phase_correlation_25 :
    natCorrelation (25 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_26 :
    natCorrelation (26 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_27 :
    natCorrelation (27 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_28 :
    natCorrelation (28 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_29 :
    natCorrelation (29 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk5 (i : Fin 5) :
    let d : Cyc := ((25 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_25
  · exact phaseCorrelation_of_nat nat_phase_correlation_26
  · exact phaseCorrelation_of_nat nat_phase_correlation_27
  · exact phaseCorrelation_of_nat nat_phase_correlation_28
  · exact phaseCorrelation_of_nat nat_phase_correlation_29

end

end Fermat.SixHundredSeven.CircularUnitCertificate
