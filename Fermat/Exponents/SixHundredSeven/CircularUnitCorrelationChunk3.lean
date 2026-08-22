import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk0

/-!
# Cyclic-correlation data at exponent 607: residues 15--19

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

private theorem nat_phase_correlation_15 :
    natCorrelation (15 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_16 :
    natCorrelation (16 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_17 :
    natCorrelation (17 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_18 :
    natCorrelation (18 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_19 :
    natCorrelation (19 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk3 (i : Fin 5) :
    let d : Cyc := ((15 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_15
  · exact phaseCorrelation_of_nat nat_phase_correlation_16
  · exact phaseCorrelation_of_nat nat_phase_correlation_17
  · exact phaseCorrelation_of_nat nat_phase_correlation_18
  · exact phaseCorrelation_of_nat nat_phase_correlation_19

end

end Fermat.SixHundredSeven.CircularUnitCertificate
