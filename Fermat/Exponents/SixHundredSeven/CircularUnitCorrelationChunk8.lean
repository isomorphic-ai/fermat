import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk0

/-!
# Cyclic-correlation data at exponent 607: residues 40--44

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

private theorem nat_phase_correlation_40 :
    natCorrelation (40 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_41 :
    natCorrelation (41 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_42 :
    natCorrelation (42 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_43 :
    natCorrelation (43 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_44 :
    natCorrelation (44 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk8 (i : Fin 5) :
    let d : Cyc := ((40 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_40
  · exact phaseCorrelation_of_nat nat_phase_correlation_41
  · exact phaseCorrelation_of_nat nat_phase_correlation_42
  · exact phaseCorrelation_of_nat nat_phase_correlation_43
  · exact phaseCorrelation_of_nat nat_phase_correlation_44

end

end Fermat.SixHundredSeven.CircularUnitCertificate
