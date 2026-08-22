import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk25
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk26
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk27

/-!
# Cyclic-correlation data at exponent 1831: residues 305--314

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

private theorem nat_phase_correlation_305 :
    natCorrelation (305 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_306 :
    natCorrelation (306 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_307 :
    natCorrelation (307 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_308 :
    natCorrelation (308 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_309 :
    natCorrelation (309 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_310 :
    natCorrelation (310 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_311 :
    natCorrelation (311 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_312 :
    natCorrelation (312 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_313 :
    natCorrelation (313 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_314 :
    natCorrelation (314 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk28 (i : Fin 10) :
    let d : Cyc := ((305 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_305
  · exact phaseCorrelation_of_nat nat_phase_correlation_306
  · exact phaseCorrelation_of_nat nat_phase_correlation_307
  · exact phaseCorrelation_of_nat nat_phase_correlation_308
  · exact phaseCorrelation_of_nat nat_phase_correlation_309
  · exact phaseCorrelation_of_nat nat_phase_correlation_310
  · exact phaseCorrelation_of_nat nat_phase_correlation_311
  · exact phaseCorrelation_of_nat nat_phase_correlation_312
  · exact phaseCorrelation_of_nat nat_phase_correlation_313
  · exact phaseCorrelation_of_nat nat_phase_correlation_314

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
