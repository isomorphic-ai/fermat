import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk28
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk29
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk30

/-!
# Cyclic-correlation data at exponent 1831: residues 335--344

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

private theorem nat_phase_correlation_335 :
    natCorrelation (335 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_336 :
    natCorrelation (336 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_337 :
    natCorrelation (337 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_338 :
    natCorrelation (338 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_339 :
    natCorrelation (339 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_340 :
    natCorrelation (340 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_341 :
    natCorrelation (341 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_342 :
    natCorrelation (342 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_343 :
    natCorrelation (343 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_344 :
    natCorrelation (344 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk31 (i : Fin 10) :
    let d : Cyc := ((335 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_335
  · exact phaseCorrelation_of_nat nat_phase_correlation_336
  · exact phaseCorrelation_of_nat nat_phase_correlation_337
  · exact phaseCorrelation_of_nat nat_phase_correlation_338
  · exact phaseCorrelation_of_nat nat_phase_correlation_339
  · exact phaseCorrelation_of_nat nat_phase_correlation_340
  · exact phaseCorrelation_of_nat nat_phase_correlation_341
  · exact phaseCorrelation_of_nat nat_phase_correlation_342
  · exact phaseCorrelation_of_nat nat_phase_correlation_343
  · exact phaseCorrelation_of_nat nat_phase_correlation_344

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
