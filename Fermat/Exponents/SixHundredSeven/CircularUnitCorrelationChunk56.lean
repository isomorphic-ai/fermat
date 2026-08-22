import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk41
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk42
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk43
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk44
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk45
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk46
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk47
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk48
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk49
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk50

/-!
# Cyclic-correlation data at exponent 607: residues 280--284

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

private theorem nat_phase_correlation_280 :
    natCorrelation (280 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_281 :
    natCorrelation (281 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_282 :
    natCorrelation (282 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_283 :
    natCorrelation (283 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_284 :
    natCorrelation (284 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk56 (i : Fin 5) :
    let d : Cyc := ((280 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_280
  · exact phaseCorrelation_of_nat nat_phase_correlation_281
  · exact phaseCorrelation_of_nat nat_phase_correlation_282
  · exact phaseCorrelation_of_nat nat_phase_correlation_283
  · exact phaseCorrelation_of_nat nat_phase_correlation_284

end

end Fermat.SixHundredSeven.CircularUnitCertificate
