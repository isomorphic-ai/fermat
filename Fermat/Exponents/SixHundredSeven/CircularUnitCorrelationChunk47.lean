import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk31
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk32
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk33
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk34
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk35
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk36
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk37
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk38
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk39
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk40

/-!
# Cyclic-correlation data at exponent 607: residues 235--239

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

private theorem nat_phase_correlation_235 :
    natCorrelation (235 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_236 :
    natCorrelation (236 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_237 :
    natCorrelation (237 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_238 :
    natCorrelation (238 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_239 :
    natCorrelation (239 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk47 (i : Fin 5) :
    let d : Cyc := ((235 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_235
  · exact phaseCorrelation_of_nat nat_phase_correlation_236
  · exact phaseCorrelation_of_nat nat_phase_correlation_237
  · exact phaseCorrelation_of_nat nat_phase_correlation_238
  · exact phaseCorrelation_of_nat nat_phase_correlation_239

end

end Fermat.SixHundredSeven.CircularUnitCertificate
