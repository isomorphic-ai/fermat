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
# Cyclic-correlation data at exponent 607: residues 225--229

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

private theorem nat_phase_correlation_225 :
    natCorrelation (225 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_226 :
    natCorrelation (226 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_227 :
    natCorrelation (227 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_228 :
    natCorrelation (228 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_229 :
    natCorrelation (229 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk45 (i : Fin 5) :
    let d : Cyc := ((225 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_225
  · exact phaseCorrelation_of_nat nat_phase_correlation_226
  · exact phaseCorrelation_of_nat nat_phase_correlation_227
  · exact phaseCorrelation_of_nat nat_phase_correlation_228
  · exact phaseCorrelation_of_nat nat_phase_correlation_229

end

end Fermat.SixHundredSeven.CircularUnitCertificate
