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
# Cyclic-correlation data at exponent 607: residues 205--209

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

private theorem nat_phase_correlation_205 :
    natCorrelation (205 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_206 :
    natCorrelation (206 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_207 :
    natCorrelation (207 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_208 :
    natCorrelation (208 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_209 :
    natCorrelation (209 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk41 (i : Fin 5) :
    let d : Cyc := ((205 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_205
  · exact phaseCorrelation_of_nat nat_phase_correlation_206
  · exact phaseCorrelation_of_nat nat_phase_correlation_207
  · exact phaseCorrelation_of_nat nat_phase_correlation_208
  · exact phaseCorrelation_of_nat nat_phase_correlation_209

end

end Fermat.SixHundredSeven.CircularUnitCertificate
