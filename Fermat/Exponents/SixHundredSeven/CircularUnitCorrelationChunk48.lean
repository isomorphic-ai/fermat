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
# Cyclic-correlation data at exponent 607: residues 240--244

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

private theorem nat_phase_correlation_240 :
    natCorrelation (240 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_241 :
    natCorrelation (241 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_242 :
    natCorrelation (242 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_243 :
    natCorrelation (243 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_244 :
    natCorrelation (244 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk48 (i : Fin 5) :
    let d : Cyc := ((240 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_240
  · exact phaseCorrelation_of_nat nat_phase_correlation_241
  · exact phaseCorrelation_of_nat nat_phase_correlation_242
  · exact phaseCorrelation_of_nat nat_phase_correlation_243
  · exact phaseCorrelation_of_nat nat_phase_correlation_244

end

end Fermat.SixHundredSeven.CircularUnitCertificate
