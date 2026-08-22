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
# Cyclic-correlation data at exponent 607: residues 270--274

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

private theorem nat_phase_correlation_270 :
    natCorrelation (270 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_271 :
    natCorrelation (271 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_272 :
    natCorrelation (272 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_273 :
    natCorrelation (273 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_274 :
    natCorrelation (274 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk54 (i : Fin 5) :
    let d : Cyc := ((270 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_270
  · exact phaseCorrelation_of_nat nat_phase_correlation_271
  · exact phaseCorrelation_of_nat nat_phase_correlation_272
  · exact phaseCorrelation_of_nat nat_phase_correlation_273
  · exact phaseCorrelation_of_nat nat_phase_correlation_274

end

end Fermat.SixHundredSeven.CircularUnitCertificate
