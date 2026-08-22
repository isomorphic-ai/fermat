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
# Cyclic-correlation data at exponent 607: residues 285--289

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

private theorem nat_phase_correlation_285 :
    natCorrelation (285 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_286 :
    natCorrelation (286 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_287 :
    natCorrelation (287 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_288 :
    natCorrelation (288 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_289 :
    natCorrelation (289 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk57 (i : Fin 5) :
    let d : Cyc := ((285 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_285
  · exact phaseCorrelation_of_nat nat_phase_correlation_286
  · exact phaseCorrelation_of_nat nat_phase_correlation_287
  · exact phaseCorrelation_of_nat nat_phase_correlation_288
  · exact phaseCorrelation_of_nat nat_phase_correlation_289

end

end Fermat.SixHundredSeven.CircularUnitCertificate
