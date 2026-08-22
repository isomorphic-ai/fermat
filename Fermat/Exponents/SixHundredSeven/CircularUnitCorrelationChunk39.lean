import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk21
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk22
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk23
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk24
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk25
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk26
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk27
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk28
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk29
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk30

/-!
# Cyclic-correlation data at exponent 607: residues 195--199

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

private theorem nat_phase_correlation_195 :
    natCorrelation (195 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_196 :
    natCorrelation (196 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_197 :
    natCorrelation (197 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_198 :
    natCorrelation (198 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_199 :
    natCorrelation (199 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk39 (i : Fin 5) :
    let d : Cyc := ((195 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_195
  · exact phaseCorrelation_of_nat nat_phase_correlation_196
  · exact phaseCorrelation_of_nat nat_phase_correlation_197
  · exact phaseCorrelation_of_nat nat_phase_correlation_198
  · exact phaseCorrelation_of_nat nat_phase_correlation_199

end

end Fermat.SixHundredSeven.CircularUnitCertificate
