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
# Cyclic-correlation data at exponent 607: residues 200--204

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

private theorem nat_phase_correlation_200 :
    natCorrelation (200 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_201 :
    natCorrelation (201 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_202 :
    natCorrelation (202 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_203 :
    natCorrelation (203 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_204 :
    natCorrelation (204 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk40 (i : Fin 5) :
    let d : Cyc := ((200 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_200
  · exact phaseCorrelation_of_nat nat_phase_correlation_201
  · exact phaseCorrelation_of_nat nat_phase_correlation_202
  · exact phaseCorrelation_of_nat nat_phase_correlation_203
  · exact phaseCorrelation_of_nat nat_phase_correlation_204

end

end Fermat.SixHundredSeven.CircularUnitCertificate
