import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk11
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk12
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk13
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk14
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk15
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk16
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk17
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk18
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk19
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk20

/-!
# Cyclic-correlation data at exponent 607: residues 105--109

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

private theorem nat_phase_correlation_105 :
    natCorrelation (105 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_106 :
    natCorrelation (106 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_107 :
    natCorrelation (107 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_108 :
    natCorrelation (108 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_109 :
    natCorrelation (109 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk21 (i : Fin 5) :
    let d : Cyc := ((105 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_105
  · exact phaseCorrelation_of_nat nat_phase_correlation_106
  · exact phaseCorrelation_of_nat nat_phase_correlation_107
  · exact phaseCorrelation_of_nat nat_phase_correlation_108
  · exact phaseCorrelation_of_nat nat_phase_correlation_109

end

end Fermat.SixHundredSeven.CircularUnitCertificate
