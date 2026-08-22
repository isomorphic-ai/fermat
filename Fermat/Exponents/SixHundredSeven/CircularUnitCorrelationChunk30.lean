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
# Cyclic-correlation data at exponent 607: residues 150--154

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

private theorem nat_phase_correlation_150 :
    natCorrelation (150 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_151 :
    natCorrelation (151 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_152 :
    natCorrelation (152 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_153 :
    natCorrelation (153 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_154 :
    natCorrelation (154 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk30 (i : Fin 5) :
    let d : Cyc := ((150 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_150
  · exact phaseCorrelation_of_nat nat_phase_correlation_151
  · exact phaseCorrelation_of_nat nat_phase_correlation_152
  · exact phaseCorrelation_of_nat nat_phase_correlation_153
  · exact phaseCorrelation_of_nat nat_phase_correlation_154

end

end Fermat.SixHundredSeven.CircularUnitCertificate
