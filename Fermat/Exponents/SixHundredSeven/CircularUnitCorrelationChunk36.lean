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
# Cyclic-correlation data at exponent 607: residues 180--184

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

private theorem nat_phase_correlation_180 :
    natCorrelation (180 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_181 :
    natCorrelation (181 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_182 :
    natCorrelation (182 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_183 :
    natCorrelation (183 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_184 :
    natCorrelation (184 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk36 (i : Fin 5) :
    let d : Cyc := ((180 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_180
  · exact phaseCorrelation_of_nat nat_phase_correlation_181
  · exact phaseCorrelation_of_nat nat_phase_correlation_182
  · exact phaseCorrelation_of_nat nat_phase_correlation_183
  · exact phaseCorrelation_of_nat nat_phase_correlation_184

end

end Fermat.SixHundredSeven.CircularUnitCertificate
