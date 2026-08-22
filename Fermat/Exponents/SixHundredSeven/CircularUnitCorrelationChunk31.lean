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
# Cyclic-correlation data at exponent 607: residues 155--159

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

private theorem nat_phase_correlation_155 :
    natCorrelation (155 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_156 :
    natCorrelation (156 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_157 :
    natCorrelation (157 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_158 :
    natCorrelation (158 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_159 :
    natCorrelation (159 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk31 (i : Fin 5) :
    let d : Cyc := ((155 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_155
  · exact phaseCorrelation_of_nat nat_phase_correlation_156
  · exact phaseCorrelation_of_nat nat_phase_correlation_157
  · exact phaseCorrelation_of_nat nat_phase_correlation_158
  · exact phaseCorrelation_of_nat nat_phase_correlation_159

end

end Fermat.SixHundredSeven.CircularUnitCertificate
