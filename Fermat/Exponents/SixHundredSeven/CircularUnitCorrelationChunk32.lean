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
# Cyclic-correlation data at exponent 607: residues 160--164

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

private theorem nat_phase_correlation_160 :
    natCorrelation (160 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_161 :
    natCorrelation (161 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_162 :
    natCorrelation (162 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_163 :
    natCorrelation (163 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_164 :
    natCorrelation (164 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk32 (i : Fin 5) :
    let d : Cyc := ((160 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_160
  · exact phaseCorrelation_of_nat nat_phase_correlation_161
  · exact phaseCorrelation_of_nat nat_phase_correlation_162
  · exact phaseCorrelation_of_nat nat_phase_correlation_163
  · exact phaseCorrelation_of_nat nat_phase_correlation_164

end

end Fermat.SixHundredSeven.CircularUnitCertificate
