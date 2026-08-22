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
# Cyclic-correlation data at exponent 607: residues 170--174

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

private theorem nat_phase_correlation_170 :
    natCorrelation (170 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_171 :
    natCorrelation (171 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_172 :
    natCorrelation (172 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_173 :
    natCorrelation (173 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_174 :
    natCorrelation (174 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk34 (i : Fin 5) :
    let d : Cyc := ((170 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_170
  · exact phaseCorrelation_of_nat nat_phase_correlation_171
  · exact phaseCorrelation_of_nat nat_phase_correlation_172
  · exact phaseCorrelation_of_nat nat_phase_correlation_173
  · exact phaseCorrelation_of_nat nat_phase_correlation_174

end

end Fermat.SixHundredSeven.CircularUnitCertificate
