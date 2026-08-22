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
# Cyclic-correlation data at exponent 607: residues 190--194

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

private theorem nat_phase_correlation_190 :
    natCorrelation (190 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_191 :
    natCorrelation (191 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_192 :
    natCorrelation (192 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_193 :
    natCorrelation (193 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_194 :
    natCorrelation (194 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk38 (i : Fin 5) :
    let d : Cyc := ((190 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_190
  · exact phaseCorrelation_of_nat nat_phase_correlation_191
  · exact phaseCorrelation_of_nat nat_phase_correlation_192
  · exact phaseCorrelation_of_nat nat_phase_correlation_193
  · exact phaseCorrelation_of_nat nat_phase_correlation_194

end

end Fermat.SixHundredSeven.CircularUnitCertificate
