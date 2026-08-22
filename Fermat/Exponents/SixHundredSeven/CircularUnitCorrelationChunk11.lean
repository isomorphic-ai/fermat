import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk1
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk2
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk3
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk4
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk5
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk6
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk7
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk8
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk9
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk10

/-!
# Cyclic-correlation data at exponent 607: residues 55--59

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

private theorem nat_phase_correlation_55 :
    natCorrelation (55 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_56 :
    natCorrelation (56 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_57 :
    natCorrelation (57 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_58 :
    natCorrelation (58 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_59 :
    natCorrelation (59 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk11 (i : Fin 5) :
    let d : Cyc := ((55 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_55
  · exact phaseCorrelation_of_nat nat_phase_correlation_56
  · exact phaseCorrelation_of_nat nat_phase_correlation_57
  · exact phaseCorrelation_of_nat nat_phase_correlation_58
  · exact phaseCorrelation_of_nat nat_phase_correlation_59

end

end Fermat.SixHundredSeven.CircularUnitCertificate
