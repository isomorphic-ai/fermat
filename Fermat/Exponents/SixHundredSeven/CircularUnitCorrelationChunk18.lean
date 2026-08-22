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
# Cyclic-correlation data at exponent 607: residues 90--94

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

private theorem nat_phase_correlation_90 :
    natCorrelation (90 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_91 :
    natCorrelation (91 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_92 :
    natCorrelation (92 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_93 :
    natCorrelation (93 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_94 :
    natCorrelation (94 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk18 (i : Fin 5) :
    let d : Cyc := ((90 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_90
  · exact phaseCorrelation_of_nat nat_phase_correlation_91
  · exact phaseCorrelation_of_nat nat_phase_correlation_92
  · exact phaseCorrelation_of_nat nat_phase_correlation_93
  · exact phaseCorrelation_of_nat nat_phase_correlation_94

end

end Fermat.SixHundredSeven.CircularUnitCertificate
