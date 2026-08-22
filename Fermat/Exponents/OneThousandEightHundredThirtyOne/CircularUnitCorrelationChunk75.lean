import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk70
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk71
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk72

/-!
# Cyclic-correlation data at exponent 1831: residues 775--784

This module kernel-checks its shifts as separate tail-recursive natural
computations. Keeping each decision in its own declaration lets Lean
release normalization state before checking the next shift.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate

noncomputable section

open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem nat_phase_correlation_775 :
    natCorrelation (775 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_776 :
    natCorrelation (776 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_777 :
    natCorrelation (777 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_778 :
    natCorrelation (778 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_779 :
    natCorrelation (779 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_780 :
    natCorrelation (780 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_781 :
    natCorrelation (781 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_782 :
    natCorrelation (782 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_783 :
    natCorrelation (783 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_784 :
    natCorrelation (784 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk75 (i : Fin 10) :
    let d : Cyc := ((775 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_775
  · exact phaseCorrelation_of_nat nat_phase_correlation_776
  · exact phaseCorrelation_of_nat nat_phase_correlation_777
  · exact phaseCorrelation_of_nat nat_phase_correlation_778
  · exact phaseCorrelation_of_nat nat_phase_correlation_779
  · exact phaseCorrelation_of_nat nat_phase_correlation_780
  · exact phaseCorrelation_of_nat nat_phase_correlation_781
  · exact phaseCorrelation_of_nat nat_phase_correlation_782
  · exact phaseCorrelation_of_nat nat_phase_correlation_783
  · exact phaseCorrelation_of_nat nat_phase_correlation_784

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
