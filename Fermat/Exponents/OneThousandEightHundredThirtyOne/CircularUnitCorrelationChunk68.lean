import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk64
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk65
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk66

/-!
# Cyclic-correlation data at exponent 1831: residues 705--714

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

private theorem nat_phase_correlation_705 :
    natCorrelation (705 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_706 :
    natCorrelation (706 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_707 :
    natCorrelation (707 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_708 :
    natCorrelation (708 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_709 :
    natCorrelation (709 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_710 :
    natCorrelation (710 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_711 :
    natCorrelation (711 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_712 :
    natCorrelation (712 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_713 :
    natCorrelation (713 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_714 :
    natCorrelation (714 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk68 (i : Fin 10) :
    let d : Cyc := ((705 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_705
  · exact phaseCorrelation_of_nat nat_phase_correlation_706
  · exact phaseCorrelation_of_nat nat_phase_correlation_707
  · exact phaseCorrelation_of_nat nat_phase_correlation_708
  · exact phaseCorrelation_of_nat nat_phase_correlation_709
  · exact phaseCorrelation_of_nat nat_phase_correlation_710
  · exact phaseCorrelation_of_nat nat_phase_correlation_711
  · exact phaseCorrelation_of_nat nat_phase_correlation_712
  · exact phaseCorrelation_of_nat nat_phase_correlation_713
  · exact phaseCorrelation_of_nat nat_phase_correlation_714

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
