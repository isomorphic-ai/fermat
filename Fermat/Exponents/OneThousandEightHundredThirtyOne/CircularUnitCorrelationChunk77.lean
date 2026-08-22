import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk73
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk74
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk75

/-!
# Cyclic-correlation data at exponent 1831: residues 795--804

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

private theorem nat_phase_correlation_795 :
    natCorrelation (795 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_796 :
    natCorrelation (796 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_797 :
    natCorrelation (797 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_798 :
    natCorrelation (798 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_799 :
    natCorrelation (799 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_800 :
    natCorrelation (800 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_801 :
    natCorrelation (801 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_802 :
    natCorrelation (802 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_803 :
    natCorrelation (803 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_804 :
    natCorrelation (804 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk77 (i : Fin 10) :
    let d : Cyc := ((795 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_795
  · exact phaseCorrelation_of_nat nat_phase_correlation_796
  · exact phaseCorrelation_of_nat nat_phase_correlation_797
  · exact phaseCorrelation_of_nat nat_phase_correlation_798
  · exact phaseCorrelation_of_nat nat_phase_correlation_799
  · exact phaseCorrelation_of_nat nat_phase_correlation_800
  · exact phaseCorrelation_of_nat nat_phase_correlation_801
  · exact phaseCorrelation_of_nat nat_phase_correlation_802
  · exact phaseCorrelation_of_nat nat_phase_correlation_803
  · exact phaseCorrelation_of_nat nat_phase_correlation_804

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
