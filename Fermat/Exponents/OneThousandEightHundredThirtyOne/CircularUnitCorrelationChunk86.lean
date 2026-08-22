import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk82
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk83
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk84

/-!
# Cyclic-correlation data at exponent 1831: residues 885--894

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

private theorem nat_phase_correlation_885 :
    natCorrelation (885 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_886 :
    natCorrelation (886 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_887 :
    natCorrelation (887 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_888 :
    natCorrelation (888 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_889 :
    natCorrelation (889 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_890 :
    natCorrelation (890 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_891 :
    natCorrelation (891 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_892 :
    natCorrelation (892 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_893 :
    natCorrelation (893 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_894 :
    natCorrelation (894 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk86 (i : Fin 10) :
    let d : Cyc := ((885 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_885
  · exact phaseCorrelation_of_nat nat_phase_correlation_886
  · exact phaseCorrelation_of_nat nat_phase_correlation_887
  · exact phaseCorrelation_of_nat nat_phase_correlation_888
  · exact phaseCorrelation_of_nat nat_phase_correlation_889
  · exact phaseCorrelation_of_nat nat_phase_correlation_890
  · exact phaseCorrelation_of_nat nat_phase_correlation_891
  · exact phaseCorrelation_of_nat nat_phase_correlation_892
  · exact phaseCorrelation_of_nat nat_phase_correlation_893
  · exact phaseCorrelation_of_nat nat_phase_correlation_894

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
