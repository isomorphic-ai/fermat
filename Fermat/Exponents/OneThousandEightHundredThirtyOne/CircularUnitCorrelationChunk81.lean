import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk76
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk77
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk78

/-!
# Cyclic-correlation data at exponent 1831: residues 835--844

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

private theorem nat_phase_correlation_835 :
    natCorrelation (835 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_836 :
    natCorrelation (836 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_837 :
    natCorrelation (837 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_838 :
    natCorrelation (838 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_839 :
    natCorrelation (839 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_840 :
    natCorrelation (840 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_841 :
    natCorrelation (841 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_842 :
    natCorrelation (842 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_843 :
    natCorrelation (843 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_844 :
    natCorrelation (844 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk81 (i : Fin 10) :
    let d : Cyc := ((835 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_835
  · exact phaseCorrelation_of_nat nat_phase_correlation_836
  · exact phaseCorrelation_of_nat nat_phase_correlation_837
  · exact phaseCorrelation_of_nat nat_phase_correlation_838
  · exact phaseCorrelation_of_nat nat_phase_correlation_839
  · exact phaseCorrelation_of_nat nat_phase_correlation_840
  · exact phaseCorrelation_of_nat nat_phase_correlation_841
  · exact phaseCorrelation_of_nat nat_phase_correlation_842
  · exact phaseCorrelation_of_nat nat_phase_correlation_843
  · exact phaseCorrelation_of_nat nat_phase_correlation_844

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
