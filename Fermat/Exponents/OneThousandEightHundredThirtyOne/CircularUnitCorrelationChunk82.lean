import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk79
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk80
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk81

/-!
# Cyclic-correlation data at exponent 1831: residues 845--854

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

private theorem nat_phase_correlation_845 :
    natCorrelation (845 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_846 :
    natCorrelation (846 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_847 :
    natCorrelation (847 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_848 :
    natCorrelation (848 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_849 :
    natCorrelation (849 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_850 :
    natCorrelation (850 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_851 :
    natCorrelation (851 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_852 :
    natCorrelation (852 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_853 :
    natCorrelation (853 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_854 :
    natCorrelation (854 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk82 (i : Fin 10) :
    let d : Cyc := ((845 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_845
  · exact phaseCorrelation_of_nat nat_phase_correlation_846
  · exact phaseCorrelation_of_nat nat_phase_correlation_847
  · exact phaseCorrelation_of_nat nat_phase_correlation_848
  · exact phaseCorrelation_of_nat nat_phase_correlation_849
  · exact phaseCorrelation_of_nat nat_phase_correlation_850
  · exact phaseCorrelation_of_nat nat_phase_correlation_851
  · exact phaseCorrelation_of_nat nat_phase_correlation_852
  · exact phaseCorrelation_of_nat nat_phase_correlation_853
  · exact phaseCorrelation_of_nat nat_phase_correlation_854

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
