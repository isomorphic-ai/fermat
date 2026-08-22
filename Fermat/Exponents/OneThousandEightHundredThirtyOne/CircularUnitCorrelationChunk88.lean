import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk85
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk86
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk87

/-!
# Cyclic-correlation data at exponent 1831: residues 905--914

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

private theorem nat_phase_correlation_905 :
    natCorrelation (905 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_906 :
    natCorrelation (906 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_907 :
    natCorrelation (907 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_908 :
    natCorrelation (908 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_909 :
    natCorrelation (909 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_910 :
    natCorrelation (910 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_911 :
    natCorrelation (911 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_912 :
    natCorrelation (912 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_913 :
    natCorrelation (913 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_914 :
    natCorrelation (914 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk88 (i : Fin 10) :
    let d : Cyc := ((905 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_905
  · exact phaseCorrelation_of_nat nat_phase_correlation_906
  · exact phaseCorrelation_of_nat nat_phase_correlation_907
  · exact phaseCorrelation_of_nat nat_phase_correlation_908
  · exact phaseCorrelation_of_nat nat_phase_correlation_909
  · exact phaseCorrelation_of_nat nat_phase_correlation_910
  · exact phaseCorrelation_of_nat nat_phase_correlation_911
  · exact phaseCorrelation_of_nat nat_phase_correlation_912
  · exact phaseCorrelation_of_nat nat_phase_correlation_913
  · exact phaseCorrelation_of_nat nat_phase_correlation_914

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
