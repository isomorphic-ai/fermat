import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk55
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk56
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk57

/-!
# Cyclic-correlation data at exponent 1831: residues 615--624

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

private theorem nat_phase_correlation_615 :
    natCorrelation (615 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_616 :
    natCorrelation (616 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_617 :
    natCorrelation (617 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_618 :
    natCorrelation (618 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_619 :
    natCorrelation (619 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_620 :
    natCorrelation (620 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_621 :
    natCorrelation (621 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_622 :
    natCorrelation (622 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_623 :
    natCorrelation (623 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_624 :
    natCorrelation (624 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk59 (i : Fin 10) :
    let d : Cyc := ((615 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_615
  · exact phaseCorrelation_of_nat nat_phase_correlation_616
  · exact phaseCorrelation_of_nat nat_phase_correlation_617
  · exact phaseCorrelation_of_nat nat_phase_correlation_618
  · exact phaseCorrelation_of_nat nat_phase_correlation_619
  · exact phaseCorrelation_of_nat nat_phase_correlation_620
  · exact phaseCorrelation_of_nat nat_phase_correlation_621
  · exact phaseCorrelation_of_nat nat_phase_correlation_622
  · exact phaseCorrelation_of_nat nat_phase_correlation_623
  · exact phaseCorrelation_of_nat nat_phase_correlation_624

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
