import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk0

/-!
# Cyclic-correlation data at exponent 1381: residues 35--44

This module kernel-checks its shifts as separate tail-recursive natural
computations. Keeping each decision in its own declaration lets Lean
release normalization state before checking the next shift.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate

noncomputable section

open Fermat.OneThousandThreeHundredEightyOne.CircularUnitCyclic
open Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem nat_phase_correlation_35 :
    natCorrelation (35 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_36 :
    natCorrelation (36 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_37 :
    natCorrelation (37 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_38 :
    natCorrelation (38 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_39 :
    natCorrelation (39 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_40 :
    natCorrelation (40 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_41 :
    natCorrelation (41 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_42 :
    natCorrelation (42 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_43 :
    natCorrelation (43 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_44 :
    natCorrelation (44 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk1 (i : Fin 10) :
    let d : Cyc := ((35 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_35
  · exact phaseCorrelation_of_nat nat_phase_correlation_36
  · exact phaseCorrelation_of_nat nat_phase_correlation_37
  · exact phaseCorrelation_of_nat nat_phase_correlation_38
  · exact phaseCorrelation_of_nat nat_phase_correlation_39
  · exact phaseCorrelation_of_nat nat_phase_correlation_40
  · exact phaseCorrelation_of_nat nat_phase_correlation_41
  · exact phaseCorrelation_of_nat nat_phase_correlation_42
  · exact phaseCorrelation_of_nat nat_phase_correlation_43
  · exact phaseCorrelation_of_nat nat_phase_correlation_44

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
