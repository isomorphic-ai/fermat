import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk0

/-!
# Cyclic-correlation data at exponent 1381: residues 45--54

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

private theorem nat_phase_correlation_45 :
    natCorrelation (45 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_46 :
    natCorrelation (46 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_47 :
    natCorrelation (47 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_48 :
    natCorrelation (48 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_49 :
    natCorrelation (49 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_50 :
    natCorrelation (50 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_51 :
    natCorrelation (51 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_52 :
    natCorrelation (52 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_53 :
    natCorrelation (53 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_54 :
    natCorrelation (54 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk2 (i : Fin 10) :
    let d : Cyc := ((45 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_45
  · exact phaseCorrelation_of_nat nat_phase_correlation_46
  · exact phaseCorrelation_of_nat nat_phase_correlation_47
  · exact phaseCorrelation_of_nat nat_phase_correlation_48
  · exact phaseCorrelation_of_nat nat_phase_correlation_49
  · exact phaseCorrelation_of_nat nat_phase_correlation_50
  · exact phaseCorrelation_of_nat nat_phase_correlation_51
  · exact phaseCorrelation_of_nat nat_phase_correlation_52
  · exact phaseCorrelation_of_nat nat_phase_correlation_53
  · exact phaseCorrelation_of_nat nat_phase_correlation_54

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
