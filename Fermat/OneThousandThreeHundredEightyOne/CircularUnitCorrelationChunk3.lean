import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk1
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk2

/-!
# Cyclic-correlation data at exponent 1381: residues 55--64

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

private theorem nat_phase_correlation_55 :
    natCorrelation (55 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_56 :
    natCorrelation (56 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_57 :
    natCorrelation (57 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_58 :
    natCorrelation (58 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_59 :
    natCorrelation (59 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_60 :
    natCorrelation (60 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_61 :
    natCorrelation (61 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_62 :
    natCorrelation (62 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_63 :
    natCorrelation (63 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_64 :
    natCorrelation (64 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk3 (i : Fin 10) :
    let d : Cyc := ((55 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_55
  · exact phaseCorrelation_of_nat nat_phase_correlation_56
  · exact phaseCorrelation_of_nat nat_phase_correlation_57
  · exact phaseCorrelation_of_nat nat_phase_correlation_58
  · exact phaseCorrelation_of_nat nat_phase_correlation_59
  · exact phaseCorrelation_of_nat nat_phase_correlation_60
  · exact phaseCorrelation_of_nat nat_phase_correlation_61
  · exact phaseCorrelation_of_nat nat_phase_correlation_62
  · exact phaseCorrelation_of_nat nat_phase_correlation_63
  · exact phaseCorrelation_of_nat nat_phase_correlation_64

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
