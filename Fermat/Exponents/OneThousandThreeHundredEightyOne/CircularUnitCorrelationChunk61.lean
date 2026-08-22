import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk58
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk59
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk60

/-!
# Cyclic-correlation data at exponent 1381: residues 635--644

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

private theorem nat_phase_correlation_635 :
    natCorrelation (635 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_636 :
    natCorrelation (636 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_637 :
    natCorrelation (637 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_638 :
    natCorrelation (638 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_639 :
    natCorrelation (639 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_640 :
    natCorrelation (640 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_641 :
    natCorrelation (641 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_642 :
    natCorrelation (642 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_643 :
    natCorrelation (643 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_644 :
    natCorrelation (644 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk61 (i : Fin 10) :
    let d : Cyc := ((635 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_635
  · exact phaseCorrelation_of_nat nat_phase_correlation_636
  · exact phaseCorrelation_of_nat nat_phase_correlation_637
  · exact phaseCorrelation_of_nat nat_phase_correlation_638
  · exact phaseCorrelation_of_nat nat_phase_correlation_639
  · exact phaseCorrelation_of_nat nat_phase_correlation_640
  · exact phaseCorrelation_of_nat nat_phase_correlation_641
  · exact phaseCorrelation_of_nat nat_phase_correlation_642
  · exact phaseCorrelation_of_nat nat_phase_correlation_643
  · exact phaseCorrelation_of_nat nat_phase_correlation_644

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
