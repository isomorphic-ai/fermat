import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk37
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk38
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk39

/-!
# Cyclic-correlation data at exponent 1381: residues 425--434

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

private theorem nat_phase_correlation_425 :
    natCorrelation (425 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_426 :
    natCorrelation (426 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_427 :
    natCorrelation (427 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_428 :
    natCorrelation (428 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_429 :
    natCorrelation (429 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_430 :
    natCorrelation (430 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_431 :
    natCorrelation (431 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_432 :
    natCorrelation (432 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_433 :
    natCorrelation (433 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_434 :
    natCorrelation (434 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk40 (i : Fin 10) :
    let d : Cyc := ((425 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_425
  · exact phaseCorrelation_of_nat nat_phase_correlation_426
  · exact phaseCorrelation_of_nat nat_phase_correlation_427
  · exact phaseCorrelation_of_nat nat_phase_correlation_428
  · exact phaseCorrelation_of_nat nat_phase_correlation_429
  · exact phaseCorrelation_of_nat nat_phase_correlation_430
  · exact phaseCorrelation_of_nat nat_phase_correlation_431
  · exact phaseCorrelation_of_nat nat_phase_correlation_432
  · exact phaseCorrelation_of_nat nat_phase_correlation_433
  · exact phaseCorrelation_of_nat nat_phase_correlation_434

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
