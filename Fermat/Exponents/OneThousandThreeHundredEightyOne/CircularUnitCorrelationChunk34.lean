import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk31
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk32
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk33

/-!
# Cyclic-correlation data at exponent 1381: residues 365--374

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

private theorem nat_phase_correlation_365 :
    natCorrelation (365 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_366 :
    natCorrelation (366 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_367 :
    natCorrelation (367 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_368 :
    natCorrelation (368 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_369 :
    natCorrelation (369 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_370 :
    natCorrelation (370 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_371 :
    natCorrelation (371 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_372 :
    natCorrelation (372 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_373 :
    natCorrelation (373 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_374 :
    natCorrelation (374 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk34 (i : Fin 10) :
    let d : Cyc := ((365 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_365
  · exact phaseCorrelation_of_nat nat_phase_correlation_366
  · exact phaseCorrelation_of_nat nat_phase_correlation_367
  · exact phaseCorrelation_of_nat nat_phase_correlation_368
  · exact phaseCorrelation_of_nat nat_phase_correlation_369
  · exact phaseCorrelation_of_nat nat_phase_correlation_370
  · exact phaseCorrelation_of_nat nat_phase_correlation_371
  · exact phaseCorrelation_of_nat nat_phase_correlation_372
  · exact phaseCorrelation_of_nat nat_phase_correlation_373
  · exact phaseCorrelation_of_nat nat_phase_correlation_374

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
