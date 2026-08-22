import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk46
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk47
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk48

/-!
# Cyclic-correlation data at exponent 1381: residues 515--524

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

private theorem nat_phase_correlation_515 :
    natCorrelation (515 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_516 :
    natCorrelation (516 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_517 :
    natCorrelation (517 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_518 :
    natCorrelation (518 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_519 :
    natCorrelation (519 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_520 :
    natCorrelation (520 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_521 :
    natCorrelation (521 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_522 :
    natCorrelation (522 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_523 :
    natCorrelation (523 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_524 :
    natCorrelation (524 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk49 (i : Fin 10) :
    let d : Cyc := ((515 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_515
  · exact phaseCorrelation_of_nat nat_phase_correlation_516
  · exact phaseCorrelation_of_nat nat_phase_correlation_517
  · exact phaseCorrelation_of_nat nat_phase_correlation_518
  · exact phaseCorrelation_of_nat nat_phase_correlation_519
  · exact phaseCorrelation_of_nat nat_phase_correlation_520
  · exact phaseCorrelation_of_nat nat_phase_correlation_521
  · exact phaseCorrelation_of_nat nat_phase_correlation_522
  · exact phaseCorrelation_of_nat nat_phase_correlation_523
  · exact phaseCorrelation_of_nat nat_phase_correlation_524

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
