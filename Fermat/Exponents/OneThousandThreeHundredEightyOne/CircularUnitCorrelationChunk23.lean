import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk19
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk20
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk21

/-!
# Cyclic-correlation data at exponent 1381: residues 255--264

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

private theorem nat_phase_correlation_255 :
    natCorrelation (255 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_256 :
    natCorrelation (256 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_257 :
    natCorrelation (257 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_258 :
    natCorrelation (258 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_259 :
    natCorrelation (259 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_260 :
    natCorrelation (260 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_261 :
    natCorrelation (261 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_262 :
    natCorrelation (262 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_263 :
    natCorrelation (263 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_264 :
    natCorrelation (264 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk23 (i : Fin 10) :
    let d : Cyc := ((255 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_255
  · exact phaseCorrelation_of_nat nat_phase_correlation_256
  · exact phaseCorrelation_of_nat nat_phase_correlation_257
  · exact phaseCorrelation_of_nat nat_phase_correlation_258
  · exact phaseCorrelation_of_nat nat_phase_correlation_259
  · exact phaseCorrelation_of_nat nat_phase_correlation_260
  · exact phaseCorrelation_of_nat nat_phase_correlation_261
  · exact phaseCorrelation_of_nat nat_phase_correlation_262
  · exact phaseCorrelation_of_nat nat_phase_correlation_263
  · exact phaseCorrelation_of_nat nat_phase_correlation_264

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
