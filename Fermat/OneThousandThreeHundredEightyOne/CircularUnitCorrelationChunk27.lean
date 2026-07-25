import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk22
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk23
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk24

/-!
# Cyclic-correlation data at exponent 1381: residues 295--304

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

private theorem nat_phase_correlation_295 :
    natCorrelation (295 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_296 :
    natCorrelation (296 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_297 :
    natCorrelation (297 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_298 :
    natCorrelation (298 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_299 :
    natCorrelation (299 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_300 :
    natCorrelation (300 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_301 :
    natCorrelation (301 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_302 :
    natCorrelation (302 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_303 :
    natCorrelation (303 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_304 :
    natCorrelation (304 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk27 (i : Fin 10) :
    let d : Cyc := ((295 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_295
  · exact phaseCorrelation_of_nat nat_phase_correlation_296
  · exact phaseCorrelation_of_nat nat_phase_correlation_297
  · exact phaseCorrelation_of_nat nat_phase_correlation_298
  · exact phaseCorrelation_of_nat nat_phase_correlation_299
  · exact phaseCorrelation_of_nat nat_phase_correlation_300
  · exact phaseCorrelation_of_nat nat_phase_correlation_301
  · exact phaseCorrelation_of_nat nat_phase_correlation_302
  · exact phaseCorrelation_of_nat nat_phase_correlation_303
  · exact phaseCorrelation_of_nat nat_phase_correlation_304

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
