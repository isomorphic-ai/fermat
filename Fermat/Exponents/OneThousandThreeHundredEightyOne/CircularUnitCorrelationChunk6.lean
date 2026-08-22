import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk3
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk4

/-!
# Cyclic-correlation data at exponent 1381: residues 85--94

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

private theorem nat_phase_correlation_85 :
    natCorrelation (85 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_86 :
    natCorrelation (86 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_87 :
    natCorrelation (87 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_88 :
    natCorrelation (88 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_89 :
    natCorrelation (89 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_90 :
    natCorrelation (90 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_91 :
    natCorrelation (91 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_92 :
    natCorrelation (92 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_93 :
    natCorrelation (93 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_94 :
    natCorrelation (94 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk6 (i : Fin 10) :
    let d : Cyc := ((85 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_85
  · exact phaseCorrelation_of_nat nat_phase_correlation_86
  · exact phaseCorrelation_of_nat nat_phase_correlation_87
  · exact phaseCorrelation_of_nat nat_phase_correlation_88
  · exact phaseCorrelation_of_nat nat_phase_correlation_89
  · exact phaseCorrelation_of_nat nat_phase_correlation_90
  · exact phaseCorrelation_of_nat nat_phase_correlation_91
  · exact phaseCorrelation_of_nat nat_phase_correlation_92
  · exact phaseCorrelation_of_nat nat_phase_correlation_93
  · exact phaseCorrelation_of_nat nat_phase_correlation_94

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
