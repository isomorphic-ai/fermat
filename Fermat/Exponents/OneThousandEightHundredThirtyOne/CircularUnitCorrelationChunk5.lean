import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk1
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk2
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk3

/-!
# Cyclic-correlation data at exponent 1831: residues 75--84

This module kernel-checks its shifts as separate tail-recursive natural
computations. Keeping each decision in its own declaration lets Lean
release normalization state before checking the next shift.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate

noncomputable section

open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem nat_phase_correlation_75 :
    natCorrelation (75 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_76 :
    natCorrelation (76 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_77 :
    natCorrelation (77 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_78 :
    natCorrelation (78 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_79 :
    natCorrelation (79 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_80 :
    natCorrelation (80 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_81 :
    natCorrelation (81 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_82 :
    natCorrelation (82 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_83 :
    natCorrelation (83 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_84 :
    natCorrelation (84 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk5 (i : Fin 10) :
    let d : Cyc := ((75 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_75
  · exact phaseCorrelation_of_nat nat_phase_correlation_76
  · exact phaseCorrelation_of_nat nat_phase_correlation_77
  · exact phaseCorrelation_of_nat nat_phase_correlation_78
  · exact phaseCorrelation_of_nat nat_phase_correlation_79
  · exact phaseCorrelation_of_nat nat_phase_correlation_80
  · exact phaseCorrelation_of_nat nat_phase_correlation_81
  · exact phaseCorrelation_of_nat nat_phase_correlation_82
  · exact phaseCorrelation_of_nat nat_phase_correlation_83
  · exact phaseCorrelation_of_nat nat_phase_correlation_84

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
