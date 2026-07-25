import Fermat.SixHundredSeven.CircularUnitCorrelationNat

/-!
# Cyclic-correlation data at exponent 607: residues 0--4

This module kernel-checks five or fewer shifts as separate tail-recursive
natural computations. The modules are arranged in restartable dependency
tiers of width ten.
-/

namespace Fermat.SixHundredSeven.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredSeven.CircularUnitCyclic
open Fermat.SixHundredSeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem nat_phase_correlation_0 :
    natCorrelation (0 : Cyc) = 1 := by
  decide

private theorem nat_phase_correlation_1 :
    natCorrelation (1 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_2 :
    natCorrelation (2 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_3 :
    natCorrelation (3 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_4 :
    natCorrelation (4 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk0 (i : Fin 5) :
    let d : Cyc := ((0 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_0
  · exact phaseCorrelation_of_nat nat_phase_correlation_1
  · exact phaseCorrelation_of_nat nat_phase_correlation_2
  · exact phaseCorrelation_of_nat nat_phase_correlation_3
  · exact phaseCorrelation_of_nat nat_phase_correlation_4

end

end Fermat.SixHundredSeven.CircularUnitCertificate
