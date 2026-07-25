import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationNat

/-!
# Cyclic-correlation data at exponent 1381: residues 0--34

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

private theorem nat_phase_correlation_5 :
    natCorrelation (5 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_6 :
    natCorrelation (6 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_7 :
    natCorrelation (7 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_8 :
    natCorrelation (8 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_9 :
    natCorrelation (9 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_10 :
    natCorrelation (10 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_11 :
    natCorrelation (11 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_12 :
    natCorrelation (12 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_13 :
    natCorrelation (13 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_14 :
    natCorrelation (14 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_15 :
    natCorrelation (15 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_16 :
    natCorrelation (16 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_17 :
    natCorrelation (17 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_18 :
    natCorrelation (18 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_19 :
    natCorrelation (19 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_20 :
    natCorrelation (20 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_21 :
    natCorrelation (21 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_22 :
    natCorrelation (22 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_23 :
    natCorrelation (23 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_24 :
    natCorrelation (24 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_25 :
    natCorrelation (25 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_26 :
    natCorrelation (26 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_27 :
    natCorrelation (27 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_28 :
    natCorrelation (28 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_29 :
    natCorrelation (29 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_30 :
    natCorrelation (30 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_31 :
    natCorrelation (31 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_32 :
    natCorrelation (32 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_33 :
    natCorrelation (33 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_34 :
    natCorrelation (34 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `35`-shift block. -/
theorem phase_correlation_chunk0 (i : Fin 35) :
    let d : Cyc := ((0 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_0
  · exact phaseCorrelation_of_nat nat_phase_correlation_1
  · exact phaseCorrelation_of_nat nat_phase_correlation_2
  · exact phaseCorrelation_of_nat nat_phase_correlation_3
  · exact phaseCorrelation_of_nat nat_phase_correlation_4
  · exact phaseCorrelation_of_nat nat_phase_correlation_5
  · exact phaseCorrelation_of_nat nat_phase_correlation_6
  · exact phaseCorrelation_of_nat nat_phase_correlation_7
  · exact phaseCorrelation_of_nat nat_phase_correlation_8
  · exact phaseCorrelation_of_nat nat_phase_correlation_9
  · exact phaseCorrelation_of_nat nat_phase_correlation_10
  · exact phaseCorrelation_of_nat nat_phase_correlation_11
  · exact phaseCorrelation_of_nat nat_phase_correlation_12
  · exact phaseCorrelation_of_nat nat_phase_correlation_13
  · exact phaseCorrelation_of_nat nat_phase_correlation_14
  · exact phaseCorrelation_of_nat nat_phase_correlation_15
  · exact phaseCorrelation_of_nat nat_phase_correlation_16
  · exact phaseCorrelation_of_nat nat_phase_correlation_17
  · exact phaseCorrelation_of_nat nat_phase_correlation_18
  · exact phaseCorrelation_of_nat nat_phase_correlation_19
  · exact phaseCorrelation_of_nat nat_phase_correlation_20
  · exact phaseCorrelation_of_nat nat_phase_correlation_21
  · exact phaseCorrelation_of_nat nat_phase_correlation_22
  · exact phaseCorrelation_of_nat nat_phase_correlation_23
  · exact phaseCorrelation_of_nat nat_phase_correlation_24
  · exact phaseCorrelation_of_nat nat_phase_correlation_25
  · exact phaseCorrelation_of_nat nat_phase_correlation_26
  · exact phaseCorrelation_of_nat nat_phase_correlation_27
  · exact phaseCorrelation_of_nat nat_phase_correlation_28
  · exact phaseCorrelation_of_nat nat_phase_correlation_29
  · exact phaseCorrelation_of_nat nat_phase_correlation_30
  · exact phaseCorrelation_of_nat nat_phase_correlation_31
  · exact phaseCorrelation_of_nat nat_phase_correlation_32
  · exact phaseCorrelation_of_nat nat_phase_correlation_33
  · exact phaseCorrelation_of_nat nat_phase_correlation_34

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
