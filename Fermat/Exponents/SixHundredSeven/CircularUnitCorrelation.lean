import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk51
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk52
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk53
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk54
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk55
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk56
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk57
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk58
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk59
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelationChunk60

/-!
# Finite cyclic-correlation data at exponent 607

Sixty-one restartable modules check all 303 cyclic shifts in blocks of five,
with a three-shift tail. The dependency graph has six parallel tiers of
width ten after the root module. Every concrete correlation is checked by
the Lean kernel as a separate tail-recursive natural computation. The final
stitch groups the chunk theorems into six bounded segments and reaches those
segments through a balanced dispatcher.
-/

namespace Fermat.SixHundredSeven.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredSeven.CircularUnitCyclic
open Fermat.SixHundredSeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! ## Generic chunk lift -/

/-- Lift a bounded chunk theorem from its local `Fin` coordinate to the
ambient cyclic coordinate. All index arithmetic and cast simplification is
elaborated once here rather than once per concrete chunk. -/
private theorem phase_correlation_of_chunk
    {offset size : ℕ} (d : Cyc)
    (hlower : offset ≤ d.val) (hupper : d.val < offset + size)
    (hchunk : ∀ i : Fin size,
      let e : Cyc := ((offset + i.val : ℕ) : Cyc)
      (∑ u : Cyc, symbolPhase u * correlationInverse (u + e)) =
        if e = 0 then 1 else 0) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  let i : Fin size := ⟨d.val - offset, by omega⟩
  simpa only [i, Nat.add_sub_of_le hlower, ZMod.natCast_zmod_val] using
    hchunk i

/-! ## Bounded segment dispatchers -/

private theorem phase_correlation_segment0
    (d : Cyc) (hupper : d.val < 50) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h0 : d.val < 5
  · exact
      phase_correlation_of_chunk (offset := 0) (size := 5)
        d (Nat.zero_le _) h0 phase_correlation_chunk0
  by_cases h1 : d.val < 10
  · exact
      phase_correlation_of_chunk (offset := 5) (size := 5)
        d (Nat.le_of_not_gt h0) h1 phase_correlation_chunk1
  by_cases h2 : d.val < 15
  · exact
      phase_correlation_of_chunk (offset := 10) (size := 5)
        d (Nat.le_of_not_gt h1) h2 phase_correlation_chunk2
  by_cases h3 : d.val < 20
  · exact
      phase_correlation_of_chunk (offset := 15) (size := 5)
        d (Nat.le_of_not_gt h2) h3 phase_correlation_chunk3
  by_cases h4 : d.val < 25
  · exact
      phase_correlation_of_chunk (offset := 20) (size := 5)
        d (Nat.le_of_not_gt h3) h4 phase_correlation_chunk4
  by_cases h5 : d.val < 30
  · exact
      phase_correlation_of_chunk (offset := 25) (size := 5)
        d (Nat.le_of_not_gt h4) h5 phase_correlation_chunk5
  by_cases h6 : d.val < 35
  · exact
      phase_correlation_of_chunk (offset := 30) (size := 5)
        d (Nat.le_of_not_gt h5) h6 phase_correlation_chunk6
  by_cases h7 : d.val < 40
  · exact
      phase_correlation_of_chunk (offset := 35) (size := 5)
        d (Nat.le_of_not_gt h6) h7 phase_correlation_chunk7
  by_cases h8 : d.val < 45
  · exact
      phase_correlation_of_chunk (offset := 40) (size := 5)
        d (Nat.le_of_not_gt h7) h8 phase_correlation_chunk8
  · exact
      phase_correlation_of_chunk (offset := 45) (size := 5)
        d (Nat.le_of_not_gt h8) hupper phase_correlation_chunk9
private theorem phase_correlation_segment1
    (d : Cyc) (hlower : 50 ≤ d.val) (hupper : d.val < 100) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h10 : d.val < 55
  · exact
      phase_correlation_of_chunk (offset := 50) (size := 5)
        d hlower h10 phase_correlation_chunk10
  by_cases h11 : d.val < 60
  · exact
      phase_correlation_of_chunk (offset := 55) (size := 5)
        d (Nat.le_of_not_gt h10) h11 phase_correlation_chunk11
  by_cases h12 : d.val < 65
  · exact
      phase_correlation_of_chunk (offset := 60) (size := 5)
        d (Nat.le_of_not_gt h11) h12 phase_correlation_chunk12
  by_cases h13 : d.val < 70
  · exact
      phase_correlation_of_chunk (offset := 65) (size := 5)
        d (Nat.le_of_not_gt h12) h13 phase_correlation_chunk13
  by_cases h14 : d.val < 75
  · exact
      phase_correlation_of_chunk (offset := 70) (size := 5)
        d (Nat.le_of_not_gt h13) h14 phase_correlation_chunk14
  by_cases h15 : d.val < 80
  · exact
      phase_correlation_of_chunk (offset := 75) (size := 5)
        d (Nat.le_of_not_gt h14) h15 phase_correlation_chunk15
  by_cases h16 : d.val < 85
  · exact
      phase_correlation_of_chunk (offset := 80) (size := 5)
        d (Nat.le_of_not_gt h15) h16 phase_correlation_chunk16
  by_cases h17 : d.val < 90
  · exact
      phase_correlation_of_chunk (offset := 85) (size := 5)
        d (Nat.le_of_not_gt h16) h17 phase_correlation_chunk17
  by_cases h18 : d.val < 95
  · exact
      phase_correlation_of_chunk (offset := 90) (size := 5)
        d (Nat.le_of_not_gt h17) h18 phase_correlation_chunk18
  · exact
      phase_correlation_of_chunk (offset := 95) (size := 5)
        d (Nat.le_of_not_gt h18) hupper phase_correlation_chunk19
private theorem phase_correlation_segment2
    (d : Cyc) (hlower : 100 ≤ d.val) (hupper : d.val < 150) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h20 : d.val < 105
  · exact
      phase_correlation_of_chunk (offset := 100) (size := 5)
        d hlower h20 phase_correlation_chunk20
  by_cases h21 : d.val < 110
  · exact
      phase_correlation_of_chunk (offset := 105) (size := 5)
        d (Nat.le_of_not_gt h20) h21 phase_correlation_chunk21
  by_cases h22 : d.val < 115
  · exact
      phase_correlation_of_chunk (offset := 110) (size := 5)
        d (Nat.le_of_not_gt h21) h22 phase_correlation_chunk22
  by_cases h23 : d.val < 120
  · exact
      phase_correlation_of_chunk (offset := 115) (size := 5)
        d (Nat.le_of_not_gt h22) h23 phase_correlation_chunk23
  by_cases h24 : d.val < 125
  · exact
      phase_correlation_of_chunk (offset := 120) (size := 5)
        d (Nat.le_of_not_gt h23) h24 phase_correlation_chunk24
  by_cases h25 : d.val < 130
  · exact
      phase_correlation_of_chunk (offset := 125) (size := 5)
        d (Nat.le_of_not_gt h24) h25 phase_correlation_chunk25
  by_cases h26 : d.val < 135
  · exact
      phase_correlation_of_chunk (offset := 130) (size := 5)
        d (Nat.le_of_not_gt h25) h26 phase_correlation_chunk26
  by_cases h27 : d.val < 140
  · exact
      phase_correlation_of_chunk (offset := 135) (size := 5)
        d (Nat.le_of_not_gt h26) h27 phase_correlation_chunk27
  by_cases h28 : d.val < 145
  · exact
      phase_correlation_of_chunk (offset := 140) (size := 5)
        d (Nat.le_of_not_gt h27) h28 phase_correlation_chunk28
  · exact
      phase_correlation_of_chunk (offset := 145) (size := 5)
        d (Nat.le_of_not_gt h28) hupper phase_correlation_chunk29
private theorem phase_correlation_segment3
    (d : Cyc) (hlower : 150 ≤ d.val) (hupper : d.val < 200) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h30 : d.val < 155
  · exact
      phase_correlation_of_chunk (offset := 150) (size := 5)
        d hlower h30 phase_correlation_chunk30
  by_cases h31 : d.val < 160
  · exact
      phase_correlation_of_chunk (offset := 155) (size := 5)
        d (Nat.le_of_not_gt h30) h31 phase_correlation_chunk31
  by_cases h32 : d.val < 165
  · exact
      phase_correlation_of_chunk (offset := 160) (size := 5)
        d (Nat.le_of_not_gt h31) h32 phase_correlation_chunk32
  by_cases h33 : d.val < 170
  · exact
      phase_correlation_of_chunk (offset := 165) (size := 5)
        d (Nat.le_of_not_gt h32) h33 phase_correlation_chunk33
  by_cases h34 : d.val < 175
  · exact
      phase_correlation_of_chunk (offset := 170) (size := 5)
        d (Nat.le_of_not_gt h33) h34 phase_correlation_chunk34
  by_cases h35 : d.val < 180
  · exact
      phase_correlation_of_chunk (offset := 175) (size := 5)
        d (Nat.le_of_not_gt h34) h35 phase_correlation_chunk35
  by_cases h36 : d.val < 185
  · exact
      phase_correlation_of_chunk (offset := 180) (size := 5)
        d (Nat.le_of_not_gt h35) h36 phase_correlation_chunk36
  by_cases h37 : d.val < 190
  · exact
      phase_correlation_of_chunk (offset := 185) (size := 5)
        d (Nat.le_of_not_gt h36) h37 phase_correlation_chunk37
  by_cases h38 : d.val < 195
  · exact
      phase_correlation_of_chunk (offset := 190) (size := 5)
        d (Nat.le_of_not_gt h37) h38 phase_correlation_chunk38
  · exact
      phase_correlation_of_chunk (offset := 195) (size := 5)
        d (Nat.le_of_not_gt h38) hupper phase_correlation_chunk39
private theorem phase_correlation_segment4
    (d : Cyc) (hlower : 200 ≤ d.val) (hupper : d.val < 250) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h40 : d.val < 205
  · exact
      phase_correlation_of_chunk (offset := 200) (size := 5)
        d hlower h40 phase_correlation_chunk40
  by_cases h41 : d.val < 210
  · exact
      phase_correlation_of_chunk (offset := 205) (size := 5)
        d (Nat.le_of_not_gt h40) h41 phase_correlation_chunk41
  by_cases h42 : d.val < 215
  · exact
      phase_correlation_of_chunk (offset := 210) (size := 5)
        d (Nat.le_of_not_gt h41) h42 phase_correlation_chunk42
  by_cases h43 : d.val < 220
  · exact
      phase_correlation_of_chunk (offset := 215) (size := 5)
        d (Nat.le_of_not_gt h42) h43 phase_correlation_chunk43
  by_cases h44 : d.val < 225
  · exact
      phase_correlation_of_chunk (offset := 220) (size := 5)
        d (Nat.le_of_not_gt h43) h44 phase_correlation_chunk44
  by_cases h45 : d.val < 230
  · exact
      phase_correlation_of_chunk (offset := 225) (size := 5)
        d (Nat.le_of_not_gt h44) h45 phase_correlation_chunk45
  by_cases h46 : d.val < 235
  · exact
      phase_correlation_of_chunk (offset := 230) (size := 5)
        d (Nat.le_of_not_gt h45) h46 phase_correlation_chunk46
  by_cases h47 : d.val < 240
  · exact
      phase_correlation_of_chunk (offset := 235) (size := 5)
        d (Nat.le_of_not_gt h46) h47 phase_correlation_chunk47
  by_cases h48 : d.val < 245
  · exact
      phase_correlation_of_chunk (offset := 240) (size := 5)
        d (Nat.le_of_not_gt h47) h48 phase_correlation_chunk48
  · exact
      phase_correlation_of_chunk (offset := 245) (size := 5)
        d (Nat.le_of_not_gt h48) hupper phase_correlation_chunk49
private theorem phase_correlation_segment5
    (d : Cyc) (hlower : 250 ≤ d.val) (hupper : d.val < 303) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h50 : d.val < 255
  · exact
      phase_correlation_of_chunk (offset := 250) (size := 5)
        d hlower h50 phase_correlation_chunk50
  by_cases h51 : d.val < 260
  · exact
      phase_correlation_of_chunk (offset := 255) (size := 5)
        d (Nat.le_of_not_gt h50) h51 phase_correlation_chunk51
  by_cases h52 : d.val < 265
  · exact
      phase_correlation_of_chunk (offset := 260) (size := 5)
        d (Nat.le_of_not_gt h51) h52 phase_correlation_chunk52
  by_cases h53 : d.val < 270
  · exact
      phase_correlation_of_chunk (offset := 265) (size := 5)
        d (Nat.le_of_not_gt h52) h53 phase_correlation_chunk53
  by_cases h54 : d.val < 275
  · exact
      phase_correlation_of_chunk (offset := 270) (size := 5)
        d (Nat.le_of_not_gt h53) h54 phase_correlation_chunk54
  by_cases h55 : d.val < 280
  · exact
      phase_correlation_of_chunk (offset := 275) (size := 5)
        d (Nat.le_of_not_gt h54) h55 phase_correlation_chunk55
  by_cases h56 : d.val < 285
  · exact
      phase_correlation_of_chunk (offset := 280) (size := 5)
        d (Nat.le_of_not_gt h55) h56 phase_correlation_chunk56
  by_cases h57 : d.val < 290
  · exact
      phase_correlation_of_chunk (offset := 285) (size := 5)
        d (Nat.le_of_not_gt h56) h57 phase_correlation_chunk57
  by_cases h58 : d.val < 295
  · exact
      phase_correlation_of_chunk (offset := 290) (size := 5)
        d (Nat.le_of_not_gt h57) h58 phase_correlation_chunk58
  by_cases h59 : d.val < 300
  · exact
      phase_correlation_of_chunk (offset := 295) (size := 5)
        d (Nat.le_of_not_gt h58) h59 phase_correlation_chunk59
  · exact
      phase_correlation_of_chunk (offset := 300) (size := 3)
        d (Nat.le_of_not_gt h59) hupper phase_correlation_chunk60

/-! ## Balanced top-level stitch -/

/-- Kernel-checked cyclic-correlation certificate. -/
theorem phase_correlation (d : Cyc) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h150 : d.val < 150
  · by_cases h50 : d.val < 50
    · exact phase_correlation_segment0 d h50
    · by_cases h100 : d.val < 100
      · exact
          phase_correlation_segment1 d (Nat.le_of_not_gt h50) h100
      · exact
          phase_correlation_segment2 d (Nat.le_of_not_gt h100) h150
  · by_cases h250 : d.val < 250
    · by_cases h200 : d.val < 200
      · exact
          phase_correlation_segment3 d (Nat.le_of_not_gt h150) h200
      · exact
          phase_correlation_segment4 d (Nat.le_of_not_gt h200) h250
    · exact
        phase_correlation_segment5 d (Nat.le_of_not_gt h250)
          (ZMod.val_lt d)

end

end Fermat.SixHundredSeven.CircularUnitCertificate
