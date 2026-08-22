import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk86
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk87
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk88

/-!
# Finite cyclic-correlation data at exponent 1831

The first calibration module checks shifts `0` through `34`. The remaining
shifts are serialized in ten-shift modules and arranged in three-file
dependency waves. Every concrete correlation is kernel-checked as a separate
tail-recursive natural computation. The final stitch groups the chunk
theorems into nine bounded segments and reaches those segments through a
balanced dispatcher.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate

noncomputable section

open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

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
    (d : Cyc) (hupper : d.val < 125) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h0 : d.val < 35
  · exact
      phase_correlation_of_chunk (offset := 0) (size := 35)
        d (Nat.zero_le _) h0 phase_correlation_chunk0
  by_cases h1 : d.val < 45
  · exact
      phase_correlation_of_chunk (offset := 35) (size := 10)
        d (Nat.le_of_not_gt h0) h1 phase_correlation_chunk1
  by_cases h2 : d.val < 55
  · exact
      phase_correlation_of_chunk (offset := 45) (size := 10)
        d (Nat.le_of_not_gt h1) h2 phase_correlation_chunk2
  by_cases h3 : d.val < 65
  · exact
      phase_correlation_of_chunk (offset := 55) (size := 10)
        d (Nat.le_of_not_gt h2) h3 phase_correlation_chunk3
  by_cases h4 : d.val < 75
  · exact
      phase_correlation_of_chunk (offset := 65) (size := 10)
        d (Nat.le_of_not_gt h3) h4 phase_correlation_chunk4
  by_cases h5 : d.val < 85
  · exact
      phase_correlation_of_chunk (offset := 75) (size := 10)
        d (Nat.le_of_not_gt h4) h5 phase_correlation_chunk5
  by_cases h6 : d.val < 95
  · exact
      phase_correlation_of_chunk (offset := 85) (size := 10)
        d (Nat.le_of_not_gt h5) h6 phase_correlation_chunk6
  by_cases h7 : d.val < 105
  · exact
      phase_correlation_of_chunk (offset := 95) (size := 10)
        d (Nat.le_of_not_gt h6) h7 phase_correlation_chunk7
  by_cases h8 : d.val < 115
  · exact
      phase_correlation_of_chunk (offset := 105) (size := 10)
        d (Nat.le_of_not_gt h7) h8 phase_correlation_chunk8
  · exact
      phase_correlation_of_chunk (offset := 115) (size := 10)
        d (Nat.le_of_not_gt h8) hupper phase_correlation_chunk9

private theorem phase_correlation_segment1
    (d : Cyc) (hlower : 125 ≤ d.val) (hupper : d.val < 225) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h10 : d.val < 135
  · exact
      phase_correlation_of_chunk (offset := 125) (size := 10)
        d hlower h10 phase_correlation_chunk10
  by_cases h11 : d.val < 145
  · exact
      phase_correlation_of_chunk (offset := 135) (size := 10)
        d (Nat.le_of_not_gt h10) h11 phase_correlation_chunk11
  by_cases h12 : d.val < 155
  · exact
      phase_correlation_of_chunk (offset := 145) (size := 10)
        d (Nat.le_of_not_gt h11) h12 phase_correlation_chunk12
  by_cases h13 : d.val < 165
  · exact
      phase_correlation_of_chunk (offset := 155) (size := 10)
        d (Nat.le_of_not_gt h12) h13 phase_correlation_chunk13
  by_cases h14 : d.val < 175
  · exact
      phase_correlation_of_chunk (offset := 165) (size := 10)
        d (Nat.le_of_not_gt h13) h14 phase_correlation_chunk14
  by_cases h15 : d.val < 185
  · exact
      phase_correlation_of_chunk (offset := 175) (size := 10)
        d (Nat.le_of_not_gt h14) h15 phase_correlation_chunk15
  by_cases h16 : d.val < 195
  · exact
      phase_correlation_of_chunk (offset := 185) (size := 10)
        d (Nat.le_of_not_gt h15) h16 phase_correlation_chunk16
  by_cases h17 : d.val < 205
  · exact
      phase_correlation_of_chunk (offset := 195) (size := 10)
        d (Nat.le_of_not_gt h16) h17 phase_correlation_chunk17
  by_cases h18 : d.val < 215
  · exact
      phase_correlation_of_chunk (offset := 205) (size := 10)
        d (Nat.le_of_not_gt h17) h18 phase_correlation_chunk18
  · exact
      phase_correlation_of_chunk (offset := 215) (size := 10)
        d (Nat.le_of_not_gt h18) hupper phase_correlation_chunk19

private theorem phase_correlation_segment2
    (d : Cyc) (hlower : 225 ≤ d.val) (hupper : d.val < 325) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h20 : d.val < 235
  · exact
      phase_correlation_of_chunk (offset := 225) (size := 10)
        d hlower h20 phase_correlation_chunk20
  by_cases h21 : d.val < 245
  · exact
      phase_correlation_of_chunk (offset := 235) (size := 10)
        d (Nat.le_of_not_gt h20) h21 phase_correlation_chunk21
  by_cases h22 : d.val < 255
  · exact
      phase_correlation_of_chunk (offset := 245) (size := 10)
        d (Nat.le_of_not_gt h21) h22 phase_correlation_chunk22
  by_cases h23 : d.val < 265
  · exact
      phase_correlation_of_chunk (offset := 255) (size := 10)
        d (Nat.le_of_not_gt h22) h23 phase_correlation_chunk23
  by_cases h24 : d.val < 275
  · exact
      phase_correlation_of_chunk (offset := 265) (size := 10)
        d (Nat.le_of_not_gt h23) h24 phase_correlation_chunk24
  by_cases h25 : d.val < 285
  · exact
      phase_correlation_of_chunk (offset := 275) (size := 10)
        d (Nat.le_of_not_gt h24) h25 phase_correlation_chunk25
  by_cases h26 : d.val < 295
  · exact
      phase_correlation_of_chunk (offset := 285) (size := 10)
        d (Nat.le_of_not_gt h25) h26 phase_correlation_chunk26
  by_cases h27 : d.val < 305
  · exact
      phase_correlation_of_chunk (offset := 295) (size := 10)
        d (Nat.le_of_not_gt h26) h27 phase_correlation_chunk27
  by_cases h28 : d.val < 315
  · exact
      phase_correlation_of_chunk (offset := 305) (size := 10)
        d (Nat.le_of_not_gt h27) h28 phase_correlation_chunk28
  · exact
      phase_correlation_of_chunk (offset := 315) (size := 10)
        d (Nat.le_of_not_gt h28) hupper phase_correlation_chunk29

private theorem phase_correlation_segment3
    (d : Cyc) (hlower : 325 ≤ d.val) (hupper : d.val < 425) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h30 : d.val < 335
  · exact
      phase_correlation_of_chunk (offset := 325) (size := 10)
        d hlower h30 phase_correlation_chunk30
  by_cases h31 : d.val < 345
  · exact
      phase_correlation_of_chunk (offset := 335) (size := 10)
        d (Nat.le_of_not_gt h30) h31 phase_correlation_chunk31
  by_cases h32 : d.val < 355
  · exact
      phase_correlation_of_chunk (offset := 345) (size := 10)
        d (Nat.le_of_not_gt h31) h32 phase_correlation_chunk32
  by_cases h33 : d.val < 365
  · exact
      phase_correlation_of_chunk (offset := 355) (size := 10)
        d (Nat.le_of_not_gt h32) h33 phase_correlation_chunk33
  by_cases h34 : d.val < 375
  · exact
      phase_correlation_of_chunk (offset := 365) (size := 10)
        d (Nat.le_of_not_gt h33) h34 phase_correlation_chunk34
  by_cases h35 : d.val < 385
  · exact
      phase_correlation_of_chunk (offset := 375) (size := 10)
        d (Nat.le_of_not_gt h34) h35 phase_correlation_chunk35
  by_cases h36 : d.val < 395
  · exact
      phase_correlation_of_chunk (offset := 385) (size := 10)
        d (Nat.le_of_not_gt h35) h36 phase_correlation_chunk36
  by_cases h37 : d.val < 405
  · exact
      phase_correlation_of_chunk (offset := 395) (size := 10)
        d (Nat.le_of_not_gt h36) h37 phase_correlation_chunk37
  by_cases h38 : d.val < 415
  · exact
      phase_correlation_of_chunk (offset := 405) (size := 10)
        d (Nat.le_of_not_gt h37) h38 phase_correlation_chunk38
  · exact
      phase_correlation_of_chunk (offset := 415) (size := 10)
        d (Nat.le_of_not_gt h38) hupper phase_correlation_chunk39

private theorem phase_correlation_segment4
    (d : Cyc) (hlower : 425 ≤ d.val) (hupper : d.val < 525) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h40 : d.val < 435
  · exact
      phase_correlation_of_chunk (offset := 425) (size := 10)
        d hlower h40 phase_correlation_chunk40
  by_cases h41 : d.val < 445
  · exact
      phase_correlation_of_chunk (offset := 435) (size := 10)
        d (Nat.le_of_not_gt h40) h41 phase_correlation_chunk41
  by_cases h42 : d.val < 455
  · exact
      phase_correlation_of_chunk (offset := 445) (size := 10)
        d (Nat.le_of_not_gt h41) h42 phase_correlation_chunk42
  by_cases h43 : d.val < 465
  · exact
      phase_correlation_of_chunk (offset := 455) (size := 10)
        d (Nat.le_of_not_gt h42) h43 phase_correlation_chunk43
  by_cases h44 : d.val < 475
  · exact
      phase_correlation_of_chunk (offset := 465) (size := 10)
        d (Nat.le_of_not_gt h43) h44 phase_correlation_chunk44
  by_cases h45 : d.val < 485
  · exact
      phase_correlation_of_chunk (offset := 475) (size := 10)
        d (Nat.le_of_not_gt h44) h45 phase_correlation_chunk45
  by_cases h46 : d.val < 495
  · exact
      phase_correlation_of_chunk (offset := 485) (size := 10)
        d (Nat.le_of_not_gt h45) h46 phase_correlation_chunk46
  by_cases h47 : d.val < 505
  · exact
      phase_correlation_of_chunk (offset := 495) (size := 10)
        d (Nat.le_of_not_gt h46) h47 phase_correlation_chunk47
  by_cases h48 : d.val < 515
  · exact
      phase_correlation_of_chunk (offset := 505) (size := 10)
        d (Nat.le_of_not_gt h47) h48 phase_correlation_chunk48
  · exact
      phase_correlation_of_chunk (offset := 515) (size := 10)
        d (Nat.le_of_not_gt h48) hupper phase_correlation_chunk49

private theorem phase_correlation_segment5
    (d : Cyc) (hlower : 525 ≤ d.val) (hupper : d.val < 625) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h50 : d.val < 535
  · exact
      phase_correlation_of_chunk (offset := 525) (size := 10)
        d hlower h50 phase_correlation_chunk50
  by_cases h51 : d.val < 545
  · exact
      phase_correlation_of_chunk (offset := 535) (size := 10)
        d (Nat.le_of_not_gt h50) h51 phase_correlation_chunk51
  by_cases h52 : d.val < 555
  · exact
      phase_correlation_of_chunk (offset := 545) (size := 10)
        d (Nat.le_of_not_gt h51) h52 phase_correlation_chunk52
  by_cases h53 : d.val < 565
  · exact
      phase_correlation_of_chunk (offset := 555) (size := 10)
        d (Nat.le_of_not_gt h52) h53 phase_correlation_chunk53
  by_cases h54 : d.val < 575
  · exact
      phase_correlation_of_chunk (offset := 565) (size := 10)
        d (Nat.le_of_not_gt h53) h54 phase_correlation_chunk54
  by_cases h55 : d.val < 585
  · exact
      phase_correlation_of_chunk (offset := 575) (size := 10)
        d (Nat.le_of_not_gt h54) h55 phase_correlation_chunk55
  by_cases h56 : d.val < 595
  · exact
      phase_correlation_of_chunk (offset := 585) (size := 10)
        d (Nat.le_of_not_gt h55) h56 phase_correlation_chunk56
  by_cases h57 : d.val < 605
  · exact
      phase_correlation_of_chunk (offset := 595) (size := 10)
        d (Nat.le_of_not_gt h56) h57 phase_correlation_chunk57
  by_cases h58 : d.val < 615
  · exact
      phase_correlation_of_chunk (offset := 605) (size := 10)
        d (Nat.le_of_not_gt h57) h58 phase_correlation_chunk58
  · exact
      phase_correlation_of_chunk (offset := 615) (size := 10)
        d (Nat.le_of_not_gt h58) hupper phase_correlation_chunk59

private theorem phase_correlation_segment6
    (d : Cyc) (hlower : 625 ≤ d.val) (hupper : d.val < 725) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h60 : d.val < 635
  · exact
      phase_correlation_of_chunk (offset := 625) (size := 10)
        d hlower h60 phase_correlation_chunk60
  by_cases h61 : d.val < 645
  · exact
      phase_correlation_of_chunk (offset := 635) (size := 10)
        d (Nat.le_of_not_gt h60) h61 phase_correlation_chunk61
  by_cases h62 : d.val < 655
  · exact
      phase_correlation_of_chunk (offset := 645) (size := 10)
        d (Nat.le_of_not_gt h61) h62 phase_correlation_chunk62
  by_cases h63 : d.val < 665
  · exact
      phase_correlation_of_chunk (offset := 655) (size := 10)
        d (Nat.le_of_not_gt h62) h63 phase_correlation_chunk63
  by_cases h64 : d.val < 675
  · exact
      phase_correlation_of_chunk (offset := 665) (size := 10)
        d (Nat.le_of_not_gt h63) h64 phase_correlation_chunk64
  by_cases h65 : d.val < 685
  · exact
      phase_correlation_of_chunk (offset := 675) (size := 10)
        d (Nat.le_of_not_gt h64) h65 phase_correlation_chunk65
  by_cases h66 : d.val < 695
  · exact
      phase_correlation_of_chunk (offset := 685) (size := 10)
        d (Nat.le_of_not_gt h65) h66 phase_correlation_chunk66
  by_cases h67 : d.val < 705
  · exact
      phase_correlation_of_chunk (offset := 695) (size := 10)
        d (Nat.le_of_not_gt h66) h67 phase_correlation_chunk67
  by_cases h68 : d.val < 715
  · exact
      phase_correlation_of_chunk (offset := 705) (size := 10)
        d (Nat.le_of_not_gt h67) h68 phase_correlation_chunk68
  · exact
      phase_correlation_of_chunk (offset := 715) (size := 10)
        d (Nat.le_of_not_gt h68) hupper phase_correlation_chunk69

private theorem phase_correlation_segment7
    (d : Cyc) (hlower : 725 ≤ d.val) (hupper : d.val < 825) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h70 : d.val < 735
  · exact
      phase_correlation_of_chunk (offset := 725) (size := 10)
        d hlower h70 phase_correlation_chunk70
  by_cases h71 : d.val < 745
  · exact
      phase_correlation_of_chunk (offset := 735) (size := 10)
        d (Nat.le_of_not_gt h70) h71 phase_correlation_chunk71
  by_cases h72 : d.val < 755
  · exact
      phase_correlation_of_chunk (offset := 745) (size := 10)
        d (Nat.le_of_not_gt h71) h72 phase_correlation_chunk72
  by_cases h73 : d.val < 765
  · exact
      phase_correlation_of_chunk (offset := 755) (size := 10)
        d (Nat.le_of_not_gt h72) h73 phase_correlation_chunk73
  by_cases h74 : d.val < 775
  · exact
      phase_correlation_of_chunk (offset := 765) (size := 10)
        d (Nat.le_of_not_gt h73) h74 phase_correlation_chunk74
  by_cases h75 : d.val < 785
  · exact
      phase_correlation_of_chunk (offset := 775) (size := 10)
        d (Nat.le_of_not_gt h74) h75 phase_correlation_chunk75
  by_cases h76 : d.val < 795
  · exact
      phase_correlation_of_chunk (offset := 785) (size := 10)
        d (Nat.le_of_not_gt h75) h76 phase_correlation_chunk76
  by_cases h77 : d.val < 805
  · exact
      phase_correlation_of_chunk (offset := 795) (size := 10)
        d (Nat.le_of_not_gt h76) h77 phase_correlation_chunk77
  by_cases h78 : d.val < 815
  · exact
      phase_correlation_of_chunk (offset := 805) (size := 10)
        d (Nat.le_of_not_gt h77) h78 phase_correlation_chunk78
  · exact
      phase_correlation_of_chunk (offset := 815) (size := 10)
        d (Nat.le_of_not_gt h78) hupper phase_correlation_chunk79

private theorem phase_correlation_segment8
    (d : Cyc) (hlower : 825 ≤ d.val) (hupper : d.val < 915) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h80 : d.val < 835
  · exact
      phase_correlation_of_chunk (offset := 825) (size := 10)
        d hlower h80 phase_correlation_chunk80
  by_cases h81 : d.val < 845
  · exact
      phase_correlation_of_chunk (offset := 835) (size := 10)
        d (Nat.le_of_not_gt h80) h81 phase_correlation_chunk81
  by_cases h82 : d.val < 855
  · exact
      phase_correlation_of_chunk (offset := 845) (size := 10)
        d (Nat.le_of_not_gt h81) h82 phase_correlation_chunk82
  by_cases h83 : d.val < 865
  · exact
      phase_correlation_of_chunk (offset := 855) (size := 10)
        d (Nat.le_of_not_gt h82) h83 phase_correlation_chunk83
  by_cases h84 : d.val < 875
  · exact
      phase_correlation_of_chunk (offset := 865) (size := 10)
        d (Nat.le_of_not_gt h83) h84 phase_correlation_chunk84
  by_cases h85 : d.val < 885
  · exact
      phase_correlation_of_chunk (offset := 875) (size := 10)
        d (Nat.le_of_not_gt h84) h85 phase_correlation_chunk85
  by_cases h86 : d.val < 895
  · exact
      phase_correlation_of_chunk (offset := 885) (size := 10)
        d (Nat.le_of_not_gt h85) h86 phase_correlation_chunk86
  by_cases h87 : d.val < 905
  · exact
      phase_correlation_of_chunk (offset := 895) (size := 10)
        d (Nat.le_of_not_gt h86) h87 phase_correlation_chunk87
  · exact
      phase_correlation_of_chunk (offset := 905) (size := 10)
        d (Nat.le_of_not_gt h87) hupper phase_correlation_chunk88

/-! ## Balanced top-level stitch -/

/-- Kernel-checked cyclic-correlation certificate. -/
theorem phase_correlation (d : Cyc) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h525 : d.val < 525
  · by_cases h325 : d.val < 325
    · by_cases h225 : d.val < 225
      · by_cases h125 : d.val < 125
        · exact phase_correlation_segment0 d h125
        · exact
            phase_correlation_segment1 d (Nat.le_of_not_gt h125) h225
      · exact
          phase_correlation_segment2 d (Nat.le_of_not_gt h225) h325
    · by_cases h425 : d.val < 425
      · exact
          phase_correlation_segment3 d (Nat.le_of_not_gt h325) h425
      · exact
          phase_correlation_segment4 d (Nat.le_of_not_gt h425) h525
  · by_cases h725 : d.val < 725
    · by_cases h625 : d.val < 625
      · exact
          phase_correlation_segment5 d (Nat.le_of_not_gt h525) h625
      · exact
          phase_correlation_segment6 d (Nat.le_of_not_gt h625) h725
    · by_cases h825 : d.val < 825
      · exact
          phase_correlation_segment7 d (Nat.le_of_not_gt h725) h825
      · exact
          phase_correlation_segment8 d (Nat.le_of_not_gt h825)
            (ZMod.val_lt d)

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
