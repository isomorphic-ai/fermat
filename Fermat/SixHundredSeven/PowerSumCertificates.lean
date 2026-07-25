import Fermat.Basic

/-!
# Modular power sum for the exponent-607 Bernoulli channel

The paired `78233`/`94693` package reports the sole irregular index `592`
and the lifted coefficient `511`. This module checks the corresponding
power sum at `592 * 607 = 359344` modulo `607⁴`. Repeated squaring keeps
kernel evaluation logarithmic in the lifted exponent.
-/

namespace Fermat.SixHundredSeven.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem pow_592_eq_bin (a : ZMod (607 ^ 3)) :
    a ^ 592 = npowBinRec 592 a := by
  change npowRecAuto 592 a = npowBinRecAuto 592 a
  rw [npowRec_eq_npowBinRec]

private theorem pow_359344_eq_bin (a : ZMod (607 ^ 4)) :
    a ^ 359344 = npowBinRec 359344 a := by
  change npowRecAuto 359344 a = npowBinRecAuto 359344 a
  rw [npowRec_eq_npowBinRec]

/-- The package's base-channel coefficient:
`S_592(607) = 607² * 363 (mod 607³)`. -/
theorem basePowerSum_592 :
    (∑ a ∈ Finset.range 607, (a : ZMod (607 ^ 3)) ^ 592) =
      607 ^ 2 * 363 := by
  simp_rw [pow_592_eq_bin]
  decide

/-- The lifted `j = 592` power-sum certificate modulo `607⁴`. -/
theorem powerSum_359344 :
    (∑ a ∈ Finset.range 607, (a : ZMod (607 ^ 4)) ^ 359344) =
      607 * 188277439 := by
  simp_rw [pow_359344_eq_bin]
  decide

/-- The nonzero correction is exactly `511 * 607²`. -/
theorem correctionQuotient :
    188277439 = 607 ^ 2 * 511 := by
  norm_num

theorem correctionQuotient_not_dvd_cube :
    ¬(607 : ℤ) ^ 3 ∣ (188277439 : ℤ) := by
  norm_num

end Fermat.SixHundredSeven.PowerSumCertificates
