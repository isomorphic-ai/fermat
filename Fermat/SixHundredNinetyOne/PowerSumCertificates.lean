import Fermat.Basic

/-!
# Modular power sums for the exponent-691 correction channels

The uploaded paired four-digit folding package identifies `12` and `200` as
the only possible irregular indices at `691`.  These two finite calculations
are the power-sum inputs to the shared direct-Faulhaber endpoint at the lifted
indices `12 * 691` and `200 * 691`.  Rewriting powers to repeated squaring
keeps kernel evaluation logarithmic in the large exponents.
-/

namespace Fermat.SixHundredNinetyOne.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem pow_8292_eq_bin (a : ZMod (691 ^ 4)) :
    a ^ 8292 = npowBinRec 8292 a := by
  change npowRecAuto 8292 a = npowBinRecAuto 8292 a
  rw [npowRec_eq_npowBinRec]

private theorem pow_138200_eq_bin (a : ZMod (691 ^ 4)) :
    a ^ 138200 = npowBinRec 138200 a := by
  change npowRecAuto 138200 a = npowBinRecAuto 138200 a
  rw [npowRec_eq_npowBinRec]

/-- The lifted `12` correction channel, modulo `691⁴`. -/
theorem powerSum_8292 :
    (∑ a ∈ Finset.range 691, (a : ZMod (691 ^ 4)) ^ 8292) =
      691 * 137514528 := by
  simp_rw [pow_8292_eq_bin]
  decide

/-- The lifted `200` correction channel, modulo `691⁴`. -/
theorem powerSum_138200 :
    (∑ a ∈ Finset.range 691, (a : ZMod (691 ^ 4)) ^ 138200) =
      691 * 204839349 := by
  simp_rw [pow_138200_eq_bin]
  decide

/-- The two residues are exactly the package coefficients, multiplied by
`691²`. -/
theorem correctionQuotients :
    137514528 = 691 ^ 2 * 288 ∧
      204839349 = 691 ^ 2 * 429 := by
  norm_num

/-- Both loops stop at valuation exactly two, hence before `691³`. -/
theorem correctionQuotients_not_dvd_cube :
    ¬(691 : ℤ) ^ 3 ∣ (137514528 : ℤ) ∧
      ¬(691 : ℤ) ^ 3 ∣ (204839349 : ℤ) := by
  norm_num

end Fermat.SixHundredNinetyOne.PowerSumCertificates
