import Fermat.Basic

/-!
# Modular power sums for the exponent-491 correction channels

The uploaded three-loop package identifies the irregular indices
`292`, `336`, and `338`.  These three finite calculations are the
power-sum inputs to the shared direct-Faulhaber endpoint.  Rewriting powers
to repeated squaring keeps kernel evaluation logarithmic in the large
exponents.
-/

namespace Fermat.FourHundredNinetyOne.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem pow_143372_eq_bin (a : ZMod (491 ^ 4)) :
    a ^ 143372 = npowBinRec 143372 a := by
  change npowRecAuto 143372 a = npowBinRecAuto 143372 a
  rw [npowRec_eq_npowBinRec]

private theorem pow_164976_eq_bin (a : ZMod (491 ^ 4)) :
    a ^ 164976 = npowBinRec 164976 a := by
  change npowRecAuto 164976 a = npowBinRecAuto 164976 a
  rw [npowRec_eq_npowBinRec]

private theorem pow_165958_eq_bin (a : ZMod (491 ^ 4)) :
    a ^ 165958 = npowBinRec 165958 a := by
  change npowRecAuto 165958 a = npowBinRecAuto 165958 a
  rw [npowRec_eq_npowBinRec]

/-- The isolated `r = 292` correction loop, modulo `491⁴`. -/
theorem powerSum_143372 :
    (∑ a ∈ Finset.range 491, (a : ZMod (491 ^ 4)) ^ 143372) =
      491 * 84619431 := by
  simp_rw [pow_143372_eq_bin]
  decide

/-- The left member `r = 336` of the coupled correction pair. -/
theorem powerSum_164976 :
    (∑ a ∈ Finset.range 491, (a : ZMod (491 ^ 4)) ^ 164976) =
      491 * 99325372 := by
  simp_rw [pow_164976_eq_bin]
  decide

/-- The right member `r = 338` of the coupled correction pair. -/
theorem powerSum_165958 :
    (∑ a ∈ Finset.range 491, (a : ZMod (491 ^ 4)) ^ 165958) =
      491 * 2651891 := by
  simp_rw [pow_165958_eq_bin]
  decide

/-- The three residues are exactly the coefficients recorded by the
package, multiplied by `491²`. -/
theorem correctionQuotients :
    84619431 = 491 ^ 2 * 351 ∧
      99325372 = 491 ^ 2 * 412 ∧
      2651891 = 491 ^ 2 * 11 := by
  norm_num

/-- Every loop stops at valuation exactly two, hence before `491³`. -/
theorem correctionQuotients_not_dvd_cube :
    ¬(491 : ℤ) ^ 3 ∣ (84619431 : ℤ) ∧
      ¬(491 : ℤ) ^ 3 ∣ (99325372 : ℤ) ∧
      ¬(491 : ℤ) ^ 3 ∣ (2651891 : ℤ) := by
  norm_num

end Fermat.FourHundredNinetyOne.PowerSumCertificates
