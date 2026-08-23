import Fermat.Descent.Irregular.CyclicNatFourier
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitMatrix

/-!
# Circular-unit irregular-channel certificate at exponent 1831

This is the standalone Case-II.1 receipt for nontrivial Fourier frequency
`278`, stored at zero-based slot `277`.  Its checked value is `882 mod 1831`.

Unlike the complete Fourier-factor certificate, this module checks only the
single channel selected by the Bernoulli irregular-index scan.  It deliberately
does not import the all-`914`-factor certificate or a determinant certificate.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel

open Fermat.Irregular.CyclicDifferenceMatrix
open Fermat.Irregular.CyclicNatFourier
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 1831) := ⟨by decide⟩

/-! ## Fourier convention -/

/-- `9 = 3²` has exact order `915` modulo `1831`. -/
theorem fourierRoot_isPrimitive : IsPrimitiveRoot (9 : ZMod 1831) 915 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hqdiv
  have hfac : q ∣ 3 * (5 * 61) := by
    simpa using hqdiv
  have hcases : q = 3 ∨ q = 5 ∨ q = 61 := by
    rcases (hq.dvd_mul).mp hfac with h3 | hrest
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h3)
    rcases (hq.dvd_mul).mp hrest with h5 | h61
    · exact Or.inr <| Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h5)
    · exact Or.inr <| Or.inr
        ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h61)
  rcases hcases with rfl | rfl | rfl <;> decide

/-- The nontrivial Fourier coefficient stored at zero-based slot `k`.

Slot `k` represents the actual frequency `k.val + 1`; the trivial frequency
is omitted from this interface.
-/
abbrev coefficient (k : Fin 914) : ZMod 1831 :=
  fourierCoeff (9 : ZMod 1831)
    fourierRoot_isPrimitive.pow_eq_one symbolPhase k

/-- The actual nontrivial frequency checked by this receipt. -/
def frequency : ℕ := 278

/-- Zero-based storage slot for actual frequency `278`. -/
def slot : Fin 914 := 277

@[simp] theorem slot_val : slot.val = 277 := rfl

@[simp] theorem slot_frequency : slot.val + 1 = frequency := rfl

/-! ## Kernel-checked receipt -/

/-- Transport one checked natural-number Horner value to the abstract Fourier
coefficient. -/
private theorem coefficient_eq_of_evaluate (k : Fin 914)
    (root value : ℕ)
    (hroot : (root : ZMod 1831) =
      (9 : ZMod 1831) ^ (k.val + 1))
    (heval : evaluate 1831 root symbolPhaseData.toList = value) :
    coefficient k = value := by
  change fourierCoeff (9 : ZMod 1831)
    fourierRoot_isPrimitive.pow_eq_one symbolPhase k = value
  rw [fourierCoeff_eq_sum_pow]
  have hcast := congrArg (fun x : ℕ ↦ (x : ZMod 1831)) heval
  rw [cast_evaluate_toList_eq_cyclicSum
    1831 915 root symbolPhaseData (by decide)] at hcast
  simpa only [symbolPhase, hroot, pow_mul, Nat.cast_ofNat] using hcast

/-- At actual frequency `278` (slot `277`), the coefficient is `882`. -/
theorem fhat_277_eq : coefficient slot = 882 :=
  coefficient_eq_of_evaluate slot 878 882
    (by decide) (by decide)

/-- The circular-unit Fourier detector at actual frequency `278` is nonzero. -/
theorem fhat_277_ne_zero : coefficient slot ≠ 0 := by
  rw [fhat_277_eq]
  decide

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel
