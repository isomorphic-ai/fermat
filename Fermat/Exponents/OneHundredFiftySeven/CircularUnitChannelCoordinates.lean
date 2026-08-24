import Fermat.Descent.Irregular.CircularUnitResiduePresentation
import Fermat.Exponents.OneHundredFiftySeven.CircularUnitMatrix

/-!
# Character coordinates at exponent 157

This module packages the data shared by every auxiliary split prime at
`p = 157`: a generator of the real residue classes, its Fourier root, the
source row and column permutations, and the corresponding class exponents.
It contains no auxiliary prime, residue phase, or determinant certificate.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitChannelCoordinates

noncomputable section

open Fermat.Irregular.AuxiliaryResidueChannels
open Fermat.Irregular.CyclicDifferenceMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

private def rowAt : Fin 77 → Fin 77 :=
  ![62,47,66,32,63,51,53,17,70,48,12,36,10,38,67,2,24,55,30,33,
    57,75,41,21,64,73,74,23,35,52,46,65,16,9,54,40,22,15,14,18,
    5,42,19,60,71,26,76,6,44,49,28,58,43,59,13,8,34,20,29,37,
    69,31,61,50,11,1,56,72,45,39,4,25,27,7,68,0,3]

private def rowInv : Fin 77 → Fin 77 :=
  ![75,65,15,76,70,40,47,73,55,33,12,64,10,54,38,37,32,7,39,42,
    57,23,36,27,16,71,45,72,50,58,18,61,3,19,56,28,11,59,13,69,
    35,22,41,52,48,68,30,1,9,49,63,5,29,6,34,17,66,20,51,53,
    43,62,0,4,24,31,2,14,74,60,8,44,67,25,26,21,46]

private def columnAt : Fin 77 → Fin 77 :=
  ![62,3,47,0,66,68,32,7,63,27,51,25,53,4,17,39,70,45,48,72,12,
    56,36,1,10,11,38,50,67,61,2,31,24,69,55,37,30,29,33,20,57,
    34,75,8,41,13,21,59,64,43,73,58,74,28,23,49,35,44,52,6,46,
    76,65,26,16,71,9,60,54,19,40,42,22,5,15,18,14]

private def columnInv : Fin 77 → Fin 77 :=
  ![3,23,30,1,13,73,59,7,43,66,24,25,20,45,76,74,64,14,75,69,
    39,46,72,54,32,11,63,9,53,37,36,31,6,38,41,56,22,35,26,15,
    70,44,71,49,57,17,60,2,18,55,27,10,58,12,68,34,21,40,51,47,
    67,29,0,8,48,62,4,28,5,33,16,65,19,50,52,42,61]

/-- Original embedding rows, reordered by the real cyclic coordinate
`[78]·[5]^r`, for nonzero coordinates `r = 1,…,77`. -/
def rowPermutation : Equiv.Perm (Fin 77) where
  toFun := rowAt
  invFun := rowInv
  left_inv i := by decide +revert
  right_inv i := by decide +revert

/-- Original circular-unit columns, reordered by `[5]^s`, for nonzero
coordinates `s = 1,…,77`. -/
def columnPermutation : Equiv.Perm (Fin 77) where
  toFun := columnAt
  invFun := columnInv
  left_inv i := by decide +revert
  right_inv i := by decide +revert

/-- Real Galois class `[78]·[5]^r`, represented modulo `157`. -/
def classExponent (r : Cyc 77) : ℕ :=
  ((78 : ZMod 157) * (5 : ZMod 157) ^ r.val).val

theorem classExponent_cast (r : Cyc 77) :
    (classExponent r : ZMod 157) =
      (78 : ZMod 157) * (5 : ZMod 157) ^ r.val := by
  exact ZMod.natCast_zmod_val _

private theorem five_pow_sq (n : ℕ) :
    (((5 : ZMod 157) ^ n) ^ 2) = (25 : ZMod 157) ^ n := by
  calc
    (((5 : ZMod 157) ^ n) ^ 2) = (5 : ZMod 157) ^ (n * 2) :=
      (pow_mul _ n 2).symm
    _ = (5 : ZMod 157) ^ (2 * n) := by rw [Nat.mul_comm]
    _ = ((5 : ZMod 157) ^ 2) ^ n := pow_mul _ 2 n
    _ = (25 : ZMod 157) ^ n := by norm_num

private theorem twentyFive_pow_cycleLength :
    (25 : ZMod 157) ^ 78 = 1 := by
  decide

theorem classExponent_add_sq (r s : Cyc 77) :
    ((classExponent (r + s) : ZMod 157) ^ 2) =
      ((classExponent r : ZMod 157) ^ 2) *
        (((5 : ZMod 157) ^ s.val) ^ 2) := by
  have hmod : (r + s).val ≡ r.val + s.val [MOD 78] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  have h25 :
      (25 : ZMod 157) ^ (r + s).val =
        (25 : ZMod 157) ^ (r.val + s.val) :=
    pow_eq_pow_of_modEq hmod twentyFive_pow_cycleLength
  rw [classExponent_cast, classExponent_cast, mul_pow, mul_pow,
    five_pow_sq, five_pow_sq, five_pow_sq, h25, pow_add]
  ring

theorem classExponent_ne_zero (r : Cyc 77) : classExponent r ≠ 0 := by
  intro hzero
  have hcast : (classExponent r : ZMod 157) = 0 := by simp [hzero]
  rw [classExponent_cast] at hcast
  exact (mul_ne_zero (by decide) (pow_ne_zero _ (by decide))) hcast

theorem classExponent_lt (r : Cyc 77) : classExponent r < 157 :=
  ZMod.val_lt _

/-- `25 = 5²` has exact order `78` modulo `157`. -/
theorem fourierRoot_isPrimitive : IsPrimitiveRoot (25 : ZMod 157) 78 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hqdiv
  have hfac : q ∣ 2 * (3 * 13) := by
    simpa using hqdiv
  have hcases : q = 2 ∨ q = 3 ∨ q = 13 := by
    rcases (hq.dvd_mul).mp hfac with h2 | hrest
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h2)
    rcases (hq.dvd_mul).mp hrest with h3 | h13
    · exact Or.inr <| Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h3)
    · exact Or.inr <| Or.inr
        ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h13)
  rcases hcases with rfl | rfl | rfl <;> decide

/-- All p-only real-class coordinates at exponent `157`. -/
def coordinates : ArithmeticCoordinates 157 (by norm_num) where
  generator := 5
  fourierRoot := 25
  fourierRoot_eq_generator_sq := by norm_num
  fourierRoot_isPrimitive := fourierRoot_isPrimitive
  column := columnPermutation
  column_square := by
    intro i
    decide +revert
  row := rowPermutation
  classExponent := classExponent
  classExponent_lt := classExponent_lt
  classExponent_ne_zero := classExponent_ne_zero
  classExponent_add_sq := classExponent_add_sq
  row_square := by
    intro j
    decide +revert

/-- Kummer row for Bernoulli index `62`. -/
def rowSixtyTwo : Fin 77 := 30

/-- Kummer row for Bernoulli index `110`. -/
def rowOneHundredTen : Fin 77 := 54

@[simp] theorem rowSixtyTwo_frequency :
    coordinates.toCharacterCoordinates.frequency rowSixtyTwo =
      (46 : Fin 77) := rfl

@[simp] theorem rowOneHundredTen_frequency :
    coordinates.toCharacterCoordinates.frequency rowOneHundredTen =
      (22 : Fin 77) := rfl

end


end Fermat.OneHundredFiftySeven.CircularUnitChannelCoordinates
