import Fermat.Descent.Irregular.CircularUnitGeneratorBridge
import Fermat.Descent.Irregular.CircularUnitResidues
import KummerCriterion.CyclotomicUnits.Saturation

/-!
# Selective circular-unit residue relations

This module connects KummerCriterion's plus-side exponent products to the
auxiliary-prime matrix in a circular-unit residue certificate. The bridge is
prime-generic: a `p`th-power relation among the squared `CPlus` generators
maps to a kernel vector of the residue matrix over `ZMod p`.

The factor `2` records that `CPlusGenerator` maps to the square of the
normalized circular unit. It is cancelled only after the residue equation
has been proved, using that `p` is odd.
-/

open scoped NumberField

namespace Fermat.Irregular.SelectiveCircularUnitResidues

noncomputable section

open NumberField
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitGeneratorBridge
open Fermat.Irregular.CircularUnitResidues
open Fermat.Irregular.CircularUnitResidues.Certificate
open KummerCriterion

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Map plus-side units into the full cyclotomic field. -/
noncomputable def plusToFullUnits : (𝓞 K⁺)ˣ →* (𝓞 K)ˣ :=
  Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom

@[simp] theorem plusToFullUnits_CPlusGenerator
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : Fin ((p - 3) / 2)) :
    plusToFullUnits (K := K)
        (CPlusGenerator (p := p) (K := K) hp_three i) =
      circularUnitFamily
          (canonicalZeta_isPrimitive (p := p) (K := K)) hp_odd i ^ 2 :=
  map_CPlusGenerator_eq_circularUnitFamily_sq hp_odd hp_three i

/-- The residue log of a squared `CPlus` generator is twice the recorded
matrix entry. -/
theorem correctedResidueLog_plusToFullUnits_CPlusGenerator
    (C : Certificate p q) (hp_three : 3 ≤ p)
    (row i : Fin ((p - 3) / 2)) :
    C.correctedResidueLog
        (canonicalZeta_isPrimitive (p := p) (K := K)) row
        (Additive.ofMul (plusToFullUnits (K := K)
          (CPlusGenerator (p := p) (K := K) hp_three i))) =
      2 * C.matrix row i := by
  have hp_odd : p ≠ 2 := by omega
  rw [plusToFullUnits_CPlusGenerator (p := p) (K := K) hp_odd hp_three]
  rw [show Additive.ofMul
      (circularUnitFamily
        (canonicalZeta_isPrimitive (p := p) (K := K)) hp_odd i ^ 2) =
      2 • Additive.ofMul
        (circularUnitFamily
          (canonicalZeta_isPrimitive (p := p) (K := K)) hp_odd i) by rfl]
  rw [map_nsmul, C.correctedResidueLog_circularUnitFamily]
  simp [nsmul_eq_mul]

/-- Residue-log evaluation of an arbitrary plus-side exponent product. The
sign disappears because it is torsion. -/
theorem correctedResidueLog_plusToFullUnits_CPlusExponentProduct
    (C : Certificate p q) (hp_three : 3 ≤ p)
    (row : Fin ((p - 3) / 2)) (s : ℤ)
    (e : Fin ((p - 3) / 2) → ℤ) :
    C.correctedResidueLog
        (canonicalZeta_isPrimitive (p := p) (K := K)) row
        (Additive.ofMul (plusToFullUnits (K := K)
          (CPlusExponentProduct (p := p) (K := K) hp_three s e))) =
      2 * Matrix.mulVec C.matrix (fun i => (e i : ZMod p)) row := by
  classical
  rw [CPlusExponentProduct, map_mul, map_zpow, map_prod]
  simp_rw [map_zpow]
  let A : (𝓞 K)ˣ := plusToFullUnits (K := K) (-1)
  let U : Fin ((p - 3) / 2) → (𝓞 K)ˣ := fun i =>
    plusToFullUnits (K := K)
      (CPlusGenerator (p := p) (K := K) hp_three i)
  have hprod : Additive.ofMul (∏ i, U i ^ e i) =
      ∑ i, e i • Additive.ofMul (U i) := rfl
  change C.correctedResidueLog
      (canonicalZeta_isPrimitive (p := p) (K := K)) row
      (Additive.ofMul (A ^ s * ∏ i, U i ^ e i)) = _
  rw [show Additive.ofMul (A ^ s * ∏ i, U i ^ e i) =
      Additive.ofMul (A ^ s) + Additive.ofMul (∏ i, U i ^ e i) by rfl]
  rw [show Additive.ofMul (A ^ s) = s • Additive.ofMul A by rfl]
  rw [hprod, map_add, map_zsmul, map_sum]
  have hsign : plusToFullUnits (K := K) (-1) ∈
      NumberField.Units.torsion K := by
    have hminus : (-1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K :=
      neg_one_mem_torsion
    simpa [plusToFullUnits] using hminus
  rw [C.correctedResidueLog_eq_zero_of_mem_torsion
    (canonicalZeta_isPrimitive (p := p) (K := K)) row _ hsign]
  simp only [smul_zero, zero_add]
  simp only [U]
  simp_rw [map_zsmul,
    correctedResidueLog_plusToFullUnits_CPlusGenerator C hp_three row]
  simp only [Matrix.mulVec, dotProduct, zsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A plus-side `p`th-power relation gives a kernel vector for every row of
the auxiliary-prime residue matrix. -/
theorem matrix_mulVec_exponents_eq_zero_of_CPlus_product_mem_powers
    (C : Certificate p q) (hp_three : 3 ≤ p)
    (s : ℤ) (e : Fin ((p - 3) / 2) → ℤ)
    (hpow : CPlusExponentProduct (p := p) (K := K) hp_three s e ∈
      pPowerSubgroup (EPlus (K := K)) p) :
    Matrix.mulVec C.matrix (fun i => (e i : ZMod p)) = 0 := by
  rcases hpow with ⟨y, _hyE, hypow⟩
  funext row
  have hzero :
      C.correctedResidueLog
          (canonicalZeta_isPrimitive (p := p) (K := K)) row
          (Additive.ofMul (plusToFullUnits (K := K)
            (CPlusExponentProduct (p := p) (K := K) hp_three s e))) = 0 := by
    rw [← hypow, map_pow]
    rw [show Additive.ofMul (plusToFullUnits (K := K) y ^ p) =
        p • Additive.ofMul (plusToFullUnits (K := K) y) by rfl]
    rw [map_nsmul]
    simp [nsmul_eq_mul]
  rw [correctedResidueLog_plusToFullUnits_CPlusExponentProduct
    C hp_three row s e] at hzero
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hpdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hpdiv with hp1 | hp2
    · exact (Fact.out : Nat.Prime p).ne_one hp1
    · exact C.hp2 hp2
  exact (mul_eq_zero.mp hzero).resolve_left htwo

end

end Fermat.Irregular.SelectiveCircularUnitResidues
