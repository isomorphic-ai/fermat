/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Quotient-ready high-flow forcing

This layer provides the integral W1/W3 interface over `RealGaugeData`.
Every integer node is derived from the indexed representative
`data.nodeLift i`; no representative of a quotient class is chosen.
-/
import Fermat.Conservation.Credit.Flow
import Fermat.Conservation.Credit.RealGauge
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Int.Basic

open scoped BigOperators

namespace Fermat.Conservation.Credit.RealFlow

open RealGauge

/-- The high Bernoulli index selected by row `k`. -/
def highIndex {p : ℕ} {data : RealGaugeData p}
    (k : Fin data.rank) : ℕ :=
  2 * (k.val + 1) * p

/-- The integral eigenvalue generated in row `k`. -/
def highEigenvalue {p : ℕ} {data : RealGaugeData p}
    (k : Fin data.rank) : ℤ :=
  (bernoulli (highIndex k)).num

/-- The canonical integer value of the indexed quotient-cycle lift. -/
def canonicalNodeValue {p : ℕ}
    (data : RealGaugeData p) (i : ℕ) : ℤ :=
  (((data.nodeLift i : ZMod p).val : ℕ) : ℤ)

/-- The generator-derived Teichmüller-style integer lift. -/
def teichNodeValue {p : ℕ}
    (data : RealGaugeData p) (i : ℕ) : ℤ :=
  canonicalNodeValue data i ^ p

/-- The exact generated high-edge coefficient in one character row. -/
def exactHighEdgeCoefficient {p : ℕ} (data : RealGaugeData p)
    (raw : Fin data.rank → ℤ) (row : Fin data.rank) : ℤ :=
  ∑ i, raw i *
    (teichNodeValue data (i.val + 1) ^
        highIndex (data := data) row -
      teichNodeValue data i.val ^
        highIndex (data := data) row)

/-- Reducing the canonical integer value recovers the indexed node lift. -/
theorem intCast_canonicalNodeValue {p : ℕ}
    (data : RealGaugeData p) (i : ℕ) :
    ((canonicalNodeValue data i : ℤ) : ZMod p) =
      (data.nodeLift i : ZMod p) := by
  letI : NeZero p := ⟨data.prime.ne_zero⟩
  simp only [canonicalNodeValue, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Frobenius leaves the indexed node unchanged modulo `p`. -/
theorem intCast_teichNodeValue {p : ℕ}
    (data : RealGaugeData p) (i : ℕ) :
    ((teichNodeValue data i : ℤ) : ZMod p) =
      (data.nodeLift i : ZMod p) := by
  letI : Fact p.Prime := ⟨data.prime⟩
  rw [teichNodeValue, Int.cast_pow, intCast_canonicalNodeValue,
    ZMod.pow_card]

/-- The exact integral high-edge coefficient reduces to the quotient-ready
C5 character coordinate. -/
theorem intCast_exactHighEdgeCoefficient {p : ℕ}
    (data : RealGaugeData p) (raw : Fin data.rank → ℤ)
    (row : Fin data.rank) :
    ((exactHighEdgeCoefficient data raw row : ℤ) : ZMod p) =
      data.characterCoordinates (fun i ↦ (raw i : ZMod p)) row := by
  letI : NeZero p := ⟨data.prime.ne_zero⟩
  simp only [exactHighEdgeCoefficient, Int.cast_sum, Int.cast_mul,
    Int.cast_sub, Int.cast_pow, intCast_teichNodeValue,
    RealGaugeData.characterCoordinates, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [data.characterMatrix_eq_high_edge_difference]
  simp [highIndex, mul_comm]

/-- The formal generator orbit on the intrinsic real residue cycle.  Its
rational scales come from the same indexed lifts as the exact integral
coefficient. -/
noncomputable abbrev generatorOrbit {p : ℕ}
    (data : RealGaugeData p) :
    Flow.GeneratorOrbit p (RealResidueGroup p) where
  cycle := data.cycle
  nodeScale := fun i ↦ (teichNodeValue data i : ℚ)
  prime := data.prime
  odd := data.odd
  coordinateDegree := fun row ↦ highIndex (data := data) row - 1

theorem generatorOrbit_coordinateDegree_add_one {p : ℕ}
    (data : RealGaugeData p) (row : Fin data.rank) :
    (generatorOrbit data).coordinateDegree row + 1 =
      highIndex (data := data) row := by
  apply Nat.sub_add_cancel
  unfold highIndex
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero
      (Nat.mul_ne_zero (by norm_num) (Nat.succ_ne_zero row.val))
      data.prime.ne_zero)

/-- Each formal edge weight is its exact indexed-lift coefficient times
the generated high Bernoulli quotient. -/
theorem generatorOrbit_weight_eq_exactHighEdge {p : ℕ}
    (data : RealGaugeData p) (row i : Fin data.rank) :
    (generatorOrbit data).weight i row =
      ((teichNodeValue data (i.val + 1) ^
          highIndex (data := data) row -
        teichNodeValue data i.val ^
          highIndex (data := data) row : ℤ) : ℚ) *
        (bernoulli (highIndex (data := data) row) /
          (highIndex (data := data) row : ℚ)) := by
  rw [Flow.GeneratorOrbit.weight_eq_bernoulli,
    generatorOrbit_coordinateDegree_add_one]
  have heven : Even (highIndex (data := data) row) := by
    simp [highIndex]
  rw [bernoulli'_eq_bernoulli, heven.neg_one_pow, one_mul]
  simp only [generatorOrbit, teichNodeValue, canonicalNodeValue]
  have hpos : 1 ≤ highIndex (data := data) row := by
    unfold highIndex
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero
        (Nat.mul_ne_zero (by norm_num) (Nat.succ_ne_zero row.val))
        data.prime.ne_zero)
  have hdegreeQ :
      ((highIndex (data := data) row - 1 : ℕ) : ℚ) + 1 =
        (highIndex (data := data) row : ℕ) := by
    exact_mod_cast Nat.sub_add_cancel hpos
  rw [hdegreeQ]
  norm_cast

/-- Regard a full finite raw vector as W1's finitely supported exponent
vector. -/
noncomputable def exponentVectorOfRaw {p : ℕ}
    (data : RealGaugeData p) (raw : Fin data.rank → ℤ) :
    (generatorOrbit data).ExponentVector :=
  Finsupp.equivFunOnFinite.symm raw

@[simp]
theorem exponentVectorOfRaw_apply {p : ℕ}
    (data : RealGaugeData p) (raw : Fin data.rank → ℤ)
    (i : Fin data.cycle.rank) :
    exponentVectorOfRaw data raw i = raw i :=
  rfl

/-- The formal exponent flow factors through the exact integral high-edge
coefficient, with no quotient representative choice. -/
theorem generatorOrbit_exponentFlow_eq_exactHighEdgeCoefficient
    {p : ℕ} (data : RealGaugeData p)
    (raw : Fin data.rank → ℤ) (row : Fin data.rank) :
    (generatorOrbit data).exponentFlow
        (exponentVectorOfRaw data raw) row =
      (exactHighEdgeCoefficient data raw row : ℚ) *
        (bernoulli (highIndex (data := data) row) /
          (highIndex (data := data) row : ℚ)) := by
  simp only [Flow.GeneratorOrbit.exponentFlow,
    Flow.GeneratorOrbit.rationalFlow,
    Flow.GeneratorOrbit.castExponent, Finsupp.linearCombination_apply,
    AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    Finsupp.mapRange.addMonoidHom_apply]
  rw [Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply]
  have hcast (z : ℤ) : (Int.castAddHom ℚ) z = (z : ℚ) := rfl
  simp only [Finsupp.mapRange_apply, Pi.smul_apply, smul_eq_mul, hcast,
    generatorOrbit_weight_eq_exactHighEdge]
  rw [exactHighEdgeCoefficient]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [exponentVectorOfRaw_apply]
  ring

/-- Integral high-flow vanishing for one exponent vector. -/
def HighFlowVanishes {p : ℕ} (data : RealGaugeData p)
    (raw : Fin data.rank → ℤ) : Prop :=
  ∀ row, (p : ℤ) ^ 3 ∣
    exactHighEdgeCoefficient data raw row *
      highEigenvalue (data := data) row

/-- The per-prime certificate contains only cube-freeness of the generated
eigenvalues. -/
structure FlowCertificate {p : ℕ}
    (data : RealGaugeData p) : Prop where
  eigenvalue_cubeFree :
    ∀ row, ¬(p : ℤ) ^ 3 ∣ highEigenvalue (data := data) row

private theorem prime_dvd_left_of_cube_dvd_mul_of_cube_free
    {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (hprod : (p : ℤ) ^ 3 ∣ a * b)
    (hb : ¬(p : ℤ) ^ 3 ∣ b) :
    (p : ℤ) ∣ a := by
  by_contra ha
  apply hb
  have hna : ¬p ∣ a.natAbs := by
    simpa [Int.natCast_dvd] using ha
  have hnat : Nat.Coprime (p ^ 3) a.natAbs :=
    (hp.coprime_pow_of_not_dvd hna).symm
  have hint : IsCoprime ((p : ℤ) ^ 3) a := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa [Int.natAbs_pow] using hnat
  exact hint.dvd_of_dvd_mul_right (by simpa [mul_comm] using hprod)

/-- C5 inversion plus cube-freeness turns high-flow vanishing into raw
exponent divisibility. -/
theorem exponent_dvd_of_highFlowVanishes {p : ℕ}
    (data : RealGaugeData p) (certificate : FlowCertificate data)
    (raw : Fin data.rank → ℤ) (hflow : HighFlowVanishes data raw) :
    ∀ i, (p : ℤ) ∣ raw i := by
  have hcharacterDvd :
      ∀ row, (p : ℤ) ∣ exactHighEdgeCoefficient data raw row :=
    fun row ↦
      prime_dvd_left_of_cube_dvd_mul_of_cube_free data.prime
        (hflow row) (certificate.eigenvalue_cubeFree row)
  have hcharacter :
      data.characterCoordinates (fun i ↦ (raw i : ZMod p)) = 0 := by
    funext row
    rw [← intCast_exactHighEdgeCoefficient]
    exact
      (ZMod.intCast_zmod_eq_zero_iff_dvd
        (exactHighEdgeCoefficient data raw row) p).2
        (hcharacterDvd row)
  have hraw :
      (fun i ↦ (raw i : ZMod p)) = 0 :=
    data.raw_eq_zero_of_character_eq_zero _ hcharacter
  intro i
  exact
    (ZMod.intCast_zmod_eq_zero_iff_dvd (raw i) p).1
      (by simpa using congrFun hraw i)

end Fermat.Conservation.Credit.RealFlow
