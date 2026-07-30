/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The real-residue gauge for every odd prime

This layer replaces a cycle inside the square subgroup by the intrinsic
real residue group `(ZMod p)ˣ / {±1}`.  A single indexed lift
`orbitLift ^ i` represents the generated quotient cycle, while its squares
give the distinct finite-field Vandermonde nodes.
-/
import Fermat.Conservation.Credit.Gauge
import Mathlib.GroupTheory.Coset.Card

open scoped Classical

namespace Fermat.Conservation.Credit.RealGauge

noncomputable section

/-- The sign subgroup `{1, -1}` of the units modulo `p`. -/
def signSubgroup (p : ℕ) : Subgroup (ZMod p)ˣ :=
  Subgroup.zpowers (-1)

/-- The Galois group of the maximal real residue orbit. -/
abbrev RealResidueGroup (p : ℕ) :=
  (ZMod p)ˣ ⧸ signSubgroup p

variable {p : ℕ}

/-- Membership in the sign subgroup is exactly equality to one of its two
displayed generators. -/
theorem signSubgroup_mem_iff (u : (ZMod p)ˣ) :
    u ∈ signSubgroup p ↔ u = 1 ∨ u = -1 := by
  constructor
  · intro hu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [neg_one_zpow_eq_ite] at hk
    by_cases heven : Even k
    · left
      simpa [heven] using hk.symm
    · right
      simpa [heven] using hk.symm
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers (-1)

/-- At an odd prime, the sign subgroup has exactly two elements. -/
theorem card_signSubgroup [Fact (Nat.Prime p)] [Fact (2 < p)] :
    Fintype.card (signSubgroup p) = 2 := by
  rw [signSubgroup, Fintype.card_zpowers]
  apply orderOf_eq_prime
  · norm_num
  · intro h
    have hval := congrArg Units.val h
    exact ZMod.neg_one_ne_one hval

/-- The real residue quotient has the expected half-order. -/
theorem card_realResidueGroup [Fact (Nat.Prime p)] [Fact (2 < p)] :
    Fintype.card (RealResidueGroup p) = (p - 1) / 2 := by
  have hcard :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (signSubgroup p)
  have hunits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime (Fact.out : Nat.Prime p)]
  have hsign : Nat.card (signSubgroup p) = 2 := by
    rw [Nat.card_eq_fintype_card, card_signSubgroup (p := p)]
  have hquot : Nat.card (RealResidueGroup p) =
      Fintype.card (RealResidueGroup p) :=
    Nat.card_eq_fintype_card
  rw [hunits, hsign, hquot] at hcard
  exact Nat.eq_div_of_mul_eq_right (by norm_num) (by
    simpa [mul_comm] using hcard.symm)

/-- Generator data for the real quotient at an arbitrary odd prime.

Only the order of the squared lift is required.  Unlike requiring both the
lift and its square to have half-order, this condition is compatible with
both odd-prime congruence classes modulo four. -/
structure RealGaugeData (p : ℕ) where
  rank : ℕ
  prime : Nat.Prime p
  odd : Odd p
  rank_spec :
    p = 2 * (rank + 1) + 1
  orbitLift : (ZMod p)ˣ
  orbitLift_square_order :
    orderOf (orbitLift ^ 2) = rank + 1

namespace RealGaugeData

variable (data : RealGaugeData p)

/-- Existing square-subgroup gauge data embeds in the quotient-ready API.
In particular, the current selected-prime record maps through this
constructor without adding any numerical fact. -/
def ofGaugeData (old : Gauge.GaugeData p) : RealGaugeData p where
  rank := old.rank
  prime := old.prime
  odd := old.odd
  rank_spec := old.rank_spec
  orbitLift := old.orbitGenerator
  orbitLift_square_order := old.orbitGenerator_square_order

@[simp]
theorem ofGaugeData_orbitLift (old : Gauge.GaugeData p) :
    (ofGaugeData old).orbitLift = old.orbitGenerator :=
  rfl

/-- The displayed rank is the usual real cyclotomic rank. -/
theorem rank_eq_half_sub_three :
    data.rank = (p - 3) / 2 := by
  symm
  calc
    (p - 3) / 2 =
        (2 * (data.rank + 1) + 1 - 3) / 2 :=
      congrArg (fun n : ℕ => (n - 3) / 2) data.rank_spec
    _ = data.rank := by omega

/-- The generator of the intrinsic real residue quotient. -/
def realOrbitGenerator : RealResidueGroup p :=
  QuotientGroup.mk data.orbitLift

/-- A unit whose square is one is a sign. -/
private theorem unit_eq_one_or_neg_one_of_sq_eq_one
    (data : RealGaugeData p)
    {u : (ZMod p)ˣ} (hu : u ^ 2 = 1) :
    u = 1 ∨ u = -1 := by
  letI : Fact (Nat.Prime p) := ⟨data.prime⟩
  have hval : (u : ZMod p) ^ 2 = 1 := by
    simpa using congrArg Units.val hu
  rcases sq_eq_one_iff.mp hval with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

/-- The quotient generator has exactly `rank + 1` powers.  The proof uses
only the exact order of the squared lift: a power dies in the quotient
exactly when the corresponding lift power is a sign. -/
theorem realOrbitGenerator_order :
    orderOf data.realOrbitGenerator = data.rank + 1 := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [signSubgroup_mem_iff]
    apply data.unit_eq_one_or_neg_one_of_sq_eq_one
    calc
      (data.orbitLift ^ (data.rank + 1)) ^ 2 =
          (data.orbitLift ^ 2) ^ (data.rank + 1) := by
            simp only [← pow_mul]
            rw [Nat.mul_comm]
      _ = 1 := by
        rw [← data.orbitLift_square_order]
        exact pow_orderOf_eq_one (data.orbitLift ^ 2)
  · rw [← data.orbitLift_square_order]
    apply orderOf_dvd_of_pow_eq_one
    have hquot :
        data.realOrbitGenerator ^
            orderOf data.realOrbitGenerator = 1 :=
      pow_orderOf_eq_one data.realOrbitGenerator
    have hsign :
        data.orbitLift ^ orderOf data.realOrbitGenerator ∈
          signSubgroup p := by
      apply (QuotientGroup.eq_one_iff _).mp
      simpa only [realOrbitGenerator, QuotientGroup.mk_pow] using hquot
    rw [signSubgroup_mem_iff] at hsign
    rcases hsign with hsign | hsign
    · calc
        (data.orbitLift ^ 2) ^
            orderOf data.realOrbitGenerator =
            (data.orbitLift ^
              orderOf data.realOrbitGenerator) ^ 2 := by
                simp only [← pow_mul]
                rw [Nat.mul_comm]
        _ = 1 := by rw [hsign, one_pow]
    · calc
        (data.orbitLift ^ 2) ^
            orderOf data.realOrbitGenerator =
            (data.orbitLift ^
              orderOf data.realOrbitGenerator) ^ 2 := by
                simp only [← pow_mul]
                rw [Nat.mul_comm]
        _ = 1 := by rw [hsign, neg_one_sq]

/-- The quotient cycle generated by the chosen lift. -/
def cycle : Cycle (RealResidueGroup p) :=
  Cycle.ofMul data.rank data.realOrbitGenerator (by
    rw [← data.realOrbitGenerator_order]
    exact pow_orderOf_eq_one data.realOrbitGenerator)

@[simp]
theorem cycle_rank :
    data.cycle.rank = data.rank :=
  rfl

@[simp]
theorem cycle_point (i : ℕ) :
    data.cycle.point i = data.realOrbitGenerator ^ i := by
  exact Cycle.ofMul_point data.rank data.realOrbitGenerator _ i

/-- The indexed representative of the `i`th quotient node.  It is derived
from the one lift rather than chosen separately for every quotient class. -/
def nodeLift (i : ℕ) : (ZMod p)ˣ :=
  data.orbitLift ^ i

@[simp]
theorem ofGaugeData_nodeLift (old : Gauge.GaugeData p) (i : ℕ) :
    (ofGaugeData old).nodeLift i = old.orbitGenerator ^ i :=
  rfl

@[simp]
theorem ofGaugeData_nodeLift_eq_cycle_point
    (old : Gauge.GaugeData p) (i : ℕ) :
    (ofGaugeData old).nodeLift i = old.cycle.point i := by
  rw [old.cycle_point]
  rfl

/-- The indexed lift represents the corresponding point of the quotient
cycle. -/
theorem mk_nodeLift (i : ℕ) :
    (QuotientGroup.mk (data.nodeLift i) : RealResidueGroup p) =
      data.cycle.point i := by
  rw [data.cycle_point]
  simp [nodeLift, realOrbitGenerator, QuotientGroup.mk_pow]

/-- The finite-field Vandermonde node is the square of the indexed lift. -/
def squaredOrbitNode (i : Fin data.rank) : ZMod p :=
  (((data.orbitLift ^ 2) ^ i.val : (ZMod p)ˣ) : ZMod p)

@[simp]
theorem ofGaugeData_squaredOrbitNode
    (old : Gauge.GaugeData p) (i : Fin old.rank) :
    (ofGaugeData old).squaredOrbitNode i = old.orbitNode i :=
  rfl

theorem squaredOrbitNode_eq_nodeLift_sq (i : Fin data.rank) :
    data.squaredOrbitNode i =
      ((data.nodeLift i.val ^ 2 : (ZMod p)ˣ) : ZMod p) := by
  simp only [squaredOrbitNode, nodeLift, ← pow_mul]
  rw [Nat.mul_comm]

/-- The displayed powers lie below the exact square order. -/
private theorem squaredOrbitNode_exponent_lt_order
    (i : Fin data.rank) :
    i.val < orderOf (data.orbitLift ^ 2) := by
  rw [data.orbitLift_square_order]
  omega

/-- Squaring the indexed representatives gives distinct Vandermonde nodes
for all `rank` displayed positions. -/
theorem squaredOrbitNode_injective :
    Function.Injective data.squaredOrbitNode := by
  intro i j hij
  have hpowers :
      (data.orbitLift ^ 2) ^ i.val =
        (data.orbitLift ^ 2) ^ j.val := by
    apply Units.ext
    exact hij
  have hexponents :
      i.val = j.val :=
    pow_injOn_Iio_orderOf
      (data.squaredOrbitNode_exponent_lt_order i)
      (data.squaredOrbitNode_exponent_lt_order j)
      hpowers
  exact Fin.ext hexponents

/-- The Vandermonde nodes seen by the even high derivatives.  This public
name matches the C5 API; `squaredOrbitNode` records how the nodes are
derived from the indexed quotient lifts. -/
abbrev orbitNode (i : Fin data.rank) : ZMod p :=
  data.squaredOrbitNode i

@[simp]
theorem ofGaugeData_orbitNode
    (old : Gauge.GaugeData p) (i : Fin old.rank) :
    (ofGaugeData old).orbitNode i = old.orbitNode i :=
  rfl

/-- Distinct indexed quotient positions give distinct Vandermonde nodes. -/
theorem orbitNode_injective :
    Function.Injective data.orbitNode :=
  data.squaredOrbitNode_injective

/-- No displayed nontrivial power of the squared lift is one. -/
theorem orbitLift_square_pow_succ_ne_one (i : Fin data.rank) :
    (data.orbitLift ^ 2) ^ (i.val + 1) ≠ 1 := by
  intro hpow
  have hdvd : orderOf (data.orbitLift ^ 2) ∣ i.val + 1 :=
    orderOf_dvd_of_pow_eq_one hpow
  rw [data.orbitLift_square_order] at hdvd
  exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd

/-- The generator-derived scale of character row `row`. -/
def rowScale (row : Fin data.rank) : ZMod p :=
  ((((data.orbitLift ^ 2) ^ (row.val + 1) : (ZMod p)ˣ) :
      ZMod p) - 1)

@[simp]
theorem ofGaugeData_rowScale
    (old : Gauge.GaugeData p) (row : Fin old.rank) :
    (ofGaugeData old).rowScale row = old.rowScale row :=
  rfl

/-- Every generator-derived row scale is nonzero. -/
theorem rowScale_ne_zero (row : Fin data.rank) :
    data.rowScale row ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨data.prime⟩
  apply sub_ne_zero.mpr
  intro h
  apply data.orbitLift_square_pow_succ_ne_one row
  apply Units.ext
  simpa using h

/-- The edge index contributes one further Vandermonde node. -/
def columnScale (i : Fin data.rank) : ZMod p :=
  data.orbitNode i

@[simp]
theorem ofGaugeData_columnScale
    (old : Gauge.GaugeData p) (i : Fin old.rank) :
    (ofGaugeData old).columnScale i = old.columnScale i :=
  rfl

/-- Every column scale is a unit. -/
theorem columnScale_ne_zero (i : Fin data.rank) :
    data.columnScale i ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨data.prime⟩
  exact Units.ne_zero ((data.orbitLift ^ 2) ^ i.val)

/-- The raw-to-character change of coordinates.  It is a row diagonal
times the transpose Vandermonde on squared indexed lifts, followed by the
column diagonal. -/
def characterMatrix :
    Matrix (Fin data.rank) (Fin data.rank) (ZMod p) :=
  Matrix.diagonal data.rowScale *
    (Matrix.vandermonde data.orbitNode).transpose *
      Matrix.diagonal data.columnScale

@[simp]
theorem ofGaugeData_characterMatrix (old : Gauge.GaugeData p) :
    (ofGaugeData old).characterMatrix = old.characterMatrix :=
  rfl

/-- Entry formula for the row- and column-scaled transpose Vandermonde
matrix. -/
theorem characterMatrix_apply (row i : Fin data.rank) :
    data.characterMatrix row i =
      data.rowScale row * data.orbitNode i ^ (row.val + 1) := by
  rw [characterMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [columnScale]
  simp [Matrix.vandermonde, pow_succ, mul_assoc]

/-- The C5 entry is exactly the finite-field reduction of the edge
difference between successive indexed lifts at degree
`2 * (row + 1) * p`.  The theorem deliberately uses `nodeLift`, not a
chosen representative of a quotient point. -/
theorem characterMatrix_eq_high_edge_difference
    (row i : Fin data.rank) :
    data.characterMatrix row i =
      ((data.nodeLift (i.val + 1) : ZMod p) ^
          (2 * (row.val + 1) * p) -
        (data.nodeLift i.val : ZMod p) ^
          (2 * (row.val + 1) * p)) := by
  letI : Fact (Nat.Prime p) := ⟨data.prime⟩
  rw [data.characterMatrix_apply]
  have hpow (x : ZMod p) (n : ℕ) : x ^ (n * p) = x ^ n := by
    rw [pow_mul, ZMod.pow_card]
  rw [hpow, hpow]
  simp only [rowScale, orbitNode, squaredOrbitNode, nodeLift,
    Units.val_pow_eq_pow_val]
  simp only [← pow_mul]
  rw [sub_mul, one_mul, ← pow_add]
  congr 1 <;> ring

/-- The generator-derived real gauge matrix is nonsingular. -/
theorem characterMatrix_det_ne_zero :
    data.characterMatrix.det ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨data.prime⟩
  rw [characterMatrix, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.det_diagonal, Matrix.det_diagonal]
  exact mul_ne_zero
    (mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr
        (fun row _ ↦ data.rowScale_ne_zero row))
      (Matrix.det_vandermonde_ne_zero_iff.mpr data.orbitNode_injective))
    (Finset.prod_ne_zero_iff.mpr
      (fun i _ ↦ data.columnScale_ne_zero i))

/-- Character coordinates are obtained by applying the one
generator-derived matrix to raw edge coordinates. -/
def characterCoordinates
    (raw : Fin data.rank → ZMod p) : Fin data.rank → ZMod p :=
  data.characterMatrix.mulVec raw

@[simp]
theorem ofGaugeData_characterCoordinates
    (old : Gauge.GaugeData p) (raw : Fin old.rank → ZMod p) :
    (ofGaugeData old).characterCoordinates raw =
      old.characterCoordinates raw :=
  rfl

/-- Vanishing character coordinates force every raw generated-edge
coordinate to vanish. -/
theorem raw_eq_zero_of_character_eq_zero
    (raw : Fin data.rank → ZMod p)
    (hcharacter : data.characterCoordinates raw = 0) :
    raw = 0 := by
  letI : Fact (Nat.Prime p) := ⟨data.prime⟩
  by_contra hraw
  have hsingular : data.characterMatrix.det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp
      ⟨raw, hraw, by
        simpa only [characterCoordinates] using hcharacter⟩
  exact data.characterMatrix_det_ne_zero hsingular

/-- Equivalently, the real generator-derived character transform is
injective. -/
theorem characterCoordinates_injective :
    Function.Injective data.characterCoordinates := by
  intro left right heq
  have hzero :
      data.characterCoordinates (left - right) = 0 := by
    letI : Fact (Nat.Prime p) := ⟨data.prime⟩
    change data.characterMatrix.mulVec (left - right) = 0
    rw [Matrix.mulVec_sub]
    change data.characterCoordinates left -
      data.characterCoordinates right = 0
    rw [heq, sub_self]
  have := data.raw_eq_zero_of_character_eq_zero (left - right) hzero
  exact sub_eq_zero.mp this

/-- The real quotient cardinality agrees with the generated cycle order. -/
theorem card_realResidueGroup_eq_rank_add_one :
    Nat.card (RealResidueGroup p) = data.rank + 1 := by
  letI : Fact (Nat.Prime p) := ⟨data.prime⟩
  letI : Fact (2 < p) := ⟨by
    rw [data.rank_spec]
    omega⟩
  have hrank :
      (p - 1) / 2 = data.rank + 1 := by
    calc
      (p - 1) / 2 =
          (2 * (data.rank + 1) + 1 - 1) / 2 :=
        congrArg (fun n : ℕ => (n - 1) / 2) data.rank_spec
      _ = data.rank + 1 := by omega
  calc
    Nat.card (RealResidueGroup p) =
        Fintype.card (RealResidueGroup p) :=
      Nat.card_eq_fintype_card
    _ = (p - 1) / 2 := card_realResidueGroup
    _ = data.rank + 1 := hrank

end RealGaugeData

end

end Fermat.Conservation.Credit.RealGauge
