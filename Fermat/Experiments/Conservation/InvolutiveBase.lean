/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The Teichmuller-twisted involutive group algebra

For a finite cyclic Galois group `Delta`, the base ring is the group algebra
`O[Delta]`.  A unit-valued Teichmuller character `omega` determines the
reflection

`(sum a_s [s])# = sum a_s omega(s) [s^-1]`.

The construction below is generic in the prime and coefficient ring.  The
prime only records the intended cyclic order; the algebraic proofs use the
finite commutative group and the unit-valued character directly.
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RingTheory.Idempotents
import Mathlib.Tactic

namespace Fermat.Conservation.InvolutiveBase

open scoped BigOperators

universe uO uDelta

/-- The generic cyclotomic indexing data: `Delta` is cyclic of order `p - 1`
and `omega` is its unit-valued Teichmuller character. -/
structure TeichmullerData (p : ℕ) (O : Type uO) (Delta : Type uDelta)
    [CommRing O] [CommGroup Delta] [Fintype Delta] where
  prime : Nat.Prime p
  cyclic : IsCyclic Delta
  card_eq : Fintype.card Delta = p - 1
  omega : Delta →* Oˣ

/-- The involutive base `Lambda = O[Delta]`. -/
abbrev GroupAlgebra (O : Type uO) (Delta : Type uDelta) [Semiring O] :=
  MonoidAlgebra O Delta

/-- A unit-valued character of `Delta`. -/
abbrev Character (O : Type uO) (Delta : Type uDelta)
    [CommRing O] [CommGroup Delta] := Delta →* Oˣ

section Hash

variable {O : Type uO} {Delta : Type uDelta}
  [CommRing O] [CommGroup Delta]

/-- A basis element is reflected and weighted by the Teichmuller character.
This monoid homomorphism is the input to the group-algebra universal
property. -/
noncomputable def twistedBasis (omega : Delta →* Oˣ) :
    Delta →* GroupAlgebra O Delta where
  toFun s := MonoidAlgebra.single s⁻¹ (omega s : O)
  map_one' := by
    rw [map_one, inv_one]
    exact (MonoidAlgebra.one_def (R := O) (M := Delta)).symm
  map_mul' s t := by
    simp only [map_mul, mul_inv_rev, MonoidAlgebra.single_mul_single]
    rw [mul_comm s⁻¹ t⁻¹]
    simp only [Units.val_mul]

/-- The Teichmuller-twisted reflection as an algebra endomorphism. -/
noncomputable def hashHom (omega : Delta →* Oˣ) :
    GroupAlgebra O Delta →ₐ[O] GroupAlgebra O Delta :=
  MonoidAlgebra.lift O (GroupAlgebra O Delta) Delta (twistedBasis omega)

@[simp]
theorem hashHom_single (omega : Delta →* Oˣ) (s : Delta) (a : O) :
    hashHom omega (MonoidAlgebra.single s a) =
      MonoidAlgebra.single s⁻¹ (a * (omega s : O)) := by
  simp [hashHom, twistedBasis, MonoidAlgebra.lift_single, Algebra.smul_def]

/-- Applying the twisted reflection twice is the identity. -/
theorem hashHom_comp_self (omega : Delta →* Oˣ) :
    (hashHom omega).comp (hashHom omega) =
      AlgHom.id O (GroupAlgebra O Delta) := by
  apply MonoidAlgebra.algHom_ext
  intro s
  simp [hashHom, twistedBasis]

/-- The `#` operation, packaged as an involutive algebra equivalence. -/
noncomputable def hash (omega : Delta →* Oˣ) :
    GroupAlgebra O Delta ≃ₐ[O] GroupAlgebra O Delta :=
  AlgEquiv.ofAlgHom (hashHom omega) (hashHom omega)
    (hashHom_comp_self omega) (hashHom_comp_self omega)

@[simp]
theorem hash_apply_single (omega : Delta →* Oˣ) (s : Delta) (a : O) :
    hash omega (MonoidAlgebra.single s a) =
      MonoidAlgebra.single s⁻¹ (a * (omega s : O)) :=
  hashHom_single omega s a

/-- The coefficient form of the defining formula for `#`. -/
theorem hash_apply (omega : Delta →* Oˣ) (x : GroupAlgebra O Delta) :
    hash omega x =
      x.sum fun s a => MonoidAlgebra.single s⁻¹ (a * (omega s : O)) := by
  change hashHom omega x = _
  rw [hashHom, MonoidAlgebra.lift_apply]
  apply Finsupp.sum_congr
  intro s _
  simp [twistedBasis, Algebra.smul_def, MonoidAlgebra.coe_algebraMap]

/-- Named involutivity theorem for the Teichmuller-twisted reflection. -/
@[simp]
theorem hash_hash (omega : Delta →* Oˣ) (x : GroupAlgebra O Delta) :
    hash omega (hash omega x) = x :=
  (hash omega).symm_apply_apply x

/-- Moving an action across the natural reflected coefficient pairing
applies `#` to the action.  This is the reflection conservation law. -/
noncomputable def reflectionPairing (omega : Delta →* Oˣ)
    (x y : GroupAlgebra O Delta) : O :=
  (hash omega x * y) 1

/-- Reflection conservation: an action moved across the pairing becomes its
reflected adjoint. -/
theorem reflection_conservation_law (omega : Delta →* Oˣ)
    (a x y : GroupAlgebra O Delta) :
    reflectionPairing omega (a * x) y =
      reflectionPairing omega x (hash omega a * y) := by
  simp only [reflectionPairing, map_mul]
  rw [mul_assoc, mul_left_comm (hash omega a)]

end Hash

section Characters

variable {O : Type uO} {Delta : Type uDelta}
  [CommRing O] [CommGroup Delta] [Fintype Delta]
  [Invertible (Fintype.card Delta : O)]

/-- The reflected character `chi* = omega chi^-1`. -/
noncomputable def reflectedCharacter (omega chi : Character O Delta) :
    Character O Delta :=
  omega * chi⁻¹

omit [Fintype Delta] [Invertible (Fintype.card Delta : O)] in
@[simp]
theorem reflectedCharacter_apply (omega chi : Character O Delta)
    (s : Delta) :
    reflectedCharacter omega chi s = omega s * (chi s)⁻¹ := rfl

omit [Fintype Delta] [Invertible (Fintype.card Delta : O)] in
@[simp]
theorem reflectedCharacter_one (omega : Character O Delta) :
    reflectedCharacter omega 1 = omega := by
  ext s
  simp [reflectedCharacter]

omit [Fintype Delta] [Invertible (Fintype.card Delta : O)] in
@[simp]
theorem reflectedCharacter_self (omega : Character O Delta) :
    reflectedCharacter omega omega = 1 := by
  ext s
  simp [reflectedCharacter]

omit [Fintype Delta] [Invertible (Fintype.card Delta : O)] in
@[simp]
theorem reflectedCharacter_reflectedCharacter
    (omega chi : Character O Delta) :
    reflectedCharacter omega (reflectedCharacter omega chi) = chi := by
  ext s
  simp [reflectedCharacter]

/-- The normalized ordinary group average. -/
noncomputable def groupAverage : GroupAlgebra O Delta :=
  ⅟(Fintype.card Delta : O) •
    ∑ g : Delta, MonoidAlgebra.of O Delta g

@[simp]
theorem groupElement_mul_groupAverage (g : Delta) :
    MonoidAlgebra.of O Delta g * groupAverage (O := O) (Delta := Delta) =
      groupAverage := by
  simp only [groupAverage, Finset.mul_sum, Algebra.mul_smul_comm,
    MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one]
  set f : Delta → GroupAlgebra O Delta := fun x =>
    MonoidAlgebra.single x 1
  change ⅟(Fintype.card Delta : O) • ∑ x : Delta, f (g * x) =
    ⅟(Fintype.card Delta : O) • ∑ x : Delta, f x
  rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) _]

/-- The normalized group average is an idempotent. -/
theorem groupAverage_isIdempotent :
    IsIdempotentElem (groupAverage (O := O) (Delta := Delta)) := by
  rw [isIdempotentElem_iff]
  nth_rw 1 [groupAverage]
  rw [Algebra.smul_mul_assoc, Finset.sum_mul]
  change ⅟(Fintype.card Delta : O) •
      (∑ i : Delta, MonoidAlgebra.single i 1 *
        groupAverage (O := O) (Delta := Delta)) = groupAverage
  simp only [← MonoidAlgebra.of_apply, groupElement_mul_groupAverage,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul O, smul_smul, invOf_mul_self, one_smul]

/-- Diagonal twisting by the inverse character. -/
noncomputable def characterTwistBasis (chi : Character O Delta) :
    Delta →* GroupAlgebra O Delta where
  toFun s := MonoidAlgebra.single s (↑((chi s)⁻¹) : O)
  map_one' := by simp [← MonoidAlgebra.one_def]
  map_mul' s t := by simp [mul_comm]

/-- The diagonal character twist as an algebra endomorphism. -/
noncomputable def characterTwistHom (chi : Character O Delta) :
    GroupAlgebra O Delta →ₐ[O] GroupAlgebra O Delta :=
  MonoidAlgebra.lift O (GroupAlgebra O Delta) Delta
    (characterTwistBasis chi)

/-- The standard character idempotent, normalized integrally by the
invertibility of `|Delta|`. -/
noncomputable def characterIdempotent (chi : Character O Delta) :
    GroupAlgebra O Delta :=
  ⅟(Fintype.card Delta : O) •
    ∑ s : Delta, MonoidAlgebra.single s (↑((chi s)⁻¹) : O)

theorem characterIdempotent_eq_twist_average (chi : Character O Delta) :
    characterIdempotent chi =
      characterTwistHom chi (groupAverage (O := O) (Delta := Delta)) := by
  simp [characterIdempotent, characterTwistHom, characterTwistBasis,
    groupAverage, MonoidAlgebra.of]

/-- The standard character element really is an idempotent. -/
theorem characterIdempotent_isIdempotent (chi : Character O Delta) :
    IsIdempotentElem (characterIdempotent chi) := by
  rw [characterIdempotent_eq_twist_average, isIdempotentElem_iff,
    ← map_mul]
  exact congrArg (characterTwistHom chi)
    (isIdempotentElem_iff.mp
      (groupAverage_isIdempotent (O := O) (Delta := Delta)))

/-- A group element acts on the standard character idempotent through the
corresponding character value.  This is the algebraic identity that turns
the idempotent into an actual eigenspace projector. -/
@[simp]
theorem groupElement_mul_characterIdempotent
    (chi : Character O Delta) (g : Delta) :
    MonoidAlgebra.of O Delta g * characterIdempotent chi =
      (chi g : O) • characterIdempotent chi := by
  simp only [characterIdempotent, Algebra.mul_smul_comm, Finset.mul_sum,
    MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single]
  rw [smul_smul, mul_comm (chi g : O) (⅟(Fintype.card Delta : O)),
    ← smul_smul]
  apply congrArg (⅟(Fintype.card Delta : O) • ·)
  calc
    ∑ x : Delta, MonoidAlgebra.single (g * x) (1 * ↑(chi x)⁻¹) =
        ∑ x : Delta, (chi g : O) •
          MonoidAlgebra.single (g * x) (↑((chi (g * x))⁻¹) : O) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [MonoidAlgebra.smul_single, one_mul]
      apply congrArg (MonoidAlgebra.single (R := O) (M := Delta) (g * x))
      change (↑((chi x)⁻¹) : O) =
        (↑(chi g * (chi (g * x))⁻¹) : O)
      exact congrArg Units.val (by simp [mul_comm])
    _ = (chi g : O) •
        ∑ x : Delta,
          MonoidAlgebra.single (g * x) (↑((chi (g * x))⁻¹) : O) := by
      rw [Finset.smul_sum]
    _ = (chi g : O) •
        ∑ x : Delta, MonoidAlgebra.single x (↑((chi x)⁻¹) : O) := by
      apply congrArg ((chi g : O) • ·)
      set f : Delta → GroupAlgebra O Delta := fun y =>
        MonoidAlgebra.single y (↑((chi y)⁻¹) : O)
      change ∑ x : Delta, f (g * x) = ∑ x : Delta, f x
      rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) _]

/-- The Teichmuller involution exchanges the `chi` and `chi*` idempotents. -/
theorem hash_characterIdempotent (omega chi : Character O Delta) :
    hash omega (characterIdempotent chi) =
      characterIdempotent (reflectedCharacter omega chi) := by
  rw [characterIdempotent, map_smul, map_sum]
  unfold characterIdempotent
  apply congrArg (⅟(Fintype.card Delta : O) • ·)
  calc
    ∑ x : Delta, hash omega
        (MonoidAlgebra.single x (↑((chi x)⁻¹) : O)) =
        ∑ x : Delta, MonoidAlgebra.single x⁻¹
          (↑((reflectedCharacter omega chi x⁻¹)⁻¹) : O) := by
      apply Finset.sum_congr rfl
      intro x _
      simp [reflectedCharacter, mul_comm]
    _ = ∑ s : Delta, MonoidAlgebra.single s
          (↑((reflectedCharacter omega chi s)⁻¹) : O) :=
      Equiv.sum_comp (Equiv.inv Delta)
        (fun s : Delta => MonoidAlgebra.single s
          (↑((reflectedCharacter omega chi s)⁻¹) : O))

/-- In particular, `#` sends the trivial projector to the `omega`
projector.  It is not generally fixed. -/
theorem hash_trivialCharacterIdempotent (omega : Character O Delta) :
    hash omega (characterIdempotent (1 : Character O Delta)) =
      characterIdempotent omega := by
  simpa using hash_characterIdempotent omega (1 : Character O Delta)

end Characters

section PlusMinus

variable {O : Type uO} {Delta : Type uDelta}
  [CommRing O] [CommGroup Delta] [Invertible (2 : O)]

/-- The group-algebra element belonging to complex conjugation. -/
noncomputable def conjugationElement (j : Delta) : GroupAlgebra O Delta :=
  MonoidAlgebra.single j 1

/-- The plus projector `(1 + j) / 2`. -/
noncomputable def plusProjector (j : Delta) : GroupAlgebra O Delta :=
  ⅟(2 : O) • (1 + conjugationElement j)

/-- The minus projector `(1 - j) / 2`. -/
noncomputable def minusProjector (j : Delta) : GroupAlgebra O Delta :=
  ⅟(2 : O) • (1 - conjugationElement j)

omit [Invertible (2 : O)] in
/-- Complex conjugation squares to one in the group algebra. -/
theorem conjugationElement_sq (j : Delta) (hj : j * j = 1) :
    conjugationElement (O := O) j * conjugationElement j = 1 := by
  simp [conjugationElement, hj, ← MonoidAlgebra.one_def]

/-- The plus character projector is idempotent. -/
theorem plusProjector_isIdempotent (j : Delta) (hj : j * j = 1) :
    IsIdempotentElem (plusProjector (O := O) j) := by
  rw [isIdempotentElem_iff, plusProjector]
  have hhalf : ⅟(2 : O) * ⅟(2 : O) * 2 = ⅟(2 : O) := by
    rw [mul_assoc, invOf_mul_self, mul_one]
  have hj' := conjugationElement_sq (O := O) j hj
  have hu : (1 + conjugationElement (O := O) j) *
      (1 + conjugationElement j) =
      (2 : O) • (1 + conjugationElement j) := by
    rw [two_smul O]
    calc
      (1 + conjugationElement j) * (1 + conjugationElement j) =
          1 + conjugationElement j + conjugationElement j +
            conjugationElement j * conjugationElement j := by ring
      _ = (1 + conjugationElement j) +
          (1 + conjugationElement j) := by rw [hj']; ring
  calc
    ⅟(2 : O) • (1 + conjugationElement j) *
        ⅟(2 : O) • (1 + conjugationElement j) =
        (⅟(2 : O) * ⅟(2 : O)) •
          ((1 + conjugationElement j) *
            (1 + conjugationElement j)) := by rw [smul_mul_smul]
    _ = (⅟(2 : O) * ⅟(2 : O)) •
        ((2 : O) • (1 + conjugationElement j)) := by rw [hu]
    _ = (⅟(2 : O) * ⅟(2 : O) * 2) •
        (1 + conjugationElement j) := by rw [smul_smul]
    _ = ⅟(2 : O) • (1 + conjugationElement j) := by rw [hhalf]

/-- The minus character projector is idempotent. -/
theorem minusProjector_isIdempotent (j : Delta) (hj : j * j = 1) :
    IsIdempotentElem (minusProjector (O := O) j) := by
  rw [isIdempotentElem_iff, minusProjector]
  have hhalf : ⅟(2 : O) * ⅟(2 : O) * 2 = ⅟(2 : O) := by
    rw [mul_assoc, invOf_mul_self, mul_one]
  have hj' := conjugationElement_sq (O := O) j hj
  have hu : (1 - conjugationElement (O := O) j) *
      (1 - conjugationElement j) =
      (2 : O) • (1 - conjugationElement j) := by
    rw [two_smul O]
    calc
      (1 - conjugationElement j) * (1 - conjugationElement j) =
          1 - conjugationElement j - conjugationElement j +
            conjugationElement j * conjugationElement j := by ring
      _ = (1 - conjugationElement j) +
          (1 - conjugationElement j) := by rw [hj']; ring
  calc
    ⅟(2 : O) • (1 - conjugationElement j) *
        ⅟(2 : O) • (1 - conjugationElement j) =
        (⅟(2 : O) * ⅟(2 : O)) •
          ((1 - conjugationElement j) *
            (1 - conjugationElement j)) := by rw [smul_mul_smul]
    _ = (⅟(2 : O) * ⅟(2 : O)) •
        ((2 : O) • (1 - conjugationElement j)) := by rw [hu]
    _ = (⅟(2 : O) * ⅟(2 : O) * 2) •
        (1 - conjugationElement j) := by rw [smul_smul]
    _ = ⅟(2 : O) • (1 - conjugationElement j) := by rw [hhalf]

omit [Invertible (2 : O)] in
/-- The sanity anchor `j# = -j`. -/
theorem hash_conjugationElement (omega : Delta →* Oˣ) (j : Delta)
    (hj : j * j = 1) (homega : (omega j : O) = -1) :
    hash omega (conjugationElement j) = -conjugationElement j := by
  have hjinv : j⁻¹ = j := inv_eq_iff_mul_eq_one.mpr hj
  rw [conjugationElement, hash_apply_single, hjinv, homega, one_mul]
  exact MonoidAlgebra.single_neg j 1

/-- The involution exchanges the plus and minus projectors before any
class-group theorem is used. -/
theorem plus_minus_projectors_exchanged (omega : Delta →* Oˣ) (j : Delta)
    (hj : j * j = 1) (homega : (omega j : O) = -1) :
    hash omega (plusProjector j) = minusProjector j ∧
      hash omega (minusProjector j) = plusProjector j := by
  constructor
  · rw [plusProjector, minusProjector, map_smul, map_add, map_one,
      hash_conjugationElement omega j hj homega]
    module
  · rw [minusProjector, plusProjector, map_smul, map_sub, map_one,
      hash_conjugationElement omega j hj homega]
    module

end PlusMinus

end Fermat.Conservation.InvolutiveBase
