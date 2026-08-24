import Fermat.Descent.Irregular.AuxiliaryResidueCharacterNaturality

/-!
# Multiplicative receipts for one auxiliary residue character

The basis-free auxiliary-prime factorization defines its scalar as an
additive character projection of the finite-field symbol phase.  A generated
certificate need not materialize that whole phase.  Since every symbol weight
is a power of the certificate root, exponentiating the projected scalar by
the root turns the sum into one multiplicative identity:

`root ^ scalar = ∏ x, symbolWeight(x) ^ characterWeight(x)`.

This file proves that identity and its converse.  The concrete selected-row
product is indexed by the canonical representatives `1, ..., (p - 1) / 2`
and contains only powers in `ZMod p` and `ZMod q`; it contains no discrete
logarithms or stored phase vector.  Thus a generator can authenticate one
Bernoulli/Kummer channel with one claimed scalar and one finite-field product
calculation.

The product has linear many factors in `p`.  How a generated file evaluates
or chunks that closed modular product is deliberately separate from the
mathematical receipt proved here.
-/

open scoped BigOperators

namespace Fermat.Irregular.CircularUnitResidues

noncomputable section

open Fermat.Irregular.AuxiliaryResidueChannels
open Fermat.Irregular.CyclotomicCharactersPrime
open Fermat.Irregular.CyclotomicLogDetPrime
open Fermat.Irregular.CyclotomicPlacesPrime
open KummerCriterion.CyclotomicUnits

variable {p q h : ℕ} [Fact p.Prime] [Fact q.Prime]

local instance realResidueFintype [Fact (2 < p)] :
    Fintype (RealResidueGroup p) := Fintype.ofFinite _

namespace Certificate

private theorem root_pow_add_val
    (C : Certificate p q) (a b : ZMod p) :
    C.root ^ (a + b).val = C.root ^ a.val * C.root ^ b.val := by
  have hab : (a + b).val ≡ a.val + b.val [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  rw [pow_eq_pow_of_modEq hab C.root_isPrimitive.pow_eq_one, pow_add]

private theorem root_pow_mul_val
    (C : Certificate p q) (a b : ZMod p) :
    C.root ^ (a * b).val = (C.root ^ a.val) ^ b.val := by
  have hab : (a * b).val ≡ a.val * b.val [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  rw [pow_eq_pow_of_modEq hab C.root_isPrimitive.pow_eq_one, pow_mul]

private theorem root_pow_sum_val
    {G : Type*} [Fintype G]
    (C : Certificate p q) (f : G → ZMod p) :
    C.root ^ (∑ x : G, f x).val =
      ∏ x : G, C.root ^ (f x).val := by
  classical
  induction (Finset.univ : Finset G) using Finset.induction with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.prod_insert hx,
        root_pow_add_val, ih]

/-- Multiplicative authentication target for one character scalar.

The orbit is enumerated by the canonical representatives of the real residue
group.  The exponent is the canonical natural representative of the inverse
character value in `ZMod p`. -/
def selectedCharacterProduct
    [Fact (2 < p)]
    (C : Certificate p q) (symbolHalf : ℕ)
    (chi : RealResidueGroup p →* (ZMod p)ˣ) :
    ZMod q :=
  ∏ k : Fin (kummerLogRank p + 1),
    C.exponentWeight symbolHalf (standardUnit (p := p) k) ^
      ((((chi (standardRealResiduesEquiv (p := p) k))⁻¹ :
        (ZMod p)ˣ) : ZMod p).val)

/-- Concrete authentication target for the Kummer row `channelRow`.

Unlike `selectedCharacterProduct`, this expression mentions neither quotient
groups nor a character map.  It is the form intended for generated finite
receipts. -/
def selectedChannelProduct
    [Fact (2 < p)]
    (C : Certificate p q) (symbolHalf : ℕ)
    (channelRow : Fin (kummerLogRank p)) : ZMod q :=
  ∏ k : Fin (kummerLogRank p + 1),
    evenSymbolWeight symbolHalf (C.root ^ (k.val + 1)) ^
      (((((k.val + 1 : ℕ) : ZMod p) ^
        (2 * kummerLogRowIndex (p := p) channelRow))⁻¹).val)

/-- The concrete selected-row product is the abstract product for the even
power character attached to that Kummer row. -/
theorem selectedCharacterProduct_evenPowerCharacter_eq
    [Fact (2 < p)]
    (C : Certificate p q) (symbolHalf : ℕ) (hp_three : 3 ≤ p)
    (channelRow : Fin (kummerLogRank p)) :
    C.selectedCharacterProduct symbolHalf
        (evenPowerCharacter (p := p) hp_three channelRow) =
      C.selectedChannelProduct symbolHalf channelRow := by
  apply Finset.prod_congr rfl
  intro k _
  congr 1
  · rw [Certificate.exponentWeight, Certificate.rootAtExponent,
      standardUnit_coe]
    congr 2
    exact ZMod.val_natCast_of_lt (standardExponent_lt (p := p) k)
  · rw [standardRealResiduesEquiv_apply, standardRealResidue,
      evenPowerCharacter, QuotientGroup.lift_mk]
    simp only [powMonoidHom_apply]
    apply congrArg ZMod.val
    simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      standardUnit_coe]

/-- Exponentiating an additive orbit scalar by the certificate root gives
the selected multiplicative character product. -/
theorem root_pow_orbitScalar_val_eq_selectedCharacterProduct
    [Fact (2 < p)]
    (C : Certificate p q) (hp_three : 3 ≤ p)
    (hm : C.symbolExponent = 2 * h)
    (chi : RealResidueGroup p →* (ZMod p)ˣ) :
    C.root ^
        (orbitScalar chi (C.realSymbolPhase hp_three hm)).val =
      C.selectedCharacterProduct h chi := by
  classical
  let phase := C.realSymbolPhase hp_three hm
  let weight : RealResidueGroup p → ZMod p := fun x ↦
    (((chi x)⁻¹ : (ZMod p)ˣ) : ZMod p)
  rw [show orbitScalar chi phase = ∑ x, phase x * weight x by rfl]
  rw [root_pow_sum_val]
  rw [show (∏ x : RealResidueGroup p,
      C.root ^ (phase x * weight x).val) =
      ∏ k : Fin (kummerLogRank p + 1),
        C.root ^
          (phase (standardRealResiduesEquiv (p := p) k) *
            weight (standardRealResiduesEquiv (p := p) k)).val by
    exact (Equiv.prod_comp (standardRealResiduesEquiv (p := p))
      (fun x : RealResidueGroup p ↦
        C.root ^ (phase x * weight x).val)).symm]
  apply Finset.prod_congr rfl
  intro k _
  rw [root_pow_mul_val]
  rw [show phase (standardRealResiduesEquiv (p := p) k) =
      C.exponentPhase hm (standardUnit (p := p) k) by
    dsimp only [phase]
    rw [standardRealResiduesEquiv_apply,
      standardRealResidue, C.realSymbolPhase_mk]]
  rw [C.root_pow_exponentPhase_val hm]

/-- A multiplicative product equality determines the additive character
scalar, because the certificate root has exact order `p`. -/
theorem orbitScalar_eq_of_selectedCharacterProduct
    [Fact (2 < p)]
    (C : Certificate p q) (hp_three : 3 ≤ p)
    (hm : C.symbolExponent = 2 * h)
    (chi : RealResidueGroup p →* (ZMod p)ˣ)
    (claimed : ZMod p)
    (hauth : C.selectedCharacterProduct h chi =
      C.root ^ claimed.val) :
    orbitScalar chi (C.realSymbolPhase hp_three hm) = claimed := by
  apply ZMod.val_injective
  apply C.root_isPrimitive.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [C.root_pow_orbitScalar_val_eq_selectedCharacterProduct hp_three hm,
    hauth]

/-- Even-character specialization of
`orbitScalar_eq_of_selectedCharacterProduct`, in the concrete form consumed
by generated Kummer-channel certificates. -/
theorem basisFreeFactorization_scalar_eq_of_selectedChannelProduct
    [Fact (2 < p)]
    (C : Certificate p q) (hp_three : 3 ≤ p)
    (hm : C.symbolExponent = 2 * h)
    (channelRow : Fin (kummerLogRank p))
    (claimed : ZMod p)
    (hauth : C.selectedChannelProduct h channelRow =
      C.root ^ claimed.val) :
    (C.basisFreeFactorization hp_three hm channelRow).scalar = claimed := by
  exact C.orbitScalar_eq_of_selectedCharacterProduct hp_three hm _ claimed
    ((C.selectedCharacterProduct_evenPowerCharacter_eq h hp_three
      channelRow).trans hauth)

/-- A generator-facing receipt for one selected Kummer channel.

The receipt stores one claimed scalar and authenticates it with one
multiplicative identity.  It does not store the auxiliary symbol phase. -/
structure SelectedChannelScalarReceipt
    [Fact (2 < p)]
    (C : Certificate p q) (hp_three : 3 ≤ p)
    (channelRow : Fin (kummerLogRank p)) where
  symbolHalf : ℕ
  symbolExponent_eq : C.symbolExponent = 2 * symbolHalf
  scalar : ZMod p
  scalar_ne : scalar ≠ 0
  authenticate :
    C.selectedChannelProduct symbolHalf channelRow = C.root ^ scalar.val

namespace SelectedChannelScalarReceipt

variable [Fact (2 < p)]
variable {C : Certificate p q} {hp_three : 3 ≤ p}
variable {channelRow : Fin (kummerLogRank p)}

/-- The existing universal basis-free factorization selected by this
receipt. -/
def factorization
    (A : SelectedChannelScalarReceipt C hp_three channelRow) :
    Factorization p q hp_three C channelRow :=
  C.basisFreeFactorization hp_three A.symbolExponent_eq channelRow

/-- The receipt identifies the scalar of its basis-free factorization. -/
theorem factorization_scalar_eq
    (A : SelectedChannelScalarReceipt C hp_three channelRow) :
    A.factorization.scalar = A.scalar := by
  exact C.basisFreeFactorization_scalar_eq_of_selectedChannelProduct
    hp_three A.symbolExponent_eq channelRow A.scalar A.authenticate

/-- The selected basis-free factorization is nonblind, ready to be used as
one row of an `AuxiliaryChannelProvider`. -/
theorem factorization_scalar_ne
    (A : SelectedChannelScalarReceipt C hp_three channelRow) :
    A.factorization.scalar ≠ 0 := by
  rw [A.factorization_scalar_eq]
  exact A.scalar_ne

end SelectedChannelScalarReceipt

end Certificate

end

end Fermat.Irregular.CircularUnitResidues
