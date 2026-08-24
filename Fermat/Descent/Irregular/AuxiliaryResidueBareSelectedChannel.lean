import Fermat.Descent.Irregular.AuxiliaryResidueSelectedChannel
import Fermat.Descent.Irregular.BernoulliChannelProjection
import Fermat.Descent.Irregular.SelectiveCircularUnitResidues

/-!
# Matrix-free input for one auxiliary residue character

An archive-scale selected-character receipt should not contain a square
residue matrix or a vector of discrete-log phases.  The finite input in this
file consists only of:

* a split auxiliary prime and a primitive `p`th root in its residue field;
* the power-residue exponent `(q - 1) / p`;
* one selected Kummer row; and
* one nonzero scalar authenticated by the multiplicative product from
  `AuxiliaryResidueSelectedChannel`.

To reuse the established global arithmetic bridge without changing it, this
file synthesizes a `CircularUnitResidues.Certificate` internally.  Its matrix
entry is *defined* as the root discrete logarithm of the corresponding
normalized circular-unit value.  This matrix is noncomputable proof
scaffolding: no generated certificate stores or evaluates it.  The public
selected receipt remains a finite equality in `ZMod p` and `ZMod q`.

Thus there are two deliberately different boundaries:

* the generated provenance is finite and matrix-free;
* the internal proof may use classical finite-group equivalences to connect
  that provenance to the existing CPlus power-relation theorem.
-/

open scoped BigOperators NumberField

namespace Fermat.Irregular.BareAuxiliaryResidueChannel

noncomputable section

open Fermat.Irregular.AuxiliaryResidueChannels
open Fermat.Irregular.BernoulliChannelProjection
open Fermat.Irregular.CircularUnitResidues
open Fermat.Irregular.CircularUnitResidues.Certificate
open Fermat.Irregular.SelectiveCircularUnitResidues
open KummerCriterion
open KummerCriterion.CyclotomicUnits

variable {p q h : ℕ} [Fact p.Prime] [Fact q.Prime]

/-- Finite split-prime input.  In particular, it contains no residue matrix
and no discrete-log phase vector. -/
structure SplitPrimeData (p q : ℕ) [Fact p.Prime] [Fact q.Prime] where
  hp2 : p ≠ 2
  symbolExponent : ℕ
  q_sub_one : q - 1 = symbolExponent * p
  root : ZMod q
  root_isPrimitive : IsPrimitiveRoot root p

namespace SplitPrimeData

variable (D : SplitPrimeData p q)

private def rootUnit : (ZMod q)ˣ :=
  Units.mk0 D.root
    (D.root_isPrimitive.ne_zero (Fact.out : p.Prime).ne_zero)

private theorem rootUnit_isPrimitive : IsPrimitiveRoot D.rootUnit p := by
  apply IsPrimitiveRoot.coe_units_iff.mp
  simpa [rootUnit] using D.root_isPrimitive

private noncomputable def powerToRootPowers :
    (ZMod q)ˣ →* Subgroup.zpowers D.rootUnit where
  toFun u := ⟨u ^ D.symbolExponent, by
    rw [D.rootUnit_isPrimitive.zpowers_eq]
    rw [mem_rootsOfUnity]
    calc
      (u ^ D.symbolExponent) ^ p = u ^ (q - 1) := by
        rw [← pow_mul, D.q_sub_one]
      _ = 1 := ZMod.units_pow_card_sub_one_eq_one q u⟩
  map_one' := by ext; simp
  map_mul' u v := by ext; simp [mul_pow]

private noncomputable def residueLog : Additive (ZMod q)ˣ →+ ZMod p :=
  D.rootUnit_isPrimitive.zmodEquivZPowers.symm.toAddMonoidHom.comp
    D.powerToRootPowers.toAdditive

private theorem root_pow_residueLog_val (u : (ZMod q)ˣ) :
    D.root ^ (D.residueLog (Additive.ofMul u)).val =
      (u : ZMod q) ^ D.symbolExponent := by
  let z : Subgroup.zpowers D.rootUnit := D.powerToRootPowers u
  let b : ZMod p := D.residueLog (Additive.ofMul u)
  have hb : ((b.val : ℕ) : ZMod p) = b := ZMod.natCast_zmod_val b
  have happly :=
    D.rootUnit_isPrimitive.zmodEquivZPowers.apply_symm_apply
      (Additive.ofMul z)
  have hpow :=
    D.rootUnit_isPrimitive.zmodEquivZPowers_apply_coe_nat b.val
  rw [hb] at hpow
  change D.rootUnit_isPrimitive.zmodEquivZPowers b = Additive.ofMul
      (⟨D.rootUnit ^ b.val, b.val, rfl⟩ : Subgroup.zpowers D.rootUnit) at hpow
  have hz :
      (⟨D.rootUnit ^ b.val, b.val, rfl⟩ : Subgroup.zpowers D.rootUnit) = z := by
    apply Additive.ofMul.injective
    rw [← hpow]
    exact happly
  have hval := congrArg
    (fun v : Subgroup.zpowers D.rootUnit ↦
      (((v.1 : (ZMod q)ˣ) : ZMod q))) hz
  calc
    D.root ^ (D.residueLog (Additive.ofMul u)).val =
        (((D.powerToRootPowers u).1 : (ZMod q)ˣ) : ZMod q) := by
      simpa [z, b, rootUnit] using hval
    _ = (u : ZMod q) ^ D.symbolExponent := rfl

private theorem normalizedUnitValue_ne_zero
    (j i : Fin ((p - 3) / 2)) :
    normalizedUnitValue D.root j i ≠ 0 := by
  let x : ZMod q := embeddingRoot D.root j
  let a : ℕ := i.val + 2
  have hxprim : IsPrimitiveRoot x p :=
    embeddingRoot_isPrimitive D.hp2 D.root_isPrimitive j
  have hx0 : x ≠ 0 :=
    hxprim.ne_zero (Fact.out : p.Prime).ne_zero
  have hx1 : 1 - x ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm
      (hxprim.ne_one (Fact.out : p.Prime).one_lt))
  have hp_three : 3 ≤ p := by
    exact (Fact.out : p.Prime).two_le.lt_or_eq.resolve_right D.hp2.symm
  have ha_pos : 0 < a := by omega
  have ha_lt : a < p := by
    dsimp only [a]
    have hi := i.isLt
    omega
  have hxa : x ^ a ≠ 1 := by
    intro hone
    have hdvd : p ∣ a := hxprim.pow_eq_one_iff_dvd a |>.mp hone
    exact (Nat.not_dvd_of_pos_of_lt ha_pos ha_lt) hdvd
  unfold normalizedUnitValue
  apply div_ne_zero
  · exact mul_ne_zero (pow_ne_zero _ hx0)
      (sub_ne_zero.mpr (Ne.symm hxa))
  · exact hx1

private def normalizedUnitValueUnit
    (j i : Fin ((p - 3) / 2)) : (ZMod q)ˣ :=
  Units.mk0 (normalizedUnitValue D.root j i)
    (D.normalizedUnitValue_ne_zero j i)

private def canonicalMatrix : Matrix (Fin ((p - 3) / 2))
    (Fin ((p - 3) / 2)) (ZMod p) := fun j i ↦
  D.residueLog (Additive.ofMul (D.normalizedUnitValueUnit j i))

/-- Internal, noncomputable realization of the established full certificate
API.  Its matrix is derived by finite-group discrete logarithms rather than
provided as generated data. -/
def canonicalCertificate : Certificate p q where
  hp2 := D.hp2
  symbolExponent := D.symbolExponent
  q_sub_one := D.q_sub_one
  root := D.root
  root_isPrimitive := D.root_isPrimitive
  matrix := D.canonicalMatrix
  entry_certificate := by
    intro j i
    exact (D.root_pow_residueLog_val
      (D.normalizedUnitValueUnit j i)).symm

/-- The concrete finite selected-character product attached directly to the
bare split-prime input.  It has `(p - 1) / 2` factors and no discrete logs. -/
def selectedChannelProduct
    (symbolHalf : ℕ) (channelRow : Fin (kummerLogRank p)) : ZMod q :=
  ∏ k : Fin (kummerLogRank p + 1),
    evenSymbolWeight symbolHalf (D.root ^ (k.val + 1)) ^
      (((((k.val + 1 : ℕ) : ZMod p) ^
        (2 * kummerLogRowIndex (p := p) channelRow))⁻¹).val)

private theorem selectedChannelProduct_eq_certificate
    [Fact (2 < p)] (symbolHalf : ℕ)
    (channelRow : Fin (kummerLogRank p)) :
    D.selectedChannelProduct symbolHalf channelRow =
      D.canonicalCertificate.selectedChannelProduct symbolHalf channelRow :=
  rfl

end SplitPrimeData

/-- The complete finite receipt for one selected Kummer row.  Its only
potentially large proof is the closed modular equality `authenticate`; no
phase or matrix values are fields. -/
structure SelectedChannelReceipt
    (D : SplitPrimeData p q) (hp_three : 3 ≤ p)
    (channelRow : Fin (kummerLogRank p)) where
  symbolHalf : ℕ
  symbolExponent_eq : D.symbolExponent = 2 * symbolHalf
  scalar : ZMod p
  scalar_ne : scalar ≠ 0
  authenticate :
    D.selectedChannelProduct symbolHalf channelRow = D.root ^ scalar.val

namespace SelectedChannelReceipt

variable {D : SplitPrimeData p q} {hp_three : 3 ≤ p}
variable {channelRow : Fin (kummerLogRank p)}

/-- Basis-free factorization exposed for compatibility with the existing
auxiliary-channel provider API. -/
def factorization
    (A : SelectedChannelReceipt D hp_three channelRow) :
    Factorization p q hp_three D.canonicalCertificate channelRow := by
  letI : Fact (2 < p) := ⟨by omega⟩
  exact D.canonicalCertificate.basisFreeFactorization hp_three
    A.symbolExponent_eq channelRow

/-- The selected factorization scalar is the claimed finite scalar. -/
theorem factorization_scalar_eq
    (A : SelectedChannelReceipt D hp_three channelRow) :
    A.factorization.scalar = A.scalar := by
  letI : Fact (2 < p) := ⟨by omega⟩
  apply Certificate.basisFreeFactorization_scalar_eq_of_selectedChannelProduct
    D.canonicalCertificate hp_three A.symbolExponent_eq channelRow A.scalar
  rw [← D.selectedChannelProduct_eq_certificate]
  exact A.authenticate

/-- The selected factorization is nonblind. -/
theorem factorization_scalar_ne
    (A : SelectedChannelReceipt D hp_three channelRow) :
    A.factorization.scalar ≠ 0 := by
  rw [A.factorization_scalar_eq]
  exact A.scalar_ne

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

/-- Bare split-prime data and one authenticated nonzero product scalar send
every global CPlus `p`th-power relation to zero in the selected intrinsic
Kummer channel.  The conclusion and the finite receipt contain no matrix. -/
theorem canonicalKummerChannel_exponents_eq_zero_of_CPlus_product_mem_powers
    (A : SelectedChannelReceipt D hp_three channelRow)
    (s : ℤ) (e : Fin (kummerLogRank p) → ℤ)
    (hpow : CPlusExponentProduct (p := p) (K := K) hp_three s e ∈
      pPowerSubgroup (EPlus (K := K)) p) :
    canonicalKummerChannel p hp_three channelRow
        (fun i ↦ (e i : ZMod p)) = 0 := by
  exact
    SelectiveCircularUnitResidues.canonicalKummerChannel_exponents_eq_zero_of_CPlus_product_mem_powers
      (K := K) D.canonicalCertificate hp_three A.factorization
      A.factorization_scalar_ne s e hpow

end SelectedChannelReceipt

/-- A matrix-free family provider at one split prime.  It stores exactly one
selected multiplicative receipt for every row in the Bernoulli support.

The q-free projection certificate is the true downstream object.  Receipts
from different auxiliary primes can therefore still be mixed by constructing
that certificate coordinatewise; this structure is only the common and
generator-friendly one-prime convenience case. -/
structure SelectedChannelProvider
    {N : ℕ} (support : BernoulliChannelSupport p N)
    (D : SplitPrimeData p q) (hp_three : 3 ≤ p) where
  receipt : ∀ i, SelectedChannelReceipt D hp_three (support.row i)

namespace SelectedChannelProvider

universe u

variable {N : ℕ} {support : BernoulliChannelSupport p N}
variable {D : SplitPrimeData p q} {hp_three : 3 ≤ p}

/-- Compile a family of matrix-free selected products into the intrinsic,
q-free vector projection receipt consumed by the Bernoulli-channel descent.
-/
def toProjectionKernelCertificate
    (A : SelectedChannelProvider support D hp_three) :
    ProjectionKernelCertificate.{u} support hp_three where
  powerRelation_kernel := by
    intro K _ _ _ _ s e hpow
    apply (support.projection_eq_zero_iff hp_three _).2
    intro i
    exact
      (A.receipt i).canonicalKummerChannel_exponents_eq_zero_of_CPlus_product_mem_powers
        s e hpow

end SelectedChannelProvider

end

end Fermat.Irregular.BareAuxiliaryResidueChannel
