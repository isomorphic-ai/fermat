/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The canonical strict primal Selmer mode at 827

This file puts the first actual generated circular unit into Mathlib's
empty-support 59-Selmer group through `selmerGroup.fromUnitLift`, and only
then applies the canonical cyclotomic character idempotent.  Thus the primal
input of the local pairing is a literal seated Selmer class, rather than the
previously separate residue wave.

The construction also exposes a decisive parity fact: the generated unit is
real, whereas `irregularCharacter59 = omega^15` is odd, so this particular
projected Selmer class is zero.  The unprojected unit receipt and its raw even
mode-44 residue wave remain genuinely nonzero; the file records both sides
instead of conflating them.

The residue certificates retained here concern the generating ring unit.
Identifying the projected Selmer class's local tame readings with the
Fourier projection is a bilinear local-comparison theorem, not a pointwise
definition, and is deliberately left to the local-pairing ledger.
-/
import Fermat.Exponents.FiftyNine.Conservation.CanonicalIrregularMode827
import Fermat.Exponents.FiftyNine.Conservation.ExplicitResiduePlaceOrbit827
import Fermat.Exponents.FiftyNine.Conservation.VostokovLocalization59
import KummerCriterion.CyclotomicUnits.KummerLogMatrix

open scoped BigOperators MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.FiftyNine.Conservation.CanonicalPrimalSelmerMode827

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.InvolutiveBase
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CapacityCertificate
open Fermat.FiftyNine.Conservation.Credit
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.PrimalOrbitResidue827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- The canonical primitive 59th root supplied by the cyclotomic extension. -/
abbrev canonicalZeta59 : K := IsCyclotomicExtension.zeta 59 ℚ K

/-- The canonical root really has exact order 59. -/
abbrev canonicalZeta59_isPrimitive :
    IsPrimitiveRoot (canonicalZeta59 K) 59 :=
  IsCyclotomicExtension.zeta_spec 59 ℚ K

/-- The first actual generated circular unit in the ring of integers. -/
noncomputable def canonicalFirstGeneratedRingUnit827 :
    (NumberField.RingOfIntegers K)ˣ :=
  Credit.generatedUnit (canonicalZeta59_isPrimitive K)
    DetectorWitness827.firstLedgerNode

/-- The class of the first generated unit modulo 59th powers. -/
noncomputable def canonicalFirstGeneratedUnitClass59 :
    UnitModP (NumberField.RingOfIntegers K) 59 :=
  Additive.ofMul <| QuotientGroup.mk'
    (powMonoidHom 59 :
      (NumberField.RingOfIntegers K)ˣ →*
        (NumberField.RingOfIntegers K)ˣ).range
    (canonicalFirstGeneratedRingUnit827 K)

/-- The first generated unit inserted through Mathlib's genuine unit leg of
the empty-support Selmer sequence. -/
noncomputable def canonicalFirstGeneratedStrictSelmer59 :
    SelmerCarrier (NumberField.RingOfIntegers K) K 59 :=
  CommonActionStage.unitInclusion
    (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
    (canonicalFirstGeneratedUnitClass59 K)

/-- Apply the canonical strict cyclotomic character projector only after the
ring unit has entered Mathlib's actual Selmer carrier. -/
noncomputable def canonicalPrimalSelmerMode827
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] :
    OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59 :=
  characterProjectorAt (cyclotomicStrictSelmerRepresentation59 K)
    irregularCharacter59 (canonicalFirstGeneratedStrictSelmer59 K)

/-- Carrier readback: the seated source is literally the character
idempotent acting on the Mathlib unit receipt. -/
theorem canonicalPrimalSelmerMode827_toSeatedCarrier
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] :
    toSeatedCarrier (canonicalPrimalSelmerMode827 K) =
      (cyclotomicStrictSelmerRepresentation59 K).asAlgebraHom
        (characterIdempotent irregularCharacter59)
        (canonicalFirstGeneratedStrictSelmer59 K) :=
  rfl

/-- Kummer-class readback of the projected source, without choosing a
representative or identifying raw and projected residue vectors. -/
theorem canonicalPrimalSelmerMode827_toKummerQuotient
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] :
    toKummerQuotient (canonicalPrimalSelmerMode827 K) =
      (Additive.toMul
        ((cyclotomicStrictSelmerRepresentation59 K).asAlgebraHom
          (characterIdempotent irregularCharacter59)
          (canonicalFirstGeneratedStrictSelmer59 K))).1 :=
  rfl

/-- The source before projection is exactly the public Mathlib-backed unit
inclusion, retained as an explicit API theorem for downstream ledgers. -/
theorem canonicalFirstGeneratedStrictSelmer59_eq_unitInclusion :
    canonicalFirstGeneratedStrictSelmer59 K =
      CommonActionStage.unitInclusion
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (canonicalFirstGeneratedUnitClass59 K) :=
  rfl

/-- Before character projection, forgetting the Selmer predicate recovers
the Kummer class of the embedded ring unit exactly. -/
theorem canonicalFirstGeneratedStrictSelmer59_kummerClass :
    (Additive.toMul (canonicalFirstGeneratedStrictSelmer59 K)).1 =
      QuotientGroup.mk'
        (powMonoidHom 59 : Kˣ →* Kˣ).range
        (Units.map (algebraMap (NumberField.RingOfIntegers K) K)
          (canonicalFirstGeneratedRingUnit827 K)) := by
  rfl

/-- The first generated ring unit is fixed by the cyclotomic automorphism
indexed by `-1`, because it belongs to the real-unit subgroup. -/
theorem cyclotomicNegOne_fixed_canonicalFirstGeneratedRingUnit827 :
    cyclotomicUnitEquiv59 K (-1)
        (Units.map (algebraMap (NumberField.RingOfIntegers K) K)
          (canonicalFirstGeneratedRingUnit827 K)) =
      Units.map (algebraMap (NumberField.RingOfIntegers K) K)
        (canonicalFirstGeneratedRingUnit827 K) := by
  letI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField
      (S := {59}) K ⟨59, rfl, by norm_num⟩
  apply Units.ext
  change KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K (-1)
      ((canonicalFirstGeneratedRingUnit827 K :
        NumberField.RingOfIntegers K) : K) =
    ((canonicalFirstGeneratedRingUnit827 K :
      NumberField.RingOfIntegers K) : K)
  rw [KummerCriterion.cyclotomicSigmaOfUnit_neg_one_eq_complexConjGal
    (p := 59) (K := K) (by norm_num)]
  have hreal :
      NumberField.IsCMField.unitsComplexConj K
          (canonicalFirstGeneratedRingUnit827 K) =
        canonicalFirstGeneratedRingUnit827 K :=
    (NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mpr
      (Credit.generatedUnit
        (canonicalZeta59_isPrimitive K)
        DetectorWitness827.firstLedgerNode).property
  have hval := congrArg
    (fun u : (NumberField.RingOfIntegers K)ˣ ↦
      ((u : NumberField.RingOfIntegers K) : K)) hreal
  exact hval

/-- Hence the genuine Mathlib unit receipt is fixed by complex conjugation
inside the canonical strict Selmer representation. -/
theorem cyclotomicNegOne_fixed_canonicalFirstGeneratedStrictSelmer59 :
    cyclotomicStrictSelmerRepresentation59 K (-1)
        (canonicalFirstGeneratedStrictSelmer59 K) =
      canonicalFirstGeneratedStrictSelmer59 K := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change cyclotomicKummerHom59 K (-1)
      (Additive.toMul (canonicalFirstGeneratedStrictSelmer59 K)).1 =
    (Additive.toMul (canonicalFirstGeneratedStrictSelmer59 K)).1
  rw [canonicalFirstGeneratedStrictSelmer59_kummerClass]
  rw [cyclotomicKummerHom59_mk]
  exact congrArg
    (QuotientGroup.mk'
      (powMonoidHom 59 : Kˣ →* Kˣ).range)
    (cyclotomicNegOne_fixed_canonicalFirstGeneratedRingUnit827 K)

/-- Reduction of the canonical irregular character at complex conjugation
is `-1`: the strict irregular seat is an odd character seat. -/
theorem irregularCharacter59_negOne_reduction :
    PadicInt.toZMod
        (irregularCharacter59 (-1) : PadicInt 59) =
      (-1 : ZMod 59) := by
  have h := DFunLike.congr_fun
    reducedCharacter59_irregularCharacter59 (-1)
  have hval := congrArg Units.val h
  calc
    PadicInt.toZMod
        (irregularCharacter59 (-1) : PadicInt 59) =
        (-1 : ZMod 59) ^ (15 : ZMod 58).val := by
      simpa [reducedCharacter59, powerCharacter59] using hval
    _ = (-1 : ZMod 59) := by decide

/-- Applying the central character idempotent to a conjugation-fixed source
leaves it conjugation-fixed. -/
theorem cyclotomicNegOne_fixed_canonicalPrimalSelmerMode827
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] :
    cyclotomicStrictSelmerRepresentation59 K (-1)
        (canonicalPrimalSelmerMode827 K).1 =
      (canonicalPrimalSelmerMode827 K).1 := by
  let rho := cyclotomicStrictSelmerRepresentation59 K
  let e := characterIdempotent irregularCharacter59
  let x := canonicalFirstGeneratedStrictSelmer59 K
  change rho (-1) (rho.asAlgebraHom e x) = rho.asAlgebraHom e x
  calc
    rho (-1) (rho.asAlgebraHom e x) =
        rho.asAlgebraHom
          (MonoidAlgebra.of (PadicInt 59) GaloisIndex59 (-1))
          (rho.asAlgebraHom e x) := by
      rw [Representation.asAlgebraHom_of]
    _ = rho.asAlgebraHom
          (MonoidAlgebra.of (PadicInt 59) GaloisIndex59 (-1) * e) x := by
      rw [map_mul]
      rfl
    _ = rho.asAlgebraHom
          (e * MonoidAlgebra.of (PadicInt 59) GaloisIndex59 (-1)) x := by
      rw [mul_comm]
    _ = rho.asAlgebraHom e
          (rho.asAlgebraHom
            (MonoidAlgebra.of (PadicInt 59) GaloisIndex59 (-1)) x) := by
      rw [map_mul]
      rfl
    _ = rho.asAlgebraHom e (rho (-1) x) := by
      rw [Representation.asAlgebraHom_of]
    _ = rho.asAlgebraHom e x := by
      rw [cyclotomicNegOne_fixed_canonicalFirstGeneratedStrictSelmer59]

/-- **Parity obstruction.** The first generated circular unit is real, but
the requested old primal irregular character is odd.  Consequently its
canonical strict character projection is exactly zero.  In particular, the
nonzero even mode-44 residue certificate cannot be recast as nonvanishing of
this mode-15 Selmer element. -/
theorem canonicalPrimalSelmerMode827_eq_zero
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] :
    canonicalPrimalSelmerMode827 K = 0 := by
  let x := canonicalPrimalSelmerMode827 K
  have heigen :
      cyclotomicStrictSelmerRepresentation59 K (-1) x.1 =
        (irregularCharacter59 (-1) : PadicInt 59) • x.1 :=
    (mem_characterEigenspace_iff
      (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59 x.1).mp x.property (-1)
  have hfixed :
      cyclotomicStrictSelmerRepresentation59 K (-1) x.1 = x.1 :=
    cyclotomicNegOne_fixed_canonicalPrimalSelmerMode827 K
  have hneg : (-1 : ZMod 59) • x.1 = x.1 := by
    rw [← irregularCharacter59_negOne_reduction]
    change (irregularCharacter59 (-1) : PadicInt 59) • x.1 = x.1
    exact heigen.symm.trans hfixed
  have hneg' : -x.1 = x.1 := by
    rw [← neg_one_smul (ZMod 59) x.1]
    exact hneg
  have hadd : x.1 + x.1 = 0 := by
    calc
      x.1 + x.1 = -x.1 + x.1 := congrArg (fun y ↦ y + x.1) hneg'.symm
      _ = 0 := neg_add_cancel x.1
  have htwo : (2 : ZMod 59) • x.1 = 0 := by
    rw [show (2 : ZMod 59) = 1 + 1 by norm_num, add_smul,
      one_smul]
    exact hadd
  apply Subtype.ext
  exact (smul_eq_zero_iff_right
    (by decide : (2 : ZMod 59) ≠ 0)).mp htwo

/-! ## Honest residue information retained by the generating unit -/

/-- The complete residue-orbit reading, bundled as an additive character on
actual ring units.  This is the homomorphism already used pointwise by
`fullOrbitUnitReading827`; bundling it exposes why it kills 59th powers. -/
noncomputable def ringUnitOrbitReading827
    (sigma : GaloisIndex59) :
    Additive (NumberField.RingOfIntegers K)ˣ →+ ZMod 59 :=
  CapacityCertificate.halfScale.comp <|
    CapacityCertificate.residueLog.comp <|
      (((Units.map
        (PrimalOrbitResidue827.orbitReductionHom827
          (canonicalZeta59_isPrimitive K) sigma)).comp
        (CapacityCertificate.realNorm (K := K))).toAdditive)

@[simp]
theorem ringUnitOrbitReading827_apply
    (sigma : GaloisIndex59)
    (u : (NumberField.RingOfIntegers K)ˣ) :
    ringUnitOrbitReading827 K sigma (Additive.ofMul u) =
      fullOrbitUnitReading827 (canonicalZeta59_isPrimitive K) u sigma :=
  rfl

/-- Every 59th power is silent in each residue-orbit character. -/
theorem ringUnitOrbitReading827_pow_fiftyNine
    (sigma : GaloisIndex59)
    (u : (NumberField.RingOfIntegers K)ˣ) :
    ringUnitOrbitReading827 K sigma (Additive.ofMul (u ^ 59)) = 0 := by
  have hp : Additive.ofMul (u ^ 59) = 59 • Additive.ofMul u := rfl
  rw [hp]
  rw [map_nsmul, ZModModule.char_nsmul_eq_zero]

/-- The first generated unit is nontrivial modulo 59th powers.  This is
detected by the existing identity-orbit residue `48`, not by a new
certificate. -/
theorem canonicalFirstGeneratedUnitClass59_ne_zero :
    canonicalFirstGeneratedUnitClass59 K ≠ 0 := by
  intro hzero
  have hquotient :
      QuotientGroup.mk'
          (powMonoidHom 59 :
            (NumberField.RingOfIntegers K)ˣ →*
              (NumberField.RingOfIntegers K)ˣ).range
          (canonicalFirstGeneratedRingUnit827 K) = 1 :=
    Additive.ofMul.injective hzero
  have hpower := (QuotientGroup.eq_one_iff
    (canonicalFirstGeneratedRingUnit827 K)).mp hquotient
  obtain ⟨u, hu⟩ := hpower
  have hsilent :
      ringUnitOrbitReading827 K 1
          (Additive.ofMul (canonicalFirstGeneratedRingUnit827 K)) = 0 := by
    rw [← hu]
    exact ringUnitOrbitReading827_pow_fiftyNine K 1 u
  have hread :
      ringUnitOrbitReading827 K 1
          (Additive.ofMul (canonicalFirstGeneratedRingUnit827 K)) =
        DetectorWitness827.firstLampReading827 := by
    rw [ringUnitOrbitReading827_apply]
    exact fullOrbitUnitReading827_firstGenerated_one
      (canonicalZeta59_isPrimitive K)
  exact DetectorWitness827.firstLampReading827_ne_zero
    (hread.symm.trans hsilent)

/-- Injectivity of Mathlib's unit leg transports the residue-detected
nonvanishing into the genuine strict Selmer carrier before projection. -/
theorem canonicalFirstGeneratedStrictSelmer59_ne_zero :
    canonicalFirstGeneratedStrictSelmer59 K ≠ 0 := by
  intro hzero
  apply canonicalFirstGeneratedUnitClass59_ne_zero K
  apply CommonActionStage.unitInclusion_injective
    (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
  simpa [canonicalFirstGeneratedStrictSelmer59] using hzero

/-- The raw complete residue vector of the canonical generating unit. -/
noncomputable def canonicalFirstGeneratedFullOrbitReading827 :
    GaloisIndex59 → ZMod 59 :=
  fullOrbitUnitReading827 (canonicalZeta59_isPrimitive K)
    (canonicalFirstGeneratedRingUnit827 K)

/-- Every raw residue coordinate is exactly the corresponding entry of the
existing kernel-checked 58-by-28 full-orbit matrix. -/
theorem canonicalFirstGeneratedFullOrbitReading827_eq_matrix
    (sigma : GaloisIndex59) :
    canonicalFirstGeneratedFullOrbitReading827 K sigma =
      fullGeneratedMatrix827 sigma DetectorWitness827.firstLedgerNode := by
  exact fullOrbitUnitReading827_generatedUnit_eq
    (canonicalZeta59_isPrimitive K) sigma
    DetectorWitness827.firstLedgerNode

/-- At the identity residue embedding, the raw source reads exactly `48`. -/
theorem canonicalFirstGeneratedFullOrbitReading827_one_eq :
    canonicalFirstGeneratedFullOrbitReading827 K 1 =
      DetectorWitness827.firstLampReading827 :=
  fullOrbitUnitReading827_firstGenerated_one
    (canonicalZeta59_isPrimitive K)

/-- Numerical spelling of the same already-banked identity residue. -/
theorem canonicalFirstGeneratedFullOrbitReading827_one_eq_fortyEight :
    canonicalFirstGeneratedFullOrbitReading827 K 1 = 48 := by
  rw [canonicalFirstGeneratedFullOrbitReading827_one_eq,
    DetectorWitness827.firstLampReading827_eq]

/-- The raw full-orbit vector is nonzero, independently of character
projection. -/
theorem canonicalFirstGeneratedFullOrbitReading827_ne_zero :
    canonicalFirstGeneratedFullOrbitReading827 K ≠ 0 := by
  intro hzero
  have hone := congrFun hzero (1 : GaloisIndex59)
  rw [canonicalFirstGeneratedFullOrbitReading827_one_eq_fortyEight] at hone
  exact (by decide : (48 : ZMod 59) ≠ 0) hone

/-- Exact readback of every Fourier coefficient against the already checked
full-orbit matrix.  No pointwise equality with the odd projected Selmer
class is asserted. -/
theorem canonicalFirstGenerated_fourierCoefficient_eq_matrix
    (eta : GaloisIndex59 →* (ZMod 59)ˣ) :
    fourierCoefficient
        (canonicalFirstGeneratedFullOrbitReading827 K) eta =
      fourierCoefficient
        (fun sigma ↦
          fullGeneratedMatrix827 sigma
            DetectorWitness827.firstLedgerNode) eta := by
  apply congrArg (fun values ↦ fourierCoefficient values eta)
  funext sigma
  exact canonicalFirstGeneratedFullOrbitReading827_eq_matrix K sigma

/-- The existing full-orbit certificate proves that the raw generated-unit
wave has a nonzero even mode `44`. -/
theorem canonicalFirstGenerated_powerFortyFour_fourier_ne_zero :
    fourierCoefficient
        (canonicalFirstGeneratedFullOrbitReading827 K)
        (powerCharacter59 44) ≠ 0 := by
  exact fullOrbitUnitReading827_generatedUnit_fourier_ne_zero_of_even_nontrivial
    (canonicalZeta59_isPrimitive K) (powerCharacter59 44)
      (by decide) (by decide) DetectorWitness827.firstLedgerNode

/-- The same nonvanishing in the repository's canonical name for the
reflected/oriented irregular mode. -/
theorem canonicalFirstGenerated_orientedIrregular_fourier_ne_zero :
    fourierCoefficient
        (canonicalFirstGeneratedFullOrbitReading827 K)
        (orientedPrimalMode827 canonicalTeichmullerCharacter59
          irregularCharacter59) ≠ 0 := by
  rw [orientedPrimalMode827_canonical_irregular]
  exact canonicalFirstGenerated_powerFortyFour_fourier_ne_zero K

end Fermat.FiftyNine.Conservation.CanonicalPrimalSelmerMode827
