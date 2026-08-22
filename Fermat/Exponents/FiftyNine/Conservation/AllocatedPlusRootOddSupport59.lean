/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Odd support of the allocated plus root at conductor 59

The genuine cyclotomic class action at `-1` is complex conjugation.  The
allocated minus root is the conjugate of the allocated plus root, while the
proved relation `(7d)` identifies its class with the negative of the plus
class.  Consequently the allocated plus root is unconditionally in the
complete odd (minus) class space.

This is strictly weaker than saying that the root lies in the one selected
`chi = omega^15` character.  The final equivalence below makes the remaining
support problem literal: the selected projector fixes the root exactly when
the complementary part inside the odd space vanishes.

No Takagi theorem, relation `(7a)`, Herbrand theorem, class-group dimension
claim, provider structure, or new axiom is imported or used.
-/
import Fermat.Exponents.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59
import Fermat.Exponents.FiftyNine.Conservation.FermatFactorConjugation59

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

namespace Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.InvolutiveBase
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59
open Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59
open Fermat.FiftyNine.Conservation.FermatFactorClassGaugeSeating59
open Fermat.FiftyNine.Conservation.FermatFactorConjugation59
open Fermat.FiftyNine.Conservation.FermatFactorSelmerSource59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.StateFactorPair
open Fermat.FiftyNine.Conservation.UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

local instance instClassTorsion59ModulePadicInt :
    Module (PadicInt 59) (ClassTorsion59 K) :=
  Module.compHom (ClassTorsion59 K) PadicInt.toZMod

noncomputable local instance instInvertibleTwoPadicInt59 :
    Invertible (2 : PadicInt 59) :=
  (PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr (by norm_num))).invertible

/-! ## The unit correction has no ideal-class obstruction -/

/-- The normalization correction enters the strict Selmer group through the
literal global-unit map. -/
theorem normalizationCorrectionStrictSelmer59_mem_unitRange
    (hZeta : IsPrimitiveRoot zeta 59) :
    normalizationCorrectionStrictSelmer59 hZeta ∈
      Set.range (unitInclusion
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)) := by
  let unitClass : UnitModP (NumberField.RingOfIntegers K) 59 :=
    Additive.ofMul <| QuotientGroup.mk'
      (powMonoidHom 59 :
        (NumberField.RingOfIntegers K)ˣ →*
          (NumberField.RingOfIntegers K)ˣ).range
      (normalizationCorrectionRingUnit59 hZeta)
  refine ⟨unitClass, ?_⟩
  rfl

/-- Hence the actual strict-Selmer class map kills the root-of-unity
normalization correction. -/
theorem strictSelmerClassLinearMap59_normalizationCorrection_eq_zero
    (hZeta : IsPrimitiveRoot zeta 59) :
    strictSelmerClassLinearMap59 K
        (normalizationCorrectionStrictSelmer59 hZeta) = 0 := by
  change fermatFactorClassGaugeMap59 (K := K)
      (normalizationCorrectionStrictSelmer59 hZeta) = 0
  exact (fermatFactorClassGaugeMap59_eq_zero_iff_mem_unitRange _).2
    (normalizationCorrectionStrictSelmer59_mem_unitRange hZeta)

/-! ## Complex conjugation is the `-1` action on the allocated root -/

/-- Naturality of the genuine strict-Selmer class map, specialized to the
cyclotomic automorphism `-1`. -/
theorem strictSelmerClassLinearMap59_cyclotomicNegOne
    (q : SelmerCarrier (NumberField.RingOfIntegers K) K 59) :
    strictSelmerClassLinearMap59 K
        (cyclotomicStrictSelmerRepresentation59 K (-1) q) =
      cyclotomicClassTorsionRepresentation59 K (-1)
        (strictSelmerClassLinearMap59 K q) := by
  apply Subtype.ext
  exact strictSelmerIdealClass59_cyclotomic K (-1) q

/-- The genuine class action at `-1` sends the allocated plus root to the
allocated minus root.  The normalization correction disappears because it
is a global unit, rather than by a supplied class relation. -/
theorem cyclotomicNegOne_allocatedPlusRoot_eq_allocatedMinusRoot
    (pair : StateLinkedIdealPair hZeta S hz) :
    cyclotomicClassTorsionRepresentation59 K (-1)
        (allocatedRootClassPTorsion pair.ledger 0) =
      allocatedRootClassPTorsion pair.ledger 1 := by
  have hplus :
      strictSelmerClassLinearMap59 K (fermatPlusStrictSelmer59 pair) =
        allocatedRootClassPTorsion pair.ledger 0 := by
    apply Subtype.ext
    exact fermatPlusStrictSelmer59_idealClass pair
  have hminus :
      strictSelmerClassLinearMap59 K (fermatMinusStrictSelmer59 pair) =
        allocatedRootClassPTorsion pair.ledger 1 := by
    apply Subtype.ext
    exact fermatMinusStrictSelmer59_idealClass pair
  have h := congrArg (strictSelmerClassLinearMap59 K)
    (fermatMinusStrictSelmer59_eq_correction_add_conj pair)
  rw [map_add,
    strictSelmerClassLinearMap59_normalizationCorrection_eq_zero,
    zero_add, strictSelmerClassLinearMap59_cyclotomicNegOne,
    hplus, hminus] at h
  exact h.symm

/-- Relation `(7d)` says that the allocated minus root is the negative of
the allocated plus root in the actual 59-torsion class carrier. -/
theorem allocatedMinusRoot_eq_neg_allocatedPlusRoot
    (pair : StateLinkedIdealPair hZeta S hz) :
    allocatedRootClassPTorsion pair.ledger 1 =
      -allocatedRootClassPTorsion pair.ledger 0 := by
  apply Subtype.ext
  exact eq_neg_of_add_eq_zero_right
    (Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.vandiverSevenD
      pair)

/-- The first unconditional character-support theorem: the allocated plus
root is anti-invariant under complex conjugation, hence belongs to the full
odd class space. -/
theorem cyclotomicNegOne_allocatedPlusRoot_eq_neg
    (pair : StateLinkedIdealPair hZeta S hz) :
    cyclotomicClassTorsionRepresentation59 K (-1)
        (allocatedRootClassPTorsion pair.ledger 0) =
      -allocatedRootClassPTorsion pair.ledger 0 := by
  rw [cyclotomicNegOne_allocatedPlusRoot_eq_allocatedMinusRoot,
    allocatedMinusRoot_eq_neg_allocatedPlusRoot]

/-! ## The complete odd projector and the exact chi-complement boundary -/

/-- The genuine minus projector `(1 - j) / 2` on class-group 59-torsion,
where `j` is cyclotomic complex conjugation. -/
noncomputable def cyclotomicClassMinusProjector59 :
    ClassTorsion59 K →ₗ[PadicInt 59] ClassTorsion59 K :=
  (cyclotomicClassTorsionRepresentation59 K).asAlgebraHom
    (minusProjector (O := PadicInt 59) (-1 : GaloisIndex59))

/-- Any class on which complex conjugation acts as `-1` is fixed by the
complete odd projector. -/
theorem cyclotomicClassMinusProjector59_eq_self_of_negOne
    (c : ClassTorsion59 K)
    (hodd : cyclotomicClassTorsionRepresentation59 K (-1) c = -c) :
    cyclotomicClassMinusProjector59 (K := K) c = c := by
  change (cyclotomicClassTorsionRepresentation59 K).asAlgebraHom
      (minusProjector (O := PadicInt 59) (-1 : GaloisIndex59)) c = c
  rw [minusProjector, map_smul, map_sub, map_one]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
  rw [show
      (cyclotomicClassTorsionRepresentation59 K).asAlgebraHom
          (conjugationElement (O := PadicInt 59) (-1 : GaloisIndex59)) c =
        cyclotomicClassTorsionRepresentation59 K (-1) c by
      rw [conjugationElement, Representation.asAlgebraHom_single, one_smul]]
  change PadicInt.toZMod (⅟(2 : PadicInt 59)) •
      (c - cyclotomicClassTorsionRepresentation59 K (-1) c) = c
  rw [hodd, sub_neg_eq_add]
  have hhalf_mul :
      PadicInt.toZMod (⅟(2 : PadicInt 59)) * (2 : ZMod 59) = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg PadicInt.toZMod
        (invOf_mul_self (2 : PadicInt 59))
  rw [← two_smul (ZMod 59) c, ← mul_smul, hhalf_mul, one_smul]

/-- In particular the actual allocated plus root is fixed by the complete
odd projector, with no character-allocation premise. -/
theorem cyclotomicClassMinusProjector59_allocatedPlusRoot
    (pair : StateLinkedIdealPair hZeta S hz) :
    cyclotomicClassMinusProjector59 (K := K)
        (allocatedRootClassPTorsion pair.ledger 0) =
      allocatedRootClassPTorsion pair.ledger 0 :=
  cyclotomicClassMinusProjector59_eq_self_of_negOne _
    (cyclotomicNegOne_allocatedPlusRoot_eq_neg pair)

/-- The W7 class gauge itself is odd.  This is the form consumed by the
pointwise Artin-readout route: the gauge is twice the allocated plus root,
so the genuine `-1` class action negates it as well. -/
theorem cyclotomicNegOne_selectedClassGauge59_eq_neg
    (pair : StateLinkedIdealPair hZeta S hz) :
    cyclotomicClassTorsionRepresentation59 K (-1)
        (selectedClassGauge59 pair) =
      -selectedClassGauge59 pair := by
  rw [selectedClassGauge59_eq_plusRoot_add_plusRoot, map_add,
    cyclotomicNegOne_allocatedPlusRoot_eq_neg]
  rw [neg_add]

/-- Consequently the actual W7 class gauge is fixed by the complete odd
projector, without any chi=15 seating premise. -/
theorem cyclotomicClassMinusProjector59_selectedClassGauge59
    (pair : StateLinkedIdealPair hZeta S hz) :
    cyclotomicClassMinusProjector59 (K := K)
        (selectedClassGauge59 pair) = selectedClassGauge59 pair :=
  cyclotomicClassMinusProjector59_eq_self_of_negOne _
    (cyclotomicNegOne_selectedClassGauge59_eq_neg pair)

/-- The part of the full odd class space not retained by the selected
`chi = omega^15` projector.  This is a derived endomorphism, not supplied
data. -/
noncomputable def cyclotomicClassIrregularComplement59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] :
    ClassTorsion59 K →ₗ[PadicInt 59] ClassTorsion59 K :=
  cyclotomicClassMinusProjector59 (K := K) -
    cyclotomicClassProjector59 K irregularCharacter59

/-- The unconditional decomposition of the allocated plus root into its
selected chi component and its remaining odd support. -/
theorem allocatedPlusRoot_eq_irregularProjection_add_complement
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    allocatedRootClassPTorsion pair.ledger 0 =
      cyclotomicClassProjector59 K irregularCharacter59
          (allocatedRootClassPTorsion pair.ledger 0) +
        cyclotomicClassIrregularComplement59 (K := K)
          (allocatedRootClassPTorsion pair.ledger 0) := by
  rw [cyclotomicClassIrregularComplement59, LinearMap.sub_apply,
    cyclotomicClassMinusProjector59_allocatedPlusRoot]
  abel

/-- Exact obstruction to the requested chi=15 seating: the selected
projector fixes the plus root if and only if its complementary odd support
vanishes.  A Herbrand/Stickelberger support theorem would discharge exactly
the right side; `(7d)` and plus-class nondivisibility have already done all
the work needed to reach it. -/
theorem allocatedPlusRoot_irregularProjector_fixed_iff_complement_eq_zero
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    cyclotomicClassProjector59 K irregularCharacter59
        (allocatedRootClassPTorsion pair.ledger 0) =
          allocatedRootClassPTorsion pair.ledger 0 ↔
      cyclotomicClassIrregularComplement59 (K := K)
          (allocatedRootClassPTorsion pair.ledger 0) = 0 := by
  rw [cyclotomicClassIrregularComplement59, LinearMap.sub_apply,
    cyclotomicClassMinusProjector59_allocatedPlusRoot]
  exact eq_comm.trans sub_eq_zero.symm

/-- The same exact chi=15 obstruction, now stated directly on the W7 class
gauge: all even support has been removed, and the only remaining question is
whether its complementary odd component vanishes. -/
theorem selectedClassGauge59_irregularProjector_fixed_iff_complement_eq_zero
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    cyclotomicClassProjector59 K irregularCharacter59
        (selectedClassGauge59 pair) = selectedClassGauge59 pair ↔
      cyclotomicClassIrregularComplement59 (K := K)
          (selectedClassGauge59 pair) = 0 := by
  rw [cyclotomicClassIrregularComplement59, LinearMap.sub_apply,
    cyclotomicClassMinusProjector59_selectedClassGauge59]
  exact eq_comm.trans sub_eq_zero.symm

end Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59
