/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The canonical p=59 irregular character mode at 827

The generic tame-orbit nonvanishing theorem asks that its reduced reflected
character be even and nontrivial.  In the actual `(59,44)` irregular channel,
neither property is additional arithmetic data.

This module constructs the genuine Teichmuller character

`omega : (ZMod 59)^x -> (PadicInt 59)^x`

through Mathlib's p-typical Witt vectors and their proved comparison with the
p-adic integers.  Its reduction is the identity character.  The class-group
character associated to the irregular index `44` is

`chi = omega^(1 - 44) = omega^15`,

so reflection gives `omega * chi^-1 = omega^44`.  Lean computes its reduction
as `powerCharacter59 44`, and kernel checks both parity and nontriviality.  The
final theorems therefore specialize the fixed-root tame-orbit detector and
its conditional wild-reading chain without `heven` or `hne` premises.  The
globally `zeta`-normalized weighted ledger is treated separately in
`CanonicalGlobalTameLedgerIrregular827`.
-/
import Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.Teichmuller

open scoped BigOperators NumberField

noncomputable section

set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.CanonicalIrregularMode827

open Fermat.Conservation
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.LocalReduction827
open Fermat.FiftyNine.Conservation.ActualTameLedger827
open Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

/-- The honest Teichmuller lift from `(ZMod 59)^x` to `PadicInt 59` units,
constructed through p-typical Witt vectors. -/
noncomputable def canonicalTeichmullerCharacter59 :
    InvolutiveBase.Character (PadicInt 59) GaloisIndex59 :=
  (Units.map (WittVector.toPadicInt 59).toMonoidHom).comp
    (Units.map (WittVector.teichmuller 59))

private theorem padicToZMod_comp_wittToPadic59 :
    (PadicInt.toZMod : PadicInt 59 →+* ZMod 59).comp
        (WittVector.toPadicInt 59) =
      WittVector.constantCoeff := by
  rw [show (PadicInt.toZMod : PadicInt 59 →+* ZMod 59) =
      PadicInt.toZModPow 1 by
    apply ZMod.ringHom_eq_of_ker_eq
    rw [PadicInt.ker_toZMod, PadicInt.ker_toZModPow, pow_one,
      PadicInt.maximalIdeal_eq_span_p]]
  rw [WittVector.toPadicInt, PadicInt.lift_spec]
  ext x
  change (TruncatedWittVector.zmodEquivTrunc 59 1).symm
      ((WittVector.truncate 1) x) = x.coeff 0
  apply (TruncatedWittVector.zmodEquivTrunc 59 1).injective
  simp only [RingEquiv.apply_symm_apply]
  have hcoeff (a : ZMod 59) :
      TruncatedWittVector.coeff (p := 59) (R := ZMod 59) (n := 1)
        ⟨0, by decide⟩ ((TruncatedWittVector.zmodEquivTrunc 59 1) a) = a := by
    rw [TruncatedWittVector.zmodEquivTrunc_apply]
    change TruncatedWittVector.coeff _
      ((a.val : ℕ) : TruncatedWittVector 59 1 (ZMod 59)) = a
    rw [show TruncatedWittVector.coeff (p := 59) (R := ZMod 59) (n := 1)
        ⟨0, by decide⟩
        ((a.val : ℕ) : TruncatedWittVector 59 1 (ZMod 59)) =
        (a.val : ZMod 59) by
      change (WittVector.truncateFun 1
        (a.val : WittVector 59 (ZMod 59))).coeff _ = _
      rw [WittVector.coeff_truncateFun]
      change WittVector.constantCoeff
        (a.val : WittVector 59 (ZMod 59)) = _
      rw [map_natCast]]
    exact ZMod.natCast_zmod_val a
  ext i
  fin_cases i
  rw [WittVector.coeff_truncate]
  exact (hcoeff (x.coeff 0)).symm

/-- Reduction of the canonical Teichmuller lift returns the original
residue-field unit. -/
theorem canonicalTeichmullerCharacter59_reduction_apply
    (sigma : GaloisIndex59) :
    reducedCharacter59 canonicalTeichmullerCharacter59 sigma = sigma := by
  apply Units.ext
  change PadicInt.toZMod
      (WittVector.toPadicInt 59
        (WittVector.teichmuller 59 (sigma : ZMod 59))) =
    (sigma : ZMod 59)
  have h := DFunLike.congr_fun padicToZMod_comp_wittToPadic59
    (WittVector.teichmuller 59 (sigma : ZMod 59))
  change PadicInt.toZMod
      (WittVector.toPadicInt 59
        (WittVector.teichmuller 59 (sigma : ZMod 59))) =
    WittVector.constantCoeff
      (WittVector.teichmuller 59 (sigma : ZMod 59)) at h
  simpa using h

/-- The canonical Teichmuller character reduces to the first power
character. -/
theorem reducedCharacter59_canonicalTeichmullerCharacter59 :
    reducedCharacter59 canonicalTeichmullerCharacter59 =
      powerCharacter59 1 := by
  apply MonoidHom.ext
  intro sigma
  rw [canonicalTeichmullerCharacter59_reduction_apply]
  change sigma = sigma ^ (1 : ZMod 58).val
  have hone : (1 : ZMod 58).val = 1 := by decide
  rw [hone, pow_one]

/-- Reduction is multiplicative on powers of p-adic characters. -/
theorem reducedCharacter59_pow
    {Delta : Type*} [CommGroup Delta]
    (eta : InvolutiveBase.Character (PadicInt 59) Delta) (n : ℕ) :
    reducedCharacter59 (eta ^ n) = reducedCharacter59 eta ^ n := by
  ext delta
  simp [reducedCharacter59]

/-- Reduction commutes with the reflected-character construction. -/
theorem reducedCharacter59_reflectedCharacter
    {Delta : Type*} [CommGroup Delta]
    (omega chi : InvolutiveBase.Character (PadicInt 59) Delta) :
    reducedCharacter59 (InvolutiveBase.reflectedCharacter omega chi) =
      reducedCharacter59 omega * (reducedCharacter59 chi)⁻¹ := by
  ext delta
  simp [reducedCharacter59, InvolutiveBase.reflectedCharacter]

/-- The p-adic character `omega^(1-44) = omega^15` indexing the unique
irregular channel `(59,44)`. -/
noncomputable def irregularCharacter59 :
    InvolutiveBase.Character (PadicInt 59) GaloisIndex59 :=
  canonicalTeichmullerCharacter59 ^ 15

/-- The canonical irregular character reduces to the fifteenth power
character. -/
theorem reducedCharacter59_irregularCharacter59 :
    reducedCharacter59 irregularCharacter59 = powerCharacter59 15 := by
  rw [irregularCharacter59, reducedCharacter59_pow,
    reducedCharacter59_canonicalTeichmullerCharacter59]
  decide +kernel +revert

/-- In the unique irregular channel, reflection seats the primal tame wave in
exactly the even power mode `44`. -/
theorem orientedPrimalMode827_canonical_irregular :
    orientedPrimalMode827 canonicalTeichmullerCharacter59
      irregularCharacter59 = powerCharacter59 44 := by
  rw [orientedPrimalMode827, reducedCharacter59_reflectedCharacter,
    reducedCharacter59_canonicalTeichmullerCharacter59,
    reducedCharacter59_irregularCharacter59]
  decide +kernel +revert

/-- The canonical reflected irregular mode is even. -/
theorem orientedPrimalMode827_canonical_irregular_even :
    orientedPrimalMode827 canonicalTeichmullerCharacter59
      irregularCharacter59 (-1) = 1 := by
  rw [orientedPrimalMode827_canonical_irregular]
  decide +kernel +revert

/-- The canonical reflected irregular mode is nontrivial. -/
theorem orientedPrimalMode827_canonical_irregular_ne_one :
    orientedPrimalMode827 canonicalTeichmullerCharacter59
      irregularCharacter59 ≠ 1 := by
  rw [orientedPrimalMode827_canonical_irregular]
  decide +kernel +revert

universe uK

variable {K : Type uK} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The actual inverse-oriented primal wave is unconditionally nonzero in
p=59's canonical irregular character seat. -/
theorem inverseOrientedPrimalUnitWave827_canonical_irregular_ne_zero
    (selected : GaloisIndex59) :
    inverseOrientedPrimalUnitWave827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 selected ≠ 0 := by
  exact inverseOrientedPrimalUnitWave827_ne_zero_of_even_nontrivial
    (K := K) canonicalTeichmullerCharacter59 irregularCharacter59
    orientedPrimalMode827_canonical_irregular_even
    orientedPrimalMode827_canonical_irregular_ne_one selected

/-- The selected honest local product is nonzero in the canonical irregular
character seat, with no parity or nontriviality premise. -/
theorem selectedProduct_actualTameOrbit827_canonical_irregular_ne_zero
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) canonicalTeichmullerCharacter59
        irregularCharacter59)
    (selected : GaloisIndex59) :
    inverseOrientedPrimalUnitWave827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 selected *
      projectedLocalizationVector827 (rhoQ827 (K := K))
        canonicalTeichmullerCharacter59 irregularCharacter59
        (tameOrbitBasePlace827 (K := K)) lift.source selected ≠ 0 := by
  exact selectedProduct_actualTameOrbit827_ne_zero
    (K := K) canonicalTeichmullerCharacter59 irregularCharacter59
    orientedPrimalMode827_canonical_irregular_even
    orientedPrimalMode827_canonical_irregular_ne_one lift selected

/-- The unweighted fixed-root 827 detector total is nonzero in the canonical
irregular character seat. -/
theorem sum_actualTameOrbitValue827_canonical_irregular_ne_zero
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) canonicalTeichmullerCharacter59
        irregularCharacter59) :
    (∑ tau : GaloisIndex59,
      actualTameOrbitValue827 (K := K) canonicalTeichmullerCharacter59
        irregularCharacter59 lift tau) ≠ 0 := by
  exact sum_actualTameOrbitValue827_ne_zero
    (K := K) canonicalTeichmullerCharacter59 irregularCharacter59
    orientedPrimalMode827_canonical_irregular_even
    orientedPrimalMode827_canonical_irregular_ne_one lift 1

/-- A supplied unweighted fixed-root balance equation forces nonvanishing of
its wild scalar in the canonical irregular character seat.  It is not the
globally normalized reciprocity equation. -/
theorem wild_ne_zero_of_actualTameOrbitReciprocity827_canonical_irregular
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) canonicalTeichmullerCharacter59
        irregularCharacter59)
    (wildReading : ZMod 59)
    (reciprocity : wildReading + ∑ tau : GaloisIndex59,
      actualTameOrbitValue827 (K := K) canonicalTeichmullerCharacter59
        irregularCharacter59 lift tau = 0) :
    wildReading ≠ 0 := by
  exact wild_ne_zero_of_actualTameOrbitReciprocity827
    (K := K) canonicalTeichmullerCharacter59 irregularCharacter59
    orientedPrimalMode827_canonical_irregular_even
    orientedPrimalMode827_canonical_irregular_ne_one lift 1
    wildReading reciprocity

/-- The unweighted fixed-root height-one detector total is nonzero in the
canonical irregular seat.  A genuine reflected lift is the only premise. -/
theorem actualTameLedger827_canonical_irregular_sum_ne_zero
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) canonicalTeichmullerCharacter59
        irregularCharacter59) :
    (actualTameLedger827 (K := K) canonicalTeichmullerCharacter59
      irregularCharacter59 lift).sum (fun _ value ↦ value) ≠ 0 := by
  exact actualTameLedger827_sum_ne_zero
    (K := K) canonicalTeichmullerCharacter59 irregularCharacter59
    orientedPrimalMode827_canonical_irregular_even
    orientedPrimalMode827_canonical_irregular_ne_one lift 1

/-- The fixed-root finite-support detector ledger itself is nonzero in the
canonical irregular seat. -/
theorem actualTameLedger827_canonical_irregular_ne_zero
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) canonicalTeichmullerCharacter59
        irregularCharacter59) :
    actualTameLedger827 (K := K) canonicalTeichmullerCharacter59
      irregularCharacter59 lift ≠ 0 := by
  exact actualTameLedger827_ne_zero
    (K := K) canonicalTeichmullerCharacter59 irregularCharacter59
    orientedPrimalMode827_canonical_irregular_even
    orientedPrimalMode827_canonical_irregular_ne_one lift 1

/-- A supplied unweighted balance equation on the fixed-root height-one
ledger forces its wild scalar to be nonzero in the canonical irregular
seat. -/
theorem wild_ne_zero_of_actualTameLedgerReciprocity827_canonical_irregular
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) canonicalTeichmullerCharacter59
        irregularCharacter59)
    (wildReading : ZMod 59)
    (reciprocity : wildReading +
      (actualTameLedger827 (K := K) canonicalTeichmullerCharacter59
        irregularCharacter59 lift).sum (fun _ value ↦ value) = 0) :
    wildReading ≠ 0 := by
  exact wild_ne_zero_of_actualTameLedgerReciprocity827
    (K := K) canonicalTeichmullerCharacter59 irregularCharacter59
    orientedPrimalMode827_canonical_irregular_even
    orientedPrimalMode827_canonical_irregular_ne_one lift 1
    wildReading reciprocity

end Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
