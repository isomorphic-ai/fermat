/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The residue Frobenius meaning of the canonical 827 readout

At a tame finite place, the power-residue character is the exponent by
which residue Frobenius scales a Kummer root.  This file proves that claim
inside the universal Kummer algebra over `ZMod 827`, then transports it to
the actual 58-place strict residue wave.

Thus the already constructed canonical mode-44 class readout is identified
with the Fourier transform of genuine residue-Frobenius exponents.  This is
the local Kummer--Artin comparison available from the current dependencies.
It does not construct a ray-class Artin map, a Hilbert class field, or prove
faithfulness of the resulting class character.
-/
import Fermat.FiftyNine.Conservation.CanonicalModeFortyFourClassFactorization827
import Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedger827
import Mathlib.RingTheory.Frobenius

open scoped NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.KummerFrobeniusRead827

open Polynomial
open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.TameSymbol
open Fermat.FiftyNine.Conservation.ActualTameLedger827
open Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
open Fermat.FiftyNine.Conservation.CanonicalModeFortyFourClassFactorization827
open Fermat.FiftyNine.Conservation.CanonicalTameLedger827
open Fermat.FiftyNine.Conservation.CyclotomicTameContext59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827
open Fermat.FiftyNine.Conservation.FermatFactorClassGaugeSeating59
open Fermat.FiftyNine.Conservation.LocalReduction827
open Fermat.FiftyNine.Conservation.OrbitPlace827
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance residueIdealIsMaximal827
    (v : Place K) : v.asIdeal.IsMaximal := v.isMaximal

local instance residueField827 (v : Place K) : Field (Residue K v) :=
  Ideal.Quotient.field v.asIdeal

local instance residueFintype827 (v : Place K) : Fintype (Residue K v) :=
  Fintype.ofFinite _

private theorem contextResidueCharacterAngular_eq_of_place_eq
    {v w : Place K} (h : v = w)
    (hv : v ∉ placesOver59 K) (hw : w ∉ placesOver59 K)
    (a : Kˣ) :
    (context K v hv).residueCharacter
        (Additive.ofMul ((context K v hv).angularComponent a)) =
      (context K w hw).residueCharacter
        (Additive.ofMul ((context K w hw).angularComponent a)) := by
  subst w
  rfl

/-! ## Universal residue Kummer algebra -/

/-- The universal degree-59 Kummer algebra of a nonzero residue `u` at 827. -/
abbrev ResidueKummerAlgebra827 (u : (ZMod Credit.attestationPrime)ˣ) :=
  AdjoinRoot (X ^ 59 - C (u : ZMod Credit.attestationPrime))

local instance residueKummerExpChar827
    (u : (ZMod Credit.attestationPrime)ˣ) :
    ExpChar (ResidueKummerAlgebra827 u) Credit.attestationPrime :=
  expChar_of_injective_ringHom
    (AdjoinRoot.of.injective_of_degree_ne_zero (by
      rw [degree_X_pow_sub_C (by norm_num : 0 < 59)]
      norm_num))
    Credit.attestationPrime

/-- The universal Kummer root in `ZMod 827[T]/(T^59-u)`. -/
noncomputable def residueKummerRoot827
    (u : (ZMod Credit.attestationPrime)ˣ) : ResidueKummerAlgebra827 u :=
  AdjoinRoot.root (X ^ 59 - C (u : ZMod Credit.attestationPrime))

@[simp]
theorem residueKummerRoot827_pow_fiftyNine
    (u : (ZMod Credit.attestationPrime)ˣ) :
    residueKummerRoot827 u ^ 59 =
      algebraMap (ZMod Credit.attestationPrime)
        (ResidueKummerAlgebra827 u) (u : ZMod Credit.attestationPrime) := by
  exact root_X_pow_sub_C_pow 59 (u : ZMod Credit.attestationPrime)

/-- In the universal residue Kummer algebra, literal 827-Frobenius scales
the Kummer root by the fourteenth-power residue symbol. -/
theorem frobenius_residueKummerRoot827
    (u : (ZMod Credit.attestationPrime)ˣ) :
    _root_.frobenius (ResidueKummerAlgebra827 u)
        Credit.attestationPrime (residueKummerRoot827 u) =
      algebraMap (ZMod Credit.attestationPrime)
          (ResidueKummerAlgebra827 u)
          ((u : ZMod Credit.attestationPrime) ^ 14) *
        residueKummerRoot827 u := by
  change residueKummerRoot827 u ^ Credit.attestationPrime = _
  calc
    residueKummerRoot827 u ^ Credit.attestationPrime =
        residueKummerRoot827 u ^ (59 * 14 + 1) := by
      norm_num [Credit.attestationPrime]
    _ = _ := by
      rw [pow_add, pow_one, pow_mul, residueKummerRoot827_pow_fiftyNine]
      rw [map_pow]

/-! ## The actual strict 827 orbit -/

/-- The angular component of a strict Selmer representative in the explicit
`ZMod 827` residue presentation at canonical place coordinate `tau`. -/
noncomputable def strictOrbitAngularComponent827
    (x : StrictCarrier59 K) (tau : GaloisIndex59) :
    (ZMod Credit.attestationPrime)ˣ :=
  (canonicalOrbitTameContext827 (K := K) tau⁻¹).angularComponent
    (strictKummerRepresentative59 K x)

/-- The discrete exponent by which residue Frobenius scales the universal
Kummer root attached to the strict input at each of the 58 places. -/
noncomputable def strictOrbitFrobeniusExponentWave827
    (x : StrictCarrier59 K) : GaloisIndex59 → ZMod 59 :=
  fun tau ↦
    (canonicalOrbitTameContext827 (K := K) tau⁻¹).residueCharacter
      (Additive.ofMul (strictOrbitAngularComponent827 K x tau))

/-- The exponent wave defined through the explicit residue Frobenius model
is exactly the canonical strict residue wave used by the mode-44 readout. -/
theorem strictOrbitFrobeniusExponentWave827_eq_residueWave
    (x : StrictCarrier59 K) :
    strictOrbitFrobeniusExponentWave827 K x =
      strictOrbitResidueWave827 K x := by
  funext tau
  let sigma : GaloisIndex59 := tau⁻¹
  let v := orbitPlace827
    (canonicalZeta59_isPrimitive (K := K)) sigma
  let hv : v ∉ placesOver59 K :=
    orbitPlace827_not_mem_placesOver59 (K := K) sigma
  let ctx := context K v hv
  let explicitCtx := canonicalOrbitTameContext827 (K := K) sigma
  let a := strictKummerRepresentative59 K x
  have htransport := TameSymbol.Context.residueCharacter_map_ringEquiv
    ctx (orbitResidueEquiv827 (K := K) sigma) explicitCtx
    (orbitResidueEquiv827_residueRootUnit (K := K) sigma)
    (ctx.angularComponent a)
  have hangular :
      Units.map (orbitResidueEquiv827 (K := K) sigma).toRingHom
          (ctx.angularComponent a) =
        strictOrbitAngularComponent827 K x tau := by
    change Units.map (orbitResidueEquiv827 (K := K) sigma).toRingHom
        (angularComponent K v a) =
      angularComponent827
        (canonicalZeta59_isPrimitive (K := K)) sigma a
    exact (orbitResidueEquiv827_angularComponent
      (K := K) sigma a).symm
  rw [hangular] at htransport
  change explicitCtx.residueCharacter
      (Additive.ofMul (strictOrbitAngularComponent827 K x tau)) =
    (context K (tameOrbitPlace827 (K := K) tau)
      (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).residueCharacter
        (Additive.ofMul
          ((context K (tameOrbitPlace827 (K := K) tau)
            (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).angularComponent
              a))
  exact htransport.trans
    (contextResidueCharacterAngular_eq_of_place_eq K
      (tameOrbitPlace827_eq_orbitPlace_inv (K := K) tau).symm
      hv (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau) a)

/-- At every actual orbit coordinate, the recorded exponent is literally
the scalar by which 827-Frobenius acts on the universal Kummer root. -/
theorem frobenius_strictOrbitKummerRoot827
    (x : StrictCarrier59 K) (tau : GaloisIndex59) :
    let u := strictOrbitAngularComponent827 K x tau
    _root_.frobenius (ResidueKummerAlgebra827 u)
        Credit.attestationPrime (residueKummerRoot827 u) =
      algebraMap (ZMod Credit.attestationPrime)
          (ResidueKummerAlgebra827 u)
          (((canonicalOrbitTameContext827 (K := K) tau⁻¹).primitiveRoot ^
            (strictOrbitFrobeniusExponentWave827 K x tau).val :
              (ZMod Credit.attestationPrime)ˣ) :
            ZMod Credit.attestationPrime) *
        residueKummerRoot827 u := by
  dsimp only
  rw [frobenius_residueKummerRoot827]
  congr 2
  have hroot :=
    TameSymbol.Context.primitiveRoot_pow_residueCharacter_val
      (canonicalOrbitTameContext827 (K := K) tau⁻¹)
      (strictOrbitAngularComponent827 K x tau)
  have hroot' := congrArg ((↑) : (ZMod Credit.attestationPrime)ˣ →
      ZMod Credit.attestationPrime) hroot.symm
  have htame :
      (canonicalOrbitTameContext827 (K := K) tau⁻¹).tameExponent = 14 := by
    norm_num [TameSymbol.Context.tameExponent, Credit.attestationPrime]
  rw [htame] at hroot'
  calc
    (strictOrbitAngularComponent827 K x tau :
        ZMod Credit.attestationPrime) ^ 14 =
        ↑(strictOrbitAngularComponent827 K x tau ^ 14) := rfl
    _ = ↑((canonicalOrbitTameContext827 (K := K) tau⁻¹).primitiveRoot ^
          (strictOrbitFrobeniusExponentWave827 K x tau).val) := by
      simpa only [strictOrbitFrobeniusExponentWave827] using hroot'

/-! ## Comparison with the descended class readout -/

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- The canonical class readout pulls back to the negative mode-44 Fourier
coefficient of the genuine residue-Frobenius exponent wave. -/
theorem canonicalModeFortyFourClassReadout827_eq_frobeniusFourier
    (x : StrictCarrier59 K) :
    canonicalModeFortyFourClassReadout827 K
        (fermatFactorClassGaugeMap59 (K := K) x) =
      -fourierCoefficient
        (strictOrbitFrobeniusExponentWave827 K x)
        (powerCharacter59 44) := by
  rw [canonicalModeFortyFourClassReadout827_classGaugeMap59]
  rw [strictOrbitNegativeModeFortyFourLinearMap827_apply]
  rw [strictOrbitFrobeniusExponentWave827_eq_residueWave]

/-! ## Axiom audit -/

/--
info: 'Fermat.FiftyNine.Conservation.KummerFrobeniusRead827.frobenius_residueKummerRoot827' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms frobenius_residueKummerRoot827

/--
info: 'Fermat.FiftyNine.Conservation.KummerFrobeniusRead827.strictOrbitFrobeniusExponentWave827_eq_residueWave' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms strictOrbitFrobeniusExponentWave827_eq_residueWave

/--
info: 'Fermat.FiftyNine.Conservation.KummerFrobeniusRead827.frobenius_strictOrbitKummerRoot827' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms frobenius_strictOrbitKummerRoot827

/--
info: 'Fermat.FiftyNine.Conservation.KummerFrobeniusRead827.canonicalModeFortyFourClassReadout827_eq_frobeniusFourier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canonicalModeFortyFourClassReadout827_eq_frobeniusFourier

end Fermat.FiftyNine.Conservation.KummerFrobeniusRead827
