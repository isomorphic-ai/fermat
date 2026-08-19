/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Local faithfulness of the 827 Kummer--Frobenius action

The residue Frobenius automorphism has order dividing `59` for every
nonzero Kummer radicand.  Here we prove the complementary statement needed
for an actual local detector: if its recorded residue exponent is nonzero,
then the automorphism is nontrivial and consequently has exact order `59`.

Thus a nonzero canonical mode-44 reading forces at least one of the 58
genuine local Kummer algebras to carry a Frobenius action of exact order
`59`.  This is local faithfulness only.  It does not assert that the class
readout is globally faithful or construct a ray-class Artin map.
-/
import Fermat.FiftyNine.Conservation.StrictOrbitKummerFrobeniusAutomorphism827
import Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59

open Polynomial
open scoped NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFaithfulness827

open Credit
open Fermat.Conservation
open Fermat.Conservation.TameSymbol
open CanonicalFullOrbitLocalPairing827
open CanonicalModeFortyFourClassFactorization827
open CanonicalTameLedger827
open CharacterLinePointwiseFaithfulness59
open CyclotomicTameContext59
open DetectorWitness827
open FermatFactorClassGaugeSeating59
open KummerFrobeniusRead827
open ResidueKummerFrobeniusAutomorphism827
open SplitPrimeFourier827
open StrictOrbitKummerFrobeniusAutomorphism827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- The universal Kummer root is a unit: its 59th power is the image of
the unit radicand.  This lets us read an automorphism's scalar multiplier
back from its action on the root without assuming the Kummer polynomial is
irreducible. -/
theorem residueKummerRoot827_isUnit
    (u : (ZMod Credit.attestationPrime)ˣ) :
    IsUnit (residueKummerRoot827 u) := by
  rw [← isUnit_pow_iff (by norm_num : 59 ≠ 0)]
  rw [residueKummerRoot827_pow_fiftyNine]
  exact u.isUnit.map
    (algebraMap (ZMod Credit.attestationPrime)
      (ResidueKummerAlgebra827 u))

/-- A nontrivial Frobenius multiplier gives a nonidentity automorphism of
the universal Kummer algebra. -/
theorem residueKummerFrobeniusAlgEquiv827_ne_one_of_multiplier_ne_one
    (u : (ZMod Credit.attestationPrime)ˣ)
    (hmultiplier : (u : ZMod Credit.attestationPrime) ^ 14 ≠ 1) :
    residueKummerFrobeniusAlgEquiv827 u ≠ 1 := by
  intro hequiv
  have hroot := congrArg
    (fun e : ResidueKummerAlgebra827 u ≃ₐ[ZMod Credit.attestationPrime]
        ResidueKummerAlgebra827 u ↦ e (residueKummerRoot827 u)) hequiv
  rw [residueKummerFrobeniusAlgEquiv827_root] at hroot
  change algebraMap (ZMod Credit.attestationPrime)
      (ResidueKummerAlgebra827 u)
        ((u : ZMod Credit.attestationPrime) ^ 14) *
      residueKummerRoot827 u = residueKummerRoot827 u at hroot
  have hmap :
      algebraMap (ZMod Credit.attestationPrime)
          (ResidueKummerAlgebra827 u)
          ((u : ZMod Credit.attestationPrime) ^ 14) = 1 := by
    apply (residueKummerRoot827_isUnit u).mul_right_cancel
    simpa only [one_mul] using hroot
  apply hmultiplier
  have hdegree :
      (X ^ 59 - C (u : ZMod Credit.attestationPrime)).degree ≠ 0 := by
    rw [degree_X_pow_sub_C (by norm_num : 0 < 59)]
    norm_num
  apply AdjoinRoot.of.injective_of_degree_ne_zero hdegree
  simpa using hmap

/-- A nonzero stored exponent makes the fourteenth-power residue multiplier
nontrivial.  This is exactly the finite-logarithm faithfulness supplied by
the selected primitive 59th root in `ZMod 827`. -/
theorem strictOrbitFrobeniusMultiplier827_ne_one_of_exponent_ne_zero
    (x : StrictCarrier59 K) (tau : GaloisIndex59)
    (hexponent : strictOrbitFrobeniusExponentWave827 K x tau ≠ 0) :
    (strictOrbitAngularComponent827 K x tau :
        ZMod Credit.attestationPrime) ^ 14 ≠ 1 := by
  let ctx := canonicalOrbitTameContext827 (K := K) tau⁻¹
  let u := strictOrbitAngularComponent827 K x tau
  let e := strictOrbitFrobeniusExponentWave827 K x tau
  have hcoordinate :=
    Fermat.Conservation.TameSymbol.Context.primitiveRoot_pow_residueCharacter_val
      ctx u
  have htame : ctx.tameExponent = 14 := by
    norm_num [TameSymbol.Context.tameExponent, Credit.attestationPrime]
  rw [htame] at hcoordinate
  change e ≠ 0 at hexponent
  intro hmultiplier
  have hmultiplierUnits : u ^ 14 = 1 := by
    apply Units.ext
    simpa using hmultiplier
  have hroot : ctx.primitiveRoot ^ e.val = 1 := by
    exact hcoordinate.trans hmultiplierUnits
  have hdvd : 59 ∣ e.val :=
    (ctx.primitiveRoot_spec.pow_eq_one_iff_dvd e.val).mp hroot
  exact (Nat.not_dvd_of_pos_of_lt
    (Nat.pos_of_ne_zero ((ZMod.val_eq_zero e).not.mpr hexponent)) e.val_lt)
    hdvd

/-- At an actual orbit coordinate, a nonzero Frobenius exponent produces a
nonidentity local Kummer automorphism. -/
theorem strictOrbitKummerFrobeniusAlgEquiv827_ne_one_of_exponent_ne_zero
    (x : StrictCarrier59 K) (tau : GaloisIndex59)
    (hexponent : strictOrbitFrobeniusExponentWave827 K x tau ≠ 0) :
    strictOrbitKummerFrobeniusAlgEquiv827 K x tau ≠ 1 := by
  exact residueKummerFrobeniusAlgEquiv827_ne_one_of_multiplier_ne_one
    (strictOrbitAngularComponent827 K x tau)
    (strictOrbitFrobeniusMultiplier827_ne_one_of_exponent_ne_zero
      K x tau hexponent)

/-- The nontrivial local action has exact prime order `59`, not merely order
dividing `59`. -/
theorem strictOrbitKummerFrobeniusAlgEquiv827_orderOf_eq_fiftyNine
    (x : StrictCarrier59 K) (tau : GaloisIndex59)
    (hexponent : strictOrbitFrobeniusExponentWave827 K x tau ≠ 0) :
    orderOf (strictOrbitKummerFrobeniusAlgEquiv827 K x tau) = 59 := by
  exact orderOf_eq_prime
    (strictOrbitKummerFrobeniusAlgEquiv827_pow_fiftyNine K x tau)
    (strictOrbitKummerFrobeniusAlgEquiv827_ne_one_of_exponent_ne_zero
      K x tau hexponent)

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- A nonzero canonical class readout cannot come from a completely trivial
58-place Frobenius action: one genuine local Kummer automorphism has exact
order `59`. -/
theorem exists_strictOrbitKummerFrobenius_orderOf_eq_fiftyNine_of_readout_ne_zero
    (x : StrictCarrier59 K)
    (hreadout :
      canonicalModeFortyFourClassReadout827 K
          (fermatFactorClassGaugeMap59 (K := K) x) ≠ 0) :
    ∃ tau : GaloisIndex59,
      orderOf (strictOrbitKummerFrobeniusAlgEquiv827 K x tau) = 59 := by
  have hwave : strictOrbitFrobeniusExponentWave827 K x ≠ 0 := by
    intro hwave
    apply hreadout
    rw [canonicalModeFortyFourClassReadout827_eq_frobeniusFourier]
    rw [hwave]
    simp
  obtain ⟨tau, htau⟩ := Function.ne_iff.mp hwave
  exact ⟨tau,
    strictOrbitKummerFrobeniusAlgEquiv827_orderOf_eq_fiftyNine
      K x tau htau⟩

/-- Nonvanishing on the actual irregular class line has a concrete local
Galois witness.  A class in that line is lifted through the genuine
surjective strict-Selmer class gauge, and one of its 58 residue Kummer
Frobenius automorphisms has exact order `59`.

The witness is deliberately existential: no class-group section or selected
Selmer representative is installed. -/
theorem exists_classGaugePreimage_with_localFrobenius_order_fiftyNine
    (hreadout :
      (canonicalModeFortyFourClassReadout827 K).comp
          (irregularClassCharacterLine59 K).subtype ≠ 0) :
    ∃ (x : StrictCarrier59 K) (tau : GaloisIndex59),
      fermatFactorClassGaugeMap59 (K := K) x ∈
          irregularClassCharacterLine59 K ∧
      orderOf (strictOrbitKummerFrobeniusAlgEquiv827 K x tau) = 59 := by
  have hexists :
      ∃ q : irregularClassCharacterLine59 K,
        canonicalModeFortyFourClassReadout827 K q.1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hreadout
    ext q
    simpa using h q
  obtain ⟨q, hq⟩ := hexists
  obtain ⟨x, hx⟩ :=
    fermatFactorClassGaugeMap59_surjective (K := K) q.1
  have hlocal :
      canonicalModeFortyFourClassReadout827 K
          (fermatFactorClassGaugeMap59 (K := K) x) ≠ 0 := by
    rw [hx]
    exact hq
  obtain ⟨tau, htau⟩ :=
    exists_strictOrbitKummerFrobenius_orderOf_eq_fiftyNine_of_readout_ne_zero
      K x hlocal
  exact ⟨x, tau, hx.symm ▸ q.property, htau⟩

/-! ## Axiom audit -/

/--
info: 'Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFaithfulness827.strictOrbitKummerFrobeniusAlgEquiv827_orderOf_eq_fiftyNine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  strictOrbitKummerFrobeniusAlgEquiv827_orderOf_eq_fiftyNine

/--
info: 'Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFaithfulness827.exists_strictOrbitKummerFrobenius_orderOf_eq_fiftyNine_of_readout_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  exists_strictOrbitKummerFrobenius_orderOf_eq_fiftyNine_of_readout_ne_zero

/--
info: 'Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFaithfulness827.exists_classGaugePreimage_with_localFrobenius_order_fiftyNine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  exists_classGaugePreimage_with_localFrobenius_order_fiftyNine

end Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFaithfulness827
