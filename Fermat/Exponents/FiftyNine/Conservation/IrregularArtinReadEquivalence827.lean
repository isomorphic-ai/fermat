/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The faithful local Artin reading on the irregular line

For a genuine `chi = omega^15` strict Selmer class, place covariance makes
the complete 827 Frobenius-exponent wave pure of reflected mode 44.  Hence
there is no Fourier cancellation: the canonical class readout is nonzero
exactly when one orbit exponent is nonzero.  Local Kummer faithfulness then
identifies this with one orbit Kummer--Frobenius automorphism having exact
order 59.

The final theorem descends this equivalence existentially to the actual
irregular class-projector image.  It chooses no section of the class gauge:
surjectivity onto the projector image is used only to obtain an existential
strict eigenspace preimage.

This is the finite local Artin-read side suggested by `7A-ARTIN-READ.md`.
It does not supply the still-missing Poitou--Tate lift or global
Kummer--Artin comparison theorem described there.
-/
import Fermat.Experiments.Conservation.GuardDependsOn
import Fermat.Exponents.FiftyNine.Conservation.IrregularPrimalClassGaugeBridge827
import Fermat.Exponents.FiftyNine.Conservation.LocalKummerFrobeniusFaithfulness827
import Fermat.Exponents.FiftyNine.Conservation.StrictOrbitResidueWavePlaceCovariance827

open Polynomial
open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.IrregularArtinReadEquivalence827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open CanonicalFullOrbitLocalPairing827
open CanonicalIrregularMode827
open CanonicalModeFortyFourClassFactorization827
open CharacterLinePointwiseFaithfulness59
open CyclotomicSelmerClassNaturality59
open CyclotomicSelmerAction59
open DetectorWitness827
open FermatFactorClassGaugeSeating59
open IrregularPrimalClassGaugeBridge827
open KummerFrobeniusRead827
open LocalKummerFrobeniusFactorization827
open LocalKummerFrobeniusFaithfulness827
open ResidueKummerFrobeniusAutomorphism827
open SplitPrimeFourier827
open StrictOrbitKummerFrobeniusAutomorphism827
open StrictOrbitResidueWavePlaceCovariance827
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

private theorem irregularOldPrimal59_nsmul_eq_zero
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    59 • x = 0 := by
  apply Subtype.ext
  exact p_nsmul_eq_zero x.1

noncomputable local instance instIrregularOldPrimal59ModuleZMod :
    Module (ZMod 59)
      (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59) :=
  AddCommGroup.zmodModule (irregularOldPrimal59_nsmul_eq_zero K)

/-! ## Pointwise local faithfulness -/

/-- A zero recorded exponent makes the corresponding local Kummer
Frobenius automorphism the identity.  This is the converse direction to
local exponent faithfulness and follows by checking the universal Kummer
root, which generates its `AdjoinRoot` algebra. -/
theorem strictOrbitKummerFrobeniusAlgEquiv827_eq_one_of_exponent_eq_zero
    (x : StrictCarrier59 K) (tau : GaloisIndex59)
    (hexponent : strictOrbitFrobeniusExponentWave827 K x tau = 0) :
    strictOrbitKummerFrobeniusAlgEquiv827 K x tau = 1 := by
  have hhom :
      (strictOrbitKummerFrobeniusAlgEquiv827 K x tau).toAlgHom =
        (1 : ResidueKummerAlgebra827
          (strictOrbitAngularComponent827 K x tau) ≃ₐ[
            ZMod Credit.attestationPrime]
          ResidueKummerAlgebra827
            (strictOrbitAngularComponent827 K x tau)).toAlgHom := by
    apply AdjoinRoot.algHom_ext
    change strictOrbitKummerFrobeniusAlgEquiv827 K x tau
        (residueKummerRoot827 (strictOrbitAngularComponent827 K x tau)) =
      residueKummerRoot827 (strictOrbitAngularComponent827 K x tau)
    rw [strictOrbitKummerFrobeniusAlgEquiv827_root]
    rw [hexponent]
    simp
  apply AlgEquiv.ext
  intro a
  exact DFunLike.congr_fun hhom a

/-- At one actual orbit place, exponent nonvanishing is exactly full prime
order of the local Kummer--Frobenius automorphism. -/
theorem strictOrbitFrobeniusExponent_ne_zero_iff_orderOf_eq_fiftyNine
    (x : StrictCarrier59 K) (tau : GaloisIndex59) :
    strictOrbitFrobeniusExponentWave827 K x tau ≠ 0 ↔
      orderOf (strictOrbitKummerFrobeniusAlgEquiv827 K x tau) = 59 := by
  constructor
  · exact strictOrbitKummerFrobeniusAlgEquiv827_orderOf_eq_fiftyNine
      K x tau
  · intro horder hexponent
    have hone :=
      strictOrbitKummerFrobeniusAlgEquiv827_eq_one_of_exponent_eq_zero
        K x tau hexponent
    rw [hone] at horder
    norm_num at horder

/-! ## The pure chi=15 wave -/

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- On the genuine irregular eigenspace, the class readout is nonzero
exactly when some one of the 58 actual Frobenius exponents is nonzero.  The
reverse implication is the new no-cancellation consequence of mode purity. -/
theorem canonicalClassReadout_ne_zero_iff_exists_frobeniusExponent_ne_zero
    (x : StrictCarrier59 K)
    (hx : x ∈ characterEigenspace
      (cyclotomicStrictSelmerRepresentation59 K) irregularCharacter59) :
    canonicalModeFortyFourClassReadout827 K
          (fermatFactorClassGaugeMap59 (K := K) x) ≠ 0 ↔
      ∃ tau : GaloisIndex59,
        strictOrbitFrobeniusExponentWave827 K x tau ≠ 0 := by
  constructor
  · intro hreadout
    have hwave : strictOrbitFrobeniusExponentWave827 K x ≠ 0 := by
      intro hwave
      apply hreadout
      rw [canonicalModeFortyFourClassReadout827_eq_frobeniusFourier]
      rw [hwave]
      simp
    exact Function.ne_iff.mp hwave
  · rintro ⟨tau, htau⟩
    rw [canonicalModeFortyFourClassReadout827_eq_frobeniusFourier]
    exact neg_ne_zero.mpr
      (frobeniusFourier_powerFortyFour_ne_zero_of_coordinate_ne_zero
        K x hx tau htau)

/-- The three concrete readings coincide on every genuine irregular
eigenclass: nonzero class readout, a nonzero orbit exponent, and a local
Kummer--Frobenius automorphism of exact order 59. -/
theorem canonicalClassReadout_ne_zero_iff_exists_localFrobenius_order_fiftyNine
    (x : StrictCarrier59 K)
    (hx : x ∈ characterEigenspace
      (cyclotomicStrictSelmerRepresentation59 K) irregularCharacter59) :
    canonicalModeFortyFourClassReadout827 K
          (fermatFactorClassGaugeMap59 (K := K) x) ≠ 0 ↔
      ∃ tau : GaloisIndex59,
        orderOf (strictOrbitKummerFrobeniusAlgEquiv827 K x tau) = 59 := by
  rw [canonicalClassReadout_ne_zero_iff_exists_frobeniusExponent_ne_zero
    K x hx]
  constructor
  · rintro ⟨tau, htau⟩
    exact ⟨tau,
      (strictOrbitFrobeniusExponent_ne_zero_iff_orderOf_eq_fiftyNine
        K x tau).mp htau⟩
  · rintro ⟨tau, htau⟩
    exact ⟨tau,
      (strictOrbitFrobeniusExponent_ne_zero_iff_orderOf_eq_fiftyNine
        K x tau).mpr htau⟩

/-! ## Existential descent to the actual irregular class line -/

/-- Nonvanishing of the canonical readout on the actual irregular class
line is equivalent to the existence of a genuine `chi = omega^15` strict
Selmer preimage with a full-order local Kummer--Frobenius action.

No representative is selected uniformly: the equality of ranges supplies
only the existential preimage needed by this proposition. -/
theorem irregularClassLineReadout_ne_zero_iff_exists_localFrobenius_order_fiftyNine :
    (canonicalModeFortyFourClassReadout827 K).comp
          (irregularClassCharacterLine59 K).subtype ≠ 0 ↔
      ∃ (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
          irregularCharacter59) (tau : GaloisIndex59),
        orderOf (strictOrbitKummerFrobeniusAlgEquiv827 K x.1 tau) = 59 := by
  constructor
  · intro hreadout
    have hexists :
        ∃ q : irregularClassCharacterLine59 K,
          canonicalModeFortyFourClassReadout827 K q.1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hreadout
      ext q
      simpa using h q
    obtain ⟨q, hq⟩ := hexists
    have hqmem : (q : ClassTorsion59 K) ∈
        LinearMap.range (irregularPrimalClassGauge59 K) := by
      rw [irregularPrimalClassGauge59_range_eq_irregularClassCharacterLine59]
      exact q.property
    obtain ⟨x, hx⟩ := hqmem
    have hxreadout :
        canonicalModeFortyFourClassReadout827 K
            (fermatFactorClassGaugeMap59 (K := K) x.1) ≠ 0 := by
      change canonicalModeFortyFourClassReadout827 K
        (irregularPrimalClassGauge59 K x) ≠ 0
      rw [hx]
      exact hq
    obtain ⟨tau, htau⟩ :=
      (canonicalClassReadout_ne_zero_iff_exists_localFrobenius_order_fiftyNine
        K x.1 x.property).mp hxreadout
    exact ⟨x, tau, htau⟩
  · rintro ⟨x, tau, htau⟩
    have hxreadout :=
      (canonicalClassReadout_ne_zero_iff_exists_localFrobenius_order_fiftyNine
        K x.1 x.property).mpr ⟨tau, htau⟩
    intro hzero
    let q : irregularClassCharacterLine59 K :=
      ⟨irregularPrimalClassGauge59 K x, by
        rw [←
          irregularPrimalClassGauge59_range_eq_irregularClassCharacterLine59 K]
        exact ⟨x, rfl⟩⟩
    have hqzero := LinearMap.congr_fun hzero q
    rw [LinearMap.zero_apply, LinearMap.comp_apply] at hqzero
    apply hxreadout
    change canonicalModeFortyFourClassReadout827 K
      (irregularPrimalClassGauge59 K x) = 0
    exact hqzero

/-! ## Axiom and proof-dependency audit -/

/--
info: 'Fermat.FiftyNine.Conservation.IrregularArtinReadEquivalence827.strictOrbitKummerFrobeniusAlgEquiv827_eq_one_of_exponent_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  strictOrbitKummerFrobeniusAlgEquiv827_eq_one_of_exponent_eq_zero

/--
info: 'Fermat.FiftyNine.Conservation.IrregularArtinReadEquivalence827.canonicalClassReadout_ne_zero_iff_exists_localFrobenius_order_fiftyNine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  canonicalClassReadout_ne_zero_iff_exists_localFrobenius_order_fiftyNine

/--
info: 'Fermat.FiftyNine.Conservation.IrregularArtinReadEquivalence827.irregularClassLineReadout_ne_zero_iff_exists_localFrobenius_order_fiftyNine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  irregularClassLineReadout_ne_zero_iff_exists_localFrobenius_order_fiftyNine

#guard_depends_on
  canonicalClassReadout_ne_zero_iff_exists_frobeniusExponent_ne_zero,
  StrictOrbitResidueWavePlaceCovariance827.frobeniusFourier_powerFortyFour_ne_zero_of_coordinate_ne_zero
#guard_depends_on
  canonicalClassReadout_ne_zero_iff_exists_localFrobenius_order_fiftyNine,
  strictOrbitKummerFrobeniusAlgEquiv827_eq_one_of_exponent_eq_zero
#guard_depends_on
  irregularClassLineReadout_ne_zero_iff_exists_localFrobenius_order_fiftyNine,
  IrregularPrimalClassGaugeBridge827.irregularPrimalClassGauge59_range_eq_irregularClassCharacterLine59

end Fermat.FiftyNine.Conservation.IrregularArtinReadEquivalence827
