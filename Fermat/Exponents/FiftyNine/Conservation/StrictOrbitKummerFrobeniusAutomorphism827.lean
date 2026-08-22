/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The actual 58-place Kummer Frobenius automorphisms

Each coordinate of the strict residue wave now determines a genuine
automorphism of its universal residue Kummer algebra.  This file transports
the explicit inverse and order-dividing-59 results to all 58 actual places
above 827, and proves that the stored Frobenius exponent is literally the
power of the canonical residue root multiplying the Kummer root.

This remains local residue arithmetic.  It does not construct a global
ray-class Artin map or a Hilbert class field.
-/
import Fermat.Exponents.FiftyNine.Conservation.ResidueKummerFrobeniusAutomorphism827

open scoped NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.StrictOrbitKummerFrobeniusAutomorphism827

open Credit
open CanonicalFullOrbitLocalPairing827
open CanonicalTameLedger827
open CyclotomicTameContext59
open DetectorWitness827
open FermatFactorClassGaugeSeating59
open KummerFrobeniusRead827
open LocalKummerFrobeniusFactorization827
open ResidueKummerFrobeniusAutomorphism827
open SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- The actual residue Kummer Frobenius automorphism attached to one strict
Selmer input and one of the 58 canonical places above 827. -/
noncomputable def strictOrbitKummerFrobeniusAlgEquiv827
    (x : StrictCarrier59 K) (tau : GaloisIndex59) :
    ResidueKummerAlgebra827 (strictOrbitAngularComponent827 K x tau) ≃ₐ[
        ZMod Credit.attestationPrime]
      ResidueKummerAlgebra827 (strictOrbitAngularComponent827 K x tau) :=
  residueKummerFrobeniusAlgEquiv827
    (strictOrbitAngularComponent827 K x tau)

/-- The actual orbit Frobenius automorphism scales its Kummer root by the
canonical residue root raised to the recorded Frobenius exponent. -/
theorem strictOrbitKummerFrobeniusAlgEquiv827_root
    (x : StrictCarrier59 K) (tau : GaloisIndex59) :
    let u := strictOrbitAngularComponent827 K x tau
    strictOrbitKummerFrobeniusAlgEquiv827 K x tau
        (residueKummerRoot827 u) =
      algebraMap (ZMod Credit.attestationPrime)
          (ResidueKummerAlgebra827 u)
          (((canonicalOrbitTameContext827 (K := K) tau⁻¹).primitiveRoot ^
            (strictOrbitFrobeniusExponentWave827 K x tau).val :
              (ZMod Credit.attestationPrime)ˣ) :
            ZMod Credit.attestationPrime) *
        residueKummerRoot827 u := by
  dsimp only [strictOrbitKummerFrobeniusAlgEquiv827]
  rw [residueKummerFrobeniusAlgEquiv827_apply]
  change residueKummerRoot827
      (strictOrbitAngularComponent827 K x tau) ^
        Fintype.card (ZMod Credit.attestationPrime) = _
  rw [ZMod.card]
  exact frobenius_strictOrbitKummerRoot827 K x tau

/-- Every actual orbit Frobenius automorphism has order dividing 59. -/
theorem strictOrbitKummerFrobeniusAlgEquiv827_pow_fiftyNine
    (x : StrictCarrier59 K) (tau : GaloisIndex59) :
    strictOrbitKummerFrobeniusAlgEquiv827 K x tau ^ 59 = 1 :=
  residueKummerFrobeniusAlgEquiv827_pow_fiftyNine
    (strictOrbitAngularComponent827 K x tau)

/-! ## Axiom audit -/

/--
info: 'Fermat.FiftyNine.Conservation.StrictOrbitKummerFrobeniusAutomorphism827.strictOrbitKummerFrobeniusAlgEquiv827_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms strictOrbitKummerFrobeniusAlgEquiv827_root

/--
info: 'Fermat.FiftyNine.Conservation.StrictOrbitKummerFrobeniusAutomorphism827.strictOrbitKummerFrobeniusAlgEquiv827_pow_fiftyNine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms strictOrbitKummerFrobeniusAlgEquiv827_pow_fiftyNine

end Fermat.FiftyNine.Conservation.StrictOrbitKummerFrobeniusAutomorphism827
