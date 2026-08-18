/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The normalized reflected eigenprofile on the complete 827 orbit

The actual full-orbit ledger uses the canonical physical place coordinate
`tameOrbitPlace827 tau`, which was already proved to be the explicit residue
place with index `tau⁻¹`.  This file puts the inverse reflected character on
that same 58-place orbit.  Its value at the chosen identity base place is
one, every place over 827 is retained, and cyclotomic place transport has
the literal left-translation law `tau ↦ sigma * tau`.

Consequently the profile transforms by
`reflectedCharacter omega chi sigma⁻¹`, equivalently by the inverse of the
reflected character at `sigma`.  Both spellings are retained below so that
the sigma/sigma-inverse convention cannot drift in a later Poitou--Tate or
Kummer--Artin adapter.

This constructs only the explicit local coefficient profile.  It does not
assert that the profile is the localization of a global reflected Selmer
class, and it supplies no profile, provider, Artin map, reciprocity law, or
Poitou--Tate lifting premise.
-/
import Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
import Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827

open scoped BigOperators MonoidAlgebra NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation

open Fermat.Conservation
open Fermat.Conservation.FiniteOrbitLedger
open ActualTameLedger827
open CanonicalTameLedger827
open CyclotomicLocalizationEquivariance827
open CyclotomicSelmerAction59
open CyclotomicTameContext59
open DetectorWitness827
open ExplicitTameOrbitReciprocity827
open SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- The residue-field character carried by the reflected 827 eigenprofile.
It is deliberately the inverse of the reduced reflected character. -/
abbrev inverseReflectedResidueCharacter827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    GaloisIndex59 →* (ZMod 59)ˣ :=
  (reducedCharacter59 (InvolutiveBase.reflectedCharacter omega chi))⁻¹

/-- The inverse reflected residue character at `sigma` is literally the
reduction of the reflected 59-adic character at `sigma⁻¹`. -/
@[simp]
theorem inverseReflectedResidueCharacter827_apply
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (sigma : GaloisIndex59) :
    ((inverseReflectedResidueCharacter827 omega chi sigma : (ZMod 59)ˣ) :
        ZMod 59) =
      PadicInt.toZMod
        (InvolutiveBase.reflectedCharacter omega chi sigma⁻¹ : PadicInt 59) := by
  simp [inverseReflectedResidueCharacter827,
    InvolutiveBase.reflectedCharacter, mul_comm]

/-- The normalized inverse-reflected Fourier vector in canonical orbit
coordinates.  It has coefficient one at the identity coordinate. -/
abbrev normalizedFullOrbitEigenprofileCoordinates827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    GaloisIndex59 → ZMod 59 :=
  characterFunction (inverseReflectedResidueCharacter827 omega chi)

/-- The coordinate vector is the pure inverse-reflected Fourier mode, with
component exactly one. -/
theorem normalizedFullOrbitEigenprofileCoordinates827_isPureCharacter
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    IsPureCharacter (inverseReflectedResidueCharacter827 omega chi)
      (normalizedFullOrbitEigenprofileCoordinates827 omega chi) := by
  exact ⟨1, by simp [normalizedFullOrbitEigenprofileCoordinates827]⟩

/-- Coordinate one is the actual chosen base place of the committed
full-orbit ledger. -/
theorem tameOrbitPlace827_one :
    tameOrbitPlace827 (K := K) 1 =
      (tameOrbitBasePlace827 (K := K)).1 := by
  rw [tameOrbitPlace827_eq_orbitPlace_inv]
  rfl

/-- Freeze the physical action convention.  Although the explicit residue
kernel named by canonical coordinate `tau` has residue index `tau⁻¹`, the
cyclotomic action by `sigma` is left translation `tau ↦ sigma * tau` in
the committed full-orbit coordinates. -/
theorem cyclotomicPlaceEquiv59_tameOrbitPlace827
    (sigma tau : GaloisIndex59) :
    cyclotomicPlaceEquiv59 K sigma
        (tameOrbitPlace827 (K := K) tau) =
      tameOrbitPlace827 (K := K) (sigma * tau) := by
  rw [tameOrbitPlace827_eq_orbitPlace_inv,
    tameOrbitPlace827_eq_orbitPlace_inv,
    OrbitPlace827.cyclotomicPlaceEquiv59_orbitPlace]
  congr 1

/-- Seat the normalized inverse-reflected coordinate vector on the actual
58 height-one places used by the committed full-orbit local pairing. -/
noncomputable def normalizedFullOrbitEigenprofileLedger827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    Place K →₀ ZMod 59 :=
  orbitLedger (tameOrbitPlace827 (K := K))
    (normalizedFullOrbitEigenprofileCoordinates827 omega chi)

/-- Exact readback in the existing full-orbit orientation. -/
@[simp]
theorem normalizedFullOrbitEigenprofileLedger827_apply
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (tau : GaloisIndex59) :
    normalizedFullOrbitEigenprofileLedger827 K omega chi
        (tameOrbitPlace827 (K := K) tau) =
      normalizedFullOrbitEigenprofileCoordinates827 omega chi tau := by
  exact orbitLedger_apply _ _
    (tameOrbitPlace827_injective (K := K)) tau

/-- The explicit profile is normalized to one at the actual chosen base
place, rather than merely at an abstract coordinate. -/
@[simp]
theorem normalizedFullOrbitEigenprofileLedger827_base
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    normalizedFullOrbitEigenprofileLedger827 K omega chi
        (tameOrbitBasePlace827 (K := K)).1 = 1 := by
  rw [← tameOrbitPlace827_one K,
    normalizedFullOrbitEigenprofileLedger827_apply]
  simp [normalizedFullOrbitEigenprofileCoordinates827,
    inverseReflectedResidueCharacter827]

/-- No 827 row was compressed or discarded: the support is exactly the
complete set of places above 827. -/
theorem normalizedFullOrbitEigenprofileLedger827_support
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    (↑(normalizedFullOrbitEigenprofileLedger827 K omega chi).support :
        Set (Place K)) =
      placesOver827 K := by
  rw [← tameOrbitPlace827_range_eq_placesOver827 (K := K)]
  apply Set.Subset.antisymm
  · exact orbitLedger_support_subset_range _ _
  · rintro v ⟨tau, rfl⟩
    rw [Finset.mem_coe, Finsupp.mem_support_iff,
      normalizedFullOrbitEigenprofileLedger827_apply]
    exact characterFunction_apply_ne_zero _ _

/-- The exact support has all 58 places of the split-prime orbit. -/
theorem normalizedFullOrbitEigenprofileLedger827_support_card
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    (normalizedFullOrbitEigenprofileLedger827 K omega chi).support.card =
      58 := by
  calc
    (normalizedFullOrbitEigenprofileLedger827 K omega chi).support.card =
        (↑(normalizedFullOrbitEigenprofileLedger827 K omega chi).support :
          Set (Place K)).ncard :=
      (Set.ncard_coe_finset _).symm
    _ = (placesOver827 K).ncard := by
      rw [normalizedFullOrbitEigenprofileLedger827_support]
    _ = 58 := placesOver827_ncard_eq_fiftyEight K

/-- The inverse-character eigenlaw, expressed first in the residue Fourier
character used to construct the profile. -/
theorem normalizedFullOrbitEigenprofileLedger827_eigenlaw
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (sigma tau : GaloisIndex59) :
    normalizedFullOrbitEigenprofileLedger827 K omega chi
        (cyclotomicPlaceEquiv59 K sigma
          (tameOrbitPlace827 (K := K) tau)) =
      ((inverseReflectedResidueCharacter827 omega chi sigma :
          (ZMod 59)ˣ) : ZMod 59) *
        normalizedFullOrbitEigenprofileLedger827 K omega chi
          (tameOrbitPlace827 (K := K) tau) := by
  rw [cyclotomicPlaceEquiv59_tameOrbitPlace827,
    normalizedFullOrbitEigenprofileLedger827_apply,
    normalizedFullOrbitEigenprofileLedger827_apply]
  exact congrArg Units.val
    (map_mul (inverseReflectedResidueCharacter827 omega chi) sigma tau)

/-- The same eigenlaw with the sigma-inverse convention made literal in the
statement: transport by `sigma` multiplies by the reduction of the reflected
character at `sigma⁻¹`. -/
theorem normalizedFullOrbitEigenprofileLedger827_reflected_eigenlaw
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (sigma tau : GaloisIndex59) :
    normalizedFullOrbitEigenprofileLedger827 K omega chi
        (cyclotomicPlaceEquiv59 K sigma
          (tameOrbitPlace827 (K := K) tau)) =
      PadicInt.toZMod
          (InvolutiveBase.reflectedCharacter omega chi sigma⁻¹ : PadicInt 59) *
        normalizedFullOrbitEigenprofileLedger827 K omega chi
          (tameOrbitPlace827 (K := K) tau) := by
  rw [← inverseReflectedResidueCharacter827_apply]
  exact normalizedFullOrbitEigenprofileLedger827_eigenlaw
    K omega chi sigma tau

/-- The complete W3 receipt.  It retains the actual place-indexed profile,
its two equivalent orientation readbacks, normalization at the chosen base,
the exact 58-place support, and the reflected cyclotomic eigenlaw. -/
structure NormalizedFullOrbitEigenprofile827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) where
  /-- The literal place-indexed profile. -/
  profile : Place K →₀ ZMod 59
  /-- Readback as the inverse reduced reflected Fourier character. -/
  orbit_reading : ∀ tau : GaloisIndex59,
    profile (tameOrbitPlace827 (K := K) tau) =
      normalizedFullOrbitEigenprofileCoordinates827 omega chi tau
  /-- The same readback with the inverse index explicit. -/
  inverse_reflected_orientation : ∀ tau : GaloisIndex59,
    profile (tameOrbitPlace827 (K := K) tau) =
      PadicInt.toZMod
        (InvolutiveBase.reflectedCharacter omega chi tau⁻¹ : PadicInt 59)
  /-- Normalization at the chosen physical base place. -/
  normalized_at_base :
    profile (tameOrbitBasePlace827 (K := K)).1 = 1
  /-- Exact physical support. -/
  support_eq_placesOver827 :
    (↑profile.support : Set (Place K)) = placesOver827 K
  /-- Machine-readable support cardinality. -/
  support_card_eq_fiftyEight : profile.support.card = 58
  /-- The reflected eigenlaw in the fixed physical action orientation. -/
  reflected_eigenlaw : ∀ sigma tau : GaloisIndex59,
    profile (cyclotomicPlaceEquiv59 K sigma
        (tameOrbitPlace827 (K := K) tau)) =
      PadicInt.toZMod
          (InvolutiveBase.reflectedCharacter omega chi sigma⁻¹ : PadicInt 59) *
        profile (tameOrbitPlace827 (K := K) tau)

/-- The concrete normalized full-orbit eigenprofile, constructed entirely
from the committed orbit equivalence and the reduced reflected character. -/
noncomputable def normalizedFullOrbitEigenprofile827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    NormalizedFullOrbitEigenprofile827 K omega chi where
  profile := normalizedFullOrbitEigenprofileLedger827 K omega chi
  orbit_reading :=
    normalizedFullOrbitEigenprofileLedger827_apply K omega chi
  inverse_reflected_orientation := fun tau ↦ by
    rw [normalizedFullOrbitEigenprofileLedger827_apply]
    change
      ((inverseReflectedResidueCharacter827 omega chi tau : (ZMod 59)ˣ) :
          ZMod 59) = _
    exact inverseReflectedResidueCharacter827_apply omega chi tau
  normalized_at_base :=
    normalizedFullOrbitEigenprofileLedger827_base K omega chi
  support_eq_placesOver827 :=
    normalizedFullOrbitEigenprofileLedger827_support K omega chi
  support_card_eq_fiftyEight :=
    normalizedFullOrbitEigenprofileLedger827_support_card K omega chi
  reflected_eigenlaw :=
    normalizedFullOrbitEigenprofileLedger827_reflected_eigenlaw
      K omega chi

end Fermat.FiftyNine.Conservation
