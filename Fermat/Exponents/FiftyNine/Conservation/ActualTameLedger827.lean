import Fermat.Experiments.Conservation.FiniteOrbitLedger
import Fermat.Exponents.FiftyNine.Conservation.CyclotomicTameContext59
import Fermat.Exponents.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827

/-!
# The fixed-root finite tame-coordinate ledger at 827

This file seats the already constructed tame-symbol values on their genuine
height-one places above `827`.  Their additive coordinates use the same fixed
attestation primitive root at every residue presentation; the unweighted sum
is therefore a Fourier detector, not the globally `zeta`-normalized sum.  It
also proves that every omitted nonwild local value vanishes.

No reciprocity assertion is made here.  The final scalar equivalence is only
the exact rewriting of this fixed-root coordinate total as the explicit
orbit sum.  `CanonicalGlobalTameLedger827` supplies the global-root weighting.
-/

open scoped BigOperators NumberField

noncomputable section

set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.ActualTameLedger827

open Fermat.Conservation
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.CyclotomicTameContext59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)

local instance residueIdealIsMaximal
    (v : Fermat.FiftyNine.Conservation.CyclotomicTameContext59.Place K) :
    v.asIdeal.IsMaximal :=
  v.isMaximal

local instance residueField
    (v : Fermat.FiftyNine.Conservation.CyclotomicTameContext59.Place K) :
    Field
      (Fermat.FiftyNine.Conservation.CyclotomicTameContext59.Residue K v) :=
  Ideal.Quotient.field v.asIdeal

local instance residueFintype
    (v : Fermat.FiftyNine.Conservation.CyclotomicTameContext59.Place K) :
    Fintype
      (Fermat.FiftyNine.Conservation.CyclotomicTameContext59.Residue K v) :=
  Fintype.ofFinite _

/-- The actual height-one place carrying canonical orbit coordinate `tau`. -/
noncomputable abbrev tameOrbitPlace827 (tau : GaloisIndex59) :
    Fermat.FiftyNine.Conservation.CyclotomicTameContext59.Place K :=
  (indexedPlaceOrbitEquiv827 K (tameOrbitBasePlace827 (K := K)) tau).1

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Distinct canonical orbit coordinates name distinct height-one places. -/
theorem tameOrbitPlace827_injective :
    Function.Injective (tameOrbitPlace827 (K := K)) := by
  intro tau sigma hplace
  apply (indexedPlaceOrbitEquiv827 K
    (tameOrbitBasePlace827 (K := K))).injective
  exact Subtype.ext hplace

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The canonical orbit coordinates enumerate exactly all height-one places
above `827`. -/
theorem tameOrbitPlace827_range_eq_placesOver827 :
    Set.range (tameOrbitPlace827 (K := K)) = placesOver827 K := by
  ext v
  constructor
  · rintro ⟨tau, rfl⟩
    exact (indexedPlaceOrbitEquiv827 K
      (tameOrbitBasePlace827 (K := K)) tau).2
  · intro hv
    let orbitEquiv := indexedPlaceOrbitEquiv827 K
      (tameOrbitBasePlace827 (K := K))
    let tau : GaloisIndex59 := orbitEquiv.symm ⟨v, hv⟩
    refine ⟨tau, ?_⟩
    exact congrArg Subtype.val (orbitEquiv.apply_symm_apply ⟨v, hv⟩)

/-- The finite fixed-root coordinate ledger: its retained entries are the
already constructed local symbols, seated at the corresponding height-one
places. -/
noncomputable def actualTameLedger827
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi) :
    Fermat.FiftyNine.Conservation.CyclotomicTameContext59.Place K →₀ ZMod 59 :=
  FiniteOrbitLedger.orbitLedger
    (tameOrbitPlace827 (K := K))
    (actualTameOrbitValue827 (K := K) omega chi lift)

/-- Restriction to the explicit orbit recovers the corresponding actual
tame-symbol value, with no comparison premise. -/
@[simp]
theorem actualTameLedger827_apply_orbit
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (tau : GaloisIndex59) :
    actualTameLedger827 (K := K) omega chi lift
        (tameOrbitPlace827 (K := K) tau) =
      actualTameOrbitValue827 (K := K) omega chi lift tau := by
  exact FiniteOrbitLedger.orbitLedger_apply
    (tameOrbitPlace827 (K := K))
    (actualTameOrbitValue827 (K := K) omega chi lift)
    (tameOrbitPlace827_injective (K := K)) tau

/-- Every ledger row outside the actual set of places over 827 is zero. -/
theorem actualTameLedger827_apply_eq_zero_of_not_over827
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (v : Fermat.FiftyNine.Conservation.CyclotomicTameContext59.Place K)
    (hv : v ∉ placesOver827 K) :
    actualTameLedger827 (K := K) omega chi lift v = 0 := by
  apply FiniteOrbitLedger.orbitLedger_apply_eq_zero_of_not_mem_range
  rintro ⟨tau, rfl⟩
  exact hv ((indexedPlaceOrbitEquiv827 K
    (tameOrbitBasePlace827 (K := K)) tau).2)

/-- The support of the finite ledger is contained in the genuine set of
height-one places above 827. -/
theorem actualTameLedger827_support_subset_placesOver827
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi) :
    ↑(actualTameLedger827 (K := K) omega chi lift).support ⊆
      placesOver827 K := by
  intro v hv
  have hvRange : v ∈ Set.range (tameOrbitPlace827 (K := K)) :=
    FiniteOrbitLedger.orbitLedger_support_subset_range
      (tameOrbitPlace827 (K := K))
      (actualTameOrbitValue827 (K := K) omega chi lift) hv
  obtain ⟨tau, rfl⟩ := hvRange
  exact (indexedPlaceOrbitEquiv827 K
    (tameOrbitBasePlace827 (K := K)) tau).2

/-- Aggregating the finite fixed-root height-one ledger is definitionally the
complete unweighted explicit tame-orbit sum. -/
theorem actualTameLedger827_sum_eq_orbit_sum
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi) :
    (actualTameLedger827 (K := K) omega chi lift).sum
        (fun _ value ↦ value) =
      ∑ tau : GaloisIndex59,
        actualTameOrbitValue827 (K := K) omega chi lift tau := by
  exact FiniteOrbitLedger.orbitLedger_sum
    (tameOrbitPlace827 (K := K))
    (actualTameOrbitValue827 (K := K) omega chi lift)

/-- Adding an arbitrary proposed wild scalar to the fixed-root ledger is
equivalent to adding it to the unweighted explicit 827-orbit sum.  This is
only a scalar rewrite; it does not assume or package reciprocity, and this
unweighted equation is not the globally normalized one. -/
theorem wild_add_actualTameLedger827_sum_eq_zero_iff
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (wild : ZMod 59) :
    wild + (actualTameLedger827 (K := K) omega chi lift).sum
        (fun _ value ↦ value) = 0 ↔
      wild + ∑ tau : GaloisIndex59,
        actualTameOrbitValue827 (K := K) omega chi lift tau = 0 := by
  rw [actualTameLedger827_sum_eq_orbit_sum]

/-- The canonical tame value at every omitted nonwild place agrees with the
ledger's zero entry. Thus omission is justified by the actual local symbol,
not by the finite-support representation alone. -/
theorem canonicalTameValue_eq_actualTameLedger827_of_outside_support
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (v : Fermat.FiftyNine.Conservation.CyclotomicTameContext59.Place K)
    (hp : v ∉ placesOver59 K) (hq : v ∉ placesOver827 K) :
    (Fermat.FiftyNine.Conservation.CyclotomicTameContext59.context K v hp).value
        (ReflectedQRelaxedLocalizationLift827.primalRepresentative
          (IsCyclotomicExtension.zeta_spec 59 ℚ K))
        lift.candidateRepresentative =
      actualTameLedger827 (K := K) omega chi lift v := by
  rw [Fermat.FiftyNine.Conservation.CyclotomicTameContext59.value_firstGenerated_candidate_eq_zero_outside_support
      K omega chi lift v hp hq,
    actualTameLedger827_apply_eq_zero_of_not_over827
      (K := K) omega chi lift v hq]

end Fermat.FiftyNine.Conservation.ActualTameLedger827
