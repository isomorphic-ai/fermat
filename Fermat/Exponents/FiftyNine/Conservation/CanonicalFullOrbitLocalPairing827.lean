/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The normalized wild row and the complete tame orbit in one pairing

The raw construction in this file is bilinear on the strict Selmer carrier
and the carrier relaxed at every place over 827.  Its distinguished row is
the normalized continuous Kummer pairing at lambda, and its other retained
rows are the genuine globally-root-oriented tame symbols at all 58 places
over 827.  The finite support is therefore constructed rather than assumed.

After restricting the two inputs to the actual `chi` and
`omega * chi^-1` eigenspaces, the same raw ledger gives a
`PlaceIndexedLocalPairing`.  Its fixed-place `hash omega` adjoint law is a
formal consequence of those two character seats.  This does not confuse that
law with the more primitive tame-symbol equivariance, which moves the place.

No global reciprocity law is asserted here.
-/
import Fermat.Exponents.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827
import Fermat.Exponents.FiftyNine.Conservation.NormalizedContinuousWildLocalization59
import Fermat.Experiments.Conservation.PointedFiniteOrbitLedger
import Fermat.Experiments.Conservation.TatePairing
import Fermat.Experiments.Conservation.TamePlacePairing

open scoped BigOperators MonoidAlgebra NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827

open Fermat.Conservation
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TameSymbol
open Fermat.Conservation.TatePairing
open CanonicalGlobalReciprocity827
open CanonicalTameLedger827
open ActualTameLedger827
open CyclotomicSelmerAction59
open CyclotomicTameContext59
open DetectorWitness827
open ExplicitTameOrbitReciprocity827
open LocalCompletion59
open LocalReduction827
open NormalizedContinuousKummerPairing59
open NormalizedContinuousWildLocalization59
open SplitPrimeFourier827
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance residueIdealIsMaximal
    (v : Place K) : v.asIdeal.IsMaximal := v.isMaximal

local instance residueField (v : Place K) : Field (Residue K v) :=
  Ideal.Quotient.field v.asIdeal

local instance residueFintype (v : Place K) : Fintype (Residue K v) :=
  Fintype.ofFinite _

/-- The actual strict empty-support Selmer carrier, before choosing a
character seat. -/
abbrev StrictCarrier59 :=
  SelmerCarrier (NumberField.RingOfIntegers K) K 59

/-- The actual carrier relaxed at every height-one place above 827. -/
abbrev RelaxedCarrier827 := QRelaxedSelmerCarrier827 K

/-- Forget the strict Selmer predicate and retain its genuine global Kummer
class. -/
def strictKummerClass59 :
    StrictCarrier59 K →+ KummerClass 59 K :=
  MonoidHom.toAdditive
    (IsDedekindDomain.selmerGroup
      (R := NumberField.RingOfIntegers K) (K := K)
      (S := (∅ : Set (Place K))) (n := 59)).subtype

/-- Forget the 827-supported Selmer predicate and retain its genuine global
Kummer class. -/
def relaxedKummerClass827 :
    RelaxedCarrier827 K →+ KummerClass 59 K :=
  MonoidHom.toAdditive
    (IsDedekindDomain.selmerGroup
      (R := NumberField.RingOfIntegers K) (K := K)
      (S := placesOver827 K) (n := 59)).subtype

/-- The normalized continuous wild bilinear form on the two unseated Selmer
carriers. -/
noncomputable def rawWildReading59 :
    StrictCarrier59 K →+ (RelaxedCarrier827 K →+ ZMod 59) :=
  AddMonoidHom.compl₂
    ((normalizedLambdaGlobalPairing59 K).comp (strictKummerClass59 K))
    (relaxedKummerClass827 K)

/-- The genuine globally-root-oriented tame symbol at one canonical place
of the complete 827 orbit. -/
noncomputable def rawTameOrbitReading827
    (tau : GaloisIndex59) :
    StrictCarrier59 K →+ (RelaxedCarrier827 K →+ ZMod 59) :=
  AddMonoidHom.compl₂
    (((context K (tameOrbitPlace827 (K := K) tau)
      (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).modP).comp
        (strictKummerClass59 K))
    (relaxedKummerClass827 K)

/-- The complete finite ledger on the raw strict/827-relaxed carriers:
one normalized wild row and all 58 genuine tame rows. -/
noncomputable def rawFullOrbitReadings827 :
    StrictCarrier59 K →+
      (RelaxedCarrier827 K →+ (Place K →₀ ZMod 59)) :=
  (rawWildReading59 K).compr₂
      (Finsupp.singleAddHom (lambdaPlace59 K)) +
    ∑ tau : GaloisIndex59,
      (rawTameOrbitReading827 K tau).compr₂
        (Finsupp.singleAddHom (tameOrbitPlace827 (K := K) tau))

@[simp]
theorem rawFullOrbitReadings827_apply
    (x : StrictCarrier59 K) (y : RelaxedCarrier827 K) :
    rawFullOrbitReadings827 K x y =
      Finsupp.single (lambdaPlace59 K) (rawWildReading59 K x y) +
        ∑ tau : GaloisIndex59,
          Finsupp.single (tameOrbitPlace827 (K := K) tau)
            (rawTameOrbitReading827 K tau x y) := by
  simp [rawFullOrbitReadings827]

/-- Pointwise, the bilinear raw construction is exactly the generic pointed
finite-orbit ledger.  The raw definition remains bilinear by construction;
this theorem is its scalar ledger adapter. -/
theorem rawFullOrbitReadings827_apply_eq_pointedOrbitLedger
    (x : StrictCarrier59 K) (y : RelaxedCarrier827 K) :
    rawFullOrbitReadings827 K x y =
      PointedFiniteOrbitLedger.pointedOrbitLedger
        (lambdaPlace59 K) (rawWildReading59 K x y)
        (tameOrbitPlace827 (K := K))
        (fun tau ↦ rawTameOrbitReading827 K tau x y) := by
  rw [rawFullOrbitReadings827_apply]
  rfl

private theorem lambdaPlace59_not_mem_tameOrbitPlace827_range :
    lambdaPlace59 K ∉ Set.range (tameOrbitPlace827 (K := K)) := by
  simpa only [tameOrbitPlace827_range_eq_placesOver827 (K := K)] using
    lambdaPlace59_not_mem_placesOver827 (K := K)

/-- Reading the raw ledger at the distinguished wild place recovers exactly
the normalized continuous Kummer pairing.  Every tame row is genuinely
seated over 827, which is disjoint from the place over 59. -/
@[simp]
theorem rawFullOrbitReadings827_apply_lambda
    (x : StrictCarrier59 K) (y : RelaxedCarrier827 K) :
    rawFullOrbitReadings827 K x y (lambdaPlace59 K) =
      rawWildReading59 K x y := by
  rw [rawFullOrbitReadings827_apply_eq_pointedOrbitLedger]
  exact PointedFiniteOrbitLedger.pointedOrbitLedger_apply_distinguished
    (lambdaPlace59 K) (rawWildReading59 K x y)
    (tameOrbitPlace827 (K := K))
    (fun tau ↦ rawTameOrbitReading827 K tau x y)
    (lambdaPlace59_not_mem_tameOrbitPlace827_range K)

/-- Reading the raw ledger at an 827 orbit place recovers exactly that
place's globally-root-oriented tame symbol. -/
@[simp]
theorem rawFullOrbitReadings827_apply_orbit
    (tau : GaloisIndex59)
    (x : StrictCarrier59 K) (y : RelaxedCarrier827 K) :
    rawFullOrbitReadings827 K x y
        (tameOrbitPlace827 (K := K) tau) =
      rawTameOrbitReading827 K tau x y := by
  rw [rawFullOrbitReadings827_apply_eq_pointedOrbitLedger]
  exact PointedFiniteOrbitLedger.pointedOrbitLedger_apply_orbit
    (lambdaPlace59 K) (rawWildReading59 K x y)
    (tameOrbitPlace827 (K := K))
    (fun tau ↦ rawTameOrbitReading827 K tau x y)
    (tameOrbitPlace827_injective (K := K))
    (lambdaPlace59_not_mem_tameOrbitPlace827_range K) tau

/-- The raw ledger is definitionally silent away from the wild place and
the complete 827 orbit. -/
theorem rawFullOrbitReadings827_apply_eq_zero_of_outside
    (x : StrictCarrier59 K) (y : RelaxedCarrier827 K)
    (v : Place K) (hwild : v ≠ lambdaPlace59 K)
    (h827 : v ∉ placesOver827 K) :
    rawFullOrbitReadings827 K x y v = 0 := by
  rw [rawFullOrbitReadings827_apply_eq_pointedOrbitLedger]
  apply
    PointedFiniteOrbitLedger.pointedOrbitLedger_apply_eq_zero_of_ne_of_not_mem_range
      (lambdaPlace59 K) (rawWildReading59 K x y)
      (tameOrbitPlace827 (K := K))
      (fun tau ↦ rawTameOrbitReading827 K tau x y) v hwild
  simpa only [tameOrbitPlace827_range_eq_placesOver827 (K := K)] using h827

/-- The constructed raw support is contained in exactly the retained wild
place and the full set of places above 827. -/
theorem rawFullOrbitReadings827_support_subset
    (x : StrictCarrier59 K) (y : RelaxedCarrier827 K) :
    ↑(rawFullOrbitReadings827 K x y).support ⊆
      Set.insert (lambdaPlace59 K) (placesOver827 K) := by
  rw [rawFullOrbitReadings827_apply_eq_pointedOrbitLedger]
  simpa only [tameOrbitPlace827_range_eq_placesOver827 (K := K)] using
    PointedFiniteOrbitLedger.pointedOrbitLedger_support_subset_insert_range
      (lambdaPlace59 K) (rawWildReading59 K x y)
      (tameOrbitPlace827 (K := K))
      (fun tau ↦ rawTameOrbitReading827 K tau x y)

/-- Aggregating the complete raw ledger is the wild reading plus the sum of
all 58 tame orbit readings, in the supplied orbit orientation. -/
theorem rawFullOrbitReadings827_sum
    (x : StrictCarrier59 K) (y : RelaxedCarrier827 K) :
    (rawFullOrbitReadings827 K x y).sum (fun _ entry ↦ entry) =
      rawWildReading59 K x y +
        ∑ tau : GaloisIndex59, rawTameOrbitReading827 K tau x y := by
  rw [rawFullOrbitReadings827_apply_eq_pointedOrbitLedger]
  exact PointedFiniteOrbitLedger.pointedOrbitLedger_sum
    (lambdaPlace59 K) (rawWildReading59 K x y)
    (tameOrbitPlace827 (K := K))
    (fun tau ↦ rawTameOrbitReading827 K tau x y)

section Seated

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)

/-- Restrict the raw global ledger to the actual primal and reflected
character eigenspaces. -/
noncomputable def seatedFullOrbitReadings827 :
    OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi →+
      (QRelaxedReflectedDual827
          (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi →+
        (Place K →₀ ZMod 59)) :=
  ((rawFullOrbitReadings827 K).comp
      (toSeatedCarrier
        (rho := cyclotomicStrictSelmerRepresentation59 K)
        (chi := chi)).toAddMonoidHom).compl₂
    (toSupportedCarrier
      (rho := cyclotomicQRelaxedSelmerRepresentation827 K)
      (eta := InvolutiveBase.reflectedCharacter omega chi)).toAddMonoidHom

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
private theorem single_smul_primal
    (delta : GaloisIndex59) (c : PadicInt 59)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi) :
    MonoidAlgebra.single delta c • x =
      (c * (chi delta : PadicInt 59)) • x := by
  have hdelta :
      characterEigenspaceRepresentation
          (cyclotomicStrictSelmerRepresentation59 K) chi delta x =
        (chi delta : PadicInt 59) • x := by
    apply Subtype.ext
    exact (mem_characterEigenspace_iff
      (cyclotomicStrictSelmerRepresentation59 K) chi x.1).mp
        x.property delta
  calc
    MonoidAlgebra.single delta c • x =
        c • characterEigenspaceRepresentation
          (cyclotomicStrictSelmerRepresentation59 K) chi delta x := by
      change ((characterEigenspaceRepresentation
        (cyclotomicStrictSelmerRepresentation59 K) chi).asAlgebraHom
        (MonoidAlgebra.single delta c)) x = _
      rw [Representation.asAlgebraHom_single]
      rfl
    _ = c • ((chi delta : PadicInt 59) • x) := by rw [hdelta]
    _ = (c * (chi delta : PadicInt 59)) • x := by rw [smul_smul]

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
private theorem hash_single_smul_reflected
    (delta : GaloisIndex59) (c : PadicInt 59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    InvolutiveBase.hash omega (MonoidAlgebra.single delta c) • y =
      (c * (chi delta : PadicInt 59)) • y := by
  rw [InvolutiveBase.hash_apply_single]
  have hdelta :
      characterEigenspaceRepresentationAt
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          (InvolutiveBase.reflectedCharacter omega chi) delta⁻¹ y =
        (InvolutiveBase.reflectedCharacter omega chi delta⁻¹ :
          PadicInt 59) • y := by
    apply Subtype.ext
    exact (mem_characterEigenspaceAt_iff
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      (InvolutiveBase.reflectedCharacter omega chi) y.1).mp
        y.property delta⁻¹
  calc
    MonoidAlgebra.single delta⁻¹ (c * (omega delta : PadicInt 59)) • y =
        (c * (omega delta : PadicInt 59)) •
          characterEigenspaceRepresentationAt
            (cyclotomicQRelaxedSelmerRepresentation827 K)
            (InvolutiveBase.reflectedCharacter omega chi) delta⁻¹ y := by
      change ((characterEigenspaceRepresentationAt
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        (InvolutiveBase.reflectedCharacter omega chi)).asAlgebraHom
        (MonoidAlgebra.single delta⁻¹
          (c * (omega delta : PadicInt 59)))) y = _
      rw [Representation.asAlgebraHom_single]
      rfl
    _ = (c * (omega delta : PadicInt 59)) •
          ((InvolutiveBase.reflectedCharacter omega chi delta⁻¹ :
            PadicInt 59) • y) := by rw [hdelta]
    _ = ((c * (omega delta : PadicInt 59)) *
          (InvolutiveBase.reflectedCharacter omega chi delta⁻¹ :
            PadicInt 59)) • y := by rw [smul_smul]
    _ = (c * (chi delta : PadicInt 59)) • y := by
      congr 1
      simp [InvolutiveBase.reflectedCharacter, mul_assoc, mul_comm,
        mul_left_comm]

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
private theorem seated_single_adjoint
    (delta : GaloisIndex59) (c : PadicInt 59)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    seatedFullOrbitReadings827 K omega chi
        (MonoidAlgebra.single delta c • x) y =
      seatedFullOrbitReadings827 K omega chi x
        (InvolutiveBase.hash omega (MonoidAlgebra.single delta c) • y) := by
  rw [single_smul_primal K chi, hash_single_smul_reflected K omega chi]
  change seatedFullOrbitReadings827 K omega chi
      ((PadicInt.toZMod (c * (chi delta : PadicInt 59))).val • x) y =
    seatedFullOrbitReadings827 K omega chi x
      ((PadicInt.toZMod (c * (chi delta : PadicInt 59))).val • y)
  rw [map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply]

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The complete finite ledger has the fixed-place `hash omega` adjoint law
after restriction to the two genuine character seats. -/
theorem seatedFullOrbitReadings827_adjoint
    (a : IntegralPadicGroupAlgebra 59 GaloisIndex59)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    seatedFullOrbitReadings827 K omega chi (a • x) y =
      seatedFullOrbitReadings827 K omega chi x
        ((InvolutiveBase.hash omega a) • y) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      calc
        seatedFullOrbitReadings827 K omega chi ((a + b) • x) y =
            seatedFullOrbitReadings827 K omega chi (a • x + b • x) y := by
          rw [add_smul]
        _ = seatedFullOrbitReadings827 K omega chi (a • x) y +
            seatedFullOrbitReadings827 K omega chi (b • x) y := by
          rw [map_add, AddMonoidHom.add_apply]
        _ = seatedFullOrbitReadings827 K omega chi x
              ((InvolutiveBase.hash omega a) • y) +
            seatedFullOrbitReadings827 K omega chi x
              ((InvolutiveBase.hash omega b) • y) := by rw [ha, hb]
        _ = seatedFullOrbitReadings827 K omega chi x
            ((InvolutiveBase.hash omega a) • y +
              (InvolutiveBase.hash omega b) • y) := by rw [map_add]
        _ = seatedFullOrbitReadings827 K omega chi x
            (((InvolutiveBase.hash omega a) +
              (InvolutiveBase.hash omega b)) • y) := by rw [add_smul]
        _ = seatedFullOrbitReadings827 K omega chi x
            ((InvolutiveBase.hash omega (a + b)) • y) := by
          exact congrArg
            (fun z : IntegralPadicGroupAlgebra 59 GaloisIndex59 ↦
              seatedFullOrbitReadings827 K omega chi x (z • y))
            (map_add (InvolutiveBase.hash omega) a b).symm
  | single delta c =>
      exact seated_single_adjoint K omega chi delta c x y

/-- The actual normalized-wild/complete-tame construction as the repository's
place-indexed Tate-pairing type. -/
noncomputable def canonicalFullOrbitLocalPairing827 :
    PlaceIndexedLocalPairing 59 GaloisIndex59 omega chi (Place K)
      (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
      (QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) where
  readings := seatedFullOrbitReadings827 K omega chi
  adjoint_law := fun _ a x y ↦
    DFunLike.congr_fun
      (seatedFullOrbitReadings827_adjoint K omega chi a x y) _

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The distinguished row of the seated pairing is the literal normalized
continuous global Kummer pairing on the two literal Selmer classes. -/
@[simp]
theorem canonicalFullOrbitLocalPairing827_pairAt_lambda
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    (canonicalFullOrbitLocalPairing827 K omega chi).pairAt
        (lambdaPlace59 K) x y =
      normalizedLambdaGlobalPairing59 K
        (toKummerClass x) (toKummerClassAt y) := by
  change rawFullOrbitReadings827 K
      ((toSeatedCarrier
        (rho := cyclotomicStrictSelmerRepresentation59 K)
        (chi := chi)).toAddMonoidHom x)
      ((toSupportedCarrier
        (rho := cyclotomicQRelaxedSelmerRepresentation827 K)
        (eta := InvolutiveBase.reflectedCharacter omega chi)).toAddMonoidHom y)
      (lambdaPlace59 K) = _
  rw [rawFullOrbitReadings827_apply_lambda]
  rfl

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Every tame orbit row of the seated pairing is the literal canonical
globally-root-oriented tame symbol on the two literal Selmer classes. -/
@[simp]
theorem canonicalFullOrbitLocalPairing827_pairAt_orbit
    (tau : GaloisIndex59)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    (canonicalFullOrbitLocalPairing827 K omega chi).pairAt
        (tameOrbitPlace827 (K := K) tau) x y =
      (context K (tameOrbitPlace827 (K := K) tau)
        (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).modP
        (toKummerClass x) (toKummerClassAt y) := by
  change rawFullOrbitReadings827 K
      ((toSeatedCarrier
        (rho := cyclotomicStrictSelmerRepresentation59 K)
        (chi := chi)).toAddMonoidHom x)
      ((toSupportedCarrier
        (rho := cyclotomicQRelaxedSelmerRepresentation827 K)
        (eta := InvolutiveBase.reflectedCharacter omega chi)).toAddMonoidHom y)
      (tameOrbitPlace827 (K := K) tau) = _
  rw [rawFullOrbitReadings827_apply_orbit]
  rfl

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The strict Selmer predicate gives the exact mod-59 valuation receipt
needed by every genuine tame context away from 59. -/
theorem strict_ordModP_eq_zero
    (v : Place K) (hp : v ∉ placesOver59 K)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi) :
    (context K v hp).ordModP (toKummerClass x) = 0 := by
  exact
    Fermat.Conservation.TamePlacePairing.Seated.ordModP_toKummerClass_eq_zero_of_ord_eq_valuation
        v (context K v hp) (context_ord K v hp) x

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Away from the allowed 827 support, the relaxed Selmer predicate gives
the same exact mod-59 valuation receipt. -/
theorem relaxed_ordModP_eq_zero_of_not_over827
    (v : Place K) (hp : v ∉ placesOver59 K)
    (h827 : v ∉ placesOver827 K)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    (context K v hp).ordModP (toKummerClassAt y) = 0 := by
  let a : Kˣ := quotientRepresentativeAt y
  have ha :
      Additive.ofMul
          (QuotientGroup.mk' (powMonoidHom 59 : Kˣ →* Kˣ).range a) =
        toKummerClassAt y := by
    rw [toKummerClassAt_apply]
    exact congrArg Additive.ofMul (quotientRepresentativeAt_mk y)
  rw [← ha, Fermat.Conservation.TameSymbol.Context.ordModP_mk,
    context_ord]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 59).mpr
    (quotientRepresentativeAt_valuation_dvd_of_not_mem v h827 y)

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Every omitted tame symbol is honestly zero: both zero valuations come
from the strict and 827-relaxed Selmer predicates, rather than from the
finite-ledger definition. -/
theorem canonical_tameModP_eq_zero_of_outside_support
    (v : Place K) (hp : v ∉ placesOver59 K)
    (h827 : v ∉ placesOver827 K)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    (context K v hp).modP (toKummerClass x) (toKummerClassAt y) = 0 := by
  exact (context K v hp).modP_eq_zero_of_ordModP_eq_zero _ _
    (strict_ordModP_eq_zero K chi v hp x)
    (relaxed_ordModP_eq_zero_of_not_over827 K omega chi v hp h827 y)

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The seated pairing has no retained row away from the distinguished wild
place and the complete 827 orbit. -/
theorem canonicalFullOrbitLocalPairing827_pairAt_eq_zero_of_outside
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (v : Place K) (hwild : v ≠ lambdaPlace59 K)
    (h827 : v ∉ placesOver827 K) :
    (canonicalFullOrbitLocalPairing827 K omega chi).pairAt v x y = 0 := by
  exact rawFullOrbitReadings827_apply_eq_zero_of_outside K _ _ v hwild h827

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The seated pairing retains no support beyond lambda and the complete set
of 827 places. -/
theorem canonicalFullOrbitLocalPairing827_support_subset
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    ↑((canonicalFullOrbitLocalPairing827 K omega chi).readings x y).support ⊆
      Set.insert (lambdaPlace59 K) (placesOver827 K) := by
  exact rawFullOrbitReadings827_support_subset K
    ((toSeatedCarrier
      (rho := cyclotomicStrictSelmerRepresentation59 K)
      (chi := chi)).toAddMonoidHom x)
    ((toSupportedCarrier
      (rho := cyclotomicQRelaxedSelmerRepresentation827 K)
      (eta := InvolutiveBase.reflectedCharacter omega chi)).toAddMonoidHom y)

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Outside 59 and 827, the constructed zero row agrees with the actual
canonical tame symbol, whose vanishing was derived independently from the
two Selmer support conditions. -/
theorem canonicalFullOrbitLocalPairing827_pairAt_eq_tameModP_of_outside_support
    (v : Place K) (hp : v ∉ placesOver59 K)
    (h827 : v ∉ placesOver827 K)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    (canonicalFullOrbitLocalPairing827 K omega chi).pairAt v x y =
      (context K v hp).modP (toKummerClass x) (toKummerClassAt y) := by
  have hwild : v ≠ lambdaPlace59 K := by
    intro hplace
    apply hp
    rw [hplace]
    exact (lambdaIdeal59_liesOver K).over
  rw [canonicalFullOrbitLocalPairing827_pairAt_eq_zero_of_outside
      K omega chi x y v hwild h827,
    canonical_tameModP_eq_zero_of_outside_support
      K omega chi v hp h827 x y]

end Seated

end Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
