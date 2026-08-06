/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Character eigenspaces on Mathlib's Selmer carrier

This file seats the two Selmer types used by the conservation stage on
Mathlib's actual unramified Selmer subgroup.  The full carrier is literally

`Additive (IsDedekindDomain.selmerGroup (S := ∅) (n := p))`,

not an unrelated provider type.  Its natural `ZMod p` action comes from the
fact that the Kummer quotient is killed by `p`; the `PadicInt p` action is
the restriction of scalars along `PadicInt.toZMod`.

A supplied action of `Delta` is then recorded as a representation on that
concrete carrier, and the character submodules are taken directly inside it.
The named maps below expose every step through the additive wrapper, the
Selmer subgroup, and the ambient Kummer quotient.

The reflected leg follows the project's existing convention
`chi* = omega * chi⁻¹` and remains a second literal Selmer eigenspace.  Its
eventual equivalence with a character dual, together with the
`InvolutiveBase.hash omega` adjoint law expected by
`CommonActionStage.ReflectedDualRealization.omegaTwistedAction`, is retained
as the named arithmetic gap `ReflectedDualCharacterGlue`; it is not silently
assumed by either eigenspace definition.

The pinned Mathlib declaration is named `IsDedekindDomain.selmerGroup` (its
local conditions use `IsDedekindDomain.HeightOneSpectrum`); some prose calls
it `HeightOneSpectrum.selmerGroup`.  All definitions below use the declaration
that actually exists at the pin.
-/
import Fermat.Conservation.CommonActionStage
import Mathlib.Algebra.Module.ZMod
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RepresentationTheory.Basic

open scoped MonoidAlgebra nonZeroDivisors

noncomputable section

namespace Fermat.Conservation.SelmerEigenspace

open Fermat.Conservation.LinkingInterfaces

universe uR uK uDelta

/-! ## The concrete carrier and its coefficient actions -/

/-- Mathlib's empty-support Selmer subgroup, only changed to additive
notation.  Unfolding this abbreviation exposes the literal
`IsDedekindDomain.selmerGroup` subtype. -/
abbrev SelmerCarrier (R : Type uR) (K : Type uK)
    [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (p : ℕ) :=
  Additive
    (IsDedekindDomain.selmerGroup
      (R := R) (K := K)
      (S := (∅ : Set (IsDedekindDomain.HeightOneSpectrum R))) (n := p))

/-- The new spelling is definitionally the carrier already used by
`CommonActionStage`; this is the first carrier-glue receipt. -/
theorem selmerCarrier_eq_commonActionStage
    (R : Type uR) (K : Type uK)
    [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (p : ℕ) :
    SelmerCarrier R K p = CommonActionStage.Selmer R K p :=
  rfl

section Coefficients

variable {R : Type uR} [CommRing R] [IsDedekindDomain R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
  {p : ℕ}

/-- Every element of the concrete Kummer quotient, hence every Selmer
element, is killed by `p`. -/
theorem p_nsmul_eq_zero (x : SelmerCarrier R K p) : p • x = 0 := by
  apply Additive.toMul.injective
  change (Additive.toMul x) ^ p = 1
  apply Subtype.ext
  change ((Additive.toMul x).1) ^ p = 1
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom p : Kˣ →* Kˣ).range (Additive.toMul x).1
  rw [← hy]
  exact (QuotientGroup.eq_one_iff (y ^ p)).mpr ⟨y, rfl⟩

/-- The canonical `ZMod p`-module structure on the actual Selmer subtype. -/
instance instModuleZMod : Module (ZMod p) (SelmerCarrier R K p) :=
  AddCommGroup.zmodModule (n := p) (G := SelmerCarrier R K p)
    p_nsmul_eq_zero

/-- The integral p-adic coefficient action factors through reduction modulo
`p`, as it must on a group killed by `p`. -/
instance instModulePadicInt [Fact p.Prime] :
    Module (PadicInt p) (SelmerCarrier R K p) :=
  Module.compHom (SelmerCarrier R K p) PadicInt.toZMod

@[simp]
theorem padicInt_smul_eq_toZMod_smul [Fact p.Prime]
    (a : PadicInt p) (x : SelmerCarrier R K p) :
    a • x = PadicInt.toZMod a • x :=
  rfl

end Coefficients

/-! ## The actual Delta eigenspaces -/

section Eigenspaces

variable {R : Type uR} [CommRing R] [IsDedekindDomain R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
  {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]

/-- A `Delta` action on the concrete Selmer subtype.  This is only a name for
Mathlib's representation type; no action is manufactured here. -/
abbrev SelmerDeltaRepresentation :=
  Representation (PadicInt p) Delta (SelmerCarrier R K p)

/-- Generic simultaneous character eigenspace.  Keeping the closure argument
at the abstract module level prevents instance search from unfolding the
concrete Kummer quotient while preserving the literal carrier predicate after
specialization. -/
private def characterEigenspaceGeneric
    {A : Type*} [CommRing A]
    {G : Type*} [CommGroup G]
    {M : Type*} [AddCommGroup M] [Module A M]
    (rho : Representation A G M)
    (chi : InvolutiveBase.Character A G) :
    Submodule A M where
  carrier := {x | ∀ g : G, rho g x = (chi g : A) • x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy g
    calc
      rho g (x + y) = rho g x + rho g y := map_add (rho g) x y
      _ = (chi g : A) • x + (chi g : A) • y := by
        rw [hx g, hy g]
      _ = (chi g : A) • (x + y) := (smul_add _ _ _).symm
  smul_mem' := by
    intro a x hx g
    calc
      rho g (a • x) = a • rho g x := map_smul (rho g) a x
      _ = a • ((chi g : A) • x) := by rw [hx g]
      _ = (chi g : A) • (a • x) := by
        rw [smul_smul, smul_smul, mul_comm]

/-- The simultaneous `chi`-eigenspace as a literal submodule of the actual
additive Selmer subtype. -/
def characterEigenspace
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta))
    (chi : InvolutiveBase.Character (PadicInt p) Delta) :
    Submodule (PadicInt p) (SelmerCarrier R K p) :=
  characterEigenspaceGeneric
    (A := PadicInt p) (G := Delta) (M := SelmerCarrier R K p) rho chi

/-- The standard additive group on the literal eigenspace subtype, named at
the namespace-owned type head so character-dual interfaces do not have to
unfold the concrete Kummer quotient during instance search. -/
instance instCharacterEigenspaceAddCommGroup
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta))
    (chi : InvolutiveBase.Character (PadicInt p) Delta) :
    AddCommGroup (characterEigenspace rho chi) :=
  @Submodule.addCommGroup
    (PadicInt p) (SelmerCarrier R K p) inferInstance inferInstance
      (instModulePadicInt (R := R) (K := K) (p := p))
      (characterEigenspace rho chi)

/-- Membership in the eigenspace is exactly the displayed simultaneous
eigenvalue law. -/
@[simp]
theorem mem_characterEigenspace_iff
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta))
    (chi : InvolutiveBase.Character (PadicInt p) Delta)
    (x : SelmerCarrier R K p) :
    x ∈ characterEigenspace rho chi ↔
      ∀ delta : Delta,
        rho delta x = (chi delta : PadicInt p) • x :=
  Iff.rfl

/-- The stage's `SelmerChi` is the actual `chi`-eigenspace subtype. -/
abbrev SelmerChi
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta))
    (chi : InvolutiveBase.Character (PadicInt p) Delta) :=
  characterEigenspace rho chi

/-- The primal carrier underlying the reflected character-dual leg. -/
abbrev SelmerChiStar
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta))
    (omega chi : InvolutiveBase.Character (PadicInt p) Delta) :=
  characterEigenspace rho (InvolutiveBase.reflectedCharacter omega chi)

/-- The action restricted to a character eigenspace.  Commutativity of
`Delta` is exactly what makes the eigenspace stable. -/
def characterEigenspaceRepresentation
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta))
    (chi : InvolutiveBase.Character (PadicInt p) Delta) :
    Representation (PadicInt p) Delta (characterEigenspace rho chi) where
  toFun delta :=
    { toFun := fun x => ⟨rho delta x.1, by
        rw [mem_characterEigenspace_iff]
        intro epsilon
        calc
          rho epsilon (rho delta x.1) = rho (epsilon * delta) x.1 := by
            simp only [map_mul, Module.End.mul_apply]
          _ = rho (delta * epsilon) x.1 := by rw [mul_comm]
          _ = rho delta (rho epsilon x.1) := by
            simp only [map_mul, Module.End.mul_apply]
          _ = rho delta ((chi epsilon : PadicInt p) • x.1) := by
            rw [(mem_characterEigenspace_iff rho chi x.1).mp x.property epsilon]
          _ = (chi epsilon : PadicInt p) • rho delta x.1 :=
            map_smul (rho delta) _ _⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add (rho delta) x.1 y.1
      map_smul' := by
        intro a x
        apply Subtype.ext
        exact map_smul (rho delta) a x.1 }
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f => f x.1) (map_one rho)
  map_mul' delta epsilon := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f => f x.1) (map_mul rho delta epsilon)

/-- Each literal Selmer eigenspace carries the integral p-adic group-algebra
module obtained from its restricted `Delta` representation. -/
noncomputable instance instCharacterEigenspaceGroupAlgebraModule
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta))
    (chi : InvolutiveBase.Character (PadicInt p) Delta) :
    Module (InvolutiveBase.GroupAlgebra (PadicInt p) Delta)
      (characterEigenspace rho chi) :=
  Module.compHom (characterEigenspace rho chi)
    (characterEigenspaceRepresentation rho chi).asAlgebraHom.toRingHom

/-- Embedded group elements act by the original `Delta` action after
coercion to the concrete Selmer subtype. -/
@[simp]
theorem coe_groupElement_smul
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta))
    (chi : InvolutiveBase.Character (PadicInt p) Delta)
    (delta : Delta) (x : characterEigenspace rho chi) :
    ((MonoidAlgebra.of (PadicInt p) Delta delta • x :
      characterEigenspace rho chi) : SelmerCarrier R K p) = rho delta x.1 := by
  have h :
      (MonoidAlgebra.of (PadicInt p) Delta delta • x :
        characterEigenspace rho chi) =
        characterEigenspaceRepresentation rho chi delta x := by
    change ((characterEigenspaceRepresentation rho chi).asAlgebraHom
      (MonoidAlgebra.of (PadicInt p) Delta delta)) x = _
    rw [Representation.asAlgebraHom_of]
  exact congrArg Subtype.val h

/-! ### Named glue through every carrier layer -/

/-- Forget the eigenspace predicate and return to the actual additive Selmer
carrier. -/
def toSeatedCarrier
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta} :
    SelmerChi rho chi →ₗ[PadicInt p] SelmerCarrier R K p :=
  (characterEigenspace rho chi).subtype

/-- The function spelling of the additive carrier inclusion used by the
stage. -/
def toAdditiveSelmer
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta}
    (x : SelmerChi rho chi) : SelmerCarrier R K p :=
  x.1

/-- Remove the additive type tag.  The codomain is definitionally
Mathlib's `IsDedekindDomain.selmerGroup` subtype. -/
def toConcreteSelmer
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta}
    (x : SelmerChi rho chi) :
    IsDedekindDomain.selmerGroup
      (R := R) (K := K)
      (S := (∅ : Set (IsDedekindDomain.HeightOneSpectrum R))) (n := p) :=
  Additive.toMul (toAdditiveSelmer x)

/-- Forget the Selmer predicate and expose the ambient Kummer quotient. -/
def toKummerQuotient
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta}
    (x : SelmerChi rho chi) :
    Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range :=
  (toConcreteSelmer x).1

/-- The fully bundled additive Kummer-class map used by local pairings.  It
is the composition of the literal eigenspace inclusion and the actual
Selmer subgroup inclusion. -/
def toKummerClass
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta} :
    SelmerChi rho chi →+
      Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) :=
  (MonoidHom.toAdditive
    (IsDedekindDomain.selmerGroup
      (R := R) (K := K)
      (S := (∅ : Set (IsDedekindDomain.HeightOneSpectrum R)))
      (n := p)).subtype).comp
    (characterEigenspace rho chi).subtype.toAddMonoidHom

@[simp]
theorem toSeatedCarrier_apply
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta}
    (x : SelmerChi rho chi) :
    toSeatedCarrier x = x.1 :=
  rfl

@[simp]
theorem toAdditiveSelmer_apply
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta}
    (x : SelmerChi rho chi) :
    toAdditiveSelmer x = x.1 :=
  rfl

@[simp]
theorem toConcreteSelmer_apply
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta}
    (x : SelmerChi rho chi) :
    toConcreteSelmer x = Additive.toMul x.1 :=
  rfl

@[simp]
theorem toKummerQuotient_apply
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta}
    (x : SelmerChi rho chi) :
    toKummerQuotient x = (toConcreteSelmer x).1 :=
  rfl

@[simp]
theorem toKummerClass_apply
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta}
    (x : SelmerChi rho chi) :
    toKummerClass x = Additive.ofMul (toKummerQuotient x) :=
  rfl

/-- No information is lost at any of the three carrier-forgetting steps. -/
theorem toAdditiveSelmer_injective
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta} :
    Function.Injective
      (toAdditiveSelmer (rho := rho) (chi := chi)) := by
  intro x y h
  apply Subtype.ext
  exact h

theorem toConcreteSelmer_injective
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta} :
    Function.Injective
      (toConcreteSelmer (rho := rho) (chi := chi)) := by
  intro x y h
  apply toAdditiveSelmer_injective
  exact Additive.toMul.injective h

theorem toKummerQuotient_injective
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta} :
    Function.Injective
      (toKummerQuotient (rho := rho) (chi := chi)) := by
  intro x y h
  apply toConcreteSelmer_injective
  exact Subtype.ext h

/-- The empty-support Selmer predicate becomes an unconditional valuation
receipt at every height-one place.  This is valuation modulo `p`; obtaining
an integer-valuation-zero local representative is a separate normalization
step and is deliberately not asserted here. -/
theorem valuationOfNeZeroMod_eq_one
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta}
    (v : IsDedekindDomain.HeightOneSpectrum R)
    (x : SelmerChi rho chi) :
    v.valuationOfNeZeroMod p (toKummerQuotient x) = 1 :=
  (toConcreteSelmer x).property v (Set.notMem_empty v)

/-- Public form of the elementary residue-class calculation that is private
inside the vendored empty-support exact-sequence proof.  This is useful
beyond this project: valuation one in the multiplicative `ZMod p` target is
exactly divisibility of the additive integer valuation by `p`. -/
theorem valuationOfNeZeroMod_mk_eq_one_iff_dvd
    (v : IsDedekindDomain.HeightOneSpectrum R) (y : Kˣ) :
    v.valuationOfNeZeroMod p
        (y : Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) = 1 ↔
      (p : ℤ) ∣ (v.valuationOfNeZero y).toAdd := by
  change ((v.valuationOfNeZero y).toAdd : ZMod p) = 0 ↔ _
  simpa using
    ZMod.intCast_zmod_eq_zero_iff_dvd (v.valuationOfNeZero y).toAdd p

/-- Every representative of a seated Selmer class has valuation divisible
by `p`.  The representative equality is explicit because a quotient class
does not carry a preferred field element. -/
theorem representative_valuation_dvd
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta}
    (v : IsDedekindDomain.HeightOneSpectrum R)
    (x : SelmerChi rho chi) (y : Kˣ)
    (hy : (y : Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) =
      toKummerQuotient x) :
    (p : ℤ) ∣ (v.valuationOfNeZero y).toAdd := by
  apply (valuationOfNeZeroMod_mk_eq_one_iff_dvd v y).mp
  rw [hy]
  exact valuationOfNeZeroMod_eq_one v x

/-- A canonical (classically chosen) field-unit representative of a seated
Selmer class. -/
noncomputable def quotientRepresentative
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta}
    (x : SelmerChi rho chi) : Kˣ :=
  (toKummerQuotient x).out

/-- The chosen representative maps back to the original Kummer class. -/
theorem quotientRepresentative_mk
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta}
    (x : SelmerChi rho chi) :
    (quotientRepresentative x :
      Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) =
        toKummerQuotient x :=
  QuotientGroup.out_eq' (toKummerQuotient x)

/-- The chosen representative has valuation divisible by `p` at every
height-one place. -/
theorem quotientRepresentative_valuation_dvd
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta}
    (v : IsDedekindDomain.HeightOneSpectrum R)
    (x : SelmerChi rho chi) :
    (p : ℤ) ∣ (v.valuationOfNeZero (quotientRepresentative x)).toAdd :=
  representative_valuation_dvd v x (quotientRepresentative x)
    (quotientRepresentative_mk x)

/-- Existential packaging convenient for downstream local-normalization
records: it supplies one representative, its quotient equality, and its
`p`-divisible valuation receipt together. -/
theorem exists_representative_valuation_dvd
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {chi : InvolutiveBase.Character (PadicInt p) Delta}
    (v : IsDedekindDomain.HeightOneSpectrum R)
    (x : SelmerChi rho chi) :
    ∃ y : Kˣ,
      (y : Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) =
          toKummerQuotient x ∧
        (p : ℤ) ∣ (v.valuationOfNeZero y).toAdd :=
  ⟨quotientRepresentative x, quotientRepresentative_mk x,
    quotientRepresentative_valuation_dvd v x⟩

end Eigenspaces

/-! ## The reflected eigenspace and its explicit duality gap -/

section ReflectedDual

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]

variable {R : Type uR} [CommRing R] [IsDedekindDomain R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The stage's second local Kummer carrier is the actual `chi*` Selmer
eigenspace.  In particular it has the same concrete quotient representatives
and the same integral group-algebra module structure as the primal leg. -/
abbrev DOmegaSelmerChiStar
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta))
    (omega chi : InvolutiveBase.Character (PadicInt p) Delta) :=
  SelmerChiStar rho omega chi

/-- The deliberately named gap between the concrete reflected Kummer
eigenspace and the contravariant character module expected by the abstract
exact-sequence package.  No such equivalence is manufactured: an eventual
arithmetic realization must provide it together with the `hash` adjoint law.
The two fields are statement-for-statement the carrier portion of
`CommonActionStage.ReflectedDualRealization`. -/
structure ReflectedDualCharacterGlue
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta))
    (omega chi : InvolutiveBase.Character (PadicInt p) Delta) where
  carrierDualEquiv :
    DOmegaSelmerChiStar rho omega chi ≃+
      CommonActionStage.SelmerCharacterDual
        (↑(characterEigenspace rho
          (InvolutiveBase.reflectedCharacter omega chi)))
  omegaTwistedAction : ∀ a d,
    carrierDualEquiv (a • d) =
      InvolutiveBase.hash omega a • carrierDualEquiv d

theorem ReflectedDualCharacterGlue.carrierDualEquiv_smul
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta))
    (omega chi : InvolutiveBase.Character (PadicInt p) Delta)
    (glue : ReflectedDualCharacterGlue rho omega chi)
    (a : InvolutiveBase.GroupAlgebra (PadicInt p) Delta)
    (d : DOmegaSelmerChiStar rho omega chi) :
    glue.carrierDualEquiv (a • d) =
      InvolutiveBase.hash omega a • glue.carrierDualEquiv d :=
  glue.omegaTwistedAction a d

/-- The paired type is definitionally the project's existing reflected
Selmer-pair convention, now with both legs concretely seated. -/
abbrev ReflectedSelmerPair
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta))
    (omega chi : InvolutiveBase.Character (PadicInt p) Delta) :=
  LinkingInterfaces.ReflectedSelmerPair
    (SelmerChi rho chi) (DOmegaSelmerChiStar rho omega chi)

end ReflectedDual

end Fermat.Conservation.SelmerEigenspace
