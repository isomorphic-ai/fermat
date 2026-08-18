/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Character eigenspaces on Mathlib's Selmer carrier

This file seats the two Selmer types used by the conservation stage on
Mathlib's actual Selmer subgroups.  For arbitrary support `S`, the carrier is
literally

`Additive (IsDedekindDomain.selmerGroup (S := S) (n := p))`.

The original full carrier remains the specialization

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

open scoped BigOperators MonoidAlgebra nonZeroDivisors

noncomputable section

namespace Fermat.Conservation.SelmerEigenspace

open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.InvolutiveBase

universe uR uK uDelta

/-! ## The concrete carriers and their coefficient actions -/

/-- Mathlib's Selmer subgroup at arbitrary support, only changed to additive
notation.  No finiteness hypothesis on `S` is needed for the carrier itself. -/
abbrev SelmerCarrierAt (R : Type uR) (K : Type uK)
    [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum R)) (p : ℕ) :=
  Additive
    (IsDedekindDomain.selmerGroup
      (R := R) (K := K) (S := S) (n := p))

/-- Mathlib's empty-support Selmer subgroup, only changed to additive
notation.  Unfolding this abbreviation exposes the literal
`IsDedekindDomain.selmerGroup` subtype. -/
abbrev SelmerCarrier (R : Type uR) (K : Type uK)
    [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (p : ℕ) :=
  SelmerCarrierAt R K
    (∅ : Set (IsDedekindDomain.HeightOneSpectrum R)) p

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

/-- Every element of the concrete Kummer quotient, hence every supported
Selmer element, is killed by `p`.  The proof is independent of support. -/
theorem p_nsmul_eq_zero
    {S : Set (IsDedekindDomain.HeightOneSpectrum R)}
    (x : SelmerCarrierAt R K S p) : p • x = 0 := by
  apply Additive.toMul.injective
  change (Additive.toMul x) ^ p = 1
  apply Subtype.ext
  change ((Additive.toMul x).1) ^ p = 1
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom p : Kˣ →* Kˣ).range (Additive.toMul x).1
  rw [← hy]
  exact (QuotientGroup.eq_one_iff (y ^ p)).mpr ⟨y, rfl⟩

/-- The canonical `ZMod p`-module structure on every actual supported Selmer
subtype. -/
instance instModuleZMod
    {S : Set (IsDedekindDomain.HeightOneSpectrum R)} :
    Module (ZMod p) (SelmerCarrierAt R K S p) :=
  AddCommGroup.zmodModule (n := p) (G := SelmerCarrierAt R K S p)
    p_nsmul_eq_zero

/-- The integral p-adic coefficient action factors through reduction modulo
`p`, as it must on a group killed by `p`. -/
instance instModulePadicInt
    {S : Set (IsDedekindDomain.HeightOneSpectrum R)} [Fact p.Prime] :
    Module (PadicInt p) (SelmerCarrierAt R K S p) :=
  Module.compHom (SelmerCarrierAt R K S p) PadicInt.toZMod

@[simp]
theorem padicInt_smul_eq_toZMod_smul [Fact p.Prime]
    {S : Set (IsDedekindDomain.HeightOneSpectrum R)}
    (a : PadicInt p) (x : SelmerCarrierAt R K S p) :
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

/-! ## Character eigenspaces at arbitrary support

This is the support-parametric form of the machinery above.  It is kept
separate from the empty-support names so the established conservation stage
continues to elaborate definitionally unchanged while the reflected detector
leg can be relaxed at a finite set of auxiliary places.
-/

section SupportedEigenspaces

variable {R : Type uR} [CommRing R] [IsDedekindDomain R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
  {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  {S : Set (IsDedekindDomain.HeightOneSpectrum R)}

/-- A supplied `Delta` action on Mathlib's literal `S`-relaxed Selmer
subgroup.  Supplying this representation includes the assertion that the
chosen support is stable; no Galois action is manufactured here. -/
abbrev SelmerDeltaRepresentationAt
    (S : Set (IsDedekindDomain.HeightOneSpectrum R)) :=
  Representation (PadicInt p) Delta (SelmerCarrierAt R K S p)

/-- The simultaneous character eigenspace inside the actual supported Selmer
carrier. -/
def characterEigenspaceAt
    (rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (eta : InvolutiveBase.Character (PadicInt p) Delta) :
    Submodule (PadicInt p) (SelmerCarrierAt R K S p) :=
  characterEigenspaceGeneric
    (A := PadicInt p) (G := Delta) (M := SelmerCarrierAt R K S p) rho eta

instance instCharacterEigenspaceAtAddCommGroup
    (rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (eta : InvolutiveBase.Character (PadicInt p) Delta) :
    AddCommGroup (characterEigenspaceAt rho eta) :=
  @Submodule.addCommGroup
    (PadicInt p) (SelmerCarrierAt R K S p) inferInstance inferInstance
      (instModulePadicInt (R := R) (K := K) (p := p) (S := S))
      (characterEigenspaceAt rho eta)

@[simp]
theorem mem_characterEigenspaceAt_iff
    (rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (eta : InvolutiveBase.Character (PadicInt p) Delta)
    (x : SelmerCarrierAt R K S p) :
    x ∈ characterEigenspaceAt rho eta ↔
      ∀ delta : Delta,
        rho delta x = (eta delta : PadicInt p) • x :=
  Iff.rfl

/-! ### The genuine supported character projector -/

section CharacterProjectorAt

variable [Fintype Delta]
  [Invertible (Fintype.card Delta : PadicInt p)]

/-- The character idempotent sends every supported Selmer class into the
corresponding simultaneous eigenspace. -/
theorem characterIdempotent_action_mem_characterEigenspaceAt
    (rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (eta : Character (PadicInt p) Delta)
    (x : SelmerCarrierAt R K S p) :
    rho.asAlgebraHom (characterIdempotent eta) x ∈
      characterEigenspaceAt rho eta := by
  rw [mem_characterEigenspaceAt_iff]
  intro delta
  calc
    rho delta (rho.asAlgebraHom (characterIdempotent eta) x) =
        rho.asAlgebraHom (MonoidAlgebra.of (PadicInt p) Delta delta)
          (rho.asAlgebraHom (characterIdempotent eta) x) := by
      rw [Representation.asAlgebraHom_of]
    _ = rho.asAlgebraHom
          (MonoidAlgebra.of (PadicInt p) Delta delta *
            characterIdempotent eta) x := by
      rw [map_mul]
      rfl
    _ = rho.asAlgebraHom
          ((eta delta : PadicInt p) • characterIdempotent eta) x := by
      rw [groupElement_mul_characterIdempotent]
    _ = (eta delta : PadicInt p) •
          rho.asAlgebraHom (characterIdempotent eta) x := by
      rw [map_smul]
      rfl

/-- The Delta-stable character projector on the literal supported carrier. -/
noncomputable def characterProjectorAt
    (rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (eta : Character (PadicInt p) Delta) :
    SelmerCarrierAt R K S p →ₗ[PadicInt p]
      characterEigenspaceAt rho eta :=
  LinearMap.codRestrict (characterEigenspaceAt rho eta)
    (rho.asAlgebraHom (characterIdempotent eta))
    (characterIdempotent_action_mem_characterEigenspaceAt rho eta)

@[simp]
theorem characterProjectorAt_apply
    (rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (eta : Character (PadicInt p) Delta)
    (x : SelmerCarrierAt R K S p) :
    (characterProjectorAt rho eta x : SelmerCarrierAt R K S p) =
      rho.asAlgebraHom (characterIdempotent eta) x :=
  rfl

/-- The supported character projector fixes every class already lying in
its target character eigenspace. -/
theorem characterProjectorAt_eq_self_of_mem
    (rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (eta : Character (PadicInt p) Delta)
    (x : SelmerCarrierAt R K S p)
    (hx : x ∈ characterEigenspaceAt rho eta) :
    (characterProjectorAt rho eta x : SelmerCarrierAt R K S p) = x := by
  change rho.asAlgebraHom (characterIdempotent eta) x = x
  rw [characterIdempotent, map_smul, map_sum]
  simp only [LinearMap.smul_apply,
    Representation.asAlgebraHom_single]
  rw [mem_characterEigenspaceAt_iff] at hx
  have heach (g : Delta) :
      (((↑((eta g)⁻¹) : PadicInt p) • rho g) :
          Module.End (PadicInt p) (SelmerCarrierAt R K S p)) x = x := by
    change (↑((eta g)⁻¹) : PadicInt p) • rho g x = x
    rw [hx g, ← mul_smul]
    simp
  change ⅟(Fintype.card Delta : PadicInt p) •
      ((∑ g ∈ Finset.univ, (↑((eta g)⁻¹) : PadicInt p) • rho g) x) = x
  rw [LinearMap.sum_apply]
  simp_rw [heach]
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul (PadicInt p), smul_smul,
    invOf_mul_self, one_smul]

/-- Applying the supported character projector twice changes nothing. -/
theorem characterProjectorAt_idempotent
    (rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (eta : Character (PadicInt p) Delta)
    (x : SelmerCarrierAt R K S p) :
    characterProjectorAt rho eta (characterProjectorAt rho eta x).1 =
      characterProjectorAt rho eta x := by
  apply Subtype.ext
  change rho.asAlgebraHom (characterIdempotent eta)
      (rho.asAlgebraHom (characterIdempotent eta) x) =
    rho.asAlgebraHom (characterIdempotent eta) x
  rw [← Module.End.mul_apply, ← map_mul,
    isIdempotentElem_iff.mp (characterIdempotent_isIdempotent eta)]

end CharacterProjectorAt

/-- The supported `eta`-eigenspace. -/
abbrev SelmerChiAt
    (rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (eta : InvolutiveBase.Character (PadicInt p) Delta) :=
  characterEigenspaceAt rho eta

/-- The supported reflected-character eigenspace. -/
abbrev SelmerChiStarAt
    (rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (omega chi : InvolutiveBase.Character (PadicInt p) Delta) :=
  characterEigenspaceAt rho (InvolutiveBase.reflectedCharacter omega chi)

/-- The supplied action restricts to every supported character eigenspace.
Commutativity of `Delta`, rather than empty support, is the load-bearing
hypothesis. -/
def characterEigenspaceRepresentationAt
    (rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (eta : InvolutiveBase.Character (PadicInt p) Delta) :
    Representation (PadicInt p) Delta (characterEigenspaceAt rho eta) where
  toFun delta :=
    { toFun := fun x => ⟨rho delta x.1, by
        rw [mem_characterEigenspaceAt_iff]
        intro epsilon
        calc
          rho epsilon (rho delta x.1) = rho (epsilon * delta) x.1 := by
            simp only [map_mul, Module.End.mul_apply]
          _ = rho (delta * epsilon) x.1 := by rw [mul_comm]
          _ = rho delta (rho epsilon x.1) := by
            simp only [map_mul, Module.End.mul_apply]
          _ = rho delta ((eta epsilon : PadicInt p) • x.1) := by
            rw [(mem_characterEigenspaceAt_iff rho eta x.1).mp
              x.property epsilon]
          _ = (eta epsilon : PadicInt p) • rho delta x.1 :=
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

noncomputable instance instCharacterEigenspaceAtGroupAlgebraModule
    (rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (eta : InvolutiveBase.Character (PadicInt p) Delta) :
    Module (InvolutiveBase.GroupAlgebra (PadicInt p) Delta)
      (characterEigenspaceAt rho eta) :=
  Module.compHom (characterEigenspaceAt rho eta)
    (characterEigenspaceRepresentationAt rho eta).asAlgebraHom.toRingHom

/-- Forget the supported eigenspace predicate. -/
def toSupportedCarrier
    {rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta} :
    SelmerChiAt rho eta →ₗ[PadicInt p] SelmerCarrierAt R K S p :=
  (characterEigenspaceAt rho eta).subtype

/-- Remove the additive tag and expose Mathlib's literal supported Selmer
subtype. -/
def toConcreteSelmerAt
    {rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (x : SelmerChiAt rho eta) :
    IsDedekindDomain.selmerGroup
      (R := R) (K := K) (S := S) (n := p) :=
  Additive.toMul x.1

/-- Forget the supported Selmer predicate and expose the ambient Kummer
quotient. -/
def toKummerQuotientAt
    {rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (x : SelmerChiAt rho eta) :
    Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range :=
  (toConcreteSelmerAt x).1

/-- The supported eigenspace inclusion into the additive Kummer quotient. -/
def toKummerClassAt
    {rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta} :
    SelmerChiAt rho eta →+
      Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) :=
  (MonoidHom.toAdditive
    (IsDedekindDomain.selmerGroup
      (R := R) (K := K) (S := S) (n := p)).subtype).comp
    (characterEigenspaceAt rho eta).subtype.toAddMonoidHom

@[simp]
theorem toKummerClassAt_apply
    {rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (x : SelmerChiAt rho eta) :
    toKummerClassAt x = Additive.ofMul (toKummerQuotientAt x) :=
  rfl

/-- A canonical representative of a supported Kummer class.  Choosing the
representative is support-independent; only its valuation receipts depend on
whether a place lies outside `S`. -/
noncomputable def quotientRepresentativeAt
    {rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (x : SelmerChiAt rho eta) : Kˣ :=
  (toKummerQuotientAt x).out

theorem quotientRepresentativeAt_mk
    {rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (x : SelmerChiAt rho eta) :
    (quotientRepresentativeAt x :
      Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) =
        toKummerQuotientAt x :=
  QuotientGroup.out_eq' (toKummerQuotientAt x)

/-- Supported Selmer membership gives valuation one modulo `p` precisely
away from the relaxed support. -/
theorem valuationOfNeZeroMod_eq_one_of_not_mem
    {rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (v : IsDedekindDomain.HeightOneSpectrum R) (hv : v ∉ S)
    (x : SelmerChiAt rho eta) :
    v.valuationOfNeZeroMod p (toKummerQuotientAt x) = 1 :=
  (toConcreteSelmerAt x).property v hv

/-- Hence every chosen representative has `p`-divisible valuation away
from the relaxed support.  No receipt is asserted on `S`. -/
theorem quotientRepresentativeAt_valuation_dvd_of_not_mem
    {rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (v : IsDedekindDomain.HeightOneSpectrum R) (hv : v ∉ S)
    (x : SelmerChiAt rho eta) :
    (p : ℤ) ∣
      (v.valuationOfNeZero (quotientRepresentativeAt x)).toAdd := by
  apply (valuationOfNeZeroMod_mk_eq_one_iff_dvd v
    (quotientRepresentativeAt x)).mp
  rw [quotientRepresentativeAt_mk]
  exact valuationOfNeZeroMod_eq_one_of_not_mem v hv x

/-- Mathlib's supported Selmer valuation, in additive coordinates.  This is
the canonical localization map on the relaxed carrier, not a supplied local
functional. -/
def supportValuation :
    SelmerCarrierAt R K S p →+ (S → ZMod p) :=
  AddMonoidHom.pi fun v =>
    MonoidHom.toAdditive <|
      (Pi.evalMonoidHom (fun _ : S => Multiplicative (ZMod p)) v).comp
        (IsDedekindDomain.selmerGroup.valuation
          (R := R) (K := K) (S := S) (n := p))

/-- One coordinate of supported Selmer localization. -/
def supportValuationAt (v : S) :
    SelmerCarrierAt R K S p →+ ZMod p :=
  MonoidHom.toAdditive <|
    (Pi.evalMonoidHom (fun _ : S => Multiplicative (ZMod p)) v).comp
      (IsDedekindDomain.selmerGroup.valuation
        (R := R) (K := K) (S := S) (n := p))

@[simp]
theorem supportValuation_apply
    (x : SelmerCarrierAt R K S p) (v : S) :
    supportValuation x v = supportValuationAt v x :=
  rfl

/-- The canonical inclusion of empty-support Selmer classes into the
`S`-relaxed carrier. -/
def emptySupportInclusion :
    SelmerCarrier R K p →+ SelmerCarrierAt R K S p :=
  MonoidHom.toAdditive <|
    Subgroup.inclusion <|
      IsDedekindDomain.selmerGroup.monotone
        (R := R) (K := K) (n := p) (Set.empty_subset S)

/-- Empty-support classes have zero localization in every newly relaxed
coordinate. -/
theorem supportValuation_emptySupportInclusion_eq_zero
    (x : SelmerCarrier R K p) :
    supportValuation (emptySupportInclusion (S := S) x) = 0 := by
  ext v
  change Multiplicative.toAdd
      (v.1.valuationOfNeZeroMod p (Additive.toMul x).1) = 0
  exact congrArg Multiplicative.toAdd
    ((Additive.toMul x).property v.1 (Set.notMem_empty v.1))

/-- Additive spelling of Mathlib's `selmerGroup.valuation_ker_eq`: the
kernel of finite-support localization is exactly the image of the original
empty-support carrier.  This settles the kernel bookkeeping at the current
pin; it says nothing about the localization image or cokernel. -/
theorem supportValuation_ker_eq_range_emptySupportInclusion :
    AddMonoidHom.ker (supportValuation (R := R) (K := K) (p := p) (S := S)) =
      AddMonoidHom.range (emptySupportInclusion
        (R := R) (K := K) (p := p) (S := S)) := by
  ext x
  constructor
  · intro hx
    rw [AddMonoidHom.mem_ker] at hx
    let y : SelmerCarrier R K p := Additive.ofMul
      ⟨(Additive.toMul x).1, by
        intro v _
        by_cases hv : v ∈ S
        · have hcoord := congrFun hx ⟨v, hv⟩
          change Multiplicative.toAdd
              (v.valuationOfNeZeroMod p (Additive.toMul x).1) = 0 at hcoord
          exact Multiplicative.toAdd.injective hcoord
        · exact (Additive.toMul x).property v hv⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    rw [AddMonoidHom.mem_ker]
    exact supportValuation_emptySupportInclusion_eq_zero y

/-- Localization restricted to one supported character eigenspace. -/
def eigenspaceSupportValuation
    (rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (eta : InvolutiveBase.Character (PadicInt p) Delta) :
    SelmerChiAt rho eta →+ (S → ZMod p) :=
  supportValuation.comp
    (characterEigenspaceAt rho eta).subtype.toAddMonoidHom

/-- One localization coordinate on a supported character eigenspace. -/
def eigenspaceSupportValuationAt
    (rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (eta : InvolutiveBase.Character (PadicInt p) Delta)
    (v : S) : SelmerChiAt rho eta →+ ZMod p :=
  supportValuationAt v |>.comp
    (characterEigenspaceAt rho eta).subtype.toAddMonoidHom

@[simp]
theorem eigenspaceSupportValuation_apply
    (rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (eta : InvolutiveBase.Character (PadicInt p) Delta)
    (x : SelmerChiAt rho eta) (v : S) :
    eigenspaceSupportValuation rho eta x v =
      eigenspaceSupportValuationAt rho eta v x :=
  rfl

/-- The stage's q-relaxed reflected dual spelling. -/
abbrev DOmegaSelmerChiStarAt
    (rho : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (omega chi : InvolutiveBase.Character (PadicInt p) Delta) :=
  SelmerChiStarAt rho omega chi

end SupportedEigenspaces

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
