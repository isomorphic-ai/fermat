/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI Codex
-/

import Fermat.Experiments.Conservation.PowerRootObstruction

/-!
# Naturality of the power-root obstruction

The generic `PowerRoot` construction starts from a homomorphism of
commutative groups.  In the principal-ideal application this is the arrow
from nonzero field elements to nonzero fractional ideals.  This file records
the functoriality that follows from a commuting square of such arrows.

There are three named faces:

* `GroupRingEquivariance` records equivariance for the group elements which
  form the basis of a group ring.  Linear extension to a particular group
  ring is deliberately not claimed by this multiplicative generic API.
* `ReflectionInterface` records the sharp/reflected square, allowing the two
  arrows to have different carrier types (as character and reflected-character
  pieces generally do).
* `LocalizationInterface` records the global-to-local principal-arrow square.
  It does not assert that the needed local Selmer or factorization carrier
  exists.  When both factorized arrows are supplied, `obstruction_square`
  proves the PowerRoot face; otherwise `ObstructionSquareLaw` is the exact
  named law an eventual local carrier must satisfy.

The proofs use the generator's characterization of roots, and expose
`root_mul` and `root_shift` explicitly as the multiplicative and
change-of-representative engines.  No arithmetic instance and no splitting
of a Selmer extension is introduced here.
-/

noncomputable section

namespace Fermat.Conservation.PowerRootNaturality

universe uP uQ uA uB uC uD uDelta

open PowerRoot

variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
  [CommGroup A] [CommGroup B] [CommGroup C] [CommGroup D]

/-! ## A commuting square of power-root arrows -/

/-- A morphism between two arrows of commutative groups.

`preserves_arrow` is precisely the square
`targetMap ∘ f = g ∘ sourceMap`.  No injectivity, surjectivity, or
arithmetic interpretation of either vertical map is included. -/
structure ArrowMorphism (f : A →* B) (g : C →* D) where
  sourceMap : A →* C
  targetMap : B →* D
  preserves_arrow : ∀ a : A, targetMap (f a) = g (sourceMap a)

namespace ArrowMorphism

variable {f : A →* B} {g : C →* D} (square : ArrowMorphism f g)

/-- Two arrow morphisms are equal when their source and target maps are
equal; the commuting-square witness is proof-irrelevant. -/
@[ext]
theorem ext {left right : ArrowMorphism f g}
    (source_eq : left.sourceMap = right.sourceMap)
    (target_eq : left.targetMap = right.targetMap) : left = right := by
  cases left
  cases right
  cases source_eq
  cases target_eq
  rfl

/-- The identity commuting square. -/
def identity (f : A →* B) : ArrowMorphism f f where
  sourceMap := MonoidHom.id A
  targetMap := MonoidHom.id B
  preserves_arrow := fun _ ↦ rfl

/-- Vertical composition of commuting arrow squares.  The `outer` square is
applied after the `inner` square. -/
def comp {E F : Type*} [CommGroup E] [CommGroup F] {h : E →* F}
    (outer : ArrowMorphism g h) (inner : ArrowMorphism f g) :
    ArrowMorphism f h where
  sourceMap := outer.sourceMap.comp inner.sourceMap
  targetMap := outer.targetMap.comp inner.targetMap
  preserves_arrow := fun a ↦ by
    change outer.targetMap (inner.targetMap (f a)) =
      h (outer.sourceMap (inner.sourceMap a))
    rw [inner.preserves_arrow, outer.preserves_arrow]

@[simp]
theorem identity_sourceMap_apply (a : A) :
    (identity f).sourceMap a = a :=
  rfl

@[simp]
theorem identity_targetMap_apply (b : B) :
    (identity f).targetMap b = b :=
  rfl

@[simp]
theorem comp_sourceMap_apply {E F : Type*} [CommGroup E] [CommGroup F]
    {h : E →* F}
    (outer : ArrowMorphism g h) (inner : ArrowMorphism f g) (a : A) :
    (outer.comp inner).sourceMap a = outer.sourceMap (inner.sourceMap a) :=
  rfl

@[simp]
theorem comp_targetMap_apply {E F : Type*} [CommGroup E] [CommGroup F]
    {h : E →* F}
    (outer : ArrowMorphism g h) (inner : ArrowMorphism f g) (b : B) :
    (outer.comp inner).targetMap b = outer.targetMap (inner.targetMap b) :=
  rfl

/-- Composition specialized to endomorphisms of one arrow. -/
private def endomorphismComp {f : A →* B}
    (outer inner : ArrowMorphism f f) : ArrowMorphism f f where
  sourceMap := outer.sourceMap.comp inner.sourceMap
  targetMap := outer.targetMap.comp inner.targetMap
  preserves_arrow := fun a ↦ by
    change outer.targetMap (inner.targetMap (f a)) =
      f (outer.sourceMap (inner.sourceMap a))
    rw [inner.preserves_arrow, outer.preserves_arrow]

/-- Endomorphisms of one arrow form a monoid under vertical composition.
Thus an arithmetic action can honestly be supplied as a monoid homomorphism
into `ArrowMorphism f f`. -/
instance endomorphismMonoid (f : A →* B) : Monoid (ArrowMorphism f f) where
  one := identity f
  mul := endomorphismComp
  one_mul square := by
    apply ext
    · ext a
      change square.sourceMap a = square.sourceMap a
      rfl
    · ext b
      change square.targetMap b = square.targetMap b
      rfl
  mul_one square := by
    apply ext
    · ext a
      change square.sourceMap a = square.sourceMap a
      rfl
    · ext b
      change square.targetMap b = square.targetMap b
      rfl
  mul_assoc first second third := by
    apply ext
    · ext a
      change first.sourceMap (second.sourceMap (third.sourceMap a)) =
        first.sourceMap (second.sourceMap (third.sourceMap a))
      rfl
    · ext b
      change first.targetMap (second.targetMap (third.targetMap b)) =
        first.targetMap (second.targetMap (third.targetMap b))
      rfl

@[simp]
theorem one_sourceMap_apply {f : A →* B} (a : A) :
    (1 : ArrowMorphism f f).sourceMap a = a :=
  rfl

@[simp]
theorem one_targetMap_apply {f : A →* B} (b : B) :
    (1 : ArrowMorphism f f).targetMap b = b :=
  rfl

@[simp]
theorem mul_sourceMap_apply {f : A →* B}
    (outer inner : ArrowMorphism f f) (a : A) :
    (outer * inner).sourceMap a =
      outer.sourceMap (inner.sourceMap a) :=
  rfl

@[simp]
theorem mul_targetMap_apply {f : A →* B}
    (outer inner : ArrowMorphism f f) (b : B) :
    (outer * inner).targetMap b =
      outer.targetMap (inner.targetMap b) :=
  rfl

/-- Monoid multiplication is the generic vertical composition. -/
theorem mul_eq_comp {f : A →* B}
    (outer inner : ArrowMorphism f f) :
    outer * inner =
      ArrowMorphism.comp (f := f) (g := f) (h := f) outer inner := by
  apply ext
  · rfl
  · rfl

/-- The square commutes after passage to power quotients. -/
theorem mapOnPowerQuotients_natural (n : ℕ)
    (q : A ⧸ powerSubgroup A n) :
    mapOnPowerQuotients g n (mapOnPowerQuotients square.sourceMap n q) =
      mapOnPowerQuotients square.targetMap n (mapOnPowerQuotients f n q) := by
  induction q using QuotientGroup.induction_on with
  | _ a =>
      simp only [mapOnPowerQuotients_mk]
      exact congrArg QuotientGroup.mk (square.preserves_arrow a).symm

/-- A commuting arrow square sends divisible representatives to divisible
representatives. -/
def mapDivisibleElements (n : ℕ) :
    divisibleElements f n →* divisibleElements g n where
  toFun x := ⟨square.sourceMap x, by
    obtain ⟨b, hb⟩ := x.property
    refine ⟨square.targetMap b, ?_⟩
    calc
      square.targetMap b ^ n = square.targetMap (b ^ n) :=
        (map_pow square.targetMap b n).symm
      _ = square.targetMap (f x) := congrArg square.targetMap hb
      _ = g (square.sourceMap x) := square.preserves_arrow x⟩
  map_one' := by
    apply Subtype.ext
    exact map_one square.sourceMap
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul square.sourceMap (x : A) (y : A)

@[simp]
theorem mapDivisibleElements_apply (n : ℕ) (x : divisibleElements f n) :
    ((square.mapDivisibleElements n x : divisibleElements g n) : C) =
      square.sourceMap x :=
  rfl

/-- A commuting arrow square sends divisible power classes to divisible
power classes. -/
def mapDivisibleClasses (n : ℕ) :
    divisibleClasses f n →* divisibleClasses g n :=
  ((mapOnPowerQuotients square.sourceMap n).restrict
      (divisibleClasses f n)).codRestrict (divisibleClasses g n) fun x ↦ by
    change mapOnPowerQuotients g n
      (mapOnPowerQuotients square.sourceMap n x) = 1
    rw [square.mapOnPowerQuotients_natural]
    rw [(MonoidHom.mem_ker.mp x.property), map_one]

@[simp]
theorem mapDivisibleClasses_apply_coe (n : ℕ) (x : divisibleClasses f n) :
    ((square.mapDivisibleClasses n x : divisibleClasses g n) :
        C ⧸ powerSubgroup C n) =
      mapOnPowerQuotients square.sourceMap n x :=
  rfl

/-- Mapping a divisible representative and then taking its class is the
same as first taking its class and then mapping it. -/
@[simp]
theorem mapDivisibleClasses_toDivisibleClasses (n : ℕ)
    (x : divisibleElements f n) :
    square.mapDivisibleClasses n (toDivisibleClasses f n x) =
      toDivisibleClasses g n (square.mapDivisibleElements n x) := by
  apply Subtype.ext
  rfl

/-- The target map descends to the cokernels of the two arrows. -/
def mapCokernel : B ⧸ f.range →* D ⧸ g.range :=
  QuotientGroup.map f.range g.range square.targetMap fun _ hb ↦ by
    obtain ⟨a, rfl⟩ := hb
    exact ⟨square.sourceMap a, (square.preserves_arrow a).symm⟩

@[simp]
theorem mapCokernel_mk (b : B) :
    square.mapCokernel (QuotientGroup.mk b) =
      QuotientGroup.mk (square.targetMap b) :=
  rfl

section Factorized

variable {P : Type uP} {Q : Type uQ} {n : ℕ} [Fact <| 0 < n]

/-- Canonical roots are natural for a commuting square between factorized
arrows.  Compatibility between chosen factorization coordinates is not
needed: torsion-freeness makes an `n`-th root unique. -/
theorem root_natural (sourceGeometry : Factorization B P)
    (targetGeometry : Factorization D Q) (x : divisibleElements f n) :
    root g n targetGeometry (square.mapDivisibleElements n x) =
      square.targetMap (root f n sourceGeometry x) := by
  apply root_eq_of_pow_eq (f := g) (n := n) targetGeometry
  calc
    square.targetMap (root f n sourceGeometry x) ^ n =
        square.targetMap (root f n sourceGeometry x ^ n) :=
      (map_pow square.targetMap (root f n sourceGeometry x) n).symm
    _ = square.targetMap (f x) :=
      congrArg square.targetMap (root_power f n sourceGeometry x)
    _ = g (square.sourceMap x) := square.preserves_arrow x

/-- Multiplicative root naturality, exposing `PowerRoot.root_mul` as the
engine rather than silently treating the root choice as arbitrary. -/
theorem root_mul_natural (sourceGeometry : Factorization B P)
    (targetGeometry : Factorization D Q) (x y : divisibleElements f n) :
    root g n targetGeometry (square.mapDivisibleElements n (x * y)) =
      square.targetMap (root f n sourceGeometry x) *
        square.targetMap (root f n sourceGeometry y) := by
  rw [square.root_natural sourceGeometry targetGeometry,
    root_mul (f := f) (n := n) sourceGeometry, map_mul]

end Factorized

/-- Mapping commutes with changing a representative by an `n`-th power. -/
@[simp]
theorem mapDivisibleElements_shift {n : ℕ}
    (x : divisibleElements f n) (y : A) :
    square.mapDivisibleElements n (shift f n x y) =
      shift g n (square.mapDivisibleElements n x) (square.sourceMap y) := by
  apply Subtype.ext
  simp only [mapDivisibleElements_apply, coe_shift, map_mul, map_pow]

section Factorized

variable {P : Type uP} {Q : Type uQ} {n : ℕ} [Fact <| 0 < n]

/-- Change-of-representative naturality, exposing `PowerRoot.root_shift` as
the engine.  The final factor is transported through the arrow square. -/
theorem root_shift_natural (sourceGeometry : Factorization B P)
    (targetGeometry : Factorization D Q) (x : divisibleElements f n) (y : A) :
    root g n targetGeometry
        (square.mapDivisibleElements n (shift f n x y)) =
      square.targetMap (root f n sourceGeometry x) *
        g (square.sourceMap y) := by
  rw [square.root_natural sourceGeometry targetGeometry,
    root_shift (f := f) (n := n) sourceGeometry, map_mul,
    square.preserves_arrow]

/-- The PowerRoot obstruction is natural for a commuting square between
factorized arrows. -/
theorem obstruction_natural (sourceGeometry : Factorization B P)
    (targetGeometry : Factorization D Q) (q : divisibleClasses f n) :
    obstruction (f := g) (n := n) targetGeometry
        (square.mapDivisibleClasses n q) =
      square.mapCokernel (obstruction (f := f) (n := n) sourceGeometry q) := by
  obtain ⟨x, rfl⟩ := toDivisibleClasses_surjective f n q
  rw [square.mapDivisibleClasses_toDivisibleClasses,
    obstruction_toDivisibleClasses, obstruction_toDivisibleClasses,
    square.mapCokernel_mk, square.root_natural sourceGeometry targetGeometry]

end Factorized

end ArrowMorphism

/-! ## Group-ring / Delta direction -/

section GroupRing

variable {Delta : Type uDelta} [Group Delta]
  [MulDistribMulAction Delta A] [MulDistribMulAction Delta B]

/-- Equivariance of the principal arrow under the Delta action.

This is the honest generic content of the group-ring direction: equivariance
for every group-like basis element.  Extending it linearly to a chosen group
ring requires additive/module carriers and is not part of this
multiplicative interface. -/
structure GroupRingEquivariance (f : A →* B) : Prop where
  map_smul : ∀ (delta : Delta) (a : A), f (delta • a) = delta • f a

namespace GroupRingEquivariance

variable {f : A →* B} (equivariance : GroupRingEquivariance (Delta := Delta) f)

private def actionHomSource (delta : Delta) : A →* A where
  toFun := fun a ↦ delta • a
  map_one' := smul_one delta
  map_mul' := smul_mul' delta

private def actionHomTarget (delta : Delta) : B →* B where
  toFun := fun b ↦ delta • b
  map_one' := smul_one delta
  map_mul' := smul_mul' delta

/-- The arrow square belonging to one Delta basis element. -/
def arrowMorphism (delta : Delta) : ArrowMorphism f f where
  sourceMap := actionHomSource delta
  targetMap := actionHomTarget delta
  preserves_arrow := fun a ↦ (equivariance.map_smul delta a).symm

@[simp]
theorem arrowMorphism_one :
    equivariance.arrowMorphism (1 : Delta) = 1 := by
  apply ArrowMorphism.ext
  · ext a
    exact one_smul Delta a
  · ext b
    exact one_smul Delta b

@[simp]
theorem arrowMorphism_mul (delta epsilon : Delta) :
    equivariance.arrowMorphism (delta * epsilon) =
      equivariance.arrowMorphism delta * equivariance.arrowMorphism epsilon := by
  apply ArrowMorphism.ext
  · ext a
    exact mul_smul delta epsilon a
  · ext b
    exact mul_smul delta epsilon b

/-- The Delta action as a genuine multiplicative action on the principal
arrow.  This is the basis-action object that may underlie a group-ring
action once appropriate additive module carriers are supplied. -/
def action : Delta →* ArrowMorphism f f where
  toFun := equivariance.arrowMorphism
  map_one' := equivariance.arrowMorphism_one
  map_mul' := equivariance.arrowMorphism_mul

@[simp]
theorem action_apply (delta : Delta) :
    equivariance.action delta = equivariance.arrowMorphism delta :=
  rfl

/-- Delta acts on divisible classes through the induced arrow square. -/
def actOnDivisibleClasses (n : ℕ) (delta : Delta) :
    divisibleClasses f n →* divisibleClasses f n :=
  (equivariance.arrowMorphism delta).mapDivisibleClasses n

/-- Delta acts on the obstruction target through the induced arrow square. -/
def actOnCokernel (delta : Delta) : B ⧸ f.range →* B ⧸ f.range :=
  (equivariance.arrowMorphism delta).mapCokernel

variable {P : Type uP} {n : ℕ} [Fact <| 0 < n]

/-- The canonical root is Delta-equivariant. -/
theorem root_equivariant (geometry : Factorization B P) (delta : Delta)
    (x : divisibleElements f n) :
    root f n geometry
        ((equivariance.arrowMorphism delta).mapDivisibleElements n x) =
      delta • root f n geometry x :=
  (equivariance.arrowMorphism delta).root_natural geometry geometry x

/-- The obstruction square is Delta-equivariant, basis element by basis
element. -/
theorem obstruction_equivariant (geometry : Factorization B P)
    (delta : Delta) (x : divisibleClasses f n) :
    obstruction (f := f) (n := n) geometry
        (equivariance.actOnDivisibleClasses n delta x) =
      equivariance.actOnCokernel delta
        (obstruction (f := f) (n := n) geometry x) :=
  (equivariance.arrowMorphism delta).obstruction_natural geometry geometry x

end GroupRingEquivariance

end GroupRing

/-! ## Reflection direction -/

/-- A reflected/sharp square between two principal arrows.

The source and target are equivalences, so the interface can connect a
character carrier to a genuinely different reflected-character carrier.
No identification of those carriers is made. -/
structure ReflectionInterface (f : A →* B) (fSharp : C →* D) where
  sourceSharp : A ≃* C
  targetSharp : B ≃* D
  preserves_principal_arrow :
    ∀ a : A, targetSharp (f a) = fSharp (sourceSharp a)

namespace ReflectionInterface

variable {f : A →* B} {fSharp : C →* D}
  (reflection : ReflectionInterface f fSharp)

/-- The forward sharp square. -/
def toArrowMorphism : ArrowMorphism f fSharp where
  sourceMap := reflection.sourceSharp.toMonoidHom
  targetMap := reflection.targetSharp.toMonoidHom
  preserves_arrow := reflection.preserves_principal_arrow

/-- The inverse reflected square, derived from the equivalences rather than
postulated as unrelated data. -/
def symmArrowMorphism : ArrowMorphism fSharp f where
  sourceMap := reflection.sourceSharp.symm.toMonoidHom
  targetMap := reflection.targetSharp.symm.toMonoidHom
  preserves_arrow := fun c ↦ by
    apply reflection.targetSharp.injective
    simpa using
      (reflection.preserves_principal_arrow
        (reflection.sourceSharp.symm c)).symm

/-- Reflection of divisible classes. -/
def reflectDivisibleClasses (n : ℕ) :
    divisibleClasses f n →* divisibleClasses fSharp n :=
  reflection.toArrowMorphism.mapDivisibleClasses n

/-- Reflection on the obstruction target. -/
def reflectCokernel : B ⧸ f.range →* D ⧸ fSharp.range :=
  reflection.toArrowMorphism.mapCokernel

variable {P : Type uP} {Q : Type uQ} {n : ℕ} [Fact <| 0 < n]

/-- Canonical roots commute with reflection. -/
theorem root_reflection (geometry : Factorization B P)
    (sharpGeometry : Factorization D Q) (x : divisibleElements f n) :
    root fSharp n sharpGeometry
        (reflection.toArrowMorphism.mapDivisibleElements n x) =
      reflection.targetSharp (root f n geometry x) :=
  reflection.toArrowMorphism.root_natural geometry sharpGeometry x

/-- The reflected PowerRoot obstruction square commutes. -/
theorem obstruction_reflection (geometry : Factorization B P)
    (sharpGeometry : Factorization D Q) (x : divisibleClasses f n) :
    obstruction (f := fSharp) (n := n) sharpGeometry
        (reflection.reflectDivisibleClasses n x) =
      reflection.reflectCokernel
        (obstruction (f := f) (n := n) geometry x) :=
  reflection.toArrowMorphism.obstruction_natural geometry sharpGeometry x

end ReflectionInterface

/-! ## Localization direction -/

/-- The global-to-local square for one place.

This structure only names the two localization maps and requires them to
preserve the principal arrow.  In particular, it does not manufacture a
local Selmer group, a completion, or a factorization of the local target. -/
structure LocalizationInterface (globalArrow : A →* B)
    (localArrow : C →* D) where
  localizeSource : A →* C
  localizeTarget : B →* D
  preserves_principal_arrow :
    ∀ a : A, localizeTarget (globalArrow a) = localArrow (localizeSource a)

namespace LocalizationInterface

variable {globalArrow : A →* B} {localArrow : C →* D}
  (localization : LocalizationInterface globalArrow localArrow)

/-- Localization as a commuting arrow morphism. -/
def toArrowMorphism : ArrowMorphism globalArrow localArrow where
  sourceMap := localization.localizeSource
  targetMap := localization.localizeTarget
  preserves_arrow := localization.preserves_principal_arrow

/-- Localization on divisible power classes. -/
def localizeDivisibleClasses (n : ℕ) :
    divisibleClasses globalArrow n →* divisibleClasses localArrow n :=
  localization.toArrowMorphism.mapDivisibleClasses n

/-- Localization on the obstruction cokernel. -/
def localizeCokernel : B ⧸ globalArrow.range →* D ⧸ localArrow.range :=
  localization.toArrowMorphism.mapCokernel

/-- The exact obstruction-square law for an abstract pair of global and
local obstruction maps.  This is a proposition, not bundled evidence and
not an assertion that the missing local arithmetic carriers exist. -/
def ObstructionSquareLaw (n : ℕ)
    (globalObstruction :
      divisibleClasses globalArrow n →* B ⧸ globalArrow.range)
    (localObstruction :
      divisibleClasses localArrow n →* D ⧸ localArrow.range) : Prop :=
  ∀ x, localObstruction (localization.localizeDivisibleClasses n x) =
    localization.localizeCokernel (globalObstruction x)

variable {P : Type uP} {Q : Type uQ} {n : ℕ} [Fact <| 0 < n]

/-- Local obstruction after localization.  This is the left route in the
PowerRoot naturality face. -/
def localObstructionAfterLocalization (localGeometry : Factorization D Q) :
    divisibleClasses globalArrow n →
      D ⧸ localArrow.range :=
  fun x ↦ obstruction (f := localArrow) (n := n) localGeometry
    (localization.localizeDivisibleClasses n x)

/-- Localization after global obstruction.  This is the right route in the
PowerRoot naturality face. -/
def localizationAfterGlobalObstruction (globalGeometry : Factorization B P) :
    divisibleClasses globalArrow n →
      D ⧸ localArrow.range :=
  fun x ↦ localization.localizeCokernel
    (obstruction (f := globalArrow) (n := n) globalGeometry x)

/-- Once both factorized carriers really exist, the localization obstruction
square commutes. -/
theorem obstruction_square (globalGeometry : Factorization B P)
    (localGeometry : Factorization D Q) (x : divisibleClasses globalArrow n) :
    localization.localObstructionAfterLocalization localGeometry x =
      localization.localizationAfterGlobalObstruction globalGeometry x :=
  localization.toArrowMorphism.obstruction_natural globalGeometry localGeometry x

/-- The canonical PowerRoot maps satisfy the named localization law whenever
both factorized carriers have actually been supplied. -/
theorem powerRootObstructionSquareLaw (globalGeometry : Factorization B P)
    (localGeometry : Factorization D Q) :
    localization.ObstructionSquareLaw n
      (obstruction (f := globalArrow) (n := n) globalGeometry)
      (obstruction (f := localArrow) (n := n) localGeometry) :=
  fun x ↦ localization.obstruction_square globalGeometry localGeometry x

end LocalizationInterface

end Fermat.Conservation.PowerRootNaturality
