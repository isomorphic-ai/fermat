/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/


/-
# Vendored power-root obstruction generator

This is a faithful port of the generic generator from the Fermat Mathlib
branch `power-root-obstruction`:

* introduction commit:
  `4ea7450c8a5844417866addb7fba766275a1945a`;
* verified integration/head commit:
  `889be7a3fee66e6630d25332a501409fa35d8590`;
* source file: `Mathlib/GroupTheory/PowerRootObstruction.lean`;
* source-file SHA-256:
  `44c80744a6c74bf4793cb45c7289f54512b43e6326c0ef46aac308f9cfb31d25`.

The generator is byte-identical at both commits.  The second commit refactors
`Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean` to instantiate this
generator at the principal-ideal arrow; that integration source has SHA-256
`a6fb493fdaf8686eed654b4b0f7abe84ef14d4198304ef4dcf9f8160c8afd2f6`.

The source uses Mathlib's newer module/export surface.  Fermat pins Mathlib
commit `0531bb79fea20efc9ce6942db46b96be5a919400` on Lean 4.31.0-rc1.  The
complete compatibility delta in this standalone port is:

1. omit the source `module` command and replace `public import` with ordinary
   `import`;
2. replace `@[expose] public noncomputable section` with an ordinary
   `noncomputable section`;
3. omit the export-control-only `@[no_expose]` attribute on `obstruction`;
4. use the pinned name `MonoidHom.restrict` where the source spells
   `MonoidHom.domRestrict`.

There are no declaration, statement, or proof-body improvements.  Apart from
these four compatibility/export deltas and this provenance header, the
source is copied verbatim.
-/

import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Obstructions to extracting roots

Let `f : A →* B` be a homomorphism of commutative groups, and suppose that `B` is freely
factorized over `P`, in the sense that it is multiplicatively equivalent to the additive group of
finitely supported integer-valued functions on `P`. An element of `A / A ^ n` is called divisible
if its image in `B / B ^ n` is trivial. Equivalently, every exponent in the factorization of its
image is divisible by `n`.

For positive `n`, the image in `B` of a divisible representative has a unique `n`-th root. Taking
the class of this root modulo the range of `f` gives an obstruction homomorphism. This file
identifies its kernel with classes coming from `f.ker`, and its range with the `n`-torsion in the
cokernel of `f`.

## Main definitions

* `PowerRoot.Factorization`: a factorization of a commutative group by integer exponents.
* `PowerRoot.divisibleClasses`: the subgroup of classes whose image is an `n`-th power.
* `PowerRoot.root`: the canonical root of the image of a divisible element.
* `PowerRoot.fromKernel`: the map from power classes in the kernel.
* `PowerRoot.obstruction`: the root obstruction in the cokernel.

## Main results

* `PowerRoot.Factorization.isMulTorsionFree`: a factorized group is torsion-free.
* `PowerRoot.root_power`, `PowerRoot.root_mul`, `PowerRoot.root_shift`: the root laws.
* `PowerRoot.fromKernel_injective`: the map from the kernel is injective.
* `PowerRoot.obstruction_ker`: exactness at the divisible classes.
* `PowerRoot.obstruction_range`: the obstruction realizes all `n`-torsion in the cokernel.
-/

noncomputable section

namespace PowerRoot

universe u v w

variable {P : Type u} {A : Type v} {B : Type w}

/-- A factorization of a commutative group over `P` by finitely supported integer exponents. -/
abbrev Factorization (B : Type w) [CommGroup B] (P : Type u) :=
  B ≃* Multiplicative (P →₀ ℤ)

namespace Factorization

variable [CommGroup B]

/-- A commutative group with a factorization by integer exponents is torsion-free. -/
theorem isMulTorsionFree (geometry : Factorization B P) : IsMulTorsionFree B :=
  geometry.injective.isMulTorsionFree geometry.toMonoidHom

end Factorization

variable [CommGroup A] [CommGroup B]

/-- The subgroup of `n`-th powers in a commutative group. -/
abbrev powerSubgroup (G : Type*) [CommGroup G] (n : ℕ) : Subgroup G :=
  (powMonoidHom n : G →* G).range

@[simp]
theorem mem_powerSubgroup {G : Type*} [CommGroup G] {n : ℕ} {x : G} :
    x ∈ powerSubgroup G n ↔ ∃ y : G, y ^ n = x := by
  simp [powerSubgroup, MonoidHom.mem_range, powMonoidHom_apply]

/-- A homomorphism induces a homomorphism between the quotients by `n`-th powers. -/
def mapOnPowerQuotients (f : A →* B) (n : ℕ) :
    A ⧸ powerSubgroup A n →* B ⧸ powerSubgroup B n :=
  QuotientGroup.map (powerSubgroup A n) (powerSubgroup B n) f <| by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, by simp [powMonoidHom_apply]⟩

@[simp]
theorem mapOnPowerQuotients_mk (f : A →* B) (n : ℕ) (x : A) :
    mapOnPowerQuotients f n (QuotientGroup.mk x) = QuotientGroup.mk (f x) :=
  rfl

/-- Elements whose image under `f` is an `n`-th power. -/
def divisibleElements (f : A →* B) (n : ℕ) : Subgroup A :=
  (powerSubgroup B n).comap f

/-- Classes modulo `n`-th powers whose image under `f` is trivial modulo `n`-th powers.

Defining this subgroup as a kernel builds independence of representatives into the definition.
See `Factorization.mk_mem_divisibleClasses_iff` for its coordinate description. -/
def divisibleClasses (f : A →* B) (n : ℕ) : Subgroup (A ⧸ powerSubgroup A n) :=
  (mapOnPowerQuotients f n).ker

namespace Factorization

variable (geometry : Factorization B P) (n : ℕ)

/-- Membership in the subgroup of `n`-th powers is coordinatewise divisibility of exponents. -/
theorem mem_powerSubgroup_iff (b : B) :
    b ∈ powerSubgroup B n ↔ ∀ p : P, (n : ℤ) ∣ (geometry b).toAdd p := by
  constructor
  · rintro ⟨c, rfl⟩ p
    simp only [powMonoidHom_apply, map_pow, toAdd_pow,
      Finsupp.nsmul_apply, Int.nsmul_eq_mul]
    exact dvd_mul_right (n : ℤ) ((geometry c).toAdd p)
  · intro h
    let c : B := geometry.symm <| Multiplicative.ofAdd <|
      (geometry b).toAdd.mapRange (fun z ↦ z.ediv n) (Int.zero_ediv _)
    refine ⟨c, ?_⟩
    apply geometry.injective
    apply Multiplicative.toAdd.injective
    ext p
    simp only [powMonoidHom_apply, map_pow, toAdd_pow, Finsupp.nsmul_apply,
      Int.nsmul_eq_mul, c, geometry.apply_symm_apply]
    rw [mul_comm]
    exact Int.ediv_mul_cancel (h p)

/-- A representative defines a divisible class exactly when its exponents are divisible by `n`.

In particular, the right-hand condition is unchanged if the representative is multiplied by an
`n`-th power. -/
theorem mk_mem_divisibleClasses_iff (f : A →* B) (a : A) :
    (QuotientGroup.mk a : A ⧸ powerSubgroup A n) ∈ divisibleClasses f n ↔
      ∀ p : P, (n : ℤ) ∣ (geometry (f a)).toAdd p := by
  rw [divisibleClasses, MonoidHom.mem_ker, mapOnPowerQuotients_mk,
    QuotientGroup.eq_one_iff, geometry.mem_powerSubgroup_iff]

/-- An element is divisible exactly when all exponents of its image are divisible by `n`. -/
theorem mem_divisibleElements_iff (f : A →* B) (a : A) :
    a ∈ divisibleElements f n ↔ ∀ p : P, (n : ℤ) ∣ (geometry (f a)).toAdd p := by
  rw [divisibleElements, Subgroup.mem_comap, geometry.mem_powerSubgroup_iff]

end Factorization

variable (f : A →* B) (n : ℕ)

/-- The natural surjection from divisible representatives to divisible classes. -/
def toDivisibleClasses : divisibleElements f n →* divisibleClasses f n :=
  ((QuotientGroup.mk' (powerSubgroup A n)).restrict (divisibleElements f n)).codRestrict
    (divisibleClasses f n) fun x ↦ by
      change mapOnPowerQuotients f n (QuotientGroup.mk (x : A)) = 1
      rw [mapOnPowerQuotients_mk, QuotientGroup.eq_one_iff]
      exact x.property

@[simp]
theorem toDivisibleClasses_apply (x : divisibleElements f n) :
    ((toDivisibleClasses f n x : divisibleClasses f n) : A ⧸ powerSubgroup A n) =
      QuotientGroup.mk (x : A) :=
  rfl

/-- Every divisible class has a divisible representative. -/
theorem toDivisibleClasses_surjective : Function.Surjective (toDivisibleClasses f n) := by
  intro x
  let a : A := x.1.out
  have ha : QuotientGroup.mk a = x.1 := QuotientGroup.out_eq' x.1
  have hfa : f a ∈ powerSubgroup B n := by
    rw [← QuotientGroup.eq_one_iff]
    rw [← mapOnPowerQuotients_mk, ha]
    exact x.property
  exact ⟨⟨a, hfa⟩, Subtype.ext ha⟩

section Root

/-- A divisible element has an `n`-th root after applying `f`. -/
theorem exists_root (x : divisibleElements f n) : ∃ b : B, b ^ n = f x := by
  simpa only [divisibleElements, Subgroup.mem_comap, mem_powerSubgroup] using x.property

/-- The canonical `n`-th root of the image of a divisible element, obtained by dividing every
factorization exponent by `n`. -/
def root (geometry : Factorization B P) [Fact <| 0 < n] (x : divisibleElements f n) : B :=
  geometry.symm <| Multiplicative.ofAdd <|
    (geometry (f x)).toAdd.mapRange (fun z ↦ z.ediv n) (Int.zero_ediv _)

/-- The canonical root is an `n`-th root of the image. -/
theorem root_power (geometry : Factorization B P) [Fact <| 0 < n]
    (x : divisibleElements f n) : root f n geometry x ^ n = f x := by
  apply geometry.injective
  apply Multiplicative.toAdd.injective
  ext p
  simp only [root, map_pow, geometry.apply_symm_apply, toAdd_pow, Finsupp.nsmul_apply,
    Int.nsmul_eq_mul]
  rw [mul_comm]
  exact Int.ediv_mul_cancel ((geometry.mem_powerSubgroup_iff n (f x)).mp x.property p)

/-- The canonical root is the unique `n`-th root of the image. -/
theorem root_eq_of_pow_eq (geometry : Factorization B P) [hn : Fact <| 0 < n]
    (x : divisibleElements f n) {b : B} (hb : b ^ n = f x) :
    root f n geometry x = b :=
  (@IsMulTorsionFree.pow_left_injective B _ (Factorization.isMulTorsionFree geometry) n
    (Nat.ne_of_gt hn.out)) ((root_power f n geometry x).trans hb.symm)

@[simp]
theorem root_one (geometry : Factorization B P) [Fact <| 0 < n] :
    root f n geometry (1 : divisibleElements f n) = 1 :=
  root_eq_of_pow_eq (f := f) (n := n) geometry 1 (by simp)

/-- The canonical root is multiplicative. -/
theorem root_mul (geometry : Factorization B P) [Fact <| 0 < n]
    (x y : divisibleElements f n) :
    root f n geometry (x * y) = root f n geometry x * root f n geometry y := by
  apply root_eq_of_pow_eq (f := f) (n := n) geometry
  simp only [mul_pow, root_power, map_mul, Subgroup.coe_mul]

/-- Multiplying a divisible representative by an `n`-th power preserves divisibility. -/
def shift (x : divisibleElements f n) (y : A) : divisibleElements f n :=
  ⟨(x : A) * y ^ n, by
    change f ((x : A) * y ^ n) ∈ powerSubgroup B n
    obtain ⟨b, hb⟩ := exists_root f n x
    refine ⟨b * f y, ?_⟩
    simp only [powMonoidHom_apply, hb, map_mul, map_pow]⟩

@[simp]
theorem coe_shift (x : divisibleElements f n) (y : A) :
    (shift f n x y : A) = x * y ^ n :=
  rfl

/-- Equivariance of the canonical root under changing a representative by an `n`-th power. -/
theorem root_shift (geometry : Factorization B P) [Fact <| 0 < n]
    (x : divisibleElements f n) (y : A) :
    root f n geometry (shift f n x y) = root f n geometry x * f y := by
  apply root_eq_of_pow_eq (f := f) (n := n) geometry
  simp only [mul_pow, root_power, map_mul, map_pow, shift, Subgroup.coe_mk]

/-- The canonical root as a homomorphism on divisible representatives. -/
def rootHom (geometry : Factorization B P) [Fact <| 0 < n] : divisibleElements f n →* B where
  toFun := root f n geometry
  map_one' := root_one (f := f) (n := n) geometry
  map_mul' := root_mul (f := f) (n := n) geometry

@[simp]
theorem rootHom_apply (geometry : Factorization B P) [Fact <| 0 < n]
    (x : divisibleElements f n) :
    rootHom (f := f) (n := n) geometry x = root f n geometry x :=
  rfl

end Root

section FromKernel

/-- The map from power classes in the kernel to divisible classes. -/
def fromKernel :
    (f.ker ⧸ powerSubgroup f.ker n) →* divisibleClasses f n :=
  (mapOnPowerQuotients f.ker.subtype n).codRestrict (divisibleClasses f n) <| by
    intro x
    induction x using QuotientGroup.induction_on with
    | _ x =>
      change mapOnPowerQuotients f n (QuotientGroup.mk (x : A)) = 1
      rw [mapOnPowerQuotients_mk, QuotientGroup.eq_one_iff, x.property]
      exact Subgroup.one_mem _

@[simp]
theorem fromKernel_mk (x : f.ker) :
    ((fromKernel f n (QuotientGroup.mk x) : divisibleClasses f n) :
      A ⧸ powerSubgroup A n) = QuotientGroup.mk (x : A) :=
  rfl

/-- The map from power classes in the kernel is injective. -/
theorem fromKernel_injective (geometry : Factorization B P) [hn : Fact <| 0 < n] :
    Function.Injective (fromKernel f n) := by
  rw [← (fromKernel f n).ker_eq_bot_iff]
  ext q
  constructor
  · intro hq
    change q = 1
    induction q using QuotientGroup.induction_on with
    | _ x =>
      have hxq : (QuotientGroup.mk (x : A) : A ⧸ powerSubgroup A n) = 1 := by
        rw [MonoidHom.mem_ker] at hq
        simpa only [fromKernel_mk, Subgroup.coe_one] using congr_arg Subtype.val hq
      obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff (x : A)).mp hxq
      have hxy : (x : A) = y ^ n := by
        simpa only [powerSubgroup, powMonoidHom_apply] using hy.symm
      have hfy : f y = 1 :=
        (@IsMulTorsionFree.pow_left_injective B _ (Factorization.isMulTorsionFree geometry) n
          (Nat.ne_of_gt hn.out)) <| by
            change (f y) ^ n = (1 : B) ^ n
            rw [← map_pow, ← hxy, x.property, one_pow]
      let y' : f.ker := ⟨y, hfy⟩
      apply (QuotientGroup.eq_one_iff x).mpr
      refine ⟨y', ?_⟩
      apply Subtype.ext
      change y ^ n = (x : A)
      exact hxy.symm
  · rintro rfl
    exact Subgroup.one_mem _

end FromKernel

section Obstruction

variable [hn : Fact <| 0 < n]

private def preObstruction (geometry : Factorization B P) : divisibleElements f n →* B ⧸ f.range :=
  (QuotientGroup.mk' f.range).comp (rootHom (f := f) (n := n) geometry)

private theorem toDivisibleClasses_ker_le_preObstruction_ker (geometry : Factorization B P) :
    (toDivisibleClasses f n).ker ≤ (preObstruction (f := f) (n := n) geometry).ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  have hxq : (QuotientGroup.mk (x : A) : A ⧸ powerSubgroup A n) = 1 :=
    congr_arg Subtype.val hx
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff (x : A)).mp hxq
  have hxy : (x : A) = y ^ n := by
    simpa only [powerSubgroup, powMonoidHom_apply] using hy.symm
  have hshift : x = shift f n (1 : divisibleElements f n) y := by
    apply Subtype.ext
    simpa only [coe_shift, Subgroup.coe_one, one_mul] using hxy
  change (QuotientGroup.mk (root f n geometry x) : B ⧸ f.range) = 1
  rw [hshift, root_shift (f := f) (n := n) geometry,
    root_one (f := f) (n := n) geometry, one_mul, QuotientGroup.eq_one_iff]
  exact ⟨y, rfl⟩

/-- The obstruction to representing a divisible class by an element of `f.ker`. -/
def obstruction (geometry : Factorization B P) : divisibleClasses f n →* B ⧸ f.range :=
  (toDivisibleClasses f n).liftOfSurjective (toDivisibleClasses_surjective f n)
    ⟨preObstruction (f := f) (n := n) geometry,
      toDivisibleClasses_ker_le_preObstruction_ker (f := f) (n := n) geometry⟩

@[simp]
theorem obstruction_toDivisibleClasses (geometry : Factorization B P)
    (x : divisibleElements f n) :
    obstruction (f := f) (n := n) geometry (toDivisibleClasses f n x) =
      QuotientGroup.mk (root f n geometry x) := by
  simp [obstruction, preObstruction]

/-- Exactness at the group of divisible classes. -/
theorem obstruction_ker (geometry : Factorization B P) :
    (obstruction (f := f) (n := n) geometry).ker = (fromKernel f n).range := by
  ext q
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := toDivisibleClasses_surjective f n q
    rw [MonoidHom.mem_ker, obstruction_toDivisibleClasses] at hq
    obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff (root f n geometry x)).mp hq
    let k : f.ker := ⟨(x : A) / y ^ n, by
      change f ((x : A) / y ^ n) = 1
      rw [map_div, map_pow, ← root_power f n geometry x, ← hy]
      rw [div_eq_mul_inv, mul_inv_cancel]⟩
    refine ⟨QuotientGroup.mk k, ?_⟩
    apply Subtype.ext
    rw [fromKernel_mk, toDivisibleClasses_apply]
    apply (QuotientGroup.mk'_eq_mk' (powerSubgroup A n)).mpr
    refine ⟨y ^ n, ⟨y, by simp [powMonoidHom_apply]⟩, ?_⟩
    simp only [k]
    exact div_mul_cancel _ _
  · rintro ⟨q, rfl⟩
    rw [MonoidHom.mem_ker]
    induction q using QuotientGroup.induction_on with
    | _ x =>
      have hroot : root f n geometry
          ⟨(x : A), show f (x : A) ∈ powerSubgroup B n from by
            rw [x.property]
            exact Subgroup.one_mem _⟩ = 1 := by
        apply root_eq_of_pow_eq (f := f) (n := n) geometry
        simpa only [one_pow] using x.property.symm
      have hclasses : fromKernel f n (QuotientGroup.mk x) =
          toDivisibleClasses f n
            ⟨(x : A), show f (x : A) ∈ powerSubgroup B n from by
              rw [x.property]
              exact Subgroup.one_mem _⟩ := by
        apply Subtype.ext
        rw [toDivisibleClasses_apply, fromKernel_mk]
      rw [hclasses, obstruction_toDivisibleClasses, hroot, QuotientGroup.mk_one]

/-- The obstruction realizes precisely the `n`-torsion in the cokernel of `f`. -/
theorem obstruction_range (geometry : Factorization B P) :
    (obstruction (f := f) (n := n) geometry).range =
      (powMonoidHom n : (B ⧸ f.range) →* (B ⧸ f.range)).ker := by
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    obtain ⟨x, rfl⟩ := toDivisibleClasses_surjective f n q
    rw [obstruction_toDivisibleClasses, ← QuotientGroup.mk_pow, root_power,
      QuotientGroup.eq_one_iff]
    exact ⟨x, rfl⟩
  · intro q hq
    induction q using QuotientGroup.induction_on with
    | _ b =>
      rw [MonoidHom.mem_ker, powMonoidHom_apply, ← QuotientGroup.mk_pow,
        QuotientGroup.eq_one_iff] at hq
      obtain ⟨a, ha⟩ := hq
      have hba : b ^ n = f a := ha.symm
      let x : divisibleElements f n := ⟨a, ⟨b, hba⟩⟩
      refine ⟨toDivisibleClasses f n x, ?_⟩
      rw [obstruction_toDivisibleClasses]
      congr 1
      exact root_eq_of_pow_eq (f := f) (n := n) geometry x hba

end Obstruction

end PowerRoot
