/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Fabian Franz

# Vendored generic derivation of the finite-S Selmer unit-class sequence

This is a faithful port of the generic power-root derivations of the
empty-support and finite-`S` Selmer unit-class sequences from our Mathlib
branches `power-root-obstruction` and `finite-s-selmer`:

* fork pull-request series:
  `https://github.com/fabianx-ai/mathlib4/pull/1` and
  `https://github.com/fabianx-ai/mathlib4/pull/2`;
* generator introduction commit:
  `4ea7450c8a5844417866addb7fba766275a1945a`;
* empty-support integration commit:
  `889be7a3fee66e6630d25332a501409fa35d8590`;
* finite-`S` branch and source commit:
  `finite-s-selmer` at
  `9ec933d5176915dc6996c0f4660c858529582b51`;
* source file: `Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean`;
* per-source SHA-256: at the empty-support integration commit,
  `a6fb493fdaf8686eed654b4b0f7abe84ef14d4198304ef4dcf9f8160c8afd2f6`;
  at the finite-`S` source commit,
  `9810a9311a0833042b5ec1d9e5e7a930cdefb30e85adcbc5c785e8e382eb7307`.

The source uses Mathlib's module-system surface on Lean 4.33.0-rc2 (`module`,
`public import`, `@[expose] public section`, and `@[no_expose]`). Fermat pins
Mathlib commit `0531bb79fea20efc9ce6942db46b96be5a919400` on Lean 4.31.0-rc1 and its
project modules use ordinary imports.

A direct comparison also found that the pinned pre-existing `SelmerGroup`
file is not byte-identical to the source branch's parent commit
`550612a8ead6b270d197c727eb666402f3b571b7`: the latter removes the local
`open Classical in` around `valuationOfNeZeroToFun`, adds
`set_option backward.isDefEq.respectTransparency.types false in` around
`valuationOfNeZeroToFun_eq`, and explicitly rewrites `valuation_def` where the
pin uses `rfl`. Those pre-existing proof-engineering changes are outside the
vendored additions, do not change the API used here, and are not copied.

The complete delta in the vendored additions is:

1. this standalone file uses ordinary `import` commands, with the pinned
   `SelmerGroup` supplying the pre-existing definitions and with the upstream
   dependencies (`Subgroup.Finsupp`, `ClassGroup.Basic`, `Factorization`, and
   `SInteger`) imported explicitly;
2. the source's `module`, `public`, and enclosing `@[expose]` commands are
   omitted, and the export-control-only `@[no_expose]` attributes are omitted;
3. the source file's two file-local notations and `quotPrecheck` option are
   repeated because they do not cross an import boundary;
4. only the requested additions are copied: the two private valuation helpers
   used by the sequence, the generic integration block from
   `fractionalIdealExponents` through `toClass_range`, and the finite-`S`
   block from `DivisorAway` through
   `map_toSClass_empty_range_eq_toClass_range`. Existing pinned `SelmerGroup`
   material and upstream documentation/import reordering are not duplicated;
5. the upstream import of `Mathlib.GroupTheory.PowerRootObstruction` is
   redirected to the provenance-pinned route-neutral copy
   `Fermat.Conservation.PowerRootObstruction`;
6. `fractionalIdealFactorization` is exported so the cube can name exactly
   the geometry used by this obstruction square, rather than constructing a
   second, propositionally equivalent geometry.  Its coordinate theorem is
   likewise public and simp-tagged, as it is at the finite-`S` source commit;
7. the source's result-type ascription on the quotient `powMonoidHom` is
   replaced by an explicit `(α := ...)` argument. Lean 4.31 otherwise chooses
   incompatible `Monoid` instance paths before learning the quotient type.

There are no declaration, statement, or proof-body improvements. Apart from
the compatibility and standalone-file deltas listed above, the vendored
declarations are copied verbatim.
-/

import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finsupp
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.DedekindDomain.SInteger
import Fermat.Conservation.PowerRootObstruction

set_option quotPrecheck false
local notation K "/" n => Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range

namespace IsDedekindDomain

noncomputable section

open WithZero
open scoped WithZero nonZeroDivisors

universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R] {K : Type v} [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

namespace HeightOneSpectrum

private theorem count_spanSingleton (x : Kˣ) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (x : K)) =
      -(v.valuationOfNeZero x).toAdd := by
  let s := IsLocalization.sec R⁰ (x : K)
  have hs : FractionalIdeal.spanSingleton R⁰ (x : K) =
      FractionalIdeal.spanSingleton R⁰ (algebraMap R K (s.2 : R))⁻¹ *
        (Ideal.span {s.1} : FractionalIdeal R⁰ K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    symm
    rw [inv_mul_eq_iff_eq_mul₀ (map_ne_zero_of_mem_nonZeroDivisors _
      (IsFractionRing.injective R K) s.2.property)]
    exact IsLocalization.sec_spec' R⁰ (x : K)
  rw [FractionalIdeal.count_well_defined K v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero) hs]
  simp [valuationOfNeZero, valuationOfNeZeroToFun, s]
  ring

private theorem valuation_mod_eq_one_iff (n : ℕ) (x : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk x) = 1 ↔
      (n : ℤ) ∣ (v.valuationOfNeZero x).toAdd := by
  change ((v.valuationOfNeZero x).toAdd : ZMod n) = 0 ↔ _
  simpa using ZMod.intCast_zmod_eq_zero_iff_dvd (v.valuationOfNeZero x).toAdd n

end HeightOneSpectrum

variable {S S' : Set <| HeightOneSpectrum R} {n : ℕ}

local notation K "⟮" S "," n "⟯" => @selmerGroup _ _ _ K _ _ _ S n

namespace selmerGroup

private def fractionalIdealExponents (I : (FractionalIdeal R⁰ K)ˣ) :
    HeightOneSpectrum R →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v ↦ FractionalIdeal.count K v (I : FractionalIdeal R⁰ K))
    (by
      simpa only [Function.support] using Filter.eventually_cofinite.mp
        (FractionalIdeal.finite_factors (I : FractionalIdeal R⁰ K)))

private theorem fractionalIdealExponents_apply (I : (FractionalIdeal R⁰ K)ˣ)
    (v : HeightOneSpectrum R) :
    fractionalIdealExponents (R := R) (K := K) I v =
      FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) :=
  rfl

private theorem fractionalIdealProduct_ne_zero (e : HeightOneSpectrum R →₀ ℤ) :
    e.prod (fun v z ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^ z) ≠ 0 := by
  rw [Finsupp.prod_ne_zero_iff]
  intro v _
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

private def fractionalIdealOfExponents (e : HeightOneSpectrum R →₀ ℤ) :
    (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (e.prod (fun v z ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^ z))
    (fractionalIdealProduct_ne_zero (R := R) (K := K) e)

/-- The factorization of nonzero fractional ideals by their height-one prime exponents. -/
def fractionalIdealFactorization :
    PowerRoot.Factorization (FractionalIdeal R⁰ K)ˣ (HeightOneSpectrum R) where
  toFun I := Multiplicative.ofAdd (fractionalIdealExponents (R := R) (K := K) I)
  invFun e := fractionalIdealOfExponents (R := R) (K := K) e.toAdd
  left_inv I := by
    apply Units.ext
    change (fractionalIdealExponents (R := R) (K := K) I).prod
      (fun v z ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^ z) = I
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K
        (fractionalIdealProduct_ne_zero (R := R) (K := K)
          (fractionalIdealExponents (R := R) (K := K) I)),
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero]
    apply finprod_congr
    intro v
    rw [FractionalIdeal.count_finsuppProd, fractionalIdealExponents_apply]
  right_inv e := by
    apply Multiplicative.toAdd.injective
    ext v
    change fractionalIdealExponents (R := R) (K := K)
      (fractionalIdealOfExponents (R := R) (K := K) e.toAdd) v = e.toAdd v
    rw [fractionalIdealExponents_apply]
    exact FractionalIdeal.count_finsuppProd K v e.toAdd
  map_mul' I J := by
    apply Multiplicative.toAdd.injective
    ext v
    change FractionalIdeal.count K v ((I * J : (FractionalIdeal R⁰ K)ˣ) :
        FractionalIdeal R⁰ K) =
      FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) +
        FractionalIdeal.count K v (J : FractionalIdeal R⁰ K)
    simpa only [Units.val_mul] using FractionalIdeal.count_mul K v I.ne_zero J.ne_zero

/-- The coordinate of the fractional-ideal factorization at a height-one prime. -/
@[simp]
theorem fractionalIdealFactorization_apply (I : (FractionalIdeal R⁰ K)ˣ)
    (v : HeightOneSpectrum R) :
    (fractionalIdealFactorization (R := R) (K := K) I).toAdd v =
      FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) :=
  fractionalIdealExponents_apply I v

private theorem mk_mem_divisibleClasses_iff (x : Kˣ) :
    (QuotientGroup.mk x : K / n) ∈
        PowerRoot.divisibleClasses (toPrincipalIdeal R K) n ↔
      ∀ v : HeightOneSpectrum R, v.valuationOfNeZeroMod n (QuotientGroup.mk x) = 1 := by
  rw [(fractionalIdealFactorization (R := R) (K := K)).mk_mem_divisibleClasses_iff]
  simp only [fractionalIdealFactorization_apply, coe_toPrincipalIdeal]
  constructor
  · intro hx v
    apply (v.valuation_mod_eq_one_iff n x).mpr
    exact Int.dvd_neg.mp (v.count_spanSingleton x ▸ hx v)
  · intro hx v
    rw [v.count_spanSingleton]
    exact Int.dvd_neg.mpr ((v.valuation_mod_eq_one_iff n x).mp (hx v))

private theorem selmerGroup_empty_eq_divisibleClasses :
    K⟮(∅ : Set <| HeightOneSpectrum R), n⟯ =
      PowerRoot.divisibleClasses (toPrincipalIdeal R K) n := by
  ext q
  induction q using QuotientGroup.induction_on with
  | _ x =>
    rw [mk_mem_divisibleClasses_iff (R := R) (K := K) (n := n)]
    constructor
    · intro hx v
      exact hx v (Set.notMem_empty v)
    · intro hx v _
      exact hx v

private def selmerEquivDivisibleClasses :
    K⟮(∅ : Set <| HeightOneSpectrum R), n⟯ ≃*
      PowerRoot.divisibleClasses (toPrincipalIdeal R K) n :=
  MulEquiv.subgroupCongr (selmerGroup_empty_eq_divisibleClasses (R := R) (K := K) (n := n))

/-- The class of the `n`-th root ideal associated to an element of `K⟮∅, n⟯`. -/
def toClass [Fact <| 0 < n] :
    K⟮(∅ : Set <| HeightOneSpectrum R), n⟯ →* ClassGroup R :=
  (ClassGroup.equiv K).symm.toMonoidHom.comp <|
    (PowerRoot.obstruction (f := toPrincipalIdeal R K) (n := n)
      (fractionalIdealFactorization (R := R) (K := K))).comp
        (selmerEquivDivisibleClasses (R := R) (K := K) (n := n)).toMonoidHom

private def unitsToPrincipalKernel : Rˣ →* (toPrincipalIdeal R K).ker where
  toFun u := ⟨Units.map (algebraMap R K : R →* K) u, by
    apply Units.ext
    rw [coe_toPrincipalIdeal, Units.val_one, ← FractionalIdeal.spanSingleton_one,
      FractionalIdeal.spanSingleton_eq_spanSingleton]
    exact ⟨u⁻¹, by simp [Units.smul_def, Algebra.smul_def]⟩⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

private theorem unitsToPrincipalKernel_surjective :
    Function.Surjective (unitsToPrincipalKernel (R := R) (K := K)) := by
  intro x
  have hspan : FractionalIdeal.spanSingleton R⁰ ((x : Kˣ) : K) =
      FractionalIdeal.spanSingleton R⁰ (1 : K) := by
    rw [FractionalIdeal.spanSingleton_one]
    simpa only [coe_toPrincipalIdeal, Units.val_one] using congr_arg Units.val x.property
  obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan
  refine ⟨u⁻¹, Subtype.ext ?_⟩
  change Units.map (algebraMap R K : R →* K) u⁻¹ = (x : Kˣ)
  rw [show Units.map (algebraMap R K : R →* K) u⁻¹ =
      (Units.map (algebraMap R K : R →* K) u)⁻¹ by simp]
  apply Units.ext
  apply Units.inv_eq_of_mul_eq_one_right
  rw [Units.coe_map]
  change (algebraMap R K) (u : R) * ((x : Kˣ) : K) = 1
  simpa only [Units.smul_def, Algebra.smul_def] using hu

private theorem unitsToPrincipalKernel_injective :
    Function.Injective (unitsToPrincipalKernel (R := R) (K := K)) := by
  intro u v huv
  apply Units.map_injective (FaithfulSMul.algebraMap_injective R K)
  exact congr_arg Subtype.val huv

private def unitsEquivPrincipalKernel : Rˣ ≃* (toPrincipalIdeal R K).ker :=
  MulEquiv.ofBijective (unitsToPrincipalKernel (R := R) (K := K))
    ⟨unitsToPrincipalKernel_injective (R := R) (K := K),
      unitsToPrincipalKernel_surjective (R := R) (K := K)⟩

private def unitsToPrincipalKernelOnPowerQuotients :
    (R / n) →* ((toPrincipalIdeal R K).ker ⧸
      PowerRoot.powerSubgroup (toPrincipalIdeal R K).ker n) :=
  PowerRoot.mapOnPowerQuotients
    (unitsEquivPrincipalKernel (R := R) (K := K)).toMonoidHom n

private theorem unitsToPrincipalKernelOnPowerQuotients_surjective :
    Function.Surjective (unitsToPrincipalKernelOnPowerQuotients
      (R := R) (K := K) (n := n)) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | _ x =>
    obtain ⟨u, rfl⟩ := (unitsEquivPrincipalKernel (R := R) (K := K)).surjective x
    exact ⟨QuotientGroup.mk u, PowerRoot.mapOnPowerQuotients_mk _ _ _⟩

private def fromPrincipalKernel :
    ((toPrincipalIdeal R K).ker ⧸
      PowerRoot.powerSubgroup (toPrincipalIdeal R K).ker n) →*
        K⟮(∅ : Set <| HeightOneSpectrum R), n⟯ :=
  (selmerEquivDivisibleClasses (R := R) (K := K) (n := n)).symm.toMonoidHom.comp
    (PowerRoot.fromKernel (toPrincipalIdeal R K) n)

private theorem fromPrincipalKernel_comp [Fact <| 0 < n] :
    (fromPrincipalKernel (R := R) (K := K) (n := n)).comp
        (unitsToPrincipalKernelOnPowerQuotients (R := R) (K := K) (n := n)) =
      fromUnitLift (R := R) (K := K) (n := n) := by
  ext u
  rfl

private theorem fromPrincipalKernel_range [Fact <| 0 < n] :
    (fromPrincipalKernel (R := R) (K := K) (n := n)).range =
      (fromUnitLift (R := R) (K := K) (n := n)).range := by
  rw [← fromPrincipalKernel_comp (R := R) (K := K) (n := n), MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective _
      (unitsToPrincipalKernelOnPowerQuotients_surjective (R := R) (K := K) (n := n)),
    ← MonoidHom.range_eq_map]

/-- The kernel of `toClass` is the range of the unit classes in `K⟮∅, n⟯`. -/
theorem toClass_ker [Fact <| 0 < n] :
    (toClass (R := R) (K := K) (n := n)).ker =
      (fromUnitLift (R := R) (K := K) (n := n)).range := by
  rw [← fromPrincipalKernel_range (R := R) (K := K) (n := n), toClass]
  calc
    _ = ((PowerRoot.obstruction (f := toPrincipalIdeal R K) (n := n)
          (fractionalIdealFactorization (R := R) (K := K))).comp
            (selmerEquivDivisibleClasses (R := R) (K := K) (n := n)).toMonoidHom).ker :=
      MonoidHom.ker_mulEquiv_comp _ (ClassGroup.equiv K).symm
    _ = Subgroup.map
        (selmerEquivDivisibleClasses (R := R) (K := K) (n := n)).symm.toMonoidHom
          (PowerRoot.obstruction (f := toPrincipalIdeal R K) (n := n)
            (fractionalIdealFactorization (R := R) (K := K))).ker :=
      MonoidHom.ker_comp_mulEquiv _
        (selmerEquivDivisibleClasses (R := R) (K := K) (n := n))
    _ = _ := by
      rw [PowerRoot.obstruction_ker (f := toPrincipalIdeal R K) (n := n),
        MonoidHom.map_range]
      rfl

private theorem classGroupEquiv_map_power_ker :
    (powMonoidHom
      (α := (FractionalIdeal R⁰ K)ˣ ⧸ (toPrincipalIdeal R K).range) n).ker.map
          (ClassGroup.equiv K).symm.toMonoidHom =
      (powMonoidHom n : ClassGroup R →* ClassGroup R).ker := by
  ext c
  constructor
  · rintro ⟨d, hd, rfl⟩
    change d ^ n = 1 at hd
    change ((ClassGroup.equiv K).symm d) ^ n = 1
    rw [← map_pow, hd, map_one]
  · intro hc
    refine ⟨ClassGroup.equiv K c, ?_, (ClassGroup.equiv K).symm_apply_apply c⟩
    change c ^ n = 1 at hc
    change (ClassGroup.equiv K c) ^ n = 1
    rw [← map_pow, hc, map_one]

/-- The range of `toClass` is the subgroup of `n`-torsion ideal classes. -/
theorem toClass_range [hn : Fact <| 0 < n] :
    (toClass (R := R) (K := K) (n := n)).range =
      (powMonoidHom n : ClassGroup R →* ClassGroup R).ker := by
  rw [toClass,
    MonoidHom.range_comp (ClassGroup.equiv K).symm.toMonoidHom,
    MonoidHom.range_comp (PowerRoot.obstruction (f := toPrincipalIdeal R K) (n := n)
      (fractionalIdealFactorization (R := R) (K := K))),
    MonoidHom.range_eq_top_of_surjective
      (selmerEquivDivisibleClasses (R := R) (K := K) (n := n)).toMonoidHom
        (selmerEquivDivisibleClasses (R := R) (K := K) (n := n)).surjective,
    ← MonoidHom.range_eq_map (PowerRoot.obstruction (f := toPrincipalIdeal R K) (n := n)
      (fractionalIdealFactorization (R := R) (K := K))),
    PowerRoot.obstruction_range (f := toPrincipalIdeal R K) (n := n),
    classGroupEquiv_map_power_ker]

/-! ### The S-unit-class exact sequence -/

/-- The group of divisors supported at height-one primes outside `S`. -/
abbrev DivisorAway (S : Set <| HeightOneSpectrum R) :=
  Multiplicative ({v : HeightOneSpectrum R // v ∉ S} →₀ ℤ)

/-- Restrict a nonzero fractional ideal to its exponents at primes outside `S`. -/
def fractionalIdealToDivisorAway (S : Set <| HeightOneSpectrum R) :
    (FractionalIdeal R⁰ K)ˣ →* DivisorAway S :=
  (Finsupp.subtypeDomainAddMonoidHom (p := fun v : HeightOneSpectrum R ↦ v ∉ S)
      (M := ℤ)).toMultiplicative.comp
    (fractionalIdealFactorization (R := R) (K := K)).toMonoidHom

@[simp]
theorem fractionalIdealToDivisorAway_apply (S : Set <| HeightOneSpectrum R)
    (I : (FractionalIdeal R⁰ K)ˣ) (v : {v : HeightOneSpectrum R // v ∉ S}) :
    (fractionalIdealToDivisorAway (R := R) (K := K) S I).toAdd v =
      FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) := by
  change (fractionalIdealFactorization (R := R) (K := K) I).toAdd v = _
  exact fractionalIdealFactorization_apply I v

/-- The away-from-`S` valuations of the principal fractional ideal of a nonzero element. -/
def principalDivisorAway (S : Set <| HeightOneSpectrum R) : Kˣ →* DivisorAway S :=
  (fractionalIdealToDivisorAway (R := R) (K := K) S).comp (toPrincipalIdeal R K)

@[simp]
theorem principalDivisorAway_apply (S : Set <| HeightOneSpectrum R) (x : Kˣ)
    (v : {v : HeightOneSpectrum R // v ∉ S}) :
    (principalDivisorAway (R := R) (K := K) S x).toAdd v =
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (x : K)) := by
  change (fractionalIdealToDivisorAway (R := R) (K := K) S
    (toPrincipalIdeal R K x)).toAdd v = _
  rw [fractionalIdealToDivisorAway_apply, coe_toPrincipalIdeal]

private theorem mk_mem_divisibleClassesAway_iff (S : Set <| HeightOneSpectrum R)
    (x : Kˣ) :
    (QuotientGroup.mk x : K / n) ∈
        PowerRoot.divisibleClasses (principalDivisorAway (R := R) (K := K) S) n ↔
      ∀ (v : HeightOneSpectrum R), v ∉ S →
        v.valuationOfNeZeroMod n (QuotientGroup.mk x) = 1 := by
  rw [PowerRoot.Factorization.mk_mem_divisibleClasses_iff
    (MulEquiv.refl (DivisorAway S))]
  change (∀ v : {v : HeightOneSpectrum R // v ∉ S},
    (n : ℤ) ∣ (principalDivisorAway (R := R) (K := K) S x).toAdd v) ↔ _
  simp_rw [principalDivisorAway_apply]
  constructor
  · intro hx v hv
    apply (v.valuation_mod_eq_one_iff n x).mpr
    exact Int.dvd_neg.mp (v.count_spanSingleton x ▸ hx ⟨v, hv⟩)
  · intro hx v
    rw [v.1.count_spanSingleton]
    exact Int.dvd_neg.mpr ((v.1.valuation_mod_eq_one_iff n x).mp (hx v v.2))

/-- The Selmer group is the group of divisible classes for the principal divisor map away from
`S`. -/
theorem eq_divisibleClasses (S : Set <| HeightOneSpectrum R) :
    K⟮S, n⟯ = PowerRoot.divisibleClasses
      (principalDivisorAway (R := R) (K := K) S) n := by
  ext q
  induction q using QuotientGroup.induction_on with
  | _ x =>
    rw [mk_mem_divisibleClassesAway_iff (R := R) (K := K) S]
    rfl

/-- The multiplicative equivalence between the Selmer group and the divisible classes for the
principal divisor map away from `S`. -/
def equivDivisibleClasses (S : Set <| HeightOneSpectrum R) :
    K⟮S, n⟯ ≃* PowerRoot.divisibleClasses
      (principalDivisorAway (R := R) (K := K) S) n :=
  MulEquiv.subgroupCongr (eq_divisibleClasses (R := R) (K := K) S)

private theorem valuationOfNeZero_toAdd_eq_zero_iff (v : HeightOneSpectrum R) (x : Kˣ) :
    (v.valuationOfNeZero x).toAdd = 0 ↔ v.valuation K x = 1 := by
  rw [← v.valuationOfNeZero_eq x, ← WithZero.coe_one, WithZero.coe_inj]
  rfl

/-- The kernel of the principal divisor map away from `S` is the group of `S`-units. -/
theorem principalDivisorAway_ker (S : Set <| HeightOneSpectrum R) :
    (principalDivisorAway (R := R) (K := K) S).ker = S.unit K := by
  ext x
  change principalDivisorAway (R := R) (K := K) S x = 1 ↔
    ∀ v : HeightOneSpectrum R, v ∉ S → v.valuation K x = 1
  constructor
  · intro hx v hv
    have h := congr_arg (fun y : DivisorAway S ↦ y.toAdd ⟨v, hv⟩) hx
    rw [principalDivisorAway_apply, v.count_spanSingleton] at h
    exact (valuationOfNeZero_toAdd_eq_zero_iff (K := K) v x).mp (neg_eq_zero.mp h)
  · intro hx
    apply Multiplicative.toAdd.injective
    apply Finsupp.ext
    intro v
    rw [principalDivisorAway_apply, v.1.count_spanSingleton]
    change -(v.1.valuationOfNeZero x).toAdd = 0
    rw [neg_eq_zero]
    exact (valuationOfNeZero_toAdd_eq_zero_iff (K := K) v.1 x).mpr (hx v.1 v.2)

/-- The multiplicative equivalence between `S`-units and the kernel of the principal divisor map
away from `S`. -/
def sUnitEquivPrincipalDivisorAwayKer (S : Set <| HeightOneSpectrum R) :
    S.unit K ≃* (principalDivisorAway (R := R) (K := K) S).ker :=
  MulEquiv.subgroupCongr (principalDivisorAway_ker (R := R) (K := K) S).symm

/-- The equivalence on power quotients induced by the identification of `S`-units with the kernel
of the principal divisor map away from `S`. -/
def sUnitClassesEquivPrincipalDivisorAwayKer (S : Set <| HeightOneSpectrum R) :
    (S.unit K ⧸ PowerRoot.powerSubgroup (S.unit K) n) ≃*
      ((principalDivisorAway (R := R) (K := K) S).ker ⧸
        PowerRoot.powerSubgroup (principalDivisorAway (R := R) (K := K) S).ker n) :=
  QuotientGroup.congr _ _ (sUnitEquivPrincipalDivisorAwayKer (R := R) (K := K) S)
    ((sUnitEquivPrincipalDivisorAwayKer (R := R) (K := K) S).map_range_powMonoidHom n)

/-- The equivalence between power classes of `S`-units and power classes of units of the ring of
`S`-integers. -/
def sUnitClassesEquivIntegerUnits (S : Set <| HeightOneSpectrum R) :
    (S.unit K ⧸ PowerRoot.powerSubgroup (S.unit K) n) ≃*
      ((S.integer K)ˣ ⧸ PowerRoot.powerSubgroup (S.integer K)ˣ n) :=
  QuotientGroup.congr _ _ (S.unitEquivUnitsInteger K)
    ((S.unitEquivUnitsInteger K).map_range_powMonoidHom n)

/-- The injection from power classes of `S`-units into the Selmer group. -/
def fromSUnitLift (S : Set <| HeightOneSpectrum R) :
    (S.unit K ⧸ PowerRoot.powerSubgroup (S.unit K) n) →* K⟮S, n⟯ :=
  (equivDivisibleClasses (R := R) (K := K) (n := n) S).symm.toMonoidHom.comp <|
    (PowerRoot.fromKernel (principalDivisorAway (R := R) (K := K) S) n).comp
      (sUnitClassesEquivPrincipalDivisorAwayKer
        (R := R) (K := K) (n := n) S).toMonoidHom

/-- The injection from power classes of units of the ring of `S`-integers into the Selmer group. -/
def fromSIntegerUnitLift (S : Set <| HeightOneSpectrum R) :
    ((S.integer K)ˣ ⧸ PowerRoot.powerSubgroup (S.integer K)ˣ n) →* K⟮S, n⟯ :=
  (fromSUnitLift (R := R) (K := K) (n := n) S).comp
    (sUnitClassesEquivIntegerUnits (R := R) (K := K) (n := n) S).symm.toMonoidHom

/-- The map from power classes of `S`-units into the Selmer group is injective. -/
theorem fromSUnitLift_injective [Fact <| 0 < n] (S : Set <| HeightOneSpectrum R) :
    Function.Injective (fromSUnitLift (R := R) (K := K) (n := n) S) :=
  (equivDivisibleClasses (R := R) (K := K) (n := n) S).symm.injective.comp <|
    (PowerRoot.fromKernel_injective
      (principalDivisorAway (R := R) (K := K) S) n (MulEquiv.refl (DivisorAway S))).comp
        (sUnitClassesEquivPrincipalDivisorAwayKer
          (R := R) (K := K) (n := n) S).injective

/-- The map from power classes of units of the ring of `S`-integers into the Selmer group is
injective. -/
theorem fromSIntegerUnitLift_injective [Fact <| 0 < n]
    (S : Set <| HeightOneSpectrum R) :
    Function.Injective (fromSIntegerUnitLift (R := R) (K := K) (n := n) S) :=
  (fromSUnitLift_injective (R := R) (K := K) S).comp
    (sUnitClassesEquivIntegerUnits (R := R) (K := K) (n := n) S).symm.injective

/-- The generic cokernel of the principal divisor map away from `S`.  It is identified below with
the class group modulo the classes of primes in `S`. -/
abbrev obstructionTarget (S : Set <| HeightOneSpectrum R) :=
  DivisorAway S ⧸ (principalDivisorAway (R := R) (K := K) S).range

/-- The class of the `n`-th root of the away-from-`S` principal divisor associated to a Selmer
class. -/
def toSClass [Fact <| 0 < n] (S : Set <| HeightOneSpectrum R) :
    K⟮S, n⟯ →* obstructionTarget (R := R) (K := K) S :=
  (PowerRoot.obstruction (f := principalDivisorAway (R := R) (K := K) S) (n := n)
    (MulEquiv.refl (DivisorAway S))).comp
      (equivDivisibleClasses (R := R) (K := K) (n := n) S).toMonoidHom

/-- The kernel of the finite-`S` obstruction is the range of the `S`-unit classes. -/
theorem toSClass_ker [Fact <| 0 < n] (S : Set <| HeightOneSpectrum R) :
    (toSClass (R := R) (K := K) (n := n) S).ker =
      (fromSUnitLift (R := R) (K := K) (n := n) S).range := by
  let e := equivDivisibleClasses (R := R) (K := K) (n := n) S
  let u := sUnitClassesEquivPrincipalDivisorAwayKer
    (R := R) (K := K) (n := n) S
  let f := PowerRoot.fromKernel (principalDivisorAway (R := R) (K := K) S) n
  let o := PowerRoot.obstruction
    (f := principalDivisorAway (R := R) (K := K) S) (n := n)
      (MulEquiv.refl (DivisorAway S))
  change (o.comp e.toMonoidHom).ker =
    (e.symm.toMonoidHom.comp (f.comp u.toMonoidHom)).range
  have hu : u.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top_of_surjective _ u.surjective
  have hfu : (f.comp u.toMonoidHom).range = f.range := calc
    _ = Subgroup.map f u.toMonoidHom.range := MonoidHom.range_comp f u.toMonoidHom
    _ = Subgroup.map f ⊤ := congr_arg (Subgroup.map f) hu
    _ = f.range := (MonoidHom.range_eq_map f).symm
  calc
    _ = Subgroup.map e.symm.toMonoidHom o.ker := MonoidHom.ker_comp_mulEquiv o e
    _ = Subgroup.map e.symm.toMonoidHom f.range := congr_arg
      (Subgroup.map e.symm.toMonoidHom) <| PowerRoot.obstruction_ker
        (f := principalDivisorAway (R := R) (K := K) S) (n := n)
          (MulEquiv.refl (DivisorAway S))
    _ = Subgroup.map e.symm.toMonoidHom (f.comp u.toMonoidHom).range :=
      congr_arg (Subgroup.map e.symm.toMonoidHom) hfu.symm
    _ = _ := (MonoidHom.range_comp e.symm.toMonoidHom (f.comp u.toMonoidHom)).symm

/-- The kernel of the finite-`S` obstruction is also the range of power classes of units of the
ring of `S`-integers. -/
theorem toSClass_ker_integerUnits [Fact <| 0 < n] (S : Set <| HeightOneSpectrum R) :
    (toSClass (R := R) (K := K) (n := n) S).ker =
      (fromSIntegerUnitLift (R := R) (K := K) (n := n) S).range := by
  rw [toSClass_ker (R := R) (K := K)]
  let e := (sUnitClassesEquivIntegerUnits (R := R) (K := K) (n := n) S).symm
  let f := fromSUnitLift (R := R) (K := K) (n := n) S
  change f.range = (f.comp e.toMonoidHom).range
  have he : e.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top_of_surjective _ e.surjective
  calc
    _ = Subgroup.map f ⊤ := MonoidHom.range_eq_map f
    _ = Subgroup.map f e.toMonoidHom.range := congr_arg (Subgroup.map f) he.symm
    _ = _ := (MonoidHom.range_comp f e.toMonoidHom).symm

/-- The range of the finite-`S` obstruction is the `n`-torsion in its generic cokernel. -/
theorem toSClass_range [Fact <| 0 < n] (S : Set <| HeightOneSpectrum R) :
    (toSClass (R := R) (K := K) (n := n) S).range =
      (powMonoidHom n : obstructionTarget (R := R) (K := K) S →*
      obstructionTarget (R := R) (K := K) S).ker := by
  let e := equivDivisibleClasses (R := R) (K := K) (n := n) S
  let o := PowerRoot.obstruction
    (f := principalDivisorAway (R := R) (K := K) S) (n := n)
      (MulEquiv.refl (DivisorAway S))
  change (o.comp e.toMonoidHom).range = _
  have he : e.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top_of_surjective _ e.surjective
  calc
    _ = Subgroup.map o e.toMonoidHom.range := MonoidHom.range_comp o e.toMonoidHom
    _ = Subgroup.map o ⊤ := congr_arg (Subgroup.map o) he
    _ = o.range := (MonoidHom.range_eq_map o).symm
    _ = _ := PowerRoot.obstruction_range
      (f := principalDivisorAway (R := R) (K := K) S) (n := n)
        (MulEquiv.refl (DivisorAway S))

/-! ### The S-class group -/

/-- Every divisor away from `S` is represented by a nonzero fractional ideal. -/
theorem fractionalIdealToDivisorAway_surjective (S : Set <| HeightOneSpectrum R) :
    Function.Surjective (fractionalIdealToDivisorAway (R := R) (K := K) S) := by
  classical
  intro e
  let e' : HeightOneSpectrum R →₀ ℤ := e.toAdd.extendDomain
  refine ⟨(fractionalIdealFactorization (R := R) (K := K)).symm
    (Multiplicative.ofAdd e'), ?_⟩
  apply Multiplicative.toAdd.injective
  apply Finsupp.ext
  intro v
  rw [fractionalIdealToDivisorAway_apply, ← fractionalIdealFactorization_apply]
  change ((fractionalIdealFactorization (R := R) (K := K))
    ((fractionalIdealFactorization (R := R) (K := K)).symm
      (Multiplicative.ofAdd e'))).toAdd v = e.toAdd v
  rw [MulEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (Finsupp.subtypeDomain_extendDomain e.toAdd) v

private def fractionalIdealToObstructionTarget (S : Set <| HeightOneSpectrum R) :
    (FractionalIdeal R⁰ K)ˣ →* obstructionTarget (R := R) (K := K) S :=
  (QuotientGroup.mk' (principalDivisorAway (R := R) (K := K) S).range).comp
    (fractionalIdealToDivisorAway (R := R) (K := K) S)

private theorem principalIdealRange_le_obstructionTarget_ker
    (S : Set <| HeightOneSpectrum R) :
    (toPrincipalIdeal R K).range ≤
      (fractionalIdealToObstructionTarget (R := R) (K := K) S).ker := by
  rintro _ ⟨x, rfl⟩
  rw [MonoidHom.mem_ker]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨x, rfl⟩

/-- The canonical map from the ordinary class group to the generic obstruction target away from
`S`. -/
def classGroupToObstructionTarget (S : Set <| HeightOneSpectrum R) :
    ClassGroup R →* obstructionTarget (R := R) (K := K) S :=
  (QuotientGroup.lift (toPrincipalIdeal R K).range
    (fractionalIdealToObstructionTarget (R := R) (K := K) S)
      (principalIdealRange_le_obstructionTarget_ker (R := R) (K := K) S)).comp
        (ClassGroup.equiv K).toMonoidHom

@[simp]
theorem classGroupToObstructionTarget_mk (S : Set <| HeightOneSpectrum R)
    (I : (FractionalIdeal R⁰ K)ˣ) :
    classGroupToObstructionTarget (R := R) (K := K) S (ClassGroup.mk K I) =
      QuotientGroup.mk (fractionalIdealToDivisorAway (R := R) (K := K) S I) := by
  have h : ClassGroup.equiv K (ClassGroup.mk K I) = QuotientGroup.mk I := by
    rw [ClassGroup.equiv_mk K K I]
    apply congr_arg (QuotientGroup.mk' (toPrincipalIdeal R K).range)
    apply Units.ext
    simp only [Units.coe_mapEquiv]
    rw [FractionalIdeal.canonicalEquiv_self]
    rfl
  rw [classGroupToObstructionTarget, MonoidHom.comp_apply]
  change (QuotientGroup.lift (toPrincipalIdeal R K).range
    (fractionalIdealToObstructionTarget (R := R) (K := K) S)
      (principalIdealRange_le_obstructionTarget_ker (R := R) (K := K) S))
        (ClassGroup.equiv K (ClassGroup.mk K I)) = _
  rw [h]
  rfl

/-- The canonical map from the ordinary class group to the away-from-`S` obstruction target is
surjective. -/
theorem classGroupToObstructionTarget_surjective (S : Set <| HeightOneSpectrum R) :
    Function.Surjective (classGroupToObstructionTarget (R := R) (K := K) S) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | _ d =>
    obtain ⟨I, rfl⟩ := fractionalIdealToDivisorAway_surjective
      (R := R) (K := K) S d
    exact ⟨ClassGroup.mk K I, classGroupToObstructionTarget_mk
      (R := R) (K := K) S I⟩

/-- The subgroup of the class group killed after discarding the prime coordinates in `S`.  Below
this is identified with the subgroup generated by the classes of primes in `S`. -/
def invertedPrimeClasses (S : Set <| HeightOneSpectrum R) : Subgroup (ClassGroup R) :=
  (classGroupToObstructionTarget (R := R) (K := K) S).ker

/-- The ideal class of a height-one prime. -/
def primeClass (v : HeightOneSpectrum R) : ClassGroup R :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩

/-- The subgroup of the class group generated by the classes of the height-one primes in `S`. -/
def classesOfPrimesIn (S : Set <| HeightOneSpectrum R) : Subgroup (ClassGroup R) :=
  Subgroup.closure (Set.range fun v : S ↦ primeClass v)

/-- The `S`-class group, presented as the ordinary class group modulo the subgroup generated by
the classes of the height-one primes in `S`. -/
abbrev SClassGroup (S : Set <| HeightOneSpectrum R) :=
  ClassGroup R ⧸ classesOfPrimesIn (R := R) S

private theorem mem_closure_basis_of_eq_zero_outside {P : Type*} (T : Set P)
    (d : Multiplicative (P →₀ ℤ)) (hd : ∀ p, p ∉ T → d.toAdd p = 0) :
    d ∈ Subgroup.closure (Set.range fun p : T ↦
      Multiplicative.ofAdd (Finsupp.single p.1 (1 : ℤ))) := by
  classical
  rw [Subgroup.mem_closure_range_iff]
  let a : T →₀ ℤ := d.toAdd.subtypeDomain (fun p ↦ p ∈ T)
  have ha : a.sum (fun p z ↦ Finsupp.single p.1 z) = a.extendDomain := by
    calc
      _ = (a.mapDomain Subtype.val).sum Finsupp.single := by
        rw [Finsupp.sum_mapDomain_index] <;> simp
      _ = a.mapDomain Subtype.val := Finsupp.sum_single _
      _ = a.extendDomain := ((Finsupp.extendDomain_eq_embDomain_subtype a).trans
        (Finsupp.embDomain_eq_mapDomain (.subtype _) a)).symm
  refine ⟨a, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Finsupp.ext
  intro p
  by_cases hp : p ∈ T
  · change d.toAdd p = (a.sum fun p z ↦
      z • Finsupp.single p.1 (1 : ℤ)) p
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [ha, Finsupp.extendDomain_apply, dif_pos hp]
    rfl
  · rw [hd p hp]
    change 0 = (a.sum fun p z ↦ z • Finsupp.single p.1 (1 : ℤ)) p
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [ha, Finsupp.extendDomain_apply, dif_neg hp]

private def divisorToClass :
    Multiplicative (HeightOneSpectrum R →₀ ℤ) →* ClassGroup R :=
  (ClassGroup.mk K).comp
    (fractionalIdealFactorization (R := R) (K := K)).symm.toMonoidHom

private theorem divisorToClass_basis (v : HeightOneSpectrum R) :
    divisorToClass (R := R) (K := K)
        (Multiplicative.ofAdd (Finsupp.single v (1 : ℤ))) = primeClass v := by
  rw [divisorToClass, MonoidHom.comp_apply, primeClass, ← ClassGroup.mk_mk0 (K := K)]
  apply congr_arg (ClassGroup.mk K)
  apply (fractionalIdealFactorization (R := R) (K := K)).injective
  change (fractionalIdealFactorization (R := R) (K := K))
      ((fractionalIdealFactorization (R := R) (K := K)).symm
        (Multiplicative.ofAdd (Finsupp.single v (1 : ℤ)))) = _
  rw [MulEquiv.apply_symm_apply]
  apply Multiplicative.toAdd.injective
  apply Finsupp.ext
  intro w
  classical
  rw [fractionalIdealFactorization_apply, FractionalIdeal.coe_mk0]
  rw [FractionalIdeal.count_maximal]
  by_cases hw : v = w <;> simp [hw]

private theorem classGroup_mk_mem_classesOfPrimesIn_of_restrict_eq_one
    (S : Set <| HeightOneSpectrum R) (I : (FractionalIdeal R⁰ K)ˣ)
    (hI : fractionalIdealToDivisorAway (R := R) (K := K) S I = 1) :
    ClassGroup.mk K I ∈ classesOfPrimesIn (R := R) S := by
  let d := fractionalIdealFactorization (R := R) (K := K) I
  have hd : ∀ v, v ∉ S → d.toAdd v = 0 := by
    intro v hv
    have h := congr_arg (fun e : DivisorAway S ↦ e.toAdd ⟨v, hv⟩) hI
    rw [fractionalIdealToDivisorAway_apply, ← fractionalIdealFactorization_apply] at h
    change FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) = 0
    exact h
  have hd_mem := mem_closure_basis_of_eq_zero_outside S d hd
  have hle :
      Subgroup.closure (Set.range fun v : S ↦
        Multiplicative.ofAdd (Finsupp.single v.1 (1 : ℤ))) ≤
        Subgroup.comap (divisorToClass (R := R) (K := K))
          (classesOfPrimesIn (R := R) S) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨v, rfl⟩
    change divisorToClass (R := R) (K := K)
      (Multiplicative.ofAdd (Finsupp.single v.1 (1 : ℤ))) ∈
        classesOfPrimesIn (R := R) S
    rw [divisorToClass_basis]
    exact Subgroup.subset_closure ⟨v, rfl⟩
  have := hle hd_mem
  change divisorToClass (R := R) (K := K) d ∈ classesOfPrimesIn (R := R) S at this
  have hdclass : divisorToClass (R := R) (K := K) d = ClassGroup.mk K I := by
    change ClassGroup.mk K ((fractionalIdealFactorization (R := R) (K := K)).symm
      (fractionalIdealFactorization (R := R) (K := K) I)) = ClassGroup.mk K I
    rw [MulEquiv.symm_apply_apply]
  rwa [hdclass] at this

private theorem fractionalIdealToDivisorAway_prime_eq_one
    (S : Set <| HeightOneSpectrum R) (v : S) :
    fractionalIdealToDivisorAway (R := R) (K := K) S
      (FractionalIdeal.mk0 K
        ⟨v.1.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.1.ne_bot⟩) = 1 := by
  apply Multiplicative.toAdd.injective
  apply Finsupp.ext
  intro w
  rw [fractionalIdealToDivisorAway_apply, FractionalIdeal.coe_mk0]
  change FractionalIdeal.count K w.1 (v.1.asIdeal : FractionalIdeal R⁰ K) = 0
  apply FractionalIdeal.count_maximal_coprime
  exact fun hvw ↦ w.2 (hvw ▸ v.2)

@[simp]
theorem classGroupToObstructionTarget_primeClass (S : Set <| HeightOneSpectrum R) (v : S) :
    classGroupToObstructionTarget (R := R) (K := K) S (primeClass v) = 1 := by
  rw [primeClass, ← ClassGroup.mk_mk0 (K := K),
    classGroupToObstructionTarget_mk,
    fractionalIdealToDivisorAway_prime_eq_one, QuotientGroup.mk_one]

private theorem classesOfPrimesIn_le_invertedPrimeClasses
    (S : Set <| HeightOneSpectrum R) :
    classesOfPrimesIn (R := R) S ≤ invertedPrimeClasses (R := R) (K := K) S := by
  rw [classesOfPrimesIn, Subgroup.closure_le]
  rintro _ ⟨v, rfl⟩
  exact classGroupToObstructionTarget_primeClass (R := R) (K := K) S v

private theorem invertedPrimeClasses_le_classesOfPrimesIn
    (S : Set <| HeightOneSpectrum R) :
    invertedPrimeClasses (R := R) (K := K) S ≤ classesOfPrimesIn (R := R) S := by
  intro c
  refine ClassGroup.induction K (P := fun c ↦
    c ∈ invertedPrimeClasses (R := R) (K := K) S →
      c ∈ classesOfPrimesIn (R := R) S) ?_ c
  intro I hc
  rw [invertedPrimeClasses, MonoidHom.mem_ker,
    classGroupToObstructionTarget_mk, QuotientGroup.eq_one_iff] at hc
  obtain ⟨x, hx⟩ := hc
  let J := I * (toPrincipalIdeal R K x)⁻¹
  have hJ : fractionalIdealToDivisorAway (R := R) (K := K) S J = 1 := by
    change fractionalIdealToDivisorAway (R := R) (K := K) S
      (I * (toPrincipalIdeal R K x)⁻¹) = 1
    rw [map_mul, map_inv]
    change fractionalIdealToDivisorAway (R := R) (K := K) S I *
      (principalDivisorAway (R := R) (K := K) S x)⁻¹ = 1
    rw [hx, mul_inv_cancel]
  have hprincipal : ClassGroup.mk K (toPrincipalIdeal R K x) = 1 := by
    rw [ClassGroup.mk_eq_one_iff]
    exact ⟨⟨(x : K), by rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]⟩⟩
  have hclass : ClassGroup.mk K J = ClassGroup.mk K I := by
    change ClassGroup.mk K (I * (toPrincipalIdeal R K x)⁻¹) = ClassGroup.mk K I
    simp only [map_mul, map_inv, hprincipal, inv_one, mul_one]
  rw [← hclass]
  exact classGroup_mk_mem_classesOfPrimesIn_of_restrict_eq_one
    (R := R) (K := K) S J hJ

/-- Discarding the divisor coordinates in `S` kills exactly the subgroup generated by the
classes of height-one primes in `S`. -/
theorem invertedPrimeClasses_eq_classesOfPrimesIn (S : Set <| HeightOneSpectrum R) :
    invertedPrimeClasses (R := R) (K := K) S = classesOfPrimesIn (R := R) S :=
  le_antisymm (invertedPrimeClasses_le_classesOfPrimesIn (R := R) (K := K) S)
    (classesOfPrimesIn_le_invertedPrimeClasses (R := R) (K := K) S)

/-- The generic obstruction target is the ordinary class group modulo the subgroup generated by
the classes of the height-one primes in `S`. -/
def obstructionTargetEquivSClassGroup (S : Set <| HeightOneSpectrum R) :
    obstructionTarget (R := R) (K := K) S ≃* SClassGroup (R := R) S :=
  (QuotientGroup.quotientKerEquivOfSurjective
    (classGroupToObstructionTarget (R := R) (K := K) S)
      (classGroupToObstructionTarget_surjective (R := R) (K := K) S)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq
          (invertedPrimeClasses_eq_classesOfPrimesIn (R := R) (K := K) S))

/-! ### Compatibility with the ordinary class sequence -/

private theorem fractionalIdealToDivisorAway_empty_injective :
    Function.Injective
      (fractionalIdealToDivisorAway (R := R) (K := K)
        (∅ : Set <| HeightOneSpectrum R)) := by
  intro I J hIJ
  apply (fractionalIdealFactorization (R := R) (K := K)).injective
  apply Multiplicative.toAdd.injective
  apply Finsupp.ext
  intro v
  have h := congr_arg
    (fun e : DivisorAway (∅ : Set <| HeightOneSpectrum R) ↦
      e.toAdd ⟨v, Set.notMem_empty v⟩) hIJ
  simpa only [fractionalIdealToDivisorAway_apply,
    fractionalIdealFactorization_apply] using h

/-- The canonical class-group map is injective when no prime coordinates are discarded. -/
theorem classGroupToObstructionTarget_empty_injective :
    Function.Injective
      (classGroupToObstructionTarget (R := R) (K := K)
        (∅ : Set <| HeightOneSpectrum R)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext c
  constructor
  · intro hc
    change c = 1
    revert hc
    refine ClassGroup.induction K ?_ c
    intro I hI
    rw [MonoidHom.mem_ker, classGroupToObstructionTarget_mk] at hI
    obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff _).mp hI
    have hxI : toPrincipalIdeal R K x = I :=
      fractionalIdealToDivisorAway_empty_injective (R := R) (K := K) <| by
        simpa only [principalDivisorAway, MonoidHom.comp_apply] using hx
    rw [← hxI]
    change ClassGroup.mk K (toPrincipalIdeal R K x) = 1
    rw [ClassGroup.mk_eq_one_iff]
    rw [coe_toPrincipalIdeal]
    exact (FractionalIdeal.isPrincipal_iff _).mpr ⟨(x : K), rfl⟩
  · rintro rfl
    exact Subgroup.one_mem _

/-- For the empty set, the generic obstruction target is the ordinary class group. -/
def obstructionTargetEmptyEquivClassGroup :
    obstructionTarget (R := R) (K := K) (∅ : Set <| HeightOneSpectrum R) ≃* ClassGroup R :=
  (MulEquiv.ofBijective
    (classGroupToObstructionTarget (R := R) (K := K)
      (∅ : Set <| HeightOneSpectrum R))
    ⟨classGroupToObstructionTarget_empty_injective (R := R) (K := K),
      classGroupToObstructionTarget_surjective (R := R) (K := K) ∅⟩).symm

private theorem classGroupEquiv_symm_mk (I : (FractionalIdeal R⁰ K)ˣ) :
    (ClassGroup.equiv K).symm (QuotientGroup.mk I) = ClassGroup.mk K I := by
  apply (ClassGroup.equiv K).injective
  rw [MulEquiv.apply_symm_apply]
  rw [ClassGroup.equiv_mk K K I]
  apply congr_arg (QuotientGroup.mk' (toPrincipalIdeal R K).range)
  apply Units.ext
  simp only [Units.coe_mapEquiv]
  rw [FractionalIdeal.canonicalEquiv_self]
  rfl

/-- Read back the ideal class selected by the empty-support Selmer
obstruction.  If a representative `x` has principal fractional ideal equal
to the `n`th power of `I`, then the class-group obstruction of its Selmer
class is literally `ClassGroup.mk K I`.

This is the public computation rule needed by arithmetic constructions that
already possess an ideal root.  It avoids choosing a second root inside the
consumer: uniqueness in the factorization geometry identifies the canonical
root used by `toClass` with the supplied one. -/
theorem toClass_eq_mk_of_representative_root [Fact <| 0 < n]
    (q : K⟮(∅ : Set <| HeightOneSpectrum R), n⟯)
    (x : Kˣ)
    (hx : q.1 = QuotientGroup.mk x)
    (I : (FractionalIdeal R⁰ K)ˣ)
    (hI : I ^ n = toPrincipalIdeal R K x) :
    toClass (R := R) (K := K) (n := n) q = ClassGroup.mk K I := by
  let f := toPrincipalIdeal R K
  let geometry := fractionalIdealFactorization (R := R) (K := K)
  let e := selmerEquivDivisibleClasses (R := R) (K := K) (n := n)
  let divisible : PowerRoot.divisibleElements f n :=
    ⟨x, (PowerRoot.mem_powerSubgroup).2 ⟨I, hI⟩⟩
  have hdivisible :
      PowerRoot.toDivisibleClasses f n divisible = e q := by
    apply Subtype.ext
    rw [PowerRoot.toDivisibleClasses_apply]
    change QuotientGroup.mk x = q.1
    exact hx.symm
  rw [toClass]
  change (ClassGroup.equiv K).symm
      (PowerRoot.obstruction (f := f) (n := n) geometry (e q)) = _
  rw [← hdivisible, PowerRoot.obstruction_toDivisibleClasses]
  rw [PowerRoot.root_eq_of_pow_eq (f := f) (n := n)
    geometry divisible hI]
  exact classGroupEquiv_symm_mk I

private theorem classGroupToObstructionTarget_toClass_eq_toSClass [Fact <| 0 < n]
    (q : K⟮(∅ : Set <| HeightOneSpectrum R),n⟯) :
    classGroupToObstructionTarget (R := R) (K := K) ∅
        (toClass (R := R) (K := K) (n := n) q) =
      toSClass (R := R) (K := K) (n := n) ∅ q := by
  let f := toPrincipalIdeal R K
  let fAway := principalDivisorAway (R := R) (K := K)
    (∅ : Set <| HeightOneSpectrum R)
  let e := selmerEquivDivisibleClasses (R := R) (K := K) (n := n)
  let eAway := equivDivisibleClasses (R := R) (K := K) (n := n)
    (∅ : Set <| HeightOneSpectrum R)
  obtain ⟨x, hx⟩ := PowerRoot.toDivisibleClasses_surjective f n (e q)
  let xAway : PowerRoot.divisibleElements fAway n := ⟨(x : Kˣ), by
    obtain ⟨I, hI⟩ := (PowerRoot.mem_powerSubgroup).mp x.property
    apply (PowerRoot.mem_powerSubgroup).mpr
    refine ⟨fractionalIdealToDivisorAway (R := R) (K := K) ∅ I, ?_⟩
    rw [← map_pow, hI]
    rfl⟩
  have hxAway : PowerRoot.toDivisibleClasses fAway n xAway = eAway q := by
    apply Subtype.ext
    rw [PowerRoot.toDivisibleClasses_apply]
    have hx' := congr_arg Subtype.val hx
    exact hx'
  rw [toClass, toSClass]
  change classGroupToObstructionTarget (R := R) (K := K) ∅
      ((ClassGroup.equiv K).symm
        (PowerRoot.obstruction (f := f) (n := n)
          (fractionalIdealFactorization (R := R) (K := K)) (e q))) =
    PowerRoot.obstruction (f := fAway) (n := n)
      (MulEquiv.refl (DivisorAway ∅)) (eAway q)
  rw [← hx, ← hxAway, PowerRoot.obstruction_toDivisibleClasses,
    PowerRoot.obstruction_toDivisibleClasses, classGroupEquiv_symm_mk,
    classGroupToObstructionTarget_mk]
  apply congr_arg QuotientGroup.mk
  let rootIdeal := PowerRoot.root f n
    (fractionalIdealFactorization (R := R) (K := K)) x
  symm
  apply PowerRoot.root_eq_of_pow_eq (f := fAway) (n := n)
    (MulEquiv.refl (DivisorAway ∅)) xAway
  change (fractionalIdealToDivisorAway (R := R) (K := K) ∅ rootIdeal) ^ n =
    fAway xAway
  rw [← map_pow, PowerRoot.root_power]
  rfl

/-- The finite-`S` obstruction specializes to the ordinary class-group obstruction at `S = ∅`. -/
theorem obstructionTargetEmptyEquivClassGroup_toSClass [Fact <| 0 < n]
    (q : K⟮(∅ : Set <| HeightOneSpectrum R),n⟯) :
    obstructionTargetEmptyEquivClassGroup (R := R) (K := K)
        (toSClass (R := R) (K := K) (n := n) ∅ q) =
      toClass (R := R) (K := K) (n := n) q := by
  let E : ClassGroup R ≃*
      obstructionTarget (R := R) (K := K) (∅ : Set <| HeightOneSpectrum R) :=
    MulEquiv.ofBijective
      (classGroupToObstructionTarget (R := R) (K := K) ∅)
      ⟨classGroupToObstructionTarget_empty_injective (R := R) (K := K),
        classGroupToObstructionTarget_surjective (R := R) (K := K) ∅⟩
  change E.symm (toSClass (R := R) (K := K) (n := n) ∅ q) = _
  apply E.injective
  rw [E.apply_symm_apply]
  exact (classGroupToObstructionTarget_toClass_eq_toSClass
    (R := R) (K := K) (n := n) q).symm

/-- Homomorphism form of the compatibility of the empty-set obstructions. -/
theorem obstructionTargetEmptyEquivClassGroup_comp_toSClass [Fact <| 0 < n] :
    (obstructionTargetEmptyEquivClassGroup (R := R) (K := K)).toMonoidHom.comp
        (toSClass (R := R) (K := K) (n := n) ∅) =
      toClass (R := R) (K := K) (n := n) := by
  ext q
  exact obstructionTargetEmptyEquivClassGroup_toSClass
    (R := R) (K := K) (n := n) q

/-- The empty-set generic and ordinary obstruction maps have the same kernel. -/
theorem toSClass_empty_ker_eq_toClass_ker [Fact <| 0 < n] :
    (toSClass (R := R) (K := K) (n := n) ∅).ker =
      (toClass (R := R) (K := K) (n := n)).ker := by
  let E := obstructionTargetEmptyEquivClassGroup (R := R) (K := K)
  let f := toSClass (R := R) (K := K) (n := n)
    (∅ : Set <| HeightOneSpectrum R)
  have h : E.toMonoidHom.comp f = toClass (R := R) (K := K) (n := n) :=
    obstructionTargetEmptyEquivClassGroup_comp_toSClass
      (R := R) (K := K) (n := n)
  calc
    f.ker = (E.toMonoidHom.comp f).ker := (MonoidHom.ker_mulEquiv_comp f E).symm
    _ = _ := congr_arg MonoidHom.ker h

/-- Mapping the empty-set generic obstruction range through the compatibility equivalence gives
the ordinary class-group obstruction range. -/
theorem map_toSClass_empty_range_eq_toClass_range [Fact <| 0 < n] :
    Subgroup.map
        (obstructionTargetEmptyEquivClassGroup (R := R) (K := K)).toMonoidHom
        (toSClass (R := R) (K := K) (n := n) ∅).range =
      (toClass (R := R) (K := K) (n := n)).range := by
  let E := obstructionTargetEmptyEquivClassGroup (R := R) (K := K)
  let f := toSClass (R := R) (K := K) (n := n)
    (∅ : Set <| HeightOneSpectrum R)
  have h : E.toMonoidHom.comp f = toClass (R := R) (K := K) (n := n) :=
    obstructionTargetEmptyEquivClassGroup_comp_toSClass
      (R := R) (K := K) (n := n)
  calc
    Subgroup.map E.toMonoidHom f.range = (E.toMonoidHom.comp f).range :=
      (MonoidHom.range_comp E.toMonoidHom f).symm
    _ = _ := congr_arg MonoidHom.range h

end selmerGroup

end

end IsDedekindDomain
