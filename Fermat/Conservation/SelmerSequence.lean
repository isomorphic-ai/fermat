/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Fabian Franz

# Vendored generic derivation of the Selmer unit-class sequence

This is a faithful port of the generic power-root derivation of the
empty-support Selmer unit-class sequence from our Mathlib branch
`power-root-obstruction`:

* pull request: `https://github.com/fabianx-ai/mathlib4/pull/1`;
* generator introduction commit:
  `4ea7450c8a5844417866addb7fba766275a1945a`;
* integration/source commit:
  `889be7a3fee66e6630d25332a501409fa35d8590`;
* source file: `Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean`;
* source-file SHA-256:
  `a6fb493fdaf8686eed654b4b0f7abe84ef14d4198304ef4dcf9f8160c8afd2f6`.

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
   `SelmerGroup` supplying the pre-existing definitions and with the two new
   upstream dependencies (`ClassGroup.Basic` and `Factorization`) imported
   explicitly;
2. the source's `module`, `public`, and enclosing `@[expose]` commands are
   omitted, and the export-control-only `@[no_expose]` attribute on `toClass`
   is omitted;
3. the source file's two file-local notations and `quotPrecheck` option are
   repeated because they do not cross an import boundary;
4. only the requested additions are copied: the two private valuation helpers
   used by the sequence and the generic integration block from
   `fractionalIdealExponents` through `toClass_range`. Existing pinned
   `SelmerGroup` material and upstream documentation/import reordering are not
   duplicated;
5. the upstream import of `Mathlib.GroupTheory.PowerRootObstruction` is
   redirected to the provenance-pinned route-neutral copy
   `Fermat.Conservation.PowerRootObstruction`;
6. the otherwise file-private `fractionalIdealFactorization` is exported so
   the cube can name exactly the geometry used by this obstruction square,
   rather than constructing a second, propositionally equivalent geometry;
7. the source's result-type ascription on the quotient `powMonoidHom` is
   replaced by an explicit `(α := ...)` argument. Lean 4.31 otherwise chooses
   incompatible `Monoid` instance paths before learning the quotient type.

There are no declaration, statement, or proof-body improvements. Apart from
the compatibility and standalone-file deltas listed above, the vendored
declarations are copied verbatim.
-/

import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
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

private theorem fractionalIdealFactorization_apply (I : (FractionalIdeal R⁰ K)ˣ)
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

end selmerGroup

end

end IsDedekindDomain
