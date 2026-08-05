/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Fabian Franz

# Vendored Selmer unit-class sequence

This is a faithful port of the empty-support Selmer unit-class sequence from:

* pull request: `https://github.com/fabianx-ai/mathlib4/pull/1`;
* source commit: `6c01b3a6a13de72eabd868ca50d743f43888af92`;
* source file: `Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean`;
* source-file SHA-256:
  `37d78b8e5b3f9b757d1eb8b33286680501820aba250644a407e36381ee34c4d2`.

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
   used by the sequence and the block from `preSelmer` through
   `toClass_range`. Existing pinned `SelmerGroup` material and upstream
   documentation/import reordering are not duplicated;
5. the source's `MonoidHom.domRestrict` is written under its name at the pin,
   `MonoidHom.restrict`;
6. the source's `Set.mem_ofPred_eq` is written under its name at the pin,
   `Set.mem_setOf_eq`.

There are no declaration, statement, or proof-body improvements. Apart from
the compatibility and standalone-file deltas listed above, the vendored
declarations are copied verbatim.
-/

import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

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

private abbrev preSelmer : Subgroup Kˣ :=
  K⟮(∅ : Set <| HeightOneSpectrum R), n⟯.comap
    (QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range)

private def preSelmerToSelmer : preSelmer (R := R) (K := K) (n := n) →*
    K⟮(∅ : Set <| HeightOneSpectrum R), n⟯ :=
  ((QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range).restrict
    (preSelmer (R := R) (K := K) (n := n))).codRestrict _ fun x ↦ x.property

private theorem preSelmerToSelmer_surjective :
    Function.Surjective (preSelmerToSelmer (R := R) (K := K) (n := n)) := by
  intro x
  let y : Kˣ := x.1.out
  have hy : QuotientGroup.mk y = x.1 := QuotientGroup.out_eq' x.1
  refine ⟨⟨y, ?_⟩, ?_⟩
  · change QuotientGroup.mk y ∈ K⟮(∅ : Set <| HeightOneSpectrum R), n⟯
    rw [hy]
    exact x.property
  · exact Subtype.ext hy

private def rootIdeal (n : ℕ) (x : Kˣ) : FractionalIdeal R⁰ K :=
  ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
    Int.ediv (FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (x : K))) n

private theorem rootIdeal_ne_zero (n : ℕ) (x : Kˣ) : rootIdeal (R := R) n x ≠ 0 := by
  apply finprod_ne_zero
  intro v
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

private theorem count_dvd (x : preSelmer (R := R) (K := K) (n := n))
    (v : HeightOneSpectrum R) :
    (n : ℤ) ∣ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton R⁰ ((x : Kˣ) : K)) := by
  rw [v.count_spanSingleton]
  have hx : v.valuationOfNeZeroMod n (QuotientGroup.mk (x : Kˣ)) = 1 :=
    x.property v (Set.notMem_empty v)
  exact Int.dvd_neg.mpr ((v.valuation_mod_eq_one_iff n (x : Kˣ)).mp hx)

private theorem rootIdeal_hasFiniteMulSupport (n : ℕ) (x : Kˣ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum R ↦
      (v.asIdeal : FractionalIdeal R⁰ K) ^
        Int.ediv (FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton R⁰ (x : K))) n := by
  have he : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      Int.ediv (FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton R⁰ (x : K))) n = 0 :=
    (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton R⁰ (x : K))).mono
      fun _ h ↦ by rw [h]; exact Int.zero_ediv _
  refine (Filter.eventually_cofinite.mp he).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq, Function.mem_mulSupport] at hv ⊢
  contrapose! hv
  simp [hv]

private theorem rootIdeal_one : rootIdeal (R := R) n (1 : Kˣ) = 1 := by
  rw [rootIdeal]
  simp only [Units.val_one, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
  rw [show Int.ediv 0 (n : ℤ) = 0 from Int.zero_ediv _]
  simp

private theorem rootIdeal_mul (x y : preSelmer (R := R) (K := K) (n := n)) :
    rootIdeal (R := R) n (x * y : Kˣ) =
      rootIdeal (R := R) n x * rootIdeal (R := R) n y := by
  rw [rootIdeal, rootIdeal, rootIdeal,
    ← finprod_mul_distrib
      (rootIdeal_hasFiniteMulSupport (R := R) (K := K) n (x : Kˣ))
      (rootIdeal_hasFiniteMulSupport (R := R) (K := K) n (y : Kˣ))]
  apply finprod_congr
  intro v
  rw [← zpow_add₀ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)]
  congr 1
  rw [show FractionalIdeal.spanSingleton R⁰ ((((x : Kˣ) * (y : Kˣ)) : Kˣ) : K) =
      FractionalIdeal.spanSingleton R⁰ ((x : Kˣ) : K) *
        FractionalIdeal.spanSingleton R⁰ ((y : Kˣ) : K) by simp]
  rw [FractionalIdeal.count_mul]
  · exact Int.add_ediv_of_dvd_left (count_dvd x v)
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr (x : Kˣ).ne_zero
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr (y : Kˣ).ne_zero

private def rootIdealHom : preSelmer (R := R) (K := K) (n := n) →*
    (FractionalIdeal R⁰ K)ˣ where
  toFun x := Units.mk0 (rootIdeal (R := R) n (x : Kˣ)) (rootIdeal_ne_zero n (x : Kˣ))
  map_one' := Units.ext rootIdeal_one
  map_mul' x y := Units.ext (rootIdeal_mul x y)

private def preToClass : preSelmer (R := R) (K := K) (n := n) →* ClassGroup R :=
  (ClassGroup.mk K).comp (rootIdealHom (R := R) (K := K) (n := n))

private theorem rootIdeal_pow [hn : Fact <| 0 < n] (y : Kˣ) :
    rootIdeal (R := R) n (y ^ n) = FractionalIdeal.spanSingleton R⁰ (y : K) := by
  rw [rootIdeal, ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr y.ne_zero)]
  apply finprod_congr
  intro v
  congr 1
  simp only [Units.val_pow_eq_pow_val, ← FractionalIdeal.spanSingleton_pow,
    FractionalIdeal.count_pow]
  exact Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hn.out))

private theorem rootIdeal_pow_eq (x : preSelmer (R := R) (K := K) (n := n)) :
    rootIdeal (R := R) n (x : Kˣ) ^ n =
      FractionalIdeal.spanSingleton R⁰ ((x : Kˣ) : K) := by
  rw [rootIdeal, finprod_pow
    (rootIdeal_hasFiniteMulSupport (R := R) (K := K) n (x : Kˣ)) n]
  conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (x : Kˣ).ne_zero)]
  apply finprod_congr
  intro v
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  exact Int.ediv_mul_cancel (count_dvd x v)

private theorem preSelmerToSelmer_ker_le [Fact <| 0 < n] :
    (preSelmerToSelmer (R := R) (K := K) (n := n)).ker ≤
      (preToClass (R := R) (K := K) (n := n)).ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  have hx' : QuotientGroup.mk (x : Kˣ) = (1 : K / n) := congr_arg Subtype.val hx
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff (x : Kˣ)).mp hx'
  change ClassGroup.mk K (Units.mk0 (rootIdeal (R := R) n (x : Kˣ))
    (rootIdeal_ne_zero n (x : Kˣ))) = 1
  rw [ClassGroup.mk_eq_one_iff]
  change (rootIdeal (R := R) n (x : Kˣ) : Submodule R K).IsPrincipal
  have hxy : (x : Kˣ) = y ^ n := by simpa only [powMonoidHom_apply] using hy.symm
  have hroot : rootIdeal (R := R) n (x : Kˣ) =
      FractionalIdeal.spanSingleton R⁰ (y : K) := by
    rw [hxy, rootIdeal_pow]
  rw [hroot]
  exact (FractionalIdeal.isPrincipal_iff _).mpr ⟨(y : K), rfl⟩

/-- The class of the `n`-th root ideal associated to an element of `K⟮∅, n⟯`. -/
def toClass [Fact <| 0 < n] :
    K⟮(∅ : Set <| HeightOneSpectrum R), n⟯ →* ClassGroup R :=
  (preSelmerToSelmer (R := R) (K := K) (n := n)).liftOfSurjective
    (preSelmerToSelmer_surjective (R := R) (K := K) (n := n))
      ⟨preToClass (R := R) (K := K) (n := n), preSelmerToSelmer_ker_le⟩

@[simp]
private theorem toClass_apply [Fact <| 0 < n]
    (x : preSelmer (R := R) (K := K) (n := n)) :
    toClass (R := R) (K := K) (n := n) (preSelmerToSelmer x) = preToClass x := by
  simp [toClass]

private theorem fromUnitLift_mk [Fact <| 0 < n] (u : Rˣ) :
    fromUnitLift (R := R) (K := K) (n := n) (QuotientGroup.mk u) =
      fromUnit (K := K) (n := n) u := rfl

private def preFromUnit (u : Rˣ) : preSelmer (R := R) (K := K) (n := n) :=
  ⟨Units.map (algebraMap R K : R →* K) u, fun v _ ↦ v.valuation_of_unit_mod_eq n u⟩

private theorem preSelmerToSelmer_preFromUnit (u : Rˣ) :
    preSelmerToSelmer (preFromUnit (K := K) (n := n) u) =
      fromUnit (K := K) (n := n) u := rfl

private theorem rootIdeal_fromUnit (u : Rˣ) :
    rootIdeal (R := R) n (Units.map (algebraMap R K : R →* K) u) = 1 := by
  rw [rootIdeal]
  have hc : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton R⁰
        (Units.map (algebraMap R K : R →* K) u : K)) = 0 := by
    intro v
    rw [v.count_spanSingleton]
    simp [v.valuation_of_unit_eq]
  simp only [hc]
  rw [show Int.ediv 0 (n : ℤ) = 0 from Int.zero_ediv _]
  simp

private theorem toClass_fromUnit [Fact <| 0 < n] (u : Rˣ) :
    toClass (R := R) (K := K) (n := n) (fromUnit (K := K) (n := n) u) = 1 := by
  rw [← preSelmerToSelmer_preFromUnit, toClass_apply]
  change ClassGroup.mk K
    (rootIdealHom (R := R) (K := K) (n := n) (preFromUnit (K := K) (n := n) u)) = 1
  rw [← map_one (ClassGroup.mk K)]
  congr 1
  apply Units.ext
  exact rootIdeal_fromUnit u

/-- The kernel of `toClass` is the range of the unit classes in `K⟮∅, n⟯`. -/
theorem toClass_ker [Fact <| 0 < n] :
    (toClass (R := R) (K := K) (n := n)).ker =
      (fromUnitLift (R := R) (K := K) (n := n)).range := by
  ext a
  constructor
  · intro ha
    obtain ⟨x, rfl⟩ := preSelmerToSelmer_surjective (R := R) (K := K) (n := n) a
    rw [MonoidHom.mem_ker, toClass_apply] at ha
    change ClassGroup.mk K (rootIdealHom (R := R) (K := K) (n := n) x) = 1 at ha
    have hp := ClassGroup.mk_eq_one_iff.mp ha
    change (rootIdeal (R := R) n (x : Kˣ) : Submodule R K).IsPrincipal at hp
    obtain ⟨y, hyJ⟩ := (FractionalIdeal.isPrincipal_iff _).mp hp
    have hy : y ≠ 0 := by
      rintro rfl
      apply rootIdeal_ne_zero (R := R) (K := K) n (x : Kˣ)
      simpa only [FractionalIdeal.spanSingleton_zero] using hyJ
    have hspan : FractionalIdeal.spanSingleton R⁰ (y ^ n) =
        FractionalIdeal.spanSingleton R⁰ ((x : Kˣ) : K) := by
      rw [← FractionalIdeal.spanSingleton_pow, ← hyJ, rootIdeal_pow_eq x]
    obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan
    refine ⟨QuotientGroup.mk u, ?_⟩
    rw [fromUnitLift_mk]
    apply Subtype.ext
    apply (QuotientGroup.mk'_eq_mk' (powMonoidHom n : Kˣ →* Kˣ).range).mpr
    refine ⟨(Units.mk0 y hy) ^ n, ⟨Units.mk0 y hy, rfl⟩, ?_⟩
    rw [Units.smul_def, Algebra.smul_def] at hu
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      Units.val_pow_eq_pow_val, Units.val_mk0]
    convert hu <;> rfl
  · rintro ⟨q, rfl⟩
    rw [MonoidHom.mem_ker]
    induction q using QuotientGroup.induction_on with
    | _ u => rw [fromUnitLift_mk, toClass_fromUnit]

/-- The range of `toClass` is the subgroup of `n`-torsion ideal classes. -/
theorem toClass_range [hn : Fact <| 0 < n] :
    (toClass (R := R) (K := K) (n := n)).range =
      (powMonoidHom n : ClassGroup R →* ClassGroup R).ker := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    obtain ⟨x, rfl⟩ := preSelmerToSelmer_surjective (R := R) (K := K) (n := n) a
    rw [toClass_apply]
    change (ClassGroup.mk K (rootIdealHom (R := R) (K := K) (n := n) x)) ^ n = 1
    rw [← map_pow, ClassGroup.mk_eq_one_iff]
    change ((rootIdeal (R := R) n (x : Kˣ) ^ n : FractionalIdeal R⁰ K) :
      Submodule R K).IsPrincipal
    rw [rootIdeal_pow_eq x]
    exact (FractionalIdeal.isPrincipal_iff _).mpr ⟨((x : Kˣ) : K), rfl⟩
  · intro c hc
    revert hc
    refine ClassGroup.induction K ?_ c
    intro I hI
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at hI
    have hIpow : ClassGroup.mk K (I ^ n) = 1 := by
      simpa only [map_pow] using hI
    have hp := ClassGroup.mk_eq_one_iff.mp hIpow
    change (((I : FractionalIdeal R⁰ K) ^ n : FractionalIdeal R⁰ K) :
      Submodule R K).IsPrincipal at hp
    obtain ⟨x, hxI⟩ :=
      (FractionalIdeal.isPrincipal_iff ((I : FractionalIdeal R⁰ K) ^ n)).mp hp
    change (I : FractionalIdeal R⁰ K) ^ n = FractionalIdeal.spanSingleton R⁰ x at hxI
    have hx : x ≠ 0 := by
      rintro rfl
      apply pow_ne_zero n I.ne_zero
      simpa only [FractionalIdeal.spanSingleton_zero] using hxI
    let y : Kˣ := Units.mk0 x hx
    have hy : y ∈ preSelmer (R := R) (K := K) (n := n) := by
      intro v _
      apply (v.valuation_mod_eq_one_iff n y).mpr
      apply Int.dvd_neg.mp
      rw [← v.count_spanSingleton]
      change (n : ℤ) ∣ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)
      rw [← hxI, FractionalIdeal.count_pow]
      exact dvd_mul_right (n : ℤ) (FractionalIdeal.count K v (I : FractionalIdeal R⁰ K))
    let z : preSelmer (R := R) (K := K) (n := n) := ⟨y, hy⟩
    refine ⟨preSelmerToSelmer z, ?_⟩
    rw [toClass_apply]
    change ClassGroup.mk K (rootIdealHom (R := R) (K := K) (n := n) z) =
      ClassGroup.mk K I
    congr 1
    apply Units.ext
    change rootIdeal (R := R) n y = (I : FractionalIdeal R⁰ K)
    rw [rootIdeal, ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero]
    apply finprod_congr
    intro v
    congr 1
    change Int.ediv (FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)) n =
      FractionalIdeal.count K v (I : FractionalIdeal R⁰ K)
    rw [← hxI, FractionalIdeal.count_pow]
    exact Int.mul_ediv_cancel_left _
      (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hn.out))

end selmerGroup

end

end IsDedekindDomain
