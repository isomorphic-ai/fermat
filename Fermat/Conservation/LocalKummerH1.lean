/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The discrete absolute-Galois Kummer map in degree one

For a field `K` and a positive integer `n`, this file constructs the classical
Kummer connecting map

`Kˣ / (Kˣ)^n → H¹(G_K, μ_n)`

for Mathlib's *discrete* group cohomology.  A representative `a` is sent to
the cocycle `σ ↦ σ(√[n]{a}) / √[n]{a}` in an algebraic closure.  The root is
chosen noncomputably; changing roots only changes the cocycle by a
coboundary, which is also what proves multiplicativity.

This is deliberately not advertised as local continuous Galois cohomology.
Pinned Mathlib has a general `continuousCohomology` functor, but currently no
low-degree cocycle/quotient API or comparison map with discrete `H1`.  The
construction here is nevertheless the honest algebraic Kummer class used by
the discrete cup-product layer.
-/
import Fermat.Conservation.TameSymbol
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Module.ZMod
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Tactic.Group

noncomputable section

namespace Fermat.Conservation.LocalKummerH1

open Fermat.Conservation.TameSymbol
open groupCohomology

variable (n : ℕ) (K : Type) [Field K] [NeZero n]

/-- The absolute Galois group used by the discrete Kummer construction. -/
abbrev AbsoluteGalois := Field.absoluteGaloisGroup K

/-- The `n`-th roots of unity in the chosen algebraic closure. -/
abbrev KummerRoots := rootsOfUnity n (AlgebraicClosure K)

/- Scoped discrete coefficient topology on the finite roots-of-unity
carrier.  Keeping this instance scoped avoids competing with any future
intrinsic topology on roots of unity. -/
namespace KummerRootsDiscrete

scoped instance : TopologicalSpace (KummerRoots n K) := ⊥
scoped instance : DiscreteTopology (KummerRoots n K) := ⟨rfl⟩

end KummerRootsDiscrete

/-- The natural action on the chosen algebraic closure.  As for units below,
this must be stated explicitly because `AbsoluteGalois` is a named definition
rather than the syntactic `AlgEquiv` type used by the generic instance. -/
instance absoluteGaloisFieldAction :
    MulDistribMulAction (AbsoluteGalois K) (AlgebraicClosure K) where
  smul σ x :=
    (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from σ) x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul σ x y := σ.map_mul x y
  smul_one σ := σ.map_one

/-- The natural action on algebraic-closure units.  This instance is stated
explicitly because `Field.absoluteGaloisGroup` is a named definition rather
than the syntactic `AlgEquiv` type expected by Mathlib's generic instance. -/
instance absoluteGaloisUnitsAction :
    MulDistribMulAction (AbsoluteGalois K) (AlgebraicClosure K)ˣ where
  smul σ a := Units.map σ.toMonoidHom a
  one_smul a := by
    apply Units.ext
    rfl
  mul_smul σ τ a := by
    apply Units.ext
    rfl
  smul_mul σ a b := by
    apply Units.ext
    exact (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from σ).map_mul a b
  smul_one σ := by
    apply Units.ext
    exact (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from σ).map_one

@[simp]
theorem coe_absoluteGalois_smul_unit
    (σ : AbsoluteGalois K) (a : (AlgebraicClosure K)ˣ) :
    ((σ • a : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
      σ • (a : AlgebraicClosure K) :=
  rfl

/-- The absolute Galois action on roots of unity, obtained by restricting its
action on the units of the algebraic closure. -/
instance kummerRootsAction :
    MulDistribMulAction (AbsoluteGalois K) (KummerRoots n K) where
  smul σ ζ := σ.toMulEquiv.restrictRootsOfUnity n ζ
  one_smul ζ := by
    apply Subtype.ext
    rfl
  mul_smul σ τ ζ := by
    apply Subtype.ext
    rfl
  smul_mul σ ζ ξ := by
    apply Subtype.ext
    exact smul_mul' σ (ζ : (AlgebraicClosure K)ˣ) ξ
  smul_one σ := by
    apply Subtype.ext
    exact smul_one σ

omit [NeZero n] in
/-- Additively written `n`-th roots of unity are killed by `n`. -/
theorem nsmul_kummerRoots_eq_zero (x : Additive (KummerRoots n K)) :
    n • x = 0 := by
  apply Additive.toMul.injective
  rw [toMul_nsmul]
  apply Subtype.ext
  exact x.toMul.prop

/-- The canonical `ZMod n`-module structure on additively written roots of
unity. -/
noncomputable instance kummerRootsZModModule :
    Module (ZMod n) (Additive (KummerRoots n K)) :=
  AddCommGroup.zmodModule (nsmul_kummerRoots_eq_zero n K)

/-- The Galois action on roots of unity, written additively. -/
instance kummerRootsAdditiveAction :
    DistribMulAction (AbsoluteGalois K) (Additive (KummerRoots n K)) where
  smul σ x := Additive.ofMul (σ • x.toMul)
  one_smul x := by
    apply Additive.toMul.injective
    exact one_smul (AbsoluteGalois K) x.toMul
  mul_smul σ τ x := by
    apply Additive.toMul.injective
    exact mul_smul σ τ x.toMul
  smul_zero σ := by
    apply Additive.toMul.injective
    exact smul_one σ
  smul_add σ x y := by
    apply Additive.toMul.injective
    exact smul_mul' σ x.toMul y.toMul

/-- One Galois operator as an additive homomorphism on `μ_n`. -/
private def galoisRootsAddHom (σ : AbsoluteGalois K) :
    Additive (KummerRoots n K) →+ Additive (KummerRoots n K) :=
  DistribSMul.toAddMonoidHom _ σ

/-- The Galois action is automatically `ZMod n`-linear: every additive map
between `ZMod n` modules commutes with the canonical scalar action. -/
instance kummerRootsSMulCommClass :
    SMulCommClass (AbsoluteGalois K) (ZMod n)
      (Additive (KummerRoots n K)) where
  smul_comm σ c x :=
    ZMod.map_smul (galoisRootsAddHom n K σ) c x

/-- The `ZMod n`-linear representation on `μ_n` underlying discrete Kummer
`H¹`. -/
abbrev rootsRepresentation :=
  Rep.ofDistribMulAction (ZMod n) (AbsoluteGalois K)
    (Additive (KummerRoots n K))

/-- Discrete group cohomology `H¹(G_K, μ_n)`.

The adjective `Discrete` is mathematically important: comparison with
continuous Galois cohomology remains a separate theorem. -/
abbrev DiscreteKummerH1 := H1 (rootsRepresentation n K)

private theorem exists_rootUnit (a : Kˣ) :
    ∃ r : (AlgebraicClosure K)ˣ,
      r ^ n = Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a := by
  obtain ⟨r, hr⟩ :=
    IsAlgClosed.exists_pow_nat_eq
      (algebraMap K (AlgebraicClosure K) (a : K)) (NeZero.pos n)
  have ha : algebraMap K (AlgebraicClosure K) (a : K) ≠ 0 :=
    by simpa only [map_zero] using
      (algebraMap K (AlgebraicClosure K)).injective.ne (Units.ne_zero a)
  have hr0 : r ≠ 0 := by
    intro h
    apply ha
    rw [← hr, h, zero_pow (NeZero.ne n)]
  refine ⟨Units.mk0 r hr0, ?_⟩
  apply Units.ext
  exact hr

/-- A noncomputably chosen `n`-th root of a base-field unit. -/
private def rootUnit (a : Kˣ) : (AlgebraicClosure K)ˣ :=
  (exists_rootUnit n K a).choose

@[simp]
private theorem rootUnit_pow (a : Kˣ) :
    rootUnit n K a ^ n =
      Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a :=
  (exists_rootUnit n K a).choose_spec

@[simp]
private theorem map_baseUnit_mul (a b : Kˣ) :
    Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom (a * b) =
      Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a *
        Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom b :=
  map_mul _ a b

@[simp]
private theorem smul_baseUnit (σ : AbsoluteGalois K) (a : Kˣ) :
    σ • Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a =
      Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a := by
  apply Units.ext
  exact σ.commutes (a : K)

/-- The representative Kummer cocycle value `σ(√[n]{a}) / √[n]{a}`. -/
def cocycleValue (a : Kˣ) (σ : AbsoluteGalois K) : KummerRoots n K :=
  ⟨σ • rootUnit n K a / rootUnit n K a, by
    rw [mem_rootsOfUnity, div_pow, ← smul_pow', rootUnit_pow,
      smul_baseUnit]
    simp⟩

@[simp]
private theorem cocycleValue_coe (a : Kˣ) (σ : AbsoluteGalois K) :
    (cocycleValue n K a σ : (AlgebraicClosure K)ˣ) =
      σ • rootUnit n K a / rootUnit n K a :=
  rfl

/-- The concrete Kummer cocycle may be evaluated using any chosen root once
the acting Galois element fixes `μ_n`.

Without the fixed-roots hypothesis, changing the root changes the cocycle by
a coboundary.  When the base field contains all `n`-th roots of unity, as in
the oriented Kummer construction, the hypothesis holds and the pointwise
cocycle value is genuinely independent of the root choice. -/
theorem cocycleValue_coe_eq_of_root
    (a : Kˣ) (σ : AbsoluteGalois K)
    (r : (AlgebraicClosure K)ˣ)
    (hr : r ^ n =
      Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a)
    (hfix : ∀ η : KummerRoots n K, σ • η = η) :
    (cocycleValue n K a σ : (AlgebraicClosure K)ˣ) = σ • r / r := by
  let η : KummerRoots n K :=
    ⟨rootUnit n K a / r, by
      rw [mem_rootsOfUnity, div_pow, rootUnit_pow, hr]
      simp⟩
  have hη := congrArg Subtype.val (hfix η)
  change σ • (rootUnit n K a / r) = rootUnit n K a / r at hη
  rw [cocycleValue_coe]
  calc
    σ • rootUnit n K a / rootUnit n K a =
        (σ • (rootUnit n K a / r)) * (σ • r) /
          ((rootUnit n K a / r) * r) := by
            rw [← smul_mul']
            congr <;> simp
    _ = (rootUnit n K a / r) * (σ • r) /
          ((rootUnit n K a / r) * r) := by rw [hη]
    _ = σ • r / r := by
      simp only [div_eq_mul_inv]
      simp [mul_assoc, mul_comm]

/-- Compatibility of the chosen Kummer cocycles under taking powers of the
Kummer exponent.  If `σ` fixes `μ_n`, then raising the chosen
`(n * m)`-Kummer cocycle to the `m`-th power gives the chosen `n`-Kummer
cocycle pointwise.

The two noncomputably selected roots need not themselves be compatible.
The preceding root-independence theorem is exactly what removes that choice
from this statement. -/
theorem cocycleValue_coe_pow_eq
    (m : ℕ) [NeZero m] [NeZero (n * m)]
    (a : Kˣ) (σ : AbsoluteGalois K)
    (hfix : ∀ η : KummerRoots n K, σ • η = η) :
    (cocycleValue (n * m) K a σ : (AlgebraicClosure K)ˣ) ^ m =
      (cocycleValue n K a σ : (AlgebraicClosure K)ˣ) := by
  have hr : (rootUnit (n * m) K a ^ m) ^ n =
      Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a := by
    rw [← pow_mul]
    simpa only [mul_comm m n] using rootUnit_pow (n * m) K a
  rw [cocycleValue_coe_eq_of_root n K a σ
    (rootUnit (n * m) K a ^ m) hr hfix]
  rw [cocycleValue_coe, div_pow, smul_pow']

private theorem cocycleValue_isMulCocycle (a : Kˣ) :
    IsMulCocycle₁ (cocycleValue n K a) := by
  intro σ τ
  apply Subtype.ext
  change
    (σ * τ) • rootUnit n K a / rootUnit n K a =
      σ • (τ • rootUnit n K a / rootUnit n K a) *
        (σ • rootUnit n K a / rootUnit n K a)
  rw [mul_smul, smul_div']
  simp [div_eq_mul_inv, ← mul_assoc]

private theorem cocycleValue_isCocycle (a : Kˣ) :
    IsCocycle₁
      (fun σ : AbsoluteGalois K ↦ Additive.ofMul (cocycleValue n K a σ)) := by
  intro σ τ
  apply Additive.toMul.injective
  exact cocycleValue_isMulCocycle n K a σ τ

open scoped KummerRootsDiscrete Pointwise

/-- The chosen-root Kummer cocycle is locally constant, hence continuous,
for the Krull topology on the absolute Galois group and the discrete topology
on `μ_n`.

Indeed, every nonempty fiber is a left coset of the stabilizer of the chosen
algebraic root.  That stabilizer is open because the algebraic closure is an
integral extension of the base field.  This is only a continuity theorem for
the concrete cocycle; it does not manufacture a comparison with continuous
group cohomology. -/
theorem continuous_cocycleValue (a : Kˣ) :
    Continuous (cocycleValue n K a) := by
  rw [continuous_discrete_rng]
  intro zeta
  by_cases hfiber : ∃ τ, cocycleValue n K a τ = zeta
  · obtain ⟨τ, hτ⟩ := hfiber
    let r : (AlgebraicClosure K)ˣ := rootUnit n K a
    have hopen :
        IsOpen (MulAction.stabilizer (AbsoluteGalois K)
          (r : AlgebraicClosure K) : Set (AbsoluteGalois K)) :=
      by
        convert stabilizer_isOpen_of_isIntegral
          (K := K) (L := AlgebraicClosure K) r using 1
    have hfiber_eq :
        cocycleValue n K a ⁻¹' {zeta} =
          τ • (MulAction.stabilizer (AbsoluteGalois K)
            (r : AlgebraicClosure K) : Set (AbsoluteGalois K)) := by
      ext σ
      rw [Set.mem_preimage, Set.mem_singleton_iff, ← hτ,
        mem_leftCoset_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      constructor
      · intro heq
        have hunit : σ • r = τ • r := by
          apply div_left_injective
          exact congrArg Subtype.val heq
        have hval : σ • (r : AlgebraicClosure K) =
            τ • (r : AlgebraicClosure K) := by
          simpa only [coe_absoluteGalois_smul_unit] using
            congrArg Units.val hunit
        rw [mul_smul, inv_smul_eq_iff]
        exact hval
      · intro hfix
        rw [mul_smul, inv_smul_eq_iff] at hfix
        apply Subtype.ext
        change σ • r / r = τ • r / r
        rw [div_left_inj]
        apply Units.ext
        simpa only [coe_absoluteGalois_smul_unit] using hfix
    rw [hfiber_eq]
    exact hopen.leftCoset τ
  · have hfiber_eq : cocycleValue n K a ⁻¹' {zeta} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro σ hσ
      apply hfiber
      exact ⟨σ, by simpa using hσ⟩
    rw [hfiber_eq]
    exact isOpen_empty

/-- The chosen-root cocycle representing the Kummer class of `a`. -/
def cocycle (a : Kˣ) : cocycles₁ (rootsRepresentation n K) :=
  cocyclesOfIsCocycle₁ (cocycleValue_isCocycle n K a)

@[simp]
theorem cocycle_apply (a : Kˣ) (σ : AbsoluteGalois K) :
    Additive.toMul (cocycle n K a σ) = cocycleValue n K a σ :=
  rfl

/-- The discrete `H¹` class of a nonzero representative. -/
def classOfUnit (a : Kˣ) : DiscreteKummerH1 n K :=
  H1π (rootsRepresentation n K) (cocycle n K a)

private def rootOfOne : KummerRoots n K :=
  ⟨rootUnit n K 1, by
    rw [mem_rootsOfUnity, rootUnit_pow]
    rfl⟩

theorem classOfUnit_one : classOfUnit n K 1 = 0 := by
  rw [classOfUnit, H1π_eq_zero_iff, coboundaries₁]
  refine ⟨Additive.ofMul (rootOfOne n K), ?_⟩
  funext σ
  apply Additive.toMul.injective
  rfl

/-- The root-choice defect measuring failure of the chosen roots to multiply
on the nose.  It lies in `μ_n`, and its coboundary is precisely the difference
between the product cocycle and the cocycle of the product. -/
private def multiplicationDefect (a b : Kˣ) : KummerRoots n K :=
  ⟨rootUnit n K (a * b) / (rootUnit n K a * rootUnit n K b), by
    rw [mem_rootsOfUnity, div_pow, mul_pow, rootUnit_pow, rootUnit_pow,
      rootUnit_pow, map_baseUnit_mul]
    simp⟩

theorem classOfUnit_mul (a b : Kˣ) :
    classOfUnit n K (a * b) = classOfUnit n K a + classOfUnit n K b := by
  rw [classOfUnit, classOfUnit, classOfUnit, ← map_add, H1π_eq_iff]
  let x := cocycle n K (a * b)
  let y := cocycle n K a + cocycle n K b
  rw [coboundaries₁]
  refine ⟨Additive.ofMul (multiplicationDefect n K a b), ?_⟩
  funext σ
  change
    σ • Additive.ofMul (multiplicationDefect n K a b) -
        Additive.ofMul (multiplicationDefect n K a b) =
      Additive.ofMul (cocycleValue n K (a * b) σ) -
        (Additive.ofMul (cocycleValue n K a σ) +
          Additive.ofMul (cocycleValue n K b σ))
  apply Additive.toMul.injective
  simp only [toMul_sub, toMul_add]
  apply Subtype.ext
  change
    σ • (rootUnit n K (a * b) /
        (rootUnit n K a * rootUnit n K b)) /
        (rootUnit n K (a * b) /
          (rootUnit n K a * rootUnit n K b)) =
      (σ • rootUnit n K (a * b) / rootUnit n K (a * b)) /
        ((σ • rootUnit n K a / rootUnit n K a) *
          (σ • rootUnit n K b / rootUnit n K b))
  rw [smul_div', smul_mul']
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- The representative Kummer map is additive after writing `Kˣ`
multiplicatively as `Additive Kˣ`. -/
def representativeMap : Additive Kˣ →+ DiscreteKummerH1 n K where
  toFun a := classOfUnit n K a.toMul
  map_zero' := classOfUnit_one n K
  map_add' a b := classOfUnit_mul n K a.toMul b.toMul

omit [NeZero n] in
/-- Every class in `H¹(G_K, μ_n)` is killed by `n`. -/
theorem nsmul_discreteKummerH1_eq_zero (x : DiscreteKummerH1 n K) :
    n • x = 0 :=
  ZModModule.char_nsmul_eq_zero n x

private def representativeMonoidHom :
    Kˣ →* Multiplicative (DiscreteKummerH1 n K) :=
  AddMonoidHom.toMultiplicative (representativeMap n K)

/-- The classical Kummer connecting map into discrete absolute-Galois
cohomology, descended through `n`-th powers. -/
def map : KummerClass n K →+ DiscreteKummerH1 n K :=
  MonoidHom.toAdditive <|
    QuotientGroup.lift (powMonoidHom n : Kˣ →* Kˣ).range
      (representativeMonoidHom n K) fun x hx ↦ by
        obtain ⟨y, rfl⟩ := hx
        change Multiplicative.ofAdd
          (representativeMap n K (n • Additive.ofMul y)) = 1
        rw [map_nsmul, nsmul_discreteKummerH1_eq_zero]
        rfl

@[simp]
theorem map_classOfUnit (a : Kˣ) :
    map n K (Additive.ofMul
      (QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range a)) =
      classOfUnit n K a := by
  rfl

end Fermat.Conservation.LocalKummerH1
