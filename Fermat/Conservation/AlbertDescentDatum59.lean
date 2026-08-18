/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The constructive Hilbert--90 datum for Albert descent at 59

Let `L/F` be cyclic of degree 59, let `zeta` be a primitive 59th root in
`F`, and suppose `zeta` is the norm of `beta : L`.  Hilbert 90 then gives a
unit `b : Lˣ` satisfying

`sigma(b) / b = beta ^ 59`

for a generator `sigma` of `Gal(L/F)`.  The norm hypothesis also forces `b`
not to be a 59th power.  These are precisely the descent data used in the
constructive direction of Albert's cyclic-embedding criterion.

This module deliberately stops at that datum.  It does **not** yet construct
the degree-59² overfield, prove the full Albert equivalence, or produce a
continuous `C_(59²)` lift of the absolute-Galois character.  Those require a
further AdjoinRoot/Galois-correspondence construction; none of that work is
hidden in the statements below.
-/
import Fermat.Conservation.KummerCyclicQuotient59
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.AlbertDescentDatum59

variable {F L : Type} [Field F] [Field L] [Algebra F L]
variable [FiniteDimensional F L] [IsGalois F L]

local instance : NeZero 59 := ⟨by decide⟩

private theorem forall_mem_zpowers_one59
    (x : Multiplicative (ZMod 59)) :
    x ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod 59)) := by
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨(x.toAdd.val : ℤ), ?_⟩
  apply Multiplicative.toAdd.injective
  simp

private theorem forall_mem_zpowers_equivGenerator59
    {G : Type*} [Group G]
    (e : G ≃* Multiplicative (ZMod 59)) (x : G) :
    x ∈ Subgroup.zpowers
      (e.symm (Multiplicative.ofAdd (1 : ZMod 59))) := by
  rw [Subgroup.mem_zpowers_iff]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (forall_mem_zpowers_one59 (e x))
  refine ⟨k, e.injective ?_⟩
  rw [map_zpow, e.apply_symm_apply, hk]

/-- The Hilbert--90 descent datum in the constructive direction of Albert's
cyclic-embedding criterion, specialized to degree `59`.

If a primitive 59th root is a norm from a cyclic degree-59 extension, then
there is a radicand `b` over the extension whose conjugate quotient is the
59th power of the norm witness, and `b` itself is not a 59th power. -/
theorem exists_albert_descent_datum59
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (sigma : L ≃ₐ[F] L)
    (hsigma : ∀ tau : L ≃ₐ[F] L, tau ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = 59)
    (beta : L) (hbeta : Algebra.norm F beta = zeta) :
    ∃ b : Lˣ,
      sigma (b : L) / (b : L) = beta ^ 59 ∧
      ∀ c : L, c ^ 59 ≠ (b : L) := by
  have hzeta0 : zeta ≠ 0 := hzeta.ne_zero (by decide)
  have hbeta0 : beta ≠ 0 := by
    intro hb0
    subst beta
    rw [Algebra.norm_zero] at hbeta
    exact hzeta0 hbeta.symm
  have hnormInvPow : Algebra.norm F (beta⁻¹ ^ 59) = 1 := by
    rw [map_pow, Algebra.norm_inv, hbeta, inv_pow, hzeta.pow_eq_one, inv_one]
  letI : IsCyclic (L ≃ₐ[F] L) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨sigma, by
      apply eq_top_iff.mpr
      exact fun tau _ => hsigma tau⟩
  obtain ⟨b, hb⟩ :=
    groupCohomology.exists_div_of_norm_eq_one
      (K := F) (L := L) (g := sigma) hsigma hnormInvPow
  have hratio : sigma (b : L) / (b : L) = beta ^ 59 := by
    calc
      sigma (b : L) / (b : L) =
          (((b : L) / sigma (b : L))⁻¹) := by
            rw [inv_div]
      _ = (beta⁻¹ ^ 59)⁻¹ := congrArg Inv.inv hb
      _ = beta ^ 59 := by simp
  refine ⟨b, hratio, ?_⟩
  intro c hc
  have hc0 : c ≠ 0 := by
    intro hc0
    subst c
    exact b.ne_zero (by simpa using hc.symm)
  let delta : L := sigma c / (beta * c)
  have hdelta : delta ^ 59 = 1 := by
    dsimp [delta]
    rw [div_pow, mul_pow, ← map_pow, hc]
    have hden : beta ^ 59 * (b : L) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hbeta0) b.ne_zero
    exact (div_eq_one_iff_eq hden).2 ((div_eq_iff b.ne_zero).mp hratio)
  have hzetaL : IsPrimitiveRoot (algebraMap F L zeta) 59 :=
    hzeta.map_of_injective (algebraMap F L).injective
  obtain ⟨i, hi, hpow⟩ := hzetaL.eq_pow_of_pow_eq_one hdelta
  have hbetaFormula :
      beta = sigma c / ((algebraMap F L zeta) ^ i * c) := by
    rw [hpow]
    change beta = sigma c / ((sigma c / (beta * c)) * c)
    field_simp [hbeta0, hc0]
  have hnormFormula := congrArg (Algebra.norm F) hbetaFormula
  have hnormSigma : Algebra.norm F (sigma c) = Algebra.norm F c :=
    Algebra.norm_eq_of_algEquiv sigma c
  rw [hbeta, div_eq_mul_inv, map_mul, Algebra.norm_inv, map_mul, map_pow,
    Algebra.norm_algebraMap, hfinrank, hnormSigma] at hnormFormula
  rw [hzeta.pow_eq_one, one_pow, one_mul] at hnormFormula
  have hnormc0 : Algebra.norm F c ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hc0
  have : zeta = 1 := by
    simpa [hnormc0] using hnormFormula
  exact hzeta.ne_one (by decide) this

section ConcreteKummer

open KummerCyclicQuotient59

variable (F : Type) [Field F]
variable (zeta a : F)
variable (hzeta : IsPrimitiveRoot zeta 59)
variable (ha : ∀ x : F, x ^ 59 ≠ a)

/-- The generator of the concrete Kummer Galois group selected by the
existing `autEquivZmod` coordinate. -/
def concreteKummerGenerator59 :
    (kummerExtension59 F a) ≃ₐ[F] (kummerExtension59 F a) :=
  (kummerGalEquiv59 F zeta a hzeta ha).symm
    (Multiplicative.ofAdd (1 : ZMod 59))

/-- A norm witness in the concrete degree-59 Kummer extension produces the
exact Hilbert--90 descent datum used to build the cyclic degree-59²
overfield in the constructive half of Albert's criterion. -/
theorem concreteKummer_exists_albert_descent_datum59
    (beta : kummerExtension59 F a)
    (hbeta : Algebra.norm F beta = zeta) :
    ∃ b : (kummerExtension59 F a)ˣ,
      concreteKummerGenerator59 F zeta a hzeta ha (b : kummerExtension59 F a) /
          (b : kummerExtension59 F a) = beta ^ 59 ∧
      ∀ c : kummerExtension59 F a, c ^ 59 ≠ (b : kummerExtension59 F a) := by
  letI : IsSplittingField F (kummerExtension59 F a)
      (kummerPolynomial59 F a) :=
    kummerExtension59_isSplittingField F a
  letI : FiniteDimensional F (kummerExtension59 F a) :=
    Polynomial.IsSplittingField.finiteDimensional
      (kummerExtension59 F a) (kummerPolynomial59 F a)
  letI : IsGalois F (kummerExtension59 F a) :=
    isGalois_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (by decide : 0 < 59)).2 hzeta⟩
      (kummerPolynomial59_irreducible F a ha)
      (kummerExtension59 F a)
  apply exists_albert_descent_datum59 zeta hzeta
    (concreteKummerGenerator59 F zeta a hzeta ha)
  · intro tau
    exact forall_mem_zpowers_equivGenerator59
      (kummerGalEquiv59 F zeta a hzeta ha).toMulEquiv tau
  · exact finrank_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (by decide : 0 < 59)).2 hzeta⟩
      (kummerPolynomial59_irreducible F a ha)
      (kummerExtension59 F a)
  · exact hbeta

end ConcreteKummer

end Fermat.Conservation.AlbertDescentDatum59
