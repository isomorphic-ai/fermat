/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The constructive Hilbert--90 datum for Albert descent at a prime

Let `L/F` be cyclic of prime degree `p`, let `zeta` be a primitive `p`-th
root in `F`, and suppose `zeta` is the norm of `beta : L`. Hilbert 90 then
gives a unit `b : Lˣ` satisfying

`sigma(b) / b = beta ^ p`,

and the norm hypothesis forces `b` not to be a `p`-th power.  The concrete
specialization uses the prime-parametric Kummer splitting field and its
oriented cyclic coordinate.
-/
import Fermat.Conservation.PrimeKummerCyclicQuotient
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.PrimeAlbertDescentDatum

open Fermat.Conservation.PrimeKummerCyclicQuotient

variable (p : ℕ) [Fact p.Prime]

local instance : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩

variable {F L : Type} [Field F] [Field L] [Algebra F L]
variable [FiniteDimensional F L] [IsGalois F L]

private theorem forall_mem_zpowers_one
    (x : Multiplicative (ZMod p)) :
    x ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod p)) := by
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨(x.toAdd.val : ℤ), ?_⟩
  apply Multiplicative.toAdd.injective
  simp

private theorem forall_mem_zpowers_equivGenerator
    {G : Type*} [Group G]
    (e : G ≃* Multiplicative (ZMod p)) (x : G) :
    x ∈ Subgroup.zpowers
      (e.symm (Multiplicative.ofAdd (1 : ZMod p))) := by
  rw [Subgroup.mem_zpowers_iff]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (forall_mem_zpowers_one p (e x))
  refine ⟨k, e.injective ?_⟩
  rw [map_zpow, e.apply_symm_apply, hk]

/-- The Hilbert--90 datum in the constructive direction of Albert's cyclic
embedding criterion at an arbitrary prime. -/
theorem exists_albert_descent_datum
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (sigma : L ≃ₐ[F] L)
    (hsigma : ∀ tau : L ≃ₐ[F] L, tau ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (beta : L) (hbeta : Algebra.norm F beta = zeta) :
    ∃ b : Lˣ,
      sigma (b : L) / (b : L) = beta ^ p ∧
      ∀ c : L, c ^ p ≠ (b : L) := by
  have hzeta0 : zeta ≠ 0 := hzeta.ne_zero (Fact.out : Nat.Prime p).ne_zero
  have hbeta0 : beta ≠ 0 := by
    intro hb0
    subst beta
    rw [Algebra.norm_zero] at hbeta
    exact hzeta0 hbeta.symm
  have hnormInvPow : Algebra.norm F (beta⁻¹ ^ p) = 1 := by
    rw [map_pow, Algebra.norm_inv, hbeta, inv_pow, hzeta.pow_eq_one, inv_one]
  letI : IsCyclic (L ≃ₐ[F] L) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨sigma, by
      apply eq_top_iff.mpr
      exact fun tau _ => hsigma tau⟩
  obtain ⟨b, hb⟩ :=
    groupCohomology.exists_div_of_norm_eq_one
      (K := F) (L := L) (g := sigma) hsigma hnormInvPow
  have hratio : sigma (b : L) / (b : L) = beta ^ p := by
    calc
      sigma (b : L) / (b : L) =
          (((b : L) / sigma (b : L))⁻¹) := by
            rw [inv_div]
      _ = (beta⁻¹ ^ p)⁻¹ := congrArg Inv.inv hb
      _ = beta ^ p := by simp
  refine ⟨b, hratio, ?_⟩
  intro c hc
  have hc0 : c ≠ 0 := by
    intro hc0
    subst c
    apply b.ne_zero
    simpa [zero_pow (Fact.out : Nat.Prime p).ne_zero] using hc.symm
  let delta : L := sigma c / (beta * c)
  have hdelta : delta ^ p = 1 := by
    dsimp [delta]
    rw [div_pow, mul_pow, ← map_pow, hc]
    have hden : beta ^ p * (b : L) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hbeta0) b.ne_zero
    exact (div_eq_one_iff_eq hden).2 ((div_eq_iff b.ne_zero).mp hratio)
  have hzetaL : IsPrimitiveRoot (algebraMap F L zeta) p :=
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
  exact hzeta.ne_one (Fact.out : Nat.Prime p).one_lt this

section ConcreteKummer

variable (F : Type) [Field F]
variable (zeta a : F)
variable (hzeta : IsPrimitiveRoot zeta p)
variable (ha : ∀ x : F, x ^ p ≠ a)

/-- The generator selected by the generic Kummer Galois coordinate. -/
def concreteKummerGenerator :
    (kummerExtension p F a) ≃ₐ[F] (kummerExtension p F a) :=
  (kummerGalEquiv p F zeta a hzeta ha).symm
    (Multiplicative.ofAdd (1 : ZMod p))

/-- A norm witness in the concrete prime-degree Kummer extension produces
the exact Hilbert--90 datum needed by the generic Albert construction. -/
theorem concreteKummer_exists_albert_descent_datum
    (beta : kummerExtension p F a)
    (hbeta : Algebra.norm F beta = zeta) :
    ∃ b : (kummerExtension p F a)ˣ,
      concreteKummerGenerator p F zeta a hzeta ha
            (b : kummerExtension p F a) /
          (b : kummerExtension p F a) = beta ^ p ∧
      ∀ c : kummerExtension p F a,
        c ^ p ≠ (b : kummerExtension p F a) := by
  letI : IsSplittingField F (kummerExtension p F a)
      (kummerPolynomial p F a) :=
    kummerExtension_isSplittingField p F a
  letI : FiniteDimensional F (kummerExtension p F a) :=
    Polynomial.IsSplittingField.finiteDimensional
      (kummerExtension p F a) (kummerPolynomial p F a)
  letI : IsGalois F (kummerExtension p F a) :=
    isGalois_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (Fact.out : Nat.Prime p).pos).2 hzeta⟩
      (kummerPolynomial_irreducible p F a ha)
      (kummerExtension p F a)
  apply exists_albert_descent_datum p zeta hzeta
    (concreteKummerGenerator p F zeta a hzeta ha)
  · intro tau
    exact forall_mem_zpowers_equivGenerator p
      (kummerGalEquiv p F zeta a hzeta ha).toMulEquiv tau
  · exact finrank_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (Fact.out : Nat.Prime p).pos).2 hzeta⟩
      (kummerPolynomial_irreducible p F a ha)
      (kummerExtension p F a)
  · exact hbeta

end ConcreteKummer

end Fermat.Conservation.PrimeAlbertDescentDatum
