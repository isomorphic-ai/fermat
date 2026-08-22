/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Explicit norm coordinates in a prime Kummer extension

This module puts an honest selected-root power basis on the concrete
splitting field of `X^p-a`.  Every extension element is represented by a
polynomial of degree below `p`, and its norm is expanded as the finite
product obtained by substituting all `zeta^i * alpha` conjugates.

It also evaluates the norm of every one-monomial perturbation
`1 + c * alpha^j`.  These are algebraic identities only: no valuation,
local reciprocity, Hilbert symbol, or norm-filtration theorem is used.
-/
import Fermat.Experiments.Conservation.KummerOnePlusRootNormPrime
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.PrimeKummerExplicitNorm

open PrimeKummerCyclicQuotient
open KummerOnePlusRootNormPrime

variable (p : ℕ) [Fact p.Prime]
variable (F : Type) [Field F]
variable (zeta a : F)
variable (hzeta : IsPrimitiveRoot zeta p)
variable (ha : ∀ b : F, b ^ p ≠ a)

local notation "E" => kummerExtension p F a

local instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

local instance : IsSplittingField F E (kummerPolynomial p F a) :=
  kummerExtension_isSplittingField p F a

local instance : FiniteDimensional F E :=
  Polynomial.IsSplittingField.finiteDimensional E
    (kummerPolynomial p F a)

/-- Mathlib's selected root in the concrete Kummer extension. -/
def selectedKummerRoot : E :=
  rootOfSplitsXPowSubC (n := p) (Fact.out : p.Prime).pos a E

theorem selectedKummerRoot_pow :
    selectedKummerRoot p F a ^ p = algebraMap F E a :=
  rootOfSplitsXPowSubC_pow (n := p) a E

/-- The selected root gives a power basis of the concrete splitting field. -/
def selectedKummerPowerBasis : PowerBasis F E :=
  (AdjoinRoot.powerBasis
      (kummerPolynomial_irreducible p F a ha).ne_zero).map
    (adjoinRootXPowSubCEquiv
      ⟨zeta, (mem_primitiveRoots (Fact.out : p.Prime).pos).2 hzeta⟩
      (kummerPolynomial_irreducible p F a ha)
      (selectedKummerRoot_pow p F a))

include hzeta ha

@[simp]
theorem selectedKummerPowerBasis_gen :
    (selectedKummerPowerBasis p F zeta a hzeta ha).gen =
      selectedKummerRoot p F a := by
  simp [selectedKummerPowerBasis, selectedKummerRoot,
    adjoinRootXPowSubCEquiv_root]

@[simp]
theorem selectedKummerPowerBasis_dim :
    (selectedKummerPowerBasis p F zeta a hzeta ha).dim = p := by
  simp [selectedKummerPowerBasis, AdjoinRoot.powerBasis_dim]

/-- Every element has a polynomial representative of degree strictly below
`p` in the selected Kummer root. -/
theorem exists_bounded_aeval_eq (beta : E) :
    ∃ f : F[X], f.natDegree < p ∧
      beta = aeval (selectedKummerRoot p F a) f := by
  simpa using
    (selectedKummerPowerBasis p F zeta a hzeta ha).exists_eq_aeval beta

/-- The automorphism indexed by `i` sends the selected root to
`zeta^i * root`. -/
def indexedKummerAutomorphism (i : Fin p) : E ≃ₐ[F] E :=
  (autEquivZmod (kummerPolynomial_irreducible p F a ha) E hzeta).symm
    (Multiplicative.ofAdd (((i : ℕ) : ZMod p)))

theorem indexedKummerAutomorphism_root (i : Fin p) :
    indexedKummerAutomorphism p F zeta a hzeta ha i
        (selectedKummerRoot p F a) =
      algebraMap F E (zeta ^ (i : ℕ)) * selectedKummerRoot p F a := by
  simpa [indexedKummerAutomorphism, Algebra.smul_def, map_pow] using
    (autEquivZmod_symm_apply_natCast
      (kummerPolynomial_irreducible p F a ha) E
      (selectedKummerRoot_pow p F a) hzeta (i : ℕ))

/-- Exact product-over-conjugates formula for every element of the concrete
Kummer extension. -/
theorem algebraMap_norm_eq_prod_indexed (beta : E) :
    algebraMap F E (Algebra.norm F beta) =
      ∏ i : Fin p, indexedKummerAutomorphism p F zeta a hzeta ha i beta := by
  letI : IsGalois F E :=
    isGalois_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (Fact.out : p.Prime).pos).2 hzeta⟩
      (kummerPolynomial_irreducible p F a ha) E
  rw [Algebra.norm_eq_prod_automorphisms]
  let eGal : (E ≃ₐ[F] E) ≃ Multiplicative (ZMod p) :=
    (autEquivZmod (kummerPolynomial_irreducible p F a ha) E hzeta).toEquiv
  let eFin : Fin p ≃ Multiplicative (ZMod p) :=
    (ZMod.finEquiv p).toEquiv.trans Multiplicative.ofAdd
  calc
    (∏ sigma : E ≃ₐ[F] E, sigma beta) =
        ∏ x : Multiplicative (ZMod p), (eGal.symm x) beta := by
          exact Fintype.prod_equiv eGal
            (fun sigma : E ≃ₐ[F] E => sigma beta)
            (fun x : Multiplicative (ZMod p) => (eGal.symm x) beta)
            (fun sigma => by simp [eGal])
    _ = ∏ i : Fin p, (eGal.symm (eFin i)) beta := by
          exact (Equiv.prod_comp eFin
            (fun x : Multiplicative (ZMod p) => (eGal.symm x) beta)).symm
    _ = ∏ i : Fin p,
          indexedKummerAutomorphism p F zeta a hzeta ha i beta := by
          apply Finset.prod_congr rfl
          intro i hi
          congr 1
          simp only [eGal, eFin, indexedKummerAutomorphism]
          have hiZ :
              (ZMod.finEquiv p) i = (((i : ℕ) : ZMod p)) := by
            cases p with
            | zero => exact (Fact.out : Nat.Prime 0).ne_zero rfl |>.elim
            | succ n =>
                apply Fin.ext
                change (i : ℕ) = ZMod.val (((i : ℕ) : ZMod (n + 1)))
                exact (ZMod.val_natCast_of_lt i.isLt).symm
          change
            (autEquivZmod (kummerPolynomial_irreducible p F a ha) E
                hzeta).symm
                (Multiplicative.ofAdd ((ZMod.finEquiv p) i)) = _
          rw [hiZ]

/-- Substituting a bounded power-basis representative turns the field norm
into a completely explicit finite product of polynomial evaluations. -/
theorem algebraMap_norm_aeval_eq_prod
    (f : F[X]) :
    algebraMap F E
        (Algebra.norm F (aeval (selectedKummerRoot p F a) f)) =
      ∏ i : Fin p,
        aeval
          (algebraMap F E (zeta ^ (i : ℕ)) *
            selectedKummerRoot p F a) f := by
  rw [algebraMap_norm_eq_prod_indexed p F zeta a hzeta ha]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← aeval_algHom_apply]
  rw [indexedKummerAutomorphism_root p F zeta a hzeta ha]

/-- Fully packaged arbitrary-element explicit norm expansion. -/
theorem exists_bounded_explicit_norm (beta : E) :
    ∃ f : F[X], f.natDegree < p ∧
      beta = aeval (selectedKummerRoot p F a) f ∧
      algebraMap F E (Algebra.norm F beta) =
        ∏ i : Fin p,
          aeval
            (algebraMap F E (zeta ^ (i : ℕ)) *
              selectedKummerRoot p F a) f := by
  obtain ⟨f, hfdegree, rfl⟩ :=
    exists_bounded_aeval_eq p F zeta a hzeta ha beta
  exact ⟨f, hfdegree, rfl, algebraMap_norm_aeval_eq_prod
    p F zeta a hzeta ha f⟩

/-- Exact norm of a single nonconstant power-basis perturbation. -/
theorem norm_one_add_smul_root_pow
    (c : F) (j : ℕ) (hj0 : 0 < j) (hjp : j < p)
    (hp2 : p ≠ 2) :
    Algebra.norm F
        (1 + algebraMap F E c * selectedKummerRoot p F a ^ j) =
      1 + c ^ p * a ^ j := by
  have hjndvd : ¬ p ∣ j := by
    intro hdvd
    have hple : p ≤ j := Nat.le_of_dvd hj0 hdvd
    omega
  have hjcoprime : j.Coprime p :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hjndvd).symm
  have heta : IsPrimitiveRoot
      (algebraMap F E (zeta ^ j)) p :=
    (hzeta.pow_of_coprime j hjcoprime).map_of_injective
      (algebraMap F E).injective
  let x : E := algebraMap F E c * selectedKummerRoot p F a ^ j
  have hxpow : x ^ p = algebraMap F E (c ^ p * a ^ j) := by
    dsimp [x]
    rw [mul_pow, ← map_pow]
    rw [show (selectedKummerRoot p F a ^ j) ^ p =
        (selectedKummerRoot p F a ^ p) ^ j by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
    rw [selectedKummerRoot_pow, ← map_pow, ← map_mul]
  apply (algebraMap F E).injective
  rw [algebraMap_norm_eq_prod_indexed p F zeta a hzeta ha]
  rw [map_add, map_one, map_mul, map_pow, map_pow]
  have hconjugate (i : Fin p) :
      indexedKummerAutomorphism p F zeta a hzeta ha i
          (1 + algebraMap F E c * selectedKummerRoot p F a ^ j) =
        1 + (algebraMap F E (zeta ^ j)) ^ (i : ℕ) * x := by
    rw [map_add, map_one, map_mul,
      (indexedKummerAutomorphism p F zeta a hzeta ha i).commutes,
      map_pow, indexedKummerAutomorphism_root p F zeta a hzeta ha]
    dsimp [x]
    rw [mul_pow]
    simp only [map_pow]
    rw [← pow_mul, mul_comm (i : ℕ) j, pow_mul]
    ring
  simp_rw [hconjugate]
  have hprod := prod_one_add_roots heta
    ((Fact.out : p.Prime).odd_of_ne_two hp2) hxpow
  rw [← Fin.prod_univ_eq_prod_range
    (fun i : ℕ =>
      1 + (algebraMap F E (zeta ^ j)) ^ i * x) p] at hprod
  exact hprod.trans (by simp only [map_mul, map_pow])

end Fermat.Conservation.PrimeKummerExplicitNorm
