/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Explicit trace coordinates in a prime Kummer extension

This module complements the explicit norm product with the corresponding
trace calculation.  A nonconstant selected-root monomial of degree below
`p` has trace zero; consequently a bounded power-basis polynomial has trace
exactly `p` times its constant coefficient.
-/
import Fermat.Experiments.Conservation.PrimeKummerExplicitNorm
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.PrimeKummerTrace

open PrimeKummerCyclicQuotient
open KummerOnePlusRootNormPrime
open PrimeKummerExplicitNorm

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

/- A nontrivial character of the finite cyclic index set has zero sum. -/
omit [Fact p.Prime] in
theorem sum_fin_primitiveRoot_pow_eq_zero
    (hz : IsPrimitiveRoot zeta p)
    (j : ℕ) (hj0 : 0 < j) (hjp : j < p) :
    ∑ i : Fin p, zeta ^ ((i : ℕ) * j) = 0 := by
  have hjndvd : ¬ p ∣ j := by
    intro hdvd
    exact (Nat.not_lt_of_ge (Nat.le_of_dvd hj0 hdvd)) hjp
  have hzpow_ne : zeta ^ j ≠ 1 := by
    exact fun h => hjndvd ((hz.pow_eq_one_iff_dvd j).mp h)
  have hgeom := geom_sum_mul (zeta ^ j) p
  have hzjp : zeta ^ (j * p) = 1 := by
    rw [Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
  rw [← pow_mul, hzjp, sub_self] at hgeom
  have hsum : ∑ i : Fin p, (zeta ^ j) ^ (i : ℕ) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right (sub_ne_zero.mpr hzpow_ne)
    simpa [Fin.sum_univ_eq_sum_range] using hgeom
  simpa [pow_mul, Nat.mul_comm] using hsum

include hzeta ha

/-- The field trace is the sum over the explicitly indexed Kummer
automorphisms. -/
theorem algebraMap_trace_eq_sum_indexed (beta : E) :
    algebraMap F E (Algebra.trace F E beta) =
      ∑ i : Fin p, indexedKummerAutomorphism p F zeta a hzeta ha i beta := by
  letI : IsGalois F E :=
    isGalois_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (Fact.out : p.Prime).pos).2 hzeta⟩
      (kummerPolynomial_irreducible p F a ha) E
  rw [trace_eq_sum_automorphisms]
  let eGal : (E ≃ₐ[F] E) ≃ Multiplicative (ZMod p) :=
    (autEquivZmod (kummerPolynomial_irreducible p F a ha) E hzeta).toEquiv
  let eFin : Fin p ≃ Multiplicative (ZMod p) :=
    (ZMod.finEquiv p).toEquiv.trans Multiplicative.ofAdd
  calc
    (∑ sigma : E ≃ₐ[F] E, sigma beta) =
        ∑ x : Multiplicative (ZMod p), (eGal.symm x) beta := by
          exact Fintype.sum_equiv eGal
            (fun sigma : E ≃ₐ[F] E => sigma beta)
            (fun x : Multiplicative (ZMod p) => (eGal.symm x) beta)
            (fun sigma => by simp [eGal])
    _ = ∑ i : Fin p, (eGal.symm (eFin i)) beta := by
          exact (Equiv.sum_comp eFin
            (fun x : Multiplicative (ZMod p) => (eGal.symm x) beta)).symm
    _ = ∑ i : Fin p,
          indexedKummerAutomorphism p F zeta a hzeta ha i beta := by
          apply Finset.sum_congr rfl
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

/-- The trace of a base-field scalar is multiplication by the Kummer
degree. -/
theorem trace_algebraMap_eq_natCast_mul (c : F) :
    Algebra.trace F E (algebraMap F E c) = (p : F) * c := by
  apply (algebraMap F E).injective
  rw [algebraMap_trace_eq_sum_indexed p F zeta a hzeta ha]
  simp only [(indexedKummerAutomorphism p F zeta a hzeta ha _).commutes,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    map_mul, map_natCast]

/-- Every nonconstant power-basis monomial below degree `p` has trace
zero. -/
theorem trace_selectedKummerRoot_pow_eq_zero
    (j : ℕ) (hj0 : 0 < j) (hjp : j < p) :
    Algebra.trace F E (selectedKummerRoot p F a ^ j) = 0 := by
  apply (algebraMap F E).injective
  rw [map_zero, algebraMap_trace_eq_sum_indexed p F zeta a hzeta ha]
  have hconjugate (i : Fin p) :
      indexedKummerAutomorphism p F zeta a hzeta ha i
          (selectedKummerRoot p F a ^ j) =
        algebraMap F E (zeta ^ ((i : ℕ) * j)) *
          selectedKummerRoot p F a ^ j := by
    rw [map_pow, indexedKummerAutomorphism_root p F zeta a hzeta ha,
      mul_pow, ← map_pow, ← pow_mul]
  simp_rw [hconjugate]
  rw [← Finset.sum_mul, ← map_sum,
    sum_fin_primitiveRoot_pow_eq_zero p F zeta hzeta j hj0 hjp,
    map_zero, zero_mul]

/-- A bounded power-basis polynomial has trace `p` times its constant
coefficient. -/
theorem trace_aeval_eq_natCast_mul_coeff_zero
    (f : F[X]) (hfdegree : f.natDegree < p) :
    Algebra.trace F E (aeval (selectedKummerRoot p F a) f) =
      (p : F) * f.coeff 0 := by
  rw [aeval_eq_sum_range' hfdegree]
  rw [map_sum]
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, Algebra.smul_def, mul_one,
      trace_algebraMap_eq_natCast_mul p F zeta a hzeta ha]
  · intro j hj hjne
    rw [map_smul,
      trace_selectedKummerRoot_pow_eq_zero p F zeta a hzeta ha j
        (Nat.pos_of_ne_zero hjne) (Finset.mem_range.mp hj),
      smul_zero]
  · intro hzero
    exfalso
    exact hzero (Finset.mem_range.mpr (Fact.out : p.Prime).pos)

/-- Every extension element has bounded Kummer coordinates whose constant
coefficient records its trace exactly. -/
theorem exists_bounded_aeval_trace_eq (beta : E) :
    ∃ f : F[X], f.natDegree < p ∧
      beta = aeval (selectedKummerRoot p F a) f ∧
      Algebra.trace F E beta = (p : F) * f.coeff 0 := by
  obtain ⟨f, hfdegree, rfl⟩ :=
    exists_bounded_aeval_eq p F zeta a hzeta ha beta
  exact ⟨f, hfdegree, rfl,
    trace_aeval_eq_natCast_mul_coeff_zero
      p F zeta a hzeta ha f hfdegree⟩

end Fermat.Conservation.PrimeKummerTrace
