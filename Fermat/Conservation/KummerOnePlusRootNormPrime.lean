/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The elementary norm of one plus a Kummer root at an odd prime

Let `E/F` be the splitting field of `X^p - a`, where `p` is odd, `F`
contains a primitive `p`-th root of unity, and the polynomial is irreducible.
If `alpha` is Mathlib's selected root in `E`, then

`Norm_{E/F}(1 + alpha) = 1 + a`.

The proof is the elementary product over the conjugates
`1 + zeta^i * alpha`.  It is independent of local fields, reciprocity,
Hilbert symbols, and cohomology.
-/
import Fermat.Conservation.PrimeKummerCyclicQuotient
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.KummerOnePlusRootNormPrime

/-- For odd `p`, the product over the `p` Kummer conjugates of `1 + alpha`
is `1 + alpha ^ p`. -/
theorem prod_one_add_roots
    {p : ℕ} {R : Type*} [Field R] {zeta alpha a : R}
    (hzeta : IsPrimitiveRoot zeta p) (hp : Odd p)
    (halpha : alpha ^ p = a) :
    ∏ i ∈ Finset.range p, (1 + zeta ^ i * alpha) = 1 + a := by
  have hpoly := X_pow_sub_C_eq_prod hzeta hp.pos halpha
  have heval := congrArg (Polynomial.eval (-1 : R)) hpoly
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_prod] at heval
  have hneg : (-1 : R) ^ p = -1 := Odd.neg_one_pow hp
  rw [hneg] at heval
  have hprodneg :
      (∏ i ∈ Finset.range p, (-1 - zeta ^ i * alpha)) =
        -(∏ i ∈ Finset.range p, (1 + zeta ^ i * alpha)) := by
    calc
      (∏ i ∈ Finset.range p, (-1 - zeta ^ i * alpha)) =
          ∏ i ∈ Finset.range p, (-(1 + zeta ^ i * alpha)) := by
            apply Finset.prod_congr rfl
            intro i hi
            ring
      _ = (-1 : R) ^ (Finset.range p).card *
          ∏ i ∈ Finset.range p, (1 + zeta ^ i * alpha) := by
            rw [Finset.prod_neg]
      _ = -(∏ i ∈ Finset.range p, (1 + zeta ^ i * alpha)) := by
            rw [Finset.card_range, hneg, neg_mul, one_mul]
  rw [hprodneg] at heval
  have h := congrArg Neg.neg heval
  simpa [sub_eq_add_neg, add_comm] using h.symm

open PrimeKummerCyclicQuotient

variable (p : ℕ) [Fact p.Prime]
variable (F : Type) [Field F]
variable (zeta a : F)
variable (hzeta : IsPrimitiveRoot zeta p)
variable (ha : ∀ b : F, b ^ p ≠ a)

include hzeta ha

/-- In an odd-prime Kummer splitting field, the norm of one plus Mathlib's
selected root is exactly `1 + a`. -/
theorem norm_one_add_kummerRoot (hp : p ≠ 2) :
    let E := kummerExtension p F a
    letI : IsSplittingField F E (kummerPolynomial p F a) :=
      kummerExtension_isSplittingField p F a
    let alpha : E := rootOfSplitsXPowSubC (n := p)
      (Fact.out : p.Prime).pos a E
    Algebra.norm F (1 + alpha) = 1 + a := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let E := kummerExtension p F a
  letI : IsSplittingField F E (kummerPolynomial p F a) :=
    kummerExtension_isSplittingField p F a
  letI : FiniteDimensional F E :=
    Polynomial.IsSplittingField.finiteDimensional E (kummerPolynomial p F a)
  letI : IsGalois F E :=
    isGalois_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (Fact.out : p.Prime).pos).2 hzeta⟩
      (kummerPolynomial_irreducible p F a ha) E
  let alpha : E := rootOfSplitsXPowSubC (n := p)
    (Fact.out : p.Prime).pos a E
  have halpha : alpha ^ p = algebraMap F E a :=
    rootOfSplitsXPowSubC_pow (n := p) a E
  apply (algebraMap F E).injective
  rw [Algebra.norm_eq_prod_automorphisms]
  rw [map_add, map_one]
  let eGal : (E ≃ₐ[F] E) ≃ Multiplicative (ZMod p) :=
    autEquivZmod (kummerPolynomial_irreducible p F a ha) E hzeta
  let eFin : Fin p ≃ Multiplicative (ZMod p) :=
    (ZMod.finEquiv p).toEquiv.trans Multiplicative.ofAdd
  calc
    (∏ sigma : E ≃ₐ[F] E, sigma (1 + alpha)) =
        ∏ x : Multiplicative (ZMod p),
          (eGal.symm x) (1 + alpha) := by
            exact Fintype.prod_equiv eGal
              (fun sigma : E ≃ₐ[F] E => sigma (1 + alpha))
              (fun x : Multiplicative (ZMod p) => (eGal.symm x) (1 + alpha))
              (fun sigma => by simp [eGal])
    _ = ∏ i : Fin p, (eGal.symm (eFin i)) (1 + alpha) := by
          exact (Equiv.prod_comp eFin
            (fun x : Multiplicative (ZMod p) =>
              (eGal.symm x) (1 + alpha))).symm
    _ = ∏ i : Fin p, (1 + (algebraMap F E zeta) ^ (i : ℕ) * alpha) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [map_add, map_one]
          dsimp [eGal, eFin]
          have hiZ :
              (ZMod.finEquiv p) i = (((i : ℕ) : ZMod p)) := by
            cases p with
            | zero => exact (Fact.out : Nat.Prime 0).ne_zero rfl |>.elim
            | succ n =>
                apply Fin.ext
                change (i : ℕ) = ZMod.val (((i : ℕ) : ZMod (n + 1)))
                exact (ZMod.val_natCast_of_lt i.isLt).symm
          rw [hiZ]
          have hact :
              ((autEquivZmod (kummerPolynomial_irreducible p F a ha) E hzeta).symm
                (Multiplicative.ofAdd (((i : ℕ) : ZMod p)))) alpha =
                (algebraMap F E zeta) ^ (i : ℕ) * alpha := by
            simpa [Algebra.smul_def, map_pow] using
              (autEquivZmod_symm_apply_natCast
                (kummerPolynomial_irreducible p F a ha) E halpha hzeta
                (i : ℕ))
          rw [hact]
    _ = 1 + algebraMap F E a := by
          have hprod := prod_one_add_roots
            (hzeta.map_of_injective (algebraMap F E).injective)
            ((Fact.out : p.Prime).odd_of_ne_two hp) halpha
          rw [← Fin.prod_univ_eq_prod_range
            (fun i : ℕ => 1 + (algebraMap F E zeta) ^ i * alpha) p] at hprod
          exact hprod

end Fermat.Conservation.KummerOnePlusRootNormPrime
