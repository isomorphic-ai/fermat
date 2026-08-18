/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The elementary norm of one plus a Kummer root at 59

Let `E/F` be the splitting field of `X^59 - a`, where `F` contains a
primitive 59th root of unity and the polynomial is irreducible.  If `alpha`
is Mathlib's selected root in `E`, then

`Norm_{E/F}(1 + alpha) = 1 + a`.

This is the elementary product over the conjugates
`1 + zeta^i * alpha`.  It needs no local-field, reciprocity, Hilbert-symbol,
or cohomological input.  In the cyclotomic application it proves that the
bare radicand `zeta_59 - 1` has `zeta_59` as a norm; any obstruction for a
unit-twisted radicand must therefore genuinely come from the twist.
-/
import Fermat.Conservation.KummerCyclicQuotient59
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.KummerOnePlusRootNorm59

/-- The elementary product identity underlying the norm calculation. -/
theorem prod_one_add_roots59
    {R : Type*} [Field R] {zeta alpha a : R}
    (hzeta : IsPrimitiveRoot zeta 59) (halpha : alpha ^ 59 = a) :
    ∏ i ∈ Finset.range 59, (1 + zeta ^ i * alpha) = 1 + a := by
  have hpoly := X_pow_sub_C_eq_prod hzeta (by norm_num : 0 < 59) halpha
  have heval := congrArg (Polynomial.eval (-1 : R)) hpoly
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_prod] at heval
  have hneg : (-1 : R) ^ 59 = -1 := by norm_num
  rw [hneg] at heval
  have hprodneg :
      (∏ i ∈ Finset.range 59, (-1 - zeta ^ i * alpha)) =
        -(∏ i ∈ Finset.range 59, (1 + zeta ^ i * alpha)) := by
    calc
      (∏ i ∈ Finset.range 59, (-1 - zeta ^ i * alpha)) =
          ∏ i ∈ Finset.range 59, (-(1 + zeta ^ i * alpha)) := by
            apply Finset.prod_congr rfl
            intro i hi
            ring
      _ = (-1 : R) ^ (Finset.range 59).card *
          ∏ i ∈ Finset.range 59, (1 + zeta ^ i * alpha) := by
            rw [Finset.prod_neg]
      _ = -(∏ i ∈ Finset.range 59, (1 + zeta ^ i * alpha)) := by
            norm_num
  rw [hprodneg] at heval
  have h := congrArg Neg.neg heval
  simpa [sub_eq_add_neg, add_comm] using h.symm

open KummerCyclicQuotient59

variable (F : Type) [Field F]
variable (zeta a : F)
variable (hzeta : IsPrimitiveRoot zeta 59)
variable (ha : ∀ b : F, b ^ 59 ≠ a)

include hzeta ha

/-- In the concrete degree-59 Kummer splitting field, the norm of one plus
Mathlib's selected root is exactly `1 + a`. -/
theorem norm_one_add_kummerRoot59 :
    let E := kummerExtension59 F a
    letI : IsSplittingField F E (kummerPolynomial59 F a) :=
      kummerExtension59_isSplittingField F a
    let alpha : E := rootOfSplitsXPowSubC (n := 59) (NeZero.pos 59) a E
    Algebra.norm F (1 + alpha) = 1 + a := by
  let E := kummerExtension59 F a
  letI : IsSplittingField F E (kummerPolynomial59 F a) :=
    kummerExtension59_isSplittingField F a
  letI : FiniteDimensional F E :=
    Polynomial.IsSplittingField.finiteDimensional E (kummerPolynomial59 F a)
  letI : IsGalois F E :=
    isGalois_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (by decide : 0 < 59)).2 hzeta⟩
      (kummerPolynomial59_irreducible F a ha) E
  let alpha : E := rootOfSplitsXPowSubC (n := 59) (NeZero.pos 59) a E
  have halpha : alpha ^ 59 = algebraMap F E a :=
    rootOfSplitsXPowSubC_pow (n := 59) a E
  apply (algebraMap F E).injective
  rw [Algebra.norm_eq_prod_automorphisms]
  rw [map_add, map_one]
  let eGal : (E ≃ₐ[F] E) ≃ Multiplicative (ZMod 59) :=
    autEquivZmod (kummerPolynomial59_irreducible F a ha) E hzeta
  let eFin : Fin 59 ≃ Multiplicative (ZMod 59) :=
    (ZMod.finEquiv 59).toEquiv.trans Multiplicative.ofAdd
  calc
    (∏ sigma : E ≃ₐ[F] E, sigma (1 + alpha)) =
        ∏ x : Multiplicative (ZMod 59),
          (eGal.symm x) (1 + alpha) := by
            exact Fintype.prod_equiv eGal
              (fun sigma : E ≃ₐ[F] E => sigma (1 + alpha))
              (fun x : Multiplicative (ZMod 59) => (eGal.symm x) (1 + alpha))
              (fun sigma => by simp [eGal])
    _ = ∏ i : Fin 59, (eGal.symm (eFin i)) (1 + alpha) := by
          exact (Equiv.prod_comp eFin
            (fun x : Multiplicative (ZMod 59) =>
              (eGal.symm x) (1 + alpha))).symm
    _ = ∏ i : Fin 59, (1 + (algebraMap F E zeta) ^ (i : ℕ) * alpha) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [map_add, map_one]
          dsimp [eGal, eFin]
          have hiZ :
              (ZMod.finEquiv 59) i = (((i : ℕ) : ZMod 59)) := by
            exact (ZMod.natCast_zmod_val ((ZMod.finEquiv 59) i)).symm
          rw [hiZ]
          have hact :
              ((autEquivZmod (kummerPolynomial59_irreducible F a ha) E hzeta).symm
                (Multiplicative.ofAdd (((i : ℕ) : ZMod 59)))) alpha =
                (algebraMap F E zeta) ^ (i : ℕ) * alpha := by
            simpa [Algebra.smul_def, map_pow] using
              (autEquivZmod_symm_apply_natCast
                (kummerPolynomial59_irreducible F a ha) E halpha hzeta
                (i : ℕ))
          rw [hact]
    _ = 1 + algebraMap F E a := by
          rw [Finset.prod_fin_eq_prod_range]
          exact prod_one_add_roots59
            (hzeta.map_of_injective (algebraMap F E).injective) halpha

end Fermat.Conservation.KummerOnePlusRootNorm59
