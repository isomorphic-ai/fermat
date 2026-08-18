/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Exact order of the constructive Albert lift at 59

This module continues `AlbertExtension59`.  It proves that the scalar-root
automorphism has order 59 and, consequently, that the constructed Albert
lift has exact order

`59 ^ 2 = 3481`.

This is an exact group-theoretic boundary, not yet the full cyclic extension
theorem.  In particular, this module does not prove that the Albert overfield
has `F`-dimension 3481, prove that it is Galois over `F`, identify all of its
automorphisms with powers of the lift, embed it in an algebraic closure, or
construct the resulting continuous `C_(59^2)` absolute-Galois quotient.
-/
import Fermat.Conservation.AlbertExtension59
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.AlbertOrder59

open AlbertExtension59

variable {F L : Type} [Field F] [Field L] [Algebra F L]
variable [FiniteDimensional F L] [IsGalois F L]

local instance : NeZero 59 := ⟨by decide⟩

variable (b : Lˣ)

omit [FiniteDimensional F L] [IsGalois F L] in
theorem scalarRootAutomorphism59_pow_algebraMap
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (n : ℕ) (x : L) :
    (scalarRootAutomorphism59 (b := b) zeta hzeta ^ n)
      (algebraMap L (albertOverfield59 b) x) =
        algebraMap L (albertOverfield59 b) x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, AlgEquiv.mul_apply,
        scalarRootAutomorphism59_algebraMap, ih]

omit [FiniteDimensional F L] [IsGalois F L] in
theorem scalarRootAutomorphism59_pow_root
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (n : ℕ) :
    (scalarRootAutomorphism59 (b := b) zeta hzeta ^ n)
      (AdjoinRoot.root (albertPolynomial59 b)) =
      algebraMap L (albertOverfield59 b) ((algebraMap F L zeta) ^ n) *
        AdjoinRoot.root (albertPolynomial59 b) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, AlgEquiv.mul_apply,
        scalarRootAutomorphism59_root, map_mul,
        scalarRootAutomorphism59_pow_algebraMap, ih, pow_succ, map_mul]
      ring

omit [FiniteDimensional F L] [IsGalois F L] in
set_option maxRecDepth 10000 in
theorem scalarRootAutomorphism59_pow_fiftyNine
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    scalarRootAutomorphism59 (b := b) zeta hzeta ^ 59 = 1 := by
  apply AlgEquiv.ext
  have heq :
      (scalarRootAutomorphism59 (b := b) zeta hzeta ^ 59).toAlgHom =
        (1 : albertOverfield59 b ≃ₐ[F] albertOverfield59 b).toAlgHom := by
    apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro x
      simp only [AlgHom.comp_apply, AdjoinRoot.coe_ofAlgHom]
      have hx := scalarRootAutomorphism59_pow_algebraMap
        (b := b) zeta hzeta 59 x
      exact hx
    · rw [AlgEquiv.coe_algHom, AlgEquiv.coe_algHom,
        scalarRootAutomorphism59_pow_root]
      rw [← map_pow, hzeta.pow_eq_one, map_one, map_one, one_mul]
      rfl
  exact fun x => DFunLike.congr_fun heq x

omit [FiniteDimensional F L] [IsGalois F L] in
theorem scalarRootAutomorphism59_ne_one
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L)) :
    scalarRootAutomorphism59 (b := b) zeta hzeta ≠ 1 := by
  intro heq
  letI : Fact (Irreducible (albertPolynomial59 b)) :=
    ⟨albertPolynomial59_irreducible b hb⟩
  let y := AdjoinRoot.root (albertPolynomial59 b)
  have hy : y ≠ 0 := root_X_pow_sub_C_ne_zero (by decide : 1 < 59) (b : L)
  have happ := congrArg
    (fun e : albertOverfield59 b ≃ₐ[F] albertOverfield59 b => e y) heq
  have hmul :
      algebraMap L (albertOverfield59 b) (algebraMap F L zeta) * y = 1 * y := by
    simpa [y] using happ
  have hcoef :
      algebraMap L (albertOverfield59 b) (algebraMap F L zeta) = 1 :=
    mul_right_cancel₀ hy hmul
  have hzetaL : algebraMap F L zeta = 1 :=
    (algebraMap L (albertOverfield59 b)).injective (by simpa using hcoef)
  have hzetaOne : zeta = 1 :=
    (algebraMap F L).injective (by simpa using hzetaL)
  exact hzeta.ne_one (by decide) hzetaOne

variable (sigma : L ≃ₐ[F] L) (beta : L)

theorem albertLiftAlgEquiv59_pow_3481
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L))
    (hsigma : ∀ tau : L ≃ₐ[F] L, tau ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = 59)
    (hbeta : Algebra.norm F beta = zeta) :
    albertLiftAlgEquiv59 sigma beta b hratio hb ^ 3481 = 1 := by
  rw [show 3481 = 59 * 59 by norm_num, pow_mul,
    albertLiftAlgEquiv59_pow_fiftyNine sigma beta b zeta hzeta
      hratio hb hsigma hfinrank hbeta,
    scalarRootAutomorphism59_pow_fiftyNine]

theorem albertLiftAlgEquiv59_pow_fiftyNine_ne_one
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L))
    (hsigma : ∀ tau : L ≃ₐ[F] L, tau ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = 59)
    (hbeta : Algebra.norm F beta = zeta) :
    albertLiftAlgEquiv59 sigma beta b hratio hb ^ 59 ≠ 1 := by
  rw [albertLiftAlgEquiv59_pow_fiftyNine sigma beta b zeta hzeta
    hratio hb hsigma hfinrank hbeta]
  exact scalarRootAutomorphism59_ne_one (b := b) zeta hzeta hb

theorem albertLiftAlgEquiv59_orderOf
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L))
    (hsigma : ∀ tau : L ≃ₐ[F] L, tau ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = 59)
    (hbeta : Algebra.norm F beta = zeta) :
    orderOf (albertLiftAlgEquiv59 sigma beta b hratio hb) = 3481 := by
  let tau := albertLiftAlgEquiv59 sigma beta b hratio hb
  have hpow : tau ^ 3481 = 1 :=
    albertLiftAlgEquiv59_pow_3481 (b := b) (sigma := sigma) (beta := beta) zeta hzeta
      hratio hb hsigma hfinrank hbeta
  have hnot : tau ^ 59 ≠ 1 :=
    albertLiftAlgEquiv59_pow_fiftyNine_ne_one
      (b := b) (sigma := sigma) (beta := beta) zeta hzeta
      hratio hb hsigma hfinrank hbeta
  have hdvd : orderOf tau ∣ 59 ^ 2 := by
    apply orderOf_dvd_iff_pow_eq_one.mpr
    norm_num [pow_two] at hpow ⊢
    exact hpow
  obtain ⟨k, hk, horder⟩ :=
    (Nat.dvd_prime_pow (by decide : Nat.Prime 59)).mp hdvd
  interval_cases k
  · have hsmall : orderOf tau ∣ 59 := by simp [horder]
    exact (hnot (orderOf_dvd_iff_pow_eq_one.mp hsmall)).elim
  · have hsmall : orderOf tau ∣ 59 := by simp [horder]
    exact (hnot (orderOf_dvd_iff_pow_eq_one.mp hsmall)).elim
  · norm_num at horder ⊢
    exact horder

end Fermat.Conservation.AlbertOrder59
