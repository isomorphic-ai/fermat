/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Exact order of the constructive Albert lift at a prime

The scalar-root automorphism has order `p`, and the generic Albert lift has
exact order `p ^ 2`.
-/
import Fermat.Experiments.Conservation.PrimeAlbertExtension
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.PrimeAlbertOrder

open Fermat.Conservation.PrimeAlbertExtension

variable (p : ℕ) [Fact p.Prime]

local instance : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩

variable {F L : Type} [Field F] [Field L] [Algebra F L]
variable [FiniteDimensional F L] [IsGalois F L]

variable (b : Lˣ)

omit [FiniteDimensional F L] [IsGalois F L] in
theorem scalarRootAutomorphism_pow_algebraMap
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (n : ℕ) (x : L) :
    (scalarRootAutomorphism p (b := b) zeta hzeta ^ n)
      (algebraMap L (albertOverfield p b) x) =
        algebraMap L (albertOverfield p b) x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, AlgEquiv.mul_apply,
        scalarRootAutomorphism_algebraMap, ih]

omit [FiniteDimensional F L] [IsGalois F L] in
theorem scalarRootAutomorphism_pow_root
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (n : ℕ) :
    (scalarRootAutomorphism p (b := b) zeta hzeta ^ n)
      (AdjoinRoot.root (albertPolynomial p b)) =
      algebraMap L (albertOverfield p b) ((algebraMap F L zeta) ^ n) *
        AdjoinRoot.root (albertPolynomial p b) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, AlgEquiv.mul_apply,
        scalarRootAutomorphism_root, map_mul,
        scalarRootAutomorphism_pow_algebraMap, ih, pow_succ, map_mul]
      ring

omit [FiniteDimensional F L] [IsGalois F L] in
set_option maxRecDepth 10000 in
theorem scalarRootAutomorphism_pow_prime
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    scalarRootAutomorphism p (b := b) zeta hzeta ^ p = 1 := by
  apply AlgEquiv.ext
  have heq :
      (scalarRootAutomorphism p (b := b) zeta hzeta ^ p).toAlgHom =
        (1 : albertOverfield p b ≃ₐ[F] albertOverfield p b).toAlgHom := by
    apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro x
      simp only [AlgHom.comp_apply, AdjoinRoot.coe_ofAlgHom]
      have hx := scalarRootAutomorphism_pow_algebraMap
        p (b := b) zeta hzeta p x
      exact hx
    · rw [AlgEquiv.coe_algHom, AlgEquiv.coe_algHom,
        scalarRootAutomorphism_pow_root]
      rw [← map_pow, hzeta.pow_eq_one, map_one, map_one, one_mul]
      rfl
  exact fun x => DFunLike.congr_fun heq x

omit [FiniteDimensional F L] [IsGalois F L] in
theorem scalarRootAutomorphism_ne_one
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hb : ∀ c : L, c ^ p ≠ (b : L)) :
    scalarRootAutomorphism p (b := b) zeta hzeta ≠ 1 := by
  intro heq
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  let y := AdjoinRoot.root (albertPolynomial p b)
  have hy : y ≠ 0 :=
    root_X_pow_sub_C_ne_zero (Fact.out : Nat.Prime p).one_lt (b : L)
  have happ := congrArg
    (fun e : albertOverfield p b ≃ₐ[F] albertOverfield p b => e y) heq
  have hmul :
      algebraMap L (albertOverfield p b) (algebraMap F L zeta) * y = 1 * y := by
    simpa [y] using happ
  have hcoef :
      algebraMap L (albertOverfield p b) (algebraMap F L zeta) = 1 :=
    mul_right_cancel₀ hy hmul
  have hzetaL : algebraMap F L zeta = 1 :=
    (algebraMap L (albertOverfield p b)).injective (by simpa using hcoef)
  have hzetaOne : zeta = 1 :=
    (algebraMap F L).injective (by simpa using hzetaL)
  exact hzeta.ne_one (Fact.out : Nat.Prime p).one_lt hzetaOne

variable (sigma : L ≃ₐ[F] L) (beta : L)

theorem albertLiftAlgEquiv_pow_primeSquared
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hsigma : ∀ tau : L ≃ₐ[F] L, tau ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (hbeta : Algebra.norm F beta = zeta) :
    albertLiftAlgEquiv p sigma beta b hratio hb ^ (p ^ 2) = 1 := by
  rw [pow_two, pow_mul,
    albertLiftAlgEquiv_pow_prime p sigma beta b zeta hzeta
      hratio hb hsigma hfinrank hbeta,
    scalarRootAutomorphism_pow_prime]

theorem albertLiftAlgEquiv_pow_prime_ne_one
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hsigma : ∀ tau : L ≃ₐ[F] L, tau ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (hbeta : Algebra.norm F beta = zeta) :
    albertLiftAlgEquiv p sigma beta b hratio hb ^ p ≠ 1 := by
  rw [albertLiftAlgEquiv_pow_prime p sigma beta b zeta hzeta
    hratio hb hsigma hfinrank hbeta]
  exact scalarRootAutomorphism_ne_one p (b := b) zeta hzeta hb

/-- The constructed Albert automorphism has exact order `p²`. -/
theorem albertLiftAlgEquiv_orderOf
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hsigma : ∀ tau : L ≃ₐ[F] L, tau ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (hbeta : Algebra.norm F beta = zeta) :
    orderOf (albertLiftAlgEquiv p sigma beta b hratio hb) = p ^ 2 := by
  let tau := albertLiftAlgEquiv p sigma beta b hratio hb
  have hpow : tau ^ (p ^ 2) = 1 :=
    albertLiftAlgEquiv_pow_primeSquared p (b := b) (sigma := sigma)
      (beta := beta) zeta hzeta hratio hb hsigma hfinrank hbeta
  have hnot : tau ^ p ≠ 1 :=
    albertLiftAlgEquiv_pow_prime_ne_one p
      (b := b) (sigma := sigma) (beta := beta) zeta hzeta
      hratio hb hsigma hfinrank hbeta
  have hdvd : orderOf tau ∣ p ^ 2 := by
    exact orderOf_dvd_iff_pow_eq_one.mpr hpow
  obtain ⟨k, hk, horder⟩ :=
    (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).mp hdvd
  interval_cases k
  · have hsmall : orderOf tau ∣ p := by simp [horder]
    exact (hnot (orderOf_dvd_iff_pow_eq_one.mp hsmall)).elim
  · have hsmall : orderOf tau ∣ p := by simp [horder]
    exact (hnot (orderOf_dvd_iff_pow_eq_one.mp hsmall)).elim
  · simpa using horder

end Fermat.Conservation.PrimeAlbertOrder
