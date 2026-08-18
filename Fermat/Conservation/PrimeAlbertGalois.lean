/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The finite cyclic Albert overfield at an arbitrary prime

The generic overfield has dimension `p²`; the `p²` powers of the lifted
automorphism exhaust its automorphism group.  Hence it is Galois and cyclic.
-/
import Fermat.Conservation.PrimeAlbertOrder
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.PrimeAlbertGalois

open Fermat.Conservation.PrimeAlbertExtension
open Fermat.Conservation.PrimeAlbertOrder

variable (p : ℕ) [Fact p.Prime]

local instance : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩

variable {F L : Type} [Field F] [Field L] [Algebra F L]
variable [FiniteDimensional F L] [IsGalois F L]

variable (b : Lˣ)

omit [IsGalois F L] in
theorem albertOverfield_finrank
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hfinrank : Module.finrank F L = p) :
    Module.finrank F (albertOverfield p b) = p ^ 2 := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  letI : Module.Finite L (albertOverfield p b) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis (albertPolynomial_irreducible p b hb).ne_zero).basis
  rw [← Module.finrank_mul_finrank F L (albertOverfield p b), hfinrank,
    (AdjoinRoot.powerBasis
      (albertPolynomial_irreducible p b hb).ne_zero).finrank,
    AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]
  exact (pow_two p).symm

variable (sigma : L ≃ₐ[F] L) (beta : L)

theorem albertLiftAlgEquiv_distinct_powers
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (hbeta : Algebra.norm F beta = zeta) :
    Function.Injective (fun i : Fin (p ^ 2) ↦
      albertLiftAlgEquiv p sigma beta b hratio hb ^ (i : ℕ)) := by
  let tau := albertLiftAlgEquiv p sigma beta b hratio hb
  have htau : orderOf tau = p ^ 2 :=
    albertLiftAlgEquiv_orderOf p (b := b) (sigma := sigma) (beta := beta)
      zeta hzeta hratio hb hsigma hfinrank hbeta
  intro i j hij
  apply Fin.ext
  have hmod := pow_eq_pow_iff_modEq.mp hij
  rw [htau] at hmod
  apply Nat.ModEq.eq_of_lt_of_lt hmod
  · exact i.isLt
  · exact j.isLt

theorem albertOverfield_card_aut
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (hbeta : Algebra.norm F beta = zeta) :
    Nat.card
      (albertOverfield p b ≃ₐ[F] albertOverfield p b) = p ^ 2 := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  letI : FiniteDimensional L (albertOverfield p b) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis (albertPolynomial_irreducible p b hb).ne_zero).basis
  letI : FiniteDimensional F (albertOverfield p b) :=
    FiniteDimensional.trans F L (albertOverfield p b)
  let tau := albertLiftAlgEquiv p sigma beta b hratio hb
  have htau : orderOf tau = p ^ 2 :=
    albertLiftAlgEquiv_orderOf p (b := b) (sigma := sigma) (beta := beta)
      zeta hzeta hratio hb hsigma hfinrank hbeta
  have hdim : Module.finrank F (albertOverfield p b) = p ^ 2 :=
    albertOverfield_finrank p b hb hfinrank
  apply Nat.le_antisymm
  · rw [← hdim]
    simpa only [Nat.card_eq_fintype_card] using
      (AlgEquiv.card_le
        (F := F) (K := albertOverfield p b))
  · rw [← htau]
    exact orderOf_le_card

theorem albertOverfield_isGalois
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (hbeta : Algebra.norm F beta = zeta) :
    letI : Fact (Irreducible (albertPolynomial p b)) :=
      ⟨albertPolynomial_irreducible p b hb⟩
    IsGalois F (albertOverfield p b) := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  letI : FiniteDimensional L (albertOverfield p b) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis (albertPolynomial_irreducible p b hb).ne_zero).basis
  letI : FiniteDimensional F (albertOverfield p b) :=
    FiniteDimensional.trans F L (albertOverfield p b)
  apply IsGalois.of_card_aut_eq_finrank F (albertOverfield p b)
  rw [albertOverfield_card_aut p b sigma beta zeta hzeta hratio hb hsigma
      hfinrank hbeta,
    albertOverfield_finrank p b hb hfinrank]

theorem albertLiftAlgEquiv_zpowers_eq_top
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (hbeta : Algebra.norm F beta = zeta) :
    Subgroup.zpowers (albertLiftAlgEquiv p sigma beta b hratio hb) = ⊤ := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  letI : FiniteDimensional L (albertOverfield p b) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis (albertPolynomial_irreducible p b hb).ne_zero).basis
  letI : FiniteDimensional F (albertOverfield p b) :=
    FiniteDimensional.trans F L (albertOverfield p b)
  apply (Subgroup.card_eq_iff_eq_top _).mp
  rw [Nat.card_zpowers,
    albertLiftAlgEquiv_orderOf p (b := b) (sigma := sigma) (beta := beta)
      zeta hzeta hratio hb hsigma hfinrank hbeta,
    albertOverfield_card_aut p b sigma beta zeta hzeta hratio hb hsigma
      hfinrank hbeta]

end Fermat.Conservation.PrimeAlbertGalois
