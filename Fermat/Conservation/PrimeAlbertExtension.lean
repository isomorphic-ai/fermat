/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The constructive Albert overfield automorphism at a prime

Starting from the generic Hilbert--90 datum, adjoin a `p`-th root of the
resulting non-power `b`.  This module constructs the `F`-automorphism
extending `sigma` by `sigmaTilde(y) = beta * y` and proves

`sigmaTilde ^ p = scalarRootAutomorphism zeta`.
-/
import Fermat.Conservation.PrimeAlbertDescentDatum
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.PrimeAlbertExtension

variable (p : ℕ) [Fact p.Prime]

local instance : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩

private theorem finEquiv_apply_natCast (i : Fin p) :
    ZMod.finEquiv p i = (i.val : ZMod p) := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      apply Fin.ext
      change i.val = i.val % (n + 1)
      exact (Nat.mod_eq_of_lt i.isLt).symm

variable {F L : Type} [Field F] [Field L] [Algebra F L]
variable [FiniteDimensional F L] [IsGalois F L]

abbrev albertPolynomial (b : Lˣ) : L[X] :=
  X ^ p - C (b : L)

abbrev albertOverfield (b : Lˣ) :=
  AdjoinRoot (albertPolynomial p b)

theorem albertPolynomial_irreducible
    (b : Lˣ) (hb : ∀ c : L, c ^ p ≠ (b : L)) :
    Irreducible (albertPolynomial p b) := by
  exact (X_pow_sub_C_irreducible_iff_of_prime
    (Fact.out : Nat.Prime p)).2 hb

variable (sigma : L ≃ₐ[F] L) (beta : L) (b : Lˣ)

omit [Fact p.Prime] [FiniteDimensional F L] [IsGalois F L] in
private theorem lift_root_compatible
    (hratio : sigma (b : L) / (b : L) = beta ^ p) :
    eval₂
      ((IsScalarTower.toAlgHom F L (albertOverfield p b)).comp sigma.toAlgHom)
      (algebraMap L (albertOverfield p b) beta *
        AdjoinRoot.root (albertPolynomial p b))
      (albertPolynomial p b) = 0 := by
  simp only [albertPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [mul_pow, root_X_pow_sub_C_pow]
  rw [← map_pow]
  have hsigmaB : sigma (b : L) = beta ^ p * (b : L) :=
    (div_eq_iff b.ne_zero).mp hratio
  change algebraMap L (albertOverfield p b) (beta ^ p) *
      algebraMap L (albertOverfield p b) (b : L) -
        algebraMap L (albertOverfield p b) (sigma (b : L)) = 0
  rw [hsigmaB, map_mul]
  exact sub_self _

/-- The `F`-algebra endomorphism extending `sigma` and sending the adjoined
root `y` to `beta * y`. -/
def albertLiftAlgHom
    (hratio : sigma (b : L) / (b : L) = beta ^ p) :
    albertOverfield p b →ₐ[F] albertOverfield p b :=
  AdjoinRoot.liftAlgHom (albertPolynomial p b)
    ((IsScalarTower.toAlgHom F L (albertOverfield p b)).comp sigma.toAlgHom)
    (algebraMap L (albertOverfield p b) beta *
      AdjoinRoot.root (albertPolynomial p b))
    (lift_root_compatible p sigma beta b hratio)

omit [Fact p.Prime] [FiniteDimensional F L] [IsGalois F L] in
@[simp]
theorem albertLiftAlgHom_root
    (hratio : sigma (b : L) / (b : L) = beta ^ p) :
    albertLiftAlgHom p sigma beta b hratio
      (AdjoinRoot.root (albertPolynomial p b)) =
        algebraMap L (albertOverfield p b) beta *
          AdjoinRoot.root (albertPolynomial p b) := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

omit [Fact p.Prime] [FiniteDimensional F L] [IsGalois F L] in
@[simp]
theorem albertLiftAlgHom_algebraMap
    (hratio : sigma (b : L) / (b : L) = beta ^ p) (x : L) :
    albertLiftAlgHom p sigma beta b hratio
      (algebraMap L (albertOverfield p b) x) =
        algebraMap L (albertOverfield p b) (sigma x) := by
  change AdjoinRoot.liftAlgHom (albertPolynomial p b)
      ((IsScalarTower.toAlgHom F L (albertOverfield p b)).comp sigma.toAlgHom)
      (algebraMap L (albertOverfield p b) beta *
        AdjoinRoot.root (albertPolynomial p b)) _
      (AdjoinRoot.of (albertPolynomial p b) x) = _
  rw [AdjoinRoot.liftAlgHom_of]
  rfl

/-- The Albert lift is an automorphism once the adjoined polynomial is
irreducible. -/
def albertLiftAlgEquiv
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L)) :
    albertOverfield p b ≃ₐ[F] albertOverfield p b := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  letI : Module.Finite L (albertOverfield p b) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis
        (albertPolynomial_irreducible p b hb).ne_zero).basis
  letI : FiniteDimensional F (albertOverfield p b) :=
    FiniteDimensional.trans F L (albertOverfield p b)
  let f := albertLiftAlgHom p sigma beta b hratio
  have hinj : Function.Injective f := f.injective
  have hsurj : Function.Surjective f :=
    LinearMap.surjective_of_injective (f := f.toLinearMap) hinj
  exact AlgEquiv.ofBijective f ⟨hinj, hsurj⟩

omit [IsGalois F L] in
@[simp]
theorem albertLiftAlgEquiv_root
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L)) :
    albertLiftAlgEquiv p sigma beta b hratio hb
      (AdjoinRoot.root (albertPolynomial p b)) =
        algebraMap L (albertOverfield p b) beta *
          AdjoinRoot.root (albertPolynomial p b) := by
  change albertLiftAlgHom p sigma beta b hratio
      (AdjoinRoot.root (albertPolynomial p b)) = _
  exact albertLiftAlgHom_root p sigma beta b hratio

omit [IsGalois F L] in
@[simp]
theorem albertLiftAlgEquiv_algebraMap
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L)) (x : L) :
    albertLiftAlgEquiv p sigma beta b hratio hb
      (algebraMap L (albertOverfield p b) x) =
        algebraMap L (albertOverfield p b) (sigma x) := by
  change albertLiftAlgHom p sigma beta b hratio
      (algebraMap L (albertOverfield p b) x) = _
  exact albertLiftAlgHom_algebraMap p sigma beta b hratio x

def orbitProduct (n : ℕ) : L :=
  ∏ i ∈ Finset.range n, (sigma ^ i) beta

omit [IsGalois F L] in
theorem albertLiftAlgEquiv_pow_algebraMap
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L)) (n : ℕ) (x : L) :
    (albertLiftAlgEquiv p sigma beta b hratio hb ^ n)
      (algebraMap L (albertOverfield p b) x) =
        algebraMap L (albertOverfield p b) ((sigma ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, AlgEquiv.mul_apply,
        albertLiftAlgEquiv_algebraMap, ih, pow_succ, AlgEquiv.mul_apply]

omit [IsGalois F L] in
theorem albertLiftAlgEquiv_pow_root
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L)) (n : ℕ) :
    (albertLiftAlgEquiv p sigma beta b hratio hb ^ n)
      (AdjoinRoot.root (albertPolynomial p b)) =
        algebraMap L (albertOverfield p b) (orbitProduct sigma beta n) *
          AdjoinRoot.root (albertPolynomial p b) := by
  induction n with
  | zero => simp [orbitProduct]
  | succ n ih =>
      rw [pow_succ]
      rw [AlgEquiv.mul_apply]
      rw [albertLiftAlgEquiv_root, map_mul,
        albertLiftAlgEquiv_pow_algebraMap, ih]
      simp only [orbitProduct, Finset.prod_range_succ]
      rw [map_mul]
      ring

theorem orbitProduct_eq_algebraMap_norm
    (hsigma : ∀ tau : L ≃ₐ[F] L, tau ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p) :
    orbitProduct sigma beta p =
      algebraMap F L (Algebra.norm F beta) := by
  rw [Algebra.norm_eq_prod_automorphisms]
  simp only [orbitProduct]
  rw [← Fin.prod_univ_eq_prod_range (fun i : ℕ => (sigma ^ i) beta) p]
  have hcard : Nat.card (L ≃ₐ[F] L) = p := by
    rw [IsGalois.card_aut_eq_finrank, hfinrank]
  let e : Multiplicative (ZMod p) ≃* (L ≃ₐ[F] L) :=
    zmodMulEquivOfGenerator hsigma hcard
  let eFin : Fin p ≃ (L ≃ₐ[F] L) :=
    (ZMod.finEquiv p).toEquiv.trans
      (Multiplicative.ofAdd.trans e.toEquiv)
  have heFin (i : Fin p) : eFin i = sigma ^ (i : ℕ) := by
    have hfinCast : ZMod.finEquiv p i = ((i.val : ℤ) : ZMod p) := by
      calc
        ZMod.finEquiv p i = ((i.val : ℕ) : ZMod p) :=
          finEquiv_apply_natCast p i
        _ = ((i.val : ℤ) : ZMod p) := by norm_cast
    calc
      eFin i = e (Multiplicative.ofAdd (ZMod.finEquiv p i)) := rfl
      _ = e (Multiplicative.ofAdd ((i.val : ℤ) : ZMod p)) := by rw [hfinCast]
      _ = sigma ^ (i.val : ℤ) :=
        zmodMulEquivOfGenerator_apply_ofAdd_intCast
          hsigma hcard (i.val : ℤ)
      _ = sigma ^ (i : ℕ) := by rw [zpow_natCast]
  apply Fintype.prod_equiv eFin
    (fun i : Fin p => (sigma ^ (i : ℕ)) beta)
    (fun tau : L ≃ₐ[F] L => tau beta)
  intro i
  rw [heFin]

def mappedRootOfUnity (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    rootsOfUnity p L :=
  rootsOfUnity.mkOfPowEq (algebraMap F L zeta) (by
    rw [← map_pow, hzeta.pow_eq_one, map_one])

/-- The Kummer automorphism over `L` which fixes the coefficient field and
scales the adjoined root by the image of `zeta`, regarded as an
`F`-automorphism. -/
def scalarRootAutomorphism
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    albertOverfield p b ≃ₐ[F] albertOverfield p b :=
  (autAdjoinRootXPowSubC p (b : L)
    (mappedRootOfUnity p (L := L) zeta hzeta)).restrictScalars F

omit [FiniteDimensional F L] [IsGalois F L] in
@[simp]
theorem scalarRootAutomorphism_root
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    scalarRootAutomorphism p (b := b) zeta hzeta
      (AdjoinRoot.root (albertPolynomial p b)) =
      algebraMap L (albertOverfield p b) (algebraMap F L zeta) *
        AdjoinRoot.root (albertPolynomial p b) := by
  rw [scalarRootAutomorphism]
  simpa [mappedRootOfUnity, Algebra.smul_def] using
    (autAdjoinRootXPowSubC_root (n := p) (b : L)
      (mappedRootOfUnity p (L := L) zeta hzeta))

omit [FiniteDimensional F L] [IsGalois F L] in
@[simp]
theorem scalarRootAutomorphism_algebraMap
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (x : L) :
    scalarRootAutomorphism p (b := b) zeta hzeta
      (algebraMap L (albertOverfield p b) x) =
        algebraMap L (albertOverfield p b) x := by
  exact (autAdjoinRootXPowSubC p (b : L)
    (mappedRootOfUnity p (L := L) zeta hzeta)).commutes x

set_option maxRecDepth 10000 in
/-- After `p` iterations, the Albert lift is exactly the Kummer automorphism
which fixes `L` and scales the new root by `zeta`. -/
theorem albertLiftAlgEquiv_pow_prime
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hsigma : ∀ tau : L ≃ₐ[F] L, tau ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (hbeta : Algebra.norm F beta = zeta) :
    albertLiftAlgEquiv p sigma beta b hratio hb ^ p =
      scalarRootAutomorphism p (b := b) zeta hzeta := by
  have horder : orderOf sigma = p := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hsigma,
      IsGalois.card_aut_eq_finrank, hfinrank]
  have hsigmaPow : sigma ^ p = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one sigma
  apply AlgEquiv.ext
  have heq :
      (albertLiftAlgEquiv p sigma beta b hratio hb ^ p).toAlgHom =
        (scalarRootAutomorphism p (b := b) zeta hzeta).toAlgHom := by
    apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro x
      simp only [AlgHom.comp_apply, AdjoinRoot.coe_ofAlgHom]
      calc
        (albertLiftAlgEquiv p sigma beta b hratio hb ^ p)
            (AdjoinRoot.of (albertPolynomial p b) x) =
            algebraMap L (albertOverfield p b) ((sigma ^ p) x) := by
              have hx := albertLiftAlgEquiv_pow_algebraMap
                p sigma beta b hratio hb p x
              exact hx
        _ = algebraMap L (albertOverfield p b) x := by
              rw [hsigmaPow]
              rfl
        _ = scalarRootAutomorphism p (b := b) zeta hzeta
            (AdjoinRoot.of (albertPolynomial p b) x) := by
              symm
              have hx := scalarRootAutomorphism_algebraMap
                p (b := b) zeta hzeta x
              exact hx
    · rw [AlgEquiv.coe_algHom, AlgEquiv.coe_algHom,
        albertLiftAlgEquiv_pow_root,
        orbitProduct_eq_algebraMap_norm p sigma beta hsigma hfinrank,
        hbeta, scalarRootAutomorphism_root]
  exact fun x => DFunLike.congr_fun heq x

end Fermat.Conservation.PrimeAlbertExtension
