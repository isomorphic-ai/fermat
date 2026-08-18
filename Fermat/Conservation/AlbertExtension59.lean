/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The constructive Albert overfield automorphism at 59

Starting from the Hilbert--90 datum in `AlbertDescentDatum59`, this module
adjoins a 59th root of the resulting non-power `b`.  It constructs the
`F`-automorphism extending a generator `sigma` of `Gal(L/F)` by

`sigmaTilde(y) = beta * y`

and computes all of its iterates on both `L` and the new root.  The central
checked identity is

`sigmaTilde ^ 59 = scalarRootAutomorphism59 zeta`,

where the right side fixes `L` and scales the new root by `zeta`.

This module deliberately stops at that exact 59th-power identity.  It does
not yet prove that the full overfield is cyclic Galois of degree `59 ^ 2`,
identify its complete automorphism group, place it inside an algebraic
closure, or construct the resulting continuous `C_(59^2)` absolute-Galois
quotient.  Those are subsequent transport and Galois-correspondence steps;
none is hidden here.
-/
import Fermat.Conservation.AlbertDescentDatum59
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.AlbertExtension59

variable {F L : Type} [Field F] [Field L] [Algebra F L]
variable [FiniteDimensional F L] [IsGalois F L]

local instance : NeZero 59 := ⟨by decide⟩

abbrev albertPolynomial59 (b : Lˣ) : L[X] :=
  X ^ 59 - C (b : L)

abbrev albertOverfield59 (b : Lˣ) :=
  AdjoinRoot (albertPolynomial59 b)

theorem albertPolynomial59_irreducible
    (b : Lˣ) (hb : ∀ c : L, c ^ 59 ≠ (b : L)) :
    Irreducible (albertPolynomial59 b) := by
  exact (X_pow_sub_C_irreducible_iff_of_prime
    (by decide : Nat.Prime 59)).2 hb

variable (sigma : L ≃ₐ[F] L) (beta : L) (b : Lˣ)

omit [FiniteDimensional F L] [IsGalois F L] in
private theorem lift_root_compatible59
    (hratio : sigma (b : L) / (b : L) = beta ^ 59) :
    eval₂
      ((IsScalarTower.toAlgHom F L (albertOverfield59 b)).comp sigma.toAlgHom)
      (algebraMap L (albertOverfield59 b) beta *
        AdjoinRoot.root (albertPolynomial59 b))
      (albertPolynomial59 b) = 0 := by
  simp only [albertPolynomial59, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [mul_pow, root_X_pow_sub_C_pow]
  rw [← map_pow]
  have hsigmaB : sigma (b : L) = beta ^ 59 * (b : L) :=
    (div_eq_iff b.ne_zero).mp hratio
  change algebraMap L (albertOverfield59 b) (beta ^ 59) *
      algebraMap L (albertOverfield59 b) (b : L) -
        algebraMap L (albertOverfield59 b) (sigma (b : L)) = 0
  rw [hsigmaB, map_mul]
  exact sub_self _

/-- The `F`-algebra endomorphism of the Albert overfield extending `sigma`
on `L` and sending the adjoined root `y` to `beta * y`. -/
def albertLiftAlgHom59
    (hratio : sigma (b : L) / (b : L) = beta ^ 59) :
    albertOverfield59 b →ₐ[F] albertOverfield59 b :=
  AdjoinRoot.liftAlgHom (albertPolynomial59 b)
    ((IsScalarTower.toAlgHom F L (albertOverfield59 b)).comp sigma.toAlgHom)
    (algebraMap L (albertOverfield59 b) beta *
      AdjoinRoot.root (albertPolynomial59 b))
    (lift_root_compatible59 sigma beta b hratio)

omit [FiniteDimensional F L] [IsGalois F L] in
@[simp]
theorem albertLiftAlgHom59_root
    (hratio : sigma (b : L) / (b : L) = beta ^ 59) :
    albertLiftAlgHom59 sigma beta b hratio
      (AdjoinRoot.root (albertPolynomial59 b)) =
        algebraMap L (albertOverfield59 b) beta *
          AdjoinRoot.root (albertPolynomial59 b) := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

omit [FiniteDimensional F L] [IsGalois F L] in
@[simp]
theorem albertLiftAlgHom59_algebraMap
    (hratio : sigma (b : L) / (b : L) = beta ^ 59) (x : L) :
    albertLiftAlgHom59 sigma beta b hratio
      (algebraMap L (albertOverfield59 b) x) =
        algebraMap L (albertOverfield59 b) (sigma x) := by
  change AdjoinRoot.liftAlgHom (albertPolynomial59 b)
      ((IsScalarTower.toAlgHom F L (albertOverfield59 b)).comp sigma.toAlgHom)
      (algebraMap L (albertOverfield59 b) beta *
        AdjoinRoot.root (albertPolynomial59 b)) _
      (AdjoinRoot.of (albertPolynomial59 b) x) = _
  rw [AdjoinRoot.liftAlgHom_of]
  rfl

/-- The Albert lift is an automorphism once the adjoined polynomial is
irreducible. -/
def albertLiftAlgEquiv59
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L)) :
    albertOverfield59 b ≃ₐ[F] albertOverfield59 b := by
  letI : Fact (Irreducible (albertPolynomial59 b)) :=
    ⟨albertPolynomial59_irreducible b hb⟩
  letI : Module.Finite L (albertOverfield59 b) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis
        (albertPolynomial59_irreducible b hb).ne_zero).basis
  letI : FiniteDimensional F (albertOverfield59 b) :=
    FiniteDimensional.trans F L (albertOverfield59 b)
  let f := albertLiftAlgHom59 sigma beta b hratio
  have hinj : Function.Injective f := f.injective
  have hsurj : Function.Surjective f :=
    LinearMap.surjective_of_injective (f := f.toLinearMap) hinj
  exact AlgEquiv.ofBijective f ⟨hinj, hsurj⟩

omit [IsGalois F L] in
@[simp]
theorem albertLiftAlgEquiv59_root
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L)) :
    albertLiftAlgEquiv59 sigma beta b hratio hb
      (AdjoinRoot.root (albertPolynomial59 b)) =
        algebraMap L (albertOverfield59 b) beta *
          AdjoinRoot.root (albertPolynomial59 b) := by
  change albertLiftAlgHom59 sigma beta b hratio
      (AdjoinRoot.root (albertPolynomial59 b)) = _
  exact albertLiftAlgHom59_root sigma beta b hratio

omit [IsGalois F L] in
@[simp]
theorem albertLiftAlgEquiv59_algebraMap
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L)) (x : L) :
    albertLiftAlgEquiv59 sigma beta b hratio hb
      (algebraMap L (albertOverfield59 b) x) =
        algebraMap L (albertOverfield59 b) (sigma x) := by
  change albertLiftAlgHom59 sigma beta b hratio
      (algebraMap L (albertOverfield59 b) x) = _
  exact albertLiftAlgHom59_algebraMap sigma beta b hratio x

def orbitProduct59 (n : ℕ) : L :=
  ∏ i ∈ Finset.range n, (sigma ^ i) beta

omit [IsGalois F L] in
theorem albertLiftAlgEquiv59_pow_algebraMap
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L)) (n : ℕ) (x : L) :
    (albertLiftAlgEquiv59 sigma beta b hratio hb ^ n)
      (algebraMap L (albertOverfield59 b) x) =
        algebraMap L (albertOverfield59 b) ((sigma ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, AlgEquiv.mul_apply,
        albertLiftAlgEquiv59_algebraMap, ih, pow_succ, AlgEquiv.mul_apply]

omit [IsGalois F L] in
theorem albertLiftAlgEquiv59_pow_root
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L)) (n : ℕ) :
    (albertLiftAlgEquiv59 sigma beta b hratio hb ^ n)
      (AdjoinRoot.root (albertPolynomial59 b)) =
        algebraMap L (albertOverfield59 b) (orbitProduct59 sigma beta n) *
          AdjoinRoot.root (albertPolynomial59 b) := by
  induction n with
  | zero => simp [orbitProduct59]
  | succ n ih =>
      rw [pow_succ]
      rw [AlgEquiv.mul_apply]
      rw [albertLiftAlgEquiv59_root, map_mul,
        albertLiftAlgEquiv59_pow_algebraMap, ih]
      simp only [orbitProduct59, Finset.prod_range_succ]
      rw [map_mul]
      ring

theorem orbitProduct59_eq_algebraMap_norm
    (hsigma : ∀ tau : L ≃ₐ[F] L, tau ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = 59) :
    orbitProduct59 sigma beta 59 =
      algebraMap F L (Algebra.norm F beta) := by
  rw [Algebra.norm_eq_prod_automorphisms]
  simp only [orbitProduct59]
  rw [← Fin.prod_univ_eq_prod_range (fun i : ℕ => (sigma ^ i) beta) 59]
  have hcard : Nat.card (L ≃ₐ[F] L) = 59 := by
    rw [IsGalois.card_aut_eq_finrank, hfinrank]
  let e : Multiplicative (ZMod 59) ≃* (L ≃ₐ[F] L) :=
    zmodMulEquivOfGenerator hsigma hcard
  let eFin : Fin 59 ≃ (L ≃ₐ[F] L) :=
    (ZMod.finEquiv 59).toEquiv.trans
      (Multiplicative.ofAdd.trans e.toEquiv)
  have heFin (i : Fin 59) : eFin i = sigma ^ (i : ℕ) := by
    have hfinCast : ZMod.finEquiv 59 i = ((i.val : ℤ) : ZMod 59) := by
      calc
        ZMod.finEquiv 59 i = ((i.val : ℕ) : ZMod 59) := by
          apply Fin.ext
          change i.val = i.val % 59
          exact (Nat.mod_eq_of_lt i.isLt).symm
        _ = ((i.val : ℤ) : ZMod 59) := by norm_cast
    calc
      eFin i = e (Multiplicative.ofAdd (ZMod.finEquiv 59 i)) := rfl
      _ = e (Multiplicative.ofAdd ((i.val : ℤ) : ZMod 59)) := by rw [hfinCast]
      _ = sigma ^ (i.val : ℤ) :=
        zmodMulEquivOfGenerator_apply_ofAdd_intCast
          hsigma hcard (i.val : ℤ)
      _ = sigma ^ (i : ℕ) := by rw [zpow_natCast]
  apply Fintype.prod_equiv eFin
    (fun i : Fin 59 => (sigma ^ (i : ℕ)) beta)
    (fun tau : L ≃ₐ[F] L => tau beta)
  intro i
  rw [heFin]

def mappedRootOfUnity59 (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    rootsOfUnity 59 L :=
  rootsOfUnity.mkOfPowEq (algebraMap F L zeta) (by
    rw [← map_pow, hzeta.pow_eq_one, map_one])

/-- The Kummer automorphism over `L` which fixes the coefficient field and
scales the adjoined root by the image of `zeta`, regarded as an
`F`-automorphism. -/
def scalarRootAutomorphism59
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    albertOverfield59 b ≃ₐ[F] albertOverfield59 b :=
  (autAdjoinRootXPowSubC 59 (b : L)
    (mappedRootOfUnity59 (L := L) zeta hzeta)).restrictScalars F

omit [FiniteDimensional F L] [IsGalois F L] in
@[simp]
theorem scalarRootAutomorphism59_root
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    scalarRootAutomorphism59 (b := b) zeta hzeta
      (AdjoinRoot.root (albertPolynomial59 b)) =
      algebraMap L (albertOverfield59 b) (algebraMap F L zeta) *
        AdjoinRoot.root (albertPolynomial59 b) := by
  rw [scalarRootAutomorphism59]
  simpa [mappedRootOfUnity59, Algebra.smul_def] using
    (autAdjoinRootXPowSubC_root (n := 59) (b : L)
      (mappedRootOfUnity59 (L := L) zeta hzeta))

omit [FiniteDimensional F L] [IsGalois F L] in
@[simp]
theorem scalarRootAutomorphism59_algebraMap
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (x : L) :
    scalarRootAutomorphism59 (b := b) zeta hzeta
      (algebraMap L (albertOverfield59 b) x) =
        algebraMap L (albertOverfield59 b) x := by
  exact (autAdjoinRootXPowSubC 59 (b : L)
    (mappedRootOfUnity59 (L := L) zeta hzeta)).commutes x

set_option maxRecDepth 10000 in
/-- After 59 iterations, the Albert lift is exactly the Kummer
automorphism which fixes `L` and scales the new root by `zeta`. -/
theorem albertLiftAlgEquiv59_pow_fiftyNine
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L))
    (hsigma : ∀ tau : L ≃ₐ[F] L, tau ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = 59)
    (hbeta : Algebra.norm F beta = zeta) :
    albertLiftAlgEquiv59 sigma beta b hratio hb ^ 59 =
      scalarRootAutomorphism59 (b := b) zeta hzeta := by
  have horder : orderOf sigma = 59 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hsigma,
      IsGalois.card_aut_eq_finrank, hfinrank]
  have hsigmaPow : sigma ^ 59 = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one sigma
  apply AlgEquiv.ext
  have heq :
      (albertLiftAlgEquiv59 sigma beta b hratio hb ^ 59).toAlgHom =
        (scalarRootAutomorphism59 (b := b) zeta hzeta).toAlgHom := by
    apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro x
      simp only [AlgHom.comp_apply, AdjoinRoot.coe_ofAlgHom]
      calc
        (albertLiftAlgEquiv59 sigma beta b hratio hb ^ 59)
            (AdjoinRoot.of (albertPolynomial59 b) x) =
            algebraMap L (albertOverfield59 b) ((sigma ^ 59) x) := by
              have hx := albertLiftAlgEquiv59_pow_algebraMap
                sigma beta b hratio hb 59 x
              exact hx
        _ = algebraMap L (albertOverfield59 b) x := by
              rw [hsigmaPow]
              rfl
        _ = scalarRootAutomorphism59 (b := b) zeta hzeta
            (AdjoinRoot.of (albertPolynomial59 b) x) := by
              symm
              have hx := scalarRootAutomorphism59_algebraMap
                (b := b) zeta hzeta x
              exact hx
    · rw [AlgEquiv.coe_algHom, AlgEquiv.coe_algHom,
        albertLiftAlgEquiv59_pow_root,
        orbitProduct59_eq_algebraMap_norm sigma beta hsigma hfinrank,
        hbeta, scalarRootAutomorphism59_root]
  exact fun x => DFunLike.congr_fun heq x

end Fermat.Conservation.AlbertExtension59
