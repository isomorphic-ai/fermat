/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Exact compatibility of the Albert and Kummer cyclic characters at a prime

For every prime `p`, the transported Albert generator restricts to the
original degree-`p` generator.  Reduction of its `C_(p²)` character is thus
exactly the supplied `C_p` character.  The concrete endpoint applies this to
the generic Kummer splitting field and constructs a continuous lift from a
norm witness.
-/
import Fermat.Experiments.Conservation.PrimeAlbertCyclicQuotient
import Fermat.Experiments.Conservation.PrimeKummerCyclicQuotient
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.PrimeAlbertCyclicCompatibility

open Fermat.Conservation.PrimeAlbertExtension
open Fermat.Conservation.PrimeAlbertGalois
open Fermat.Conservation.PrimeAlbertCyclicQuotient
open Fermat.Conservation.PrimeCyclicExtension

variable (p : ℕ) [Fact p.Prime]

local instance : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
local instance : NeZero (p ^ 2) :=
  ⟨pow_ne_zero 2 (Fact.out : Nat.Prime p).ne_zero⟩

local instance : TopologicalSpace (CyclicGroup p) := ⊥
local instance : DiscreteTopology (CyclicGroup p) := ⟨rfl⟩
local instance : TopologicalSpace (CyclicGroupSquared p) := ⊥
local instance : DiscreteTopology (CyclicGroupSquared p) := ⟨rfl⟩

variable {F L : Type} [Field F] [Field L] [Algebra F L]
variable [FiniteDimensional F L] [IsGalois F L]

variable (b : Lˣ) (sigma : L ≃ₐ[F] L) (beta : L)

/-- The abstract Albert lift restricts to the original degree-`p`
automorphism. -/
theorem albertLiftAlgEquiv_restrictNormal
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L)) :
    letI : Fact (Irreducible (albertPolynomial p b)) :=
      ⟨albertPolynomial_irreducible p b hb⟩
    AlgEquiv.restrictNormalHom L
      (albertLiftAlgEquiv p sigma beta b hratio hb) = sigma := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L (albertOverfield p b)).injective
  have hcomm := AlgEquiv.restrictNormal_commutes
    (albertLiftAlgEquiv p sigma beta b hratio hb) L x
  rw [albertLiftAlgEquiv_algebraMap] at hcomm
  exact hcomm

/-- The generator-oriented cyclic coordinate on `Gal(L/F)`. -/
def generatorGalEquiv
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p) :
    (L ≃ₐ[F] L) ≃ₜ* CyclicGroup p := by
  have hcard : Nat.card (L ≃ₐ[F] L) = p := by
    rw [IsGalois.card_aut_eq_finrank, hfinrank]
  let e : (L ≃ₐ[F] L) ≃* CyclicGroup p :=
    (zmodMulEquivOfGenerator hsigma hcard).symm
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

theorem generatorGalEquiv_apply_generator
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p) :
    generatorGalEquiv p sigma hsigma hfinrank sigma =
      Multiplicative.ofAdd (1 : ZMod p) := by
  simp only [generatorGalEquiv]
  exact zmodMulEquivOfGenerator_symm_apply_generator hsigma
    (by rw [IsGalois.card_aut_eq_finrank, hfinrank])

@[simp]
theorem reduction_ofAdd_one :
    reduction p (Multiplicative.ofAdd (1 : ZMod (p ^ 2))) =
      Multiplicative.ofAdd (1 : ZMod p) := by
  apply Multiplicative.toAdd.injective
  change ZMod.castHom (p_dvd_p_sq p) (ZMod p) 1 = 1
  simp

/-- Restriction from the transported closure Galois group back to the
original degree-`p` field, via the chosen embedding equivalence. -/
def albertClosureRestriction
    (iL : L →ₐ[F] AlgebraicClosure F)
    (hb : ∀ c : L, c ^ p ≠ (b : L)) :
    (albertClosureField p b iL hb ≃ₐ[F]
      albertClosureField p b iL hb) →*
        (L ≃ₐ[F] L) := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  exact (AlgEquiv.restrictNormalHom L).comp
    (AlgEquiv.autCongr
      (albertOverfieldEquivClosure p b iL hb)).symm.toMonoidHom

theorem albertClosureRestriction_generator
    (iL : L →ₐ[F] AlgebraicClosure F)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L)) :
    albertClosureRestriction p b iL hb
      (albertClosureGenerator p b sigma beta iL hratio hb) = sigma := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  change AlgEquiv.restrictNormalHom L
    ((AlgEquiv.autCongr (albertOverfieldEquivClosure p b iL hb)).symm
      (AlgEquiv.autCongr (albertOverfieldEquivClosure p b iL hb)
        (albertLiftAlgEquiv p sigma beta b hratio hb))) = sigma
  rw [MulEquiv.symm_apply_apply]
  exact albertLiftAlgEquiv_restrictNormal p b sigma beta hratio hb

theorem albertClosureGalEquiv_apply_generator
    (iL : L →ₐ[F] AlgebraicClosure F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (hbeta : Algebra.norm F beta = zeta) :
    albertClosureGalEquiv p b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta
      (albertClosureGenerator p b sigma beta iL hratio hb) =
        Multiplicative.ofAdd (1 : ZMod (p ^ 2)) := by
  simp only [albertClosureGalEquiv]
  exact zmodMulEquivOfGenerator_symm_apply_generator
    (fun rho ↦ by
      rw [albertClosureGenerator_zpowers_eq_top p b sigma beta iL zeta hzeta
        hratio hb hsigma hfinrank hbeta]
      exact Subgroup.mem_top rho)
    (albertClosureField_card_aut p b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta)

/-- The finite cyclic-coordinate square commutes. -/
theorem albertFiniteCyclicCompatibility
    (iL : L →ₐ[F] AlgebraicClosure F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (hbeta : Algebra.norm F beta = zeta) :
    (reduction p).toMonoidHom.comp
        (albertClosureGalEquiv p b sigma beta iL zeta hzeta
          hratio hb hsigma hfinrank hbeta).toMulEquiv.toMonoidHom =
      (generatorGalEquiv p sigma hsigma hfinrank).toMulEquiv.toMonoidHom.comp
        (albertClosureRestriction p b iL hb) := by
  let tau := albertClosureGenerator p b sigma beta iL hratio hb
  have htau : ∀ rho, rho ∈ Subgroup.zpowers tau := by
    intro rho
    rw [albertClosureGenerator_zpowers_eq_top p b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta]
    exact Subgroup.mem_top rho
  apply (MonoidHom.eq_iff_eq_on_generator htau _ _).mpr
  simp only [MonoidHom.comp_apply]
  dsimp [tau]
  change reduction p
      (albertClosureGalEquiv p b sigma beta iL zeta hzeta
        hratio hb hsigma hfinrank hbeta
        (albertClosureGenerator p b sigma beta iL hratio hb)) =
    generatorGalEquiv p sigma hsigma hfinrank
      (albertClosureRestriction p b iL hb
        (albertClosureGenerator p b sigma beta iL hratio hb))
  rw [albertClosureGalEquiv_apply_generator p b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta,
    reduction_ofAdd_one,
    albertClosureRestriction_generator p b sigma beta iL hratio hb,
    generatorGalEquiv_apply_generator p sigma hsigma hfinrank]

section ConcreteIntermediateField

variable (K : IntermediateField F (AlgebraicClosure F))
variable [FiniteDimensional F K] [IsGalois F K]

omit [FiniteDimensional F L] [IsGalois F L]
    [FiniteDimensional F K] [IsGalois F K] in
set_option maxHeartbeats 800000 in
theorem albertBase_le_closure
    (bK : Kˣ)
    (hb : ∀ c : K, c ^ p ≠ (bK : K)) :
    K ≤ albertClosureField p bK K.val hb := by
  letI : Fact (Irreducible (albertPolynomial p bK)) :=
    ⟨albertPolynomial_irreducible p bK hb⟩
  intro x hx
  change x ∈ (albertClosureEmbedding p bK K.val hb).fieldRange
  rw [AlgHom.mem_fieldRange]
  refine ⟨algebraMap K (albertOverfield p bK) ⟨x, hx⟩, ?_⟩
  have hres := albertClosureEmbedding_restrictDomain p bK K.val hb
  exact DFunLike.congr_fun hres ⟨x, hx⟩

/-- The original intermediate field, regarded as an intermediate field of
the Albert closure image. -/
def albertBaseInsideClosure
    (bK : Kˣ)
    (hb : ∀ c : K, c ^ p ≠ (bK : K)) :
    IntermediateField F (albertClosureField p bK K.val hb) :=
  IntermediateField.restrict (albertBase_le_closure p K bK hb)

/-- The tautological equivalence from the original intermediate field to
its copy inside the Albert closure image. -/
def albertBaseEquivInsideClosure
    (bK : Kˣ)
    (hb : ∀ c : K, c ^ p ≠ (bK : K)) :
    K ≃ₐ[F] albertBaseInsideClosure p K bK hb :=
  IntermediateField.restrict_algEquiv (albertBase_le_closure p K bK hb)

omit [FiniteDimensional F L] [IsGalois F L]
    [FiniteDimensional F K] [IsGalois F K] in
set_option maxHeartbeats 800000 in
theorem albertOverfieldEquivClosure_commutes_base
    (bK : Kˣ)
    (hb : ∀ c : K, c ^ p ≠ (bK : K))
    (x : K) :
    albertOverfieldEquivClosure p bK K.val hb
        (algebraMap K (albertOverfield p bK) x) =
      algebraMap (albertBaseInsideClosure p K bK hb)
        (albertClosureField p bK K.val hb)
        (albertBaseEquivInsideClosure p K bK hb x) := by
  apply Subtype.ext
  change albertClosureEmbedding p bK K.val hb
      (algebraMap K (albertOverfield p bK) x) = x
  have hres := albertClosureEmbedding_restrictDomain p bK K.val hb
  exact DFunLike.congr_fun hres x

/-- Genuine tower restriction from the Albert closure image to the original
intermediate field. -/
def albertConcreteRestriction
    (bK : Kˣ)
    (hb : ∀ c : K, c ^ p ≠ (bK : K)) :
    (albertClosureField p bK K.val hb ≃ₐ[F]
      albertClosureField p bK K.val hb) →* (K ≃ₐ[F] K) := by
  let B := albertBaseInsideClosure p K bK hb
  let eB := albertBaseEquivInsideClosure p K bK hb
  letI : IsGalois F B := IsGalois.of_algEquiv eB
  exact (AlgEquiv.autCongr eB).symm.toMonoidHom.comp
    (AlgEquiv.restrictNormalHom B)

set_option maxHeartbeats 800000 in
theorem albertConcreteRestriction_generator
    (bK : Kˣ) (sigmaK : K ≃ₐ[F] K) (betaK : K)
    (hratio : sigmaK (bK : K) / (bK : K) = betaK ^ p)
    (hb : ∀ c : K, c ^ p ≠ (bK : K)) :
    albertConcreteRestriction p K bK hb
      (albertClosureGenerator p bK sigmaK betaK K.val hratio hb) = sigmaK := by
  let B := albertBaseInsideClosure p K bK hb
  let eB := albertBaseEquivInsideClosure p K bK hb
  let eM := albertOverfieldEquivClosure p bK K.val hb
  let tau := albertLiftAlgEquiv p sigmaK betaK bK hratio hb
  let tauN := albertClosureGenerator p bK sigmaK betaK K.val hratio hb
  letI : IsGalois F B := IsGalois.of_algEquiv eB
  change (AlgEquiv.autCongr eB).symm
      (AlgEquiv.restrictNormalHom B tauN) = sigmaK
  apply (AlgEquiv.autCongr eB).injective
  rw [MulEquiv.apply_symm_apply]
  apply AlgEquiv.ext
  intro y
  let x := eB.symm y
  have hy : y = eB x := by simp [x]
  rw [hy]
  apply (algebraMap B (albertClosureField p bK K.val hb)).injective
  change (↑((AlgEquiv.restrictNormalHom B tauN) (eB x)) :
      albertClosureField p bK K.val hb) = _
  rw [AlgEquiv.restrictNormalHom_apply]
  change tauN
      (algebraMap B (albertClosureField p bK K.val hb) (eB x)) =
    algebraMap B (albertClosureField p bK K.val hb)
      ((AlgEquiv.autCongr eB sigmaK) (eB x))
  rw [← albertOverfieldEquivClosure_commutes_base p K bK hb x]
  change (AlgEquiv.autCongr eM tau)
      (eM (algebraMap K (albertOverfield p bK) x)) = _
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply]
  dsimp [tau]
  change eM (albertLiftAlgEquiv p sigmaK betaK bK hratio hb
      (algebraMap K (albertOverfield p bK) x)) = _
  rw [albertLiftAlgEquiv_algebraMap]
  rw [albertOverfieldEquivClosure_commutes_base p K bK hb (sigmaK x)]
  rfl

theorem albertConcreteFiniteCyclicCompatibility
    (bK : Kˣ) (sigmaK : K ≃ₐ[F] K) (betaK : K)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigmaK (bK : K) / (bK : K) = betaK ^ p)
    (hb : ∀ c : K, c ^ p ≠ (bK : K))
    (hsigma : ∀ rho : K ≃ₐ[F] K, rho ∈ Subgroup.zpowers sigmaK)
    (hfinrank : Module.finrank F K = p)
    (hbeta : Algebra.norm F betaK = zeta) :
    (reduction p).toMonoidHom.comp
        (albertClosureGalEquiv p bK sigmaK betaK K.val zeta hzeta
          hratio hb hsigma hfinrank hbeta).toMulEquiv.toMonoidHom =
      (generatorGalEquiv p sigmaK hsigma hfinrank).toMulEquiv.toMonoidHom.comp
        (albertConcreteRestriction p K bK hb) := by
  let tau := albertClosureGenerator p bK sigmaK betaK K.val hratio hb
  have htau : ∀ rho, rho ∈ Subgroup.zpowers tau := by
    intro rho
    rw [albertClosureGenerator_zpowers_eq_top p bK sigmaK betaK K.val zeta hzeta
      hratio hb hsigma hfinrank hbeta]
    exact Subgroup.mem_top rho
  apply (MonoidHom.eq_iff_eq_on_generator htau _ _).mpr
  simp only [MonoidHom.comp_apply]
  dsimp [tau]
  change reduction p
      (albertClosureGalEquiv p bK sigmaK betaK K.val zeta hzeta
        hratio hb hsigma hfinrank hbeta
        (albertClosureGenerator p bK sigmaK betaK K.val hratio hb)) =
    generatorGalEquiv p sigmaK hsigma hfinrank
      (albertConcreteRestriction p K bK hb
        (albertClosureGenerator p bK sigmaK betaK K.val hratio hb))
  rw [albertClosureGalEquiv_apply_generator p bK sigmaK betaK K.val zeta hzeta
      hratio hb hsigma hfinrank hbeta,
    reduction_ofAdd_one,
    albertConcreteRestriction_generator p K bK sigmaK betaK hratio hb,
    generatorGalEquiv_apply_generator p sigmaK hsigma hfinrank]

set_option maxHeartbeats 1000000 in
theorem albertConcreteRestriction_absoluteGalois
    (bK : Kˣ) (sigmaK : K ≃ₐ[F] K) (betaK : K)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigmaK (bK : K) / (bK : K) = betaK ^ p)
    (hb : ∀ c : K, c ^ p ≠ (bK : K))
    (hsigma : ∀ rho : K ≃ₐ[F] K, rho ∈ Subgroup.zpowers sigmaK)
    (hfinrank : Module.finrank F K = p)
    (hbeta : Algebra.norm F betaK = zeta)
    (g : Field.absoluteGaloisGroup F) :
    letI : IsGalois F (albertClosureField p bK K.val hb) :=
      albertClosureField_isGalois p bK sigmaK betaK K.val zeta hzeta
        hratio hb hsigma hfinrank hbeta
    albertConcreteRestriction p K bK hb
        (ContinuousCyclicQuotient.absoluteGaloisRestriction F
          (albertClosureField p bK K.val hb) g) =
      ContinuousCyclicQuotient.absoluteGaloisRestriction F K g := by
  let N := albertClosureField p bK K.val hb
  let B := albertBaseInsideClosure p K bK hb
  let eB := albertBaseEquivInsideClosure p K bK hb
  letI : IsGalois F N :=
    albertClosureField_isGalois p bK sigmaK betaK K.val zeta hzeta
      hratio hb hsigma hfinrank hbeta
  letI : IsGalois F B := IsGalois.of_algEquiv eB
  change (AlgEquiv.autCongr eB).symm
      (AlgEquiv.restrictNormalHom B
        (AlgEquiv.restrictNormalHom N g)) =
    AlgEquiv.restrictNormalHom K g
  apply (AlgEquiv.autCongr eB).injective
  rw [MulEquiv.apply_symm_apply]
  apply AlgEquiv.ext
  intro y
  let x := eB.symm y
  have hy : y = eB x := by simp [x]
  rw [hy]
  apply Subtype.ext
  apply Subtype.ext
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply]
  rw [AlgEquiv.restrictNormalHom_apply]
  rw [AlgEquiv.restrictNormalHom_apply]
  change (show AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F from g)
      (x : AlgebraicClosure F) =
    ((AlgEquiv.restrictNormalHom K g) x : AlgebraicClosure F)
  rw [AlgEquiv.restrictNormalHom_apply]

/-- The original `C_p` absolute-Galois quotient in the cyclic coordinate
which sends `sigmaK` to one. -/
def generatorCharacter
    (sigmaK : K ≃ₐ[F] K)
    (hsigma : ∀ rho : K ≃ₐ[F] K, rho ∈ Subgroup.zpowers sigmaK)
    (hfinrank : Module.finrank F K = p) :
    Field.absoluteGaloisGroup F →ₜ* CyclicGroup p :=
  ContinuousCyclicQuotient.cyclicQuotient F p K
    (generatorGalEquiv p sigmaK hsigma hfinrank)

set_option maxHeartbeats 1000000 in
/-- Exact Albert compatibility on the absolute Galois group. -/
theorem albertCharacter_reduction_eq_generatorCharacter
    (bK : Kˣ) (sigmaK : K ≃ₐ[F] K) (betaK : K)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigmaK (bK : K) / (bK : K) = betaK ^ p)
    (hb : ∀ c : K, c ^ p ≠ (bK : K))
    (hsigma : ∀ rho : K ≃ₐ[F] K, rho ∈ Subgroup.zpowers sigmaK)
    (hfinrank : Module.finrank F K = p)
    (hbeta : Algebra.norm F betaK = zeta) :
    (reduction p).comp
        (albertCharacter p bK sigmaK betaK K.val zeta hzeta
          hratio hb hsigma hfinrank hbeta) =
      generatorCharacter p K sigmaK hsigma hfinrank := by
  letI : IsGalois F (albertClosureField p bK K.val hb) :=
    albertClosureField_isGalois p bK sigmaK betaK K.val zeta hzeta
      hratio hb hsigma hfinrank hbeta
  apply ContinuousMonoidHom.ext
  intro g
  change reduction p
      (albertClosureGalEquiv p bK sigmaK betaK K.val zeta hzeta
        hratio hb hsigma hfinrank hbeta
        (ContinuousCyclicQuotient.absoluteGaloisRestriction F
          (albertClosureField p bK K.val hb) g)) =
    generatorGalEquiv p sigmaK hsigma hfinrank
      (ContinuousCyclicQuotient.absoluteGaloisRestriction F K g)
  have hfinite := DFunLike.congr_fun
    (albertConcreteFiniteCyclicCompatibility p K bK sigmaK betaK zeta hzeta
      hratio hb hsigma hfinrank hbeta)
    (ContinuousCyclicQuotient.absoluteGaloisRestriction F
      (albertClosureField p bK K.val hb) g)
  simp only [MonoidHom.comp_apply] at hfinite
  rw [albertConcreteRestriction_absoluteGalois p K bK sigmaK betaK zeta hzeta
    hratio hb hsigma hfinrank hbeta g] at hfinite
  exact hfinite

end ConcreteIntermediateField

section ConcreteKummer

open Fermat.Conservation.PrimeAlbertDescentDatum
open Fermat.Conservation.PrimeKummerCyclicQuotient

variable (F : Type) [Field F]
variable (zeta a : F)
variable (hzeta : IsPrimitiveRoot zeta p)
variable (ha : ∀ x : F, x ^ p ≠ a)

private theorem concreteKummerGenerator_ne_one :
    concreteKummerGenerator p F zeta a hzeta ha ≠ 1 := by
  letI : Fact (1 < p) := ⟨(Fact.out : Nat.Prime p).one_lt⟩
  intro h
  have himage := congrArg
    (fun rho ↦ kummerGalEquiv p F zeta a hzeta ha rho) h
  simp [concreteKummerGenerator] at himage

theorem generatorGalEquiv_eq_kummerGalEquiv
    (hsigma : ∀ rho : kummerExtension p F a ≃ₐ[F] kummerExtension p F a,
      rho ∈ Subgroup.zpowers
        (concreteKummerGenerator p F zeta a hzeta ha))
    (hfinrank : Module.finrank F (kummerExtension p F a) = p) :
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
    generatorGalEquiv p
        (concreteKummerGenerator p F zeta a hzeta ha) hsigma hfinrank =
      kummerGalEquiv p F zeta a hzeta ha := by
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
  apply ContinuousMulEquiv.ext
  have heq :
      (generatorGalEquiv p
        (concreteKummerGenerator p F zeta a hzeta ha)
        hsigma hfinrank).toMulEquiv =
      (kummerGalEquiv p F zeta a hzeta ha).toMulEquiv := by
    apply (MulEquiv.eq_iff_eq_on_generator hsigma _ _).mpr
    change generatorGalEquiv p
        (concreteKummerGenerator p F zeta a hzeta ha) hsigma hfinrank
          (concreteKummerGenerator p F zeta a hzeta ha) =
      kummerGalEquiv p F zeta a hzeta ha
        (concreteKummerGenerator p F zeta a hzeta ha)
    rw [generatorGalEquiv_apply_generator]
    simp [concreteKummerGenerator]
  intro rho
  exact DFunLike.congr_fun heq rho

set_option maxHeartbeats 1200000 in
/-- Constructive Albert direction for the concrete prime Kummer character:
a norm witness produces a continuous `C_(p²)` character whose reduction is
exactly the existing `C_p` Kummer character. -/
theorem concreteKummer_exists_albertCharacter
    (beta : kummerExtension p F a)
    (hbeta : Algebra.norm F beta = zeta) :
    ∃ psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroupSquared p,
      (reduction p).comp psi =
        kummerCharacter p F zeta a hzeta ha := by
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
  let sigma := concreteKummerGenerator p F zeta a hzeta ha
  have hfinrank : Module.finrank F (kummerExtension p F a) = p :=
    finrank_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (Fact.out : Nat.Prime p).pos).2 hzeta⟩
      (kummerPolynomial_irreducible p F a ha)
      (kummerExtension p F a)
  have hcard : Nat.card
      (kummerExtension p F a ≃ₐ[F] kummerExtension p F a) = p := by
    rw [IsGalois.card_aut_eq_finrank, hfinrank]
  have hsigma : ∀ rho : kummerExtension p F a ≃ₐ[F] kummerExtension p F a,
      rho ∈ Subgroup.zpowers sigma := by
    intro rho
    exact mem_zpowers_of_prime_card hcard
      (concreteKummerGenerator_ne_one p F zeta a hzeta ha)
  obtain ⟨bK, hratio, hb⟩ :=
    concreteKummer_exists_albert_descent_datum
      p F zeta a hzeta ha beta hbeta
  let psi := albertCharacter p bK sigma beta
    (kummerExtension p F a).val zeta hzeta
      hratio hb hsigma hfinrank hbeta
  refine ⟨psi, ?_⟩
  calc
    (reduction p).comp psi =
        generatorCharacter p (kummerExtension p F a)
          sigma hsigma hfinrank :=
      albertCharacter_reduction_eq_generatorCharacter
        p (kummerExtension p F a) bK sigma beta zeta hzeta
          hratio hb hsigma hfinrank hbeta
    _ = kummerCharacter p F zeta a hzeta ha := by
      unfold generatorCharacter
      rw [generatorGalEquiv_eq_kummerGalEquiv p F zeta a hzeta ha
        hsigma hfinrank]
      rfl

end ConcreteKummer

end Fermat.Conservation.PrimeAlbertCyclicCompatibility
