/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The continuous cyclic Albert quotient at an arbitrary prime

This transports the generic finite Albert overfield into a chosen algebraic
closure and constructs its continuous, surjective `C_(p²)` absolute-Galois
character.  The chosen embedding extends the supplied embedding of the
degree-`p` subfield.
-/
import Fermat.Conservation.PrimeAlbertGalois
import Fermat.Conservation.PrimeCyclicExtension
import Fermat.Conservation.ContinuousCyclicQuotient
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Instances.ZMod
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.PrimeAlbertCyclicQuotient

open Fermat.Conservation.PrimeAlbertExtension
open Fermat.Conservation.PrimeAlbertOrder
open Fermat.Conservation.PrimeAlbertGalois
open Fermat.Conservation.PrimeCyclicExtension

variable (p : ℕ) [Fact p.Prime]

local instance : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
local instance : NeZero (p ^ 2) :=
  ⟨pow_ne_zero 2 (Fact.out : Nat.Prime p).ne_zero⟩

local instance : TopologicalSpace (CyclicGroupSquared p) := ⊥
local instance : DiscreteTopology (CyclicGroupSquared p) := ⟨rfl⟩

variable {F L : Type} [Field F] [Field L] [Algebra F L]
variable [FiniteDimensional F L] [IsGalois F L]

variable (b : Lˣ)

/-- An embedding of the Albert overfield into the chosen algebraic closure
which extends the supplied embedding of its degree-`p` subfield. -/
def albertClosureEmbedding
    (iL : L →ₐ[F] AlgebraicClosure F)
    (hb : ∀ c : L, c ^ p ≠ (b : L)) :
    albertOverfield p b →ₐ[F] AlgebraicClosure F := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  letI : FiniteDimensional L (albertOverfield p b) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis (albertPolynomial_irreducible p b hb).ne_zero).basis
  exact Classical.choose
    (IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
      (K := F) (L := L) (M := AlgebraicClosure F)
      (E := albertOverfield p b) iL)

omit [FiniteDimensional F L] [IsGalois F L] in
theorem albertClosureEmbedding_restrictDomain
    (iL : L →ₐ[F] AlgebraicClosure F)
    (hb : ∀ c : L, c ^ p ≠ (b : L)) :
    (albertClosureEmbedding p b iL hb).restrictDomain L = iL := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  letI : FiniteDimensional L (albertOverfield p b) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis (albertPolynomial_irreducible p b hb).ne_zero).basis
  exact Classical.choose_spec
    (IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
      (K := F) (L := L) (M := AlgebraicClosure F)
      (E := albertOverfield p b) iL)

/-- The image of the Albert overfield in the chosen algebraic closure. -/
def albertClosureField
    (iL : L →ₐ[F] AlgebraicClosure F)
    (hb : ∀ c : L, c ^ p ≠ (b : L)) :
    IntermediateField F (AlgebraicClosure F) := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  exact (albertClosureEmbedding p b iL hb).fieldRange

/-- The abstract Albert overfield is `F`-isomorphic to its chosen image. -/
def albertOverfieldEquivClosure
    (iL : L →ₐ[F] AlgebraicClosure F)
    (hb : ∀ c : L, c ^ p ≠ (b : L)) :
    albertOverfield p b ≃ₐ[F] albertClosureField p b iL hb := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  exact AlgEquiv.ofInjectiveField (albertClosureEmbedding p b iL hb)

variable (sigma : L ≃ₐ[F] L) (beta : L)

/-- The finite Albert overfield remains Galois after embedding it into the
chosen algebraic closure. -/
theorem albertClosureField_isGalois
    (iL : L →ₐ[F] AlgebraicClosure F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (hbeta : Algebra.norm F beta = zeta) :
    IsGalois F (albertClosureField p b iL hb) := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  letI : IsGalois F (albertOverfield p b) :=
    albertOverfield_isGalois p b sigma beta zeta hzeta
      hratio hb hsigma hfinrank hbeta
  exact IsGalois.of_algEquiv (albertOverfieldEquivClosure p b iL hb)

/-- The Albert generator transported to the chosen intermediate field. -/
def albertClosureGenerator
    (iL : L →ₐ[F] AlgebraicClosure F)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L)) :
    albertClosureField p b iL hb ≃ₐ[F]
      albertClosureField p b iL hb :=
  AlgEquiv.autCongr (albertOverfieldEquivClosure p b iL hb)
    (albertLiftAlgEquiv p sigma beta b hratio hb)

theorem albertClosureGenerator_zpowers_eq_top
    (iL : L →ₐ[F] AlgebraicClosure F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (hbeta : Algebra.norm F beta = zeta) :
    Subgroup.zpowers
      (albertClosureGenerator p b sigma beta iL hratio hb) = ⊤ := by
  let e := albertOverfieldEquivClosure p b iL hb
  let tau := albertLiftAlgEquiv p sigma beta b hratio hb
  have htop : Subgroup.zpowers tau = ⊤ :=
    albertLiftAlgEquiv_zpowers_eq_top p b sigma beta zeta hzeta
      hratio hb hsigma hfinrank hbeta
  rw [Subgroup.eq_top_iff']
  intro rho
  obtain ⟨rho0, rfl⟩ := (AlgEquiv.autCongr e).surjective rho
  have hrho : rho0 ∈ Subgroup.zpowers tau := by
    rw [htop]
    exact Subgroup.mem_top rho0
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hrho
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨k, ?_⟩
  change (AlgEquiv.autCongr e tau) ^ k = AlgEquiv.autCongr e rho0
  rw [← map_zpow, hk]

theorem albertClosureField_card_aut
    (iL : L →ₐ[F] AlgebraicClosure F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (hbeta : Algebra.norm F beta = zeta) :
    Nat.card
      (albertClosureField p b iL hb ≃ₐ[F]
        albertClosureField p b iL hb) = p ^ 2 := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  calc
    Nat.card
        (albertClosureField p b iL hb ≃ₐ[F]
          albertClosureField p b iL hb) =
        Nat.card (albertOverfield p b ≃ₐ[F] albertOverfield p b) :=
      (Nat.card_congr
        (AlgEquiv.autCongr
          (albertOverfieldEquivClosure p b iL hb)).toEquiv).symm
    _ = p ^ 2 := albertOverfield_card_aut p b sigma beta zeta hzeta
      hratio hb hsigma hfinrank hbeta

/-- The Galois group of the chosen closure image, continuously and
generator-preservingly identified with `C_(p²)`. -/
def albertClosureGalEquiv
    (iL : L →ₐ[F] AlgebraicClosure F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (hbeta : Algebra.norm F beta = zeta) :
    ((albertClosureField p b iL hb ≃ₐ[F]
        albertClosureField p b iL hb) ≃ₜ*
      CyclicGroupSquared p) := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  letI : FiniteDimensional L (albertOverfield p b) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis (albertPolynomial_irreducible p b hb).ne_zero).basis
  letI : FiniteDimensional F (albertOverfield p b) :=
    FiniteDimensional.trans F L (albertOverfield p b)
  letI : FiniteDimensional F (albertClosureField p b iL hb) :=
    (albertOverfieldEquivClosure p b iL hb).toLinearEquiv.finiteDimensional
  letI : IsGalois F (albertClosureField p b iL hb) :=
    albertClosureField_isGalois p b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta
  let tau := albertClosureGenerator p b sigma beta iL hratio hb
  have htau : ∀ rho, rho ∈ Subgroup.zpowers tau := by
    intro rho
    rw [albertClosureGenerator_zpowers_eq_top p b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta]
    exact Subgroup.mem_top rho
  have hcard : Nat.card
      (albertClosureField p b iL hb ≃ₐ[F]
        albertClosureField p b iL hb) = p ^ 2 :=
    albertClosureField_card_aut p b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta
  let e :
      (albertClosureField p b iL hb ≃ₐ[F]
        albertClosureField p b iL hb) ≃*
          CyclicGroupSquared p :=
    (zmodMulEquivOfGenerator htau hcard).symm
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The continuous cyclic `C_(p²)` quotient supplied by the constructive
Albert overfield. -/
def albertCharacter
    (iL : L →ₐ[F] AlgebraicClosure F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (hbeta : Algebra.norm F beta = zeta) :
    Field.absoluteGaloisGroup F →ₜ* CyclicGroupSquared p := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  letI : FiniteDimensional L (albertOverfield p b) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis (albertPolynomial_irreducible p b hb).ne_zero).basis
  letI : FiniteDimensional F (albertOverfield p b) :=
    FiniteDimensional.trans F L (albertOverfield p b)
  letI : FiniteDimensional F (albertClosureField p b iL hb) :=
    (albertOverfieldEquivClosure p b iL hb).toLinearEquiv.finiteDimensional
  letI : IsGalois F (albertClosureField p b iL hb) :=
    albertClosureField_isGalois p b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta
  exact ContinuousCyclicQuotient.cyclicQuotient F (p ^ 2)
    (albertClosureField p b iL hb)
    (albertClosureGalEquiv p b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta)

theorem albertCharacter_surjective
    (iL : L →ₐ[F] AlgebraicClosure F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (hratio : sigma (b : L) / (b : L) = beta ^ p)
    (hb : ∀ c : L, c ^ p ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = p)
    (hbeta : Algebra.norm F beta = zeta) :
    Function.Surjective
      (albertCharacter p b sigma beta iL zeta hzeta
        hratio hb hsigma hfinrank hbeta) := by
  letI : Fact (Irreducible (albertPolynomial p b)) :=
    ⟨albertPolynomial_irreducible p b hb⟩
  letI : FiniteDimensional L (albertOverfield p b) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis (albertPolynomial_irreducible p b hb).ne_zero).basis
  letI : FiniteDimensional F (albertOverfield p b) :=
    FiniteDimensional.trans F L (albertOverfield p b)
  letI : FiniteDimensional F (albertClosureField p b iL hb) :=
    (albertOverfieldEquivClosure p b iL hb).toLinearEquiv.finiteDimensional
  letI : IsGalois F (albertClosureField p b iL hb) :=
    albertClosureField_isGalois p b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta
  exact ContinuousCyclicQuotient.cyclicQuotient_surjective F (p ^ 2)
    (albertClosureField p b iL hb)
    (albertClosureGalEquiv p b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta)

end Fermat.Conservation.PrimeAlbertCyclicQuotient
