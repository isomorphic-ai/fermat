/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The continuous cyclic Albert quotient at 59

This module transports the finite cyclic Albert overfield into a chosen
algebraic closure.  Crucially, the chosen embedding extends a supplied
embedding of the original degree-59 field.  The image is Galois, its
automorphism group is continuously identified with
`Multiplicative (ZMod 3481)` using the transported Albert generator, and
absolute-Galois restriction gives a continuous surjective cyclic quotient.

This module proves the existence and orientation of the order-3481 quotient.
It does not yet prove the final compatibility square saying that reduction
modulo 59 of this quotient equals the original supplied order-59 Kummer
character.  That theorem additionally requires restriction of the
transported generator to the embedded degree-59 subfield; it is the next
explicit boundary and is not hidden here.
-/
import Fermat.Experiments.Conservation.AlbertGalois59
import Fermat.Experiments.Conservation.ContinuousCyclicQuotient
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Instances.ZMod
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.AlbertCyclicQuotient59

open AlbertExtension59 AlbertOrder59 AlbertGalois59

abbrev CyclicGroup3481 := Multiplicative (ZMod 3481)

local instance : TopologicalSpace CyclicGroup3481 := ⊥
local instance : DiscreteTopology CyclicGroup3481 := ⟨rfl⟩

variable {F L : Type} [Field F] [Field L] [Algebra F L]
variable [FiniteDimensional F L] [IsGalois F L]

local instance : NeZero 59 := ⟨by decide⟩

variable (b : Lˣ)

/-- An embedding of the Albert overfield into the chosen algebraic closure
which extends the supplied embedding of its degree-59 subfield. -/
def albertClosureEmbedding59
    (iL : L →ₐ[F] AlgebraicClosure F)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L)) :
    albertOverfield59 b →ₐ[F] AlgebraicClosure F := by
  letI : Fact (Irreducible (albertPolynomial59 b)) :=
    ⟨albertPolynomial59_irreducible b hb⟩
  letI : FiniteDimensional L (albertOverfield59 b) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis (albertPolynomial59_irreducible b hb).ne_zero).basis
  exact Classical.choose
    (IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
      (K := F) (L := L) (M := AlgebraicClosure F)
      (E := albertOverfield59 b) iL)

omit [FiniteDimensional F L] [IsGalois F L] in
theorem albertClosureEmbedding59_restrictDomain
    (iL : L →ₐ[F] AlgebraicClosure F)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L)) :
    (albertClosureEmbedding59 b iL hb).restrictDomain L = iL := by
  letI : Fact (Irreducible (albertPolynomial59 b)) :=
    ⟨albertPolynomial59_irreducible b hb⟩
  letI : FiniteDimensional L (albertOverfield59 b) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis (albertPolynomial59_irreducible b hb).ne_zero).basis
  exact Classical.choose_spec
    (IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
      (K := F) (L := L) (M := AlgebraicClosure F)
      (E := albertOverfield59 b) iL)

/-- The image of the Albert overfield in the chosen algebraic closure. -/
def albertClosureField59
    (iL : L →ₐ[F] AlgebraicClosure F)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L)) :
    IntermediateField F (AlgebraicClosure F) := by
  letI : Fact (Irreducible (albertPolynomial59 b)) :=
    ⟨albertPolynomial59_irreducible b hb⟩
  exact (albertClosureEmbedding59 b iL hb).fieldRange

/-- The abstract Albert overfield is `F`-isomorphic to its chosen image. -/
def albertOverfieldEquivClosure59
    (iL : L →ₐ[F] AlgebraicClosure F)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L)) :
    albertOverfield59 b ≃ₐ[F] albertClosureField59 b iL hb := by
  letI : Fact (Irreducible (albertPolynomial59 b)) :=
    ⟨albertPolynomial59_irreducible b hb⟩
  exact AlgEquiv.ofInjectiveField (albertClosureEmbedding59 b iL hb)

variable (sigma : L ≃ₐ[F] L) (beta : L)

/-- The finite Albert overfield remains Galois after embedding it into the
chosen algebraic closure. -/
theorem albertClosureField59_isGalois
    (iL : L →ₐ[F] AlgebraicClosure F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = 59)
    (hbeta : Algebra.norm F beta = zeta) :
    IsGalois F (albertClosureField59 b iL hb) := by
  letI : Fact (Irreducible (albertPolynomial59 b)) :=
    ⟨albertPolynomial59_irreducible b hb⟩
  letI : IsGalois F (albertOverfield59 b) :=
    albertOverfield59_isGalois b sigma beta zeta hzeta
      hratio hb hsigma hfinrank hbeta
  exact IsGalois.of_algEquiv (albertOverfieldEquivClosure59 b iL hb)

/-- The Albert generator transported to the chosen intermediate field. -/
def albertClosureGenerator59
    (iL : L →ₐ[F] AlgebraicClosure F)
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L)) :
    albertClosureField59 b iL hb ≃ₐ[F]
      albertClosureField59 b iL hb :=
  AlgEquiv.autCongr (albertOverfieldEquivClosure59 b iL hb)
    (albertLiftAlgEquiv59 sigma beta b hratio hb)

theorem albertClosureGenerator59_zpowers_eq_top
    (iL : L →ₐ[F] AlgebraicClosure F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = 59)
    (hbeta : Algebra.norm F beta = zeta) :
    Subgroup.zpowers
      (albertClosureGenerator59 b sigma beta iL hratio hb) = ⊤ := by
  let e := albertOverfieldEquivClosure59 b iL hb
  let tau := albertLiftAlgEquiv59 sigma beta b hratio hb
  have htop : Subgroup.zpowers tau = ⊤ :=
    albertLiftAlgEquiv59_zpowers_eq_top b sigma beta zeta hzeta
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

theorem albertClosureField59_card_aut
    (iL : L →ₐ[F] AlgebraicClosure F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = 59)
    (hbeta : Algebra.norm F beta = zeta) :
    Nat.card
      (albertClosureField59 b iL hb ≃ₐ[F]
        albertClosureField59 b iL hb) = 3481 := by
  letI : Fact (Irreducible (albertPolynomial59 b)) :=
    ⟨albertPolynomial59_irreducible b hb⟩
  calc
    Nat.card
        (albertClosureField59 b iL hb ≃ₐ[F]
          albertClosureField59 b iL hb) =
        Nat.card (albertOverfield59 b ≃ₐ[F] albertOverfield59 b) :=
      (Nat.card_congr
        (AlgEquiv.autCongr
          (albertOverfieldEquivClosure59 b iL hb)).toEquiv).symm
    _ = 3481 := albertOverfield59_card_aut b sigma beta zeta hzeta
      hratio hb hsigma hfinrank hbeta

/-- The Galois group of the chosen closure image, continuously and
generator-preservingly identified with the cyclic group of order 3481. -/
def albertClosureGalEquiv3481
    (iL : L →ₐ[F] AlgebraicClosure F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = 59)
    (hbeta : Algebra.norm F beta = zeta) :
    ((albertClosureField59 b iL hb ≃ₐ[F]
        albertClosureField59 b iL hb) ≃ₜ*
      CyclicGroup3481) := by
  letI : Fact (Irreducible (albertPolynomial59 b)) :=
    ⟨albertPolynomial59_irreducible b hb⟩
  letI : FiniteDimensional L (albertOverfield59 b) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis (albertPolynomial59_irreducible b hb).ne_zero).basis
  letI : FiniteDimensional F (albertOverfield59 b) :=
    FiniteDimensional.trans F L (albertOverfield59 b)
  letI : FiniteDimensional F (albertClosureField59 b iL hb) :=
    (albertOverfieldEquivClosure59 b iL hb).toLinearEquiv.finiteDimensional
  letI : IsGalois F (albertClosureField59 b iL hb) :=
    albertClosureField59_isGalois b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta
  let tau := albertClosureGenerator59 b sigma beta iL hratio hb
  have htau : ∀ rho, rho ∈ Subgroup.zpowers tau := by
    intro rho
    rw [albertClosureGenerator59_zpowers_eq_top b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta]
    exact Subgroup.mem_top rho
  have hcard : Nat.card
      (albertClosureField59 b iL hb ≃ₐ[F]
        albertClosureField59 b iL hb) = 3481 :=
    albertClosureField59_card_aut b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta
  let e :
      (albertClosureField59 b iL hb ≃ₐ[F]
        albertClosureField59 b iL hb) ≃*
          CyclicGroup3481 :=
    (zmodMulEquivOfGenerator htau hcard).symm
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The continuous cyclic order-3481 quotient supplied by the constructive
Albert overfield. -/
def albertCharacter3481
    (iL : L →ₐ[F] AlgebraicClosure F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = 59)
    (hbeta : Algebra.norm F beta = zeta) :
    Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481 := by
  letI : Fact (Irreducible (albertPolynomial59 b)) :=
    ⟨albertPolynomial59_irreducible b hb⟩
  letI : FiniteDimensional L (albertOverfield59 b) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis (albertPolynomial59_irreducible b hb).ne_zero).basis
  letI : FiniteDimensional F (albertOverfield59 b) :=
    FiniteDimensional.trans F L (albertOverfield59 b)
  letI : FiniteDimensional F (albertClosureField59 b iL hb) :=
    (albertOverfieldEquivClosure59 b iL hb).toLinearEquiv.finiteDimensional
  letI : IsGalois F (albertClosureField59 b iL hb) :=
    albertClosureField59_isGalois b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta
  exact ContinuousCyclicQuotient.cyclicQuotient F 3481
    (albertClosureField59 b iL hb)
    (albertClosureGalEquiv3481 b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta)

theorem albertCharacter3481_surjective
    (iL : L →ₐ[F] AlgebraicClosure F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = 59)
    (hbeta : Algebra.norm F beta = zeta) :
    Function.Surjective
      (albertCharacter3481 b sigma beta iL zeta hzeta
        hratio hb hsigma hfinrank hbeta) := by
  letI : Fact (Irreducible (albertPolynomial59 b)) :=
    ⟨albertPolynomial59_irreducible b hb⟩
  letI : FiniteDimensional L (albertOverfield59 b) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis (albertPolynomial59_irreducible b hb).ne_zero).basis
  letI : FiniteDimensional F (albertOverfield59 b) :=
    FiniteDimensional.trans F L (albertOverfield59 b)
  letI : FiniteDimensional F (albertClosureField59 b iL hb) :=
    (albertOverfieldEquivClosure59 b iL hb).toLinearEquiv.finiteDimensional
  letI : IsGalois F (albertClosureField59 b iL hb) :=
    albertClosureField59_isGalois b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta
  exact ContinuousCyclicQuotient.cyclicQuotient_surjective F 3481
    (albertClosureField59 b iL hb)
    (albertClosureGalEquiv3481 b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta)

end Fermat.Conservation.AlbertCyclicQuotient59
