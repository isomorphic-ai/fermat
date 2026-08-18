import Fermat.Conservation.AlbertCyclicQuotient59
import Fermat.Conservation.KummerCyclicQuotient59
import Mathlib.Tactic

/-!
# Exact compatibility of the Albert and Kummer cyclic characters at 59

This file proves the constructive Albert direction for the concrete Kummer
extension.  The transported Albert generator genuinely restricts to the
Kummer generator, so reduction of the resulting order-3481 character modulo
59 is exactly the existing order-59 Kummer character.  Consequently a witness
`Algebra.norm F beta = zeta` produces the required continuous lift.

The converse implication is deliberately not asserted here.
-/

open Polynomial

noncomputable section

namespace Fermat.Conservation.AlbertCyclicCompatibility59

open AlbertExtension59 AlbertGalois59 AlbertCyclicQuotient59

abbrev CyclicGroup59 := Multiplicative (ZMod 59)

local instance : TopologicalSpace CyclicGroup59 := ⊥
local instance : DiscreteTopology CyclicGroup59 := ⟨rfl⟩
local instance : TopologicalSpace CyclicGroup3481 := ⊥
local instance : DiscreteTopology CyclicGroup3481 := ⟨rfl⟩

variable {F L : Type} [Field F] [Field L] [Algebra F L]
variable [FiniteDimensional F L] [IsGalois F L]

local instance : NeZero 59 := ⟨by decide⟩

variable (b : Lˣ) (sigma : L ≃ₐ[F] L) (beta : L)

/-- The abstract Albert lift restricts to the original degree-59
automorphism. -/
theorem albertLiftAlgEquiv59_restrictNormal
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L)) :
    letI : Fact (Irreducible (albertPolynomial59 b)) :=
      ⟨albertPolynomial59_irreducible b hb⟩
    AlgEquiv.restrictNormalHom L
      (albertLiftAlgEquiv59 sigma beta b hratio hb) = sigma := by
  letI : Fact (Irreducible (albertPolynomial59 b)) :=
    ⟨albertPolynomial59_irreducible b hb⟩
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L (albertOverfield59 b)).injective
  have hcomm := AlgEquiv.restrictNormal_commutes
    (albertLiftAlgEquiv59 sigma beta b hratio hb) L x
  rw [albertLiftAlgEquiv59_algebraMap] at hcomm
  exact hcomm

/-- Reduction of the cyclic exponent modulo 59. -/
def cyclicReduction3481To59 : CyclicGroup3481 →ₜ* CyclicGroup59 where
  toMonoidHom := AddMonoidHom.toMultiplicative
    (ZMod.castHom (by norm_num : 59 ∣ 3481) (ZMod 59)).toAddMonoidHom
  continuous_toFun := continuous_of_discreteTopology

/-- The generator-oriented cyclic coordinate on `Gal(L/F)`. -/
def generatorGalEquiv59
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = 59) :
    (L ≃ₐ[F] L) ≃ₜ* CyclicGroup59 := by
  have hcard : Nat.card (L ≃ₐ[F] L) = 59 := by
    rw [IsGalois.card_aut_eq_finrank, hfinrank]
  let e : (L ≃ₐ[F] L) ≃* CyclicGroup59 :=
    (zmodMulEquivOfGenerator hsigma hcard).symm
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

theorem generatorGalEquiv59_apply_generator
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = 59) :
    generatorGalEquiv59 sigma hsigma hfinrank sigma =
      Multiplicative.ofAdd (1 : ZMod 59) := by
  simp only [generatorGalEquiv59]
  exact zmodMulEquivOfGenerator_symm_apply_generator hsigma
    (by rw [IsGalois.card_aut_eq_finrank, hfinrank])

@[simp]
theorem cyclicReduction3481To59_ofAdd_one :
    cyclicReduction3481To59 (Multiplicative.ofAdd (1 : ZMod 3481)) =
      Multiplicative.ofAdd (1 : ZMod 59) := by
  rfl

/-- An element of `C3481` reducing to the standard generator of `C59` has
unit additive coordinate modulo `59²`, and hence generates `C3481`. -/
theorem cyclicReduction3481To59_preimage_generator_isUnit
    (x : CyclicGroup3481)
    (hx : cyclicReduction3481To59 x =
      Multiplicative.ofAdd (1 : ZMod 59)) :
    IsUnit x.toAdd := by
  rw [← ZMod.natCast_zmod_val x.toAdd]
  rw [ZMod.isUnit_iff_coprime]
  have hnot : ¬59 ∣ x.toAdd.val := by
    intro hdvd
    have hxzero : (x.toAdd.val : ZMod 59) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact hdvd
    have hxone : (x.toAdd.val : ZMod 59) = 1 := by
      have h := congrArg Multiplicative.toAdd hx
      change ZMod.castHom (by norm_num : 59 ∣ 3481) (ZMod 59)
          x.toAdd = 1 at h
      rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
      exact h
    rw [hxzero] at hxone
    have hne : (0 : ZMod 59) ≠ (1 : ZMod 59) := by decide
    exact hne hxone
  have hcop := Nat.Prime.coprime_pow_of_not_dvd
    (by decide : Nat.Prime 59) hnot (m := 2)
  norm_num at hcop ⊢
  exact hcop

/-- Surjectivity after reduction from `C3481` to `C59` already forces
surjectivity before reduction.  Indeed, a preimage of the standard
generator has unit coordinate modulo `59²`, so its powers cover all of
`C3481`. -/
theorem surjective_of_cyclicReduction3481To59_comp_surjective
    {G : Type} [Group G]
    (psi : G →* CyclicGroup3481)
    (hsurj : Function.Surjective
      (cyclicReduction3481To59.toMonoidHom.comp psi)) :
    Function.Surjective psi := by
  obtain ⟨g, hg⟩ := hsurj (Multiplicative.ofAdd (1 : ZMod 59))
  let x := psi g
  have hxred : cyclicReduction3481To59 x =
      Multiplicative.ofAdd (1 : ZMod 59) := hg
  have hxunit : IsUnit x.toAdd :=
    cyclicReduction3481To59_preimage_generator_isUnit x hxred
  intro y
  let u : (ZMod 3481)ˣ := hxunit.unit
  let n : ℕ := (((u⁻¹ : (ZMod 3481)ˣ) : ZMod 3481) * y.toAdd).val
  refine ⟨g ^ n, ?_⟩
  rw [map_pow]
  apply Multiplicative.toAdd.injective
  change n • x.toAdd = y.toAdd
  have hu : (u : ZMod 3481) = x.toAdd := hxunit.unit_spec
  rw [← hu, nsmul_eq_mul]
  change (n : ZMod 3481) * (u : ZMod 3481) = y.toAdd
  rw [show (n : ZMod 3481) =
      ((u⁻¹ : (ZMod 3481)ˣ) : ZMod 3481) * y.toAdd by
    exact ZMod.natCast_zmod_val _]
  calc
    (((u⁻¹ : (ZMod 3481)ˣ) : ZMod 3481) * y.toAdd) *
        (u : ZMod 3481) =
      (((u⁻¹ : (ZMod 3481)ˣ) : ZMod 3481) * (u : ZMod 3481)) *
        y.toAdd := by ac_rfl
    _ = y.toAdd := by simp

/-- Continuous specialization of
`surjective_of_cyclicReduction3481To59_comp_surjective`. -/
theorem continuous_surjective_of_cyclicReduction3481To59_comp_surjective
    {G : Type} [Group G] [TopologicalSpace G]
    (psi : G →ₜ* CyclicGroup3481)
    (hsurj : Function.Surjective (cyclicReduction3481To59.comp psi)) :
    Function.Surjective psi :=
  surjective_of_cyclicReduction3481To59_comp_surjective psi.toMonoidHom hsurj

/-- Restriction from the transported closure Galois group back to the
original degree-59 field, via the chosen embedding equivalence. -/
def albertClosureRestriction59
    (iL : L →ₐ[F] AlgebraicClosure F)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L)) :
    (albertClosureField59 b iL hb ≃ₐ[F]
      albertClosureField59 b iL hb) →*
        (L ≃ₐ[F] L) := by
  letI : Fact (Irreducible (albertPolynomial59 b)) :=
    ⟨albertPolynomial59_irreducible b hb⟩
  exact (AlgEquiv.restrictNormalHom L).comp
    (AlgEquiv.autCongr
      (albertOverfieldEquivClosure59 b iL hb)).symm.toMonoidHom

theorem albertClosureRestriction59_generator
    (iL : L →ₐ[F] AlgebraicClosure F)
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L)) :
    albertClosureRestriction59 b iL hb
      (albertClosureGenerator59 b sigma beta iL hratio hb) = sigma := by
  letI : Fact (Irreducible (albertPolynomial59 b)) :=
    ⟨albertPolynomial59_irreducible b hb⟩
  change AlgEquiv.restrictNormalHom L
    ((AlgEquiv.autCongr (albertOverfieldEquivClosure59 b iL hb)).symm
      (AlgEquiv.autCongr (albertOverfieldEquivClosure59 b iL hb)
        (albertLiftAlgEquiv59 sigma beta b hratio hb))) = sigma
  rw [MulEquiv.symm_apply_apply]
  exact albertLiftAlgEquiv59_restrictNormal b sigma beta hratio hb

theorem albertClosureGalEquiv3481_apply_generator
    (iL : L →ₐ[F] AlgebraicClosure F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = 59)
    (hbeta : Algebra.norm F beta = zeta) :
    albertClosureGalEquiv3481 b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta
      (albertClosureGenerator59 b sigma beta iL hratio hb) =
        Multiplicative.ofAdd (1 : ZMod 3481) := by
  simp only [albertClosureGalEquiv3481]
  exact zmodMulEquivOfGenerator_symm_apply_generator
    (fun rho ↦ by
      rw [albertClosureGenerator59_zpowers_eq_top b sigma beta iL zeta hzeta
        hratio hb hsigma hfinrank hbeta]
      exact Subgroup.mem_top rho)
    (albertClosureField59_card_aut b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta)

/-- The finite cyclic-coordinate square commutes: reducing the transported
Albert coordinate modulo 59 is the same as restricting to `L` and then
reading the original generator-oriented coordinate. -/
theorem albertFiniteCyclicCompatibility59
    (iL : L →ₐ[F] AlgebraicClosure F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (hratio : sigma (b : L) / (b : L) = beta ^ 59)
    (hb : ∀ c : L, c ^ 59 ≠ (b : L))
    (hsigma : ∀ rho : L ≃ₐ[F] L, rho ∈ Subgroup.zpowers sigma)
    (hfinrank : Module.finrank F L = 59)
    (hbeta : Algebra.norm F beta = zeta) :
    cyclicReduction3481To59.toMonoidHom.comp
        (albertClosureGalEquiv3481 b sigma beta iL zeta hzeta
          hratio hb hsigma hfinrank hbeta).toMulEquiv.toMonoidHom =
      (generatorGalEquiv59 sigma hsigma hfinrank).toMulEquiv.toMonoidHom.comp
        (albertClosureRestriction59 b iL hb) := by
  let tau := albertClosureGenerator59 b sigma beta iL hratio hb
  have htau : ∀ rho, rho ∈ Subgroup.zpowers tau := by
    intro rho
    rw [albertClosureGenerator59_zpowers_eq_top b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta]
    exact Subgroup.mem_top rho
  apply (MonoidHom.eq_iff_eq_on_generator htau _ _).mpr
  simp only [MonoidHom.comp_apply]
  dsimp [tau]
  change cyclicReduction3481To59
      (albertClosureGalEquiv3481 b sigma beta iL zeta hzeta
        hratio hb hsigma hfinrank hbeta
        (albertClosureGenerator59 b sigma beta iL hratio hb)) =
    generatorGalEquiv59 sigma hsigma hfinrank
      (albertClosureRestriction59 b iL hb
        (albertClosureGenerator59 b sigma beta iL hratio hb))
  rw [albertClosureGalEquiv3481_apply_generator b sigma beta iL zeta hzeta
      hratio hb hsigma hfinrank hbeta,
    cyclicReduction3481To59_ofAdd_one,
    albertClosureRestriction59_generator b sigma beta iL hratio hb,
    generatorGalEquiv59_apply_generator sigma hsigma hfinrank]

section ConcreteIntermediateField

variable (K : IntermediateField F (AlgebraicClosure F))
variable [FiniteDimensional F K] [IsGalois F K]

omit [FiniteDimensional F L] [IsGalois F L]
    [FiniteDimensional F K] [IsGalois F K] in
set_option maxHeartbeats 800000 in
theorem albertBase_le_closure59
    (bK : Kˣ)
    (hb : ∀ c : K, c ^ 59 ≠ (bK : K)) :
    K ≤ albertClosureField59 bK K.val hb := by
  letI : Fact (Irreducible (albertPolynomial59 bK)) :=
    ⟨albertPolynomial59_irreducible bK hb⟩
  intro x hx
  change x ∈ (albertClosureEmbedding59 bK K.val hb).fieldRange
  rw [AlgHom.mem_fieldRange]
  refine ⟨algebraMap K (albertOverfield59 bK) ⟨x, hx⟩, ?_⟩
  have hres := albertClosureEmbedding59_restrictDomain bK K.val hb
  exact DFunLike.congr_fun hres ⟨x, hx⟩

/-- The original intermediate field, regarded as an intermediate field of
the Albert closure image. -/
def albertBaseInsideClosure59
    (bK : Kˣ)
    (hb : ∀ c : K, c ^ 59 ≠ (bK : K)) :
    IntermediateField F (albertClosureField59 bK K.val hb) :=
  IntermediateField.restrict (albertBase_le_closure59 K bK hb)

/-- The tautological equivalence from the original intermediate field to
its copy inside the Albert closure image. -/
def albertBaseEquivInsideClosure59
    (bK : Kˣ)
    (hb : ∀ c : K, c ^ 59 ≠ (bK : K)) :
    K ≃ₐ[F] albertBaseInsideClosure59 K bK hb :=
  IntermediateField.restrict_algEquiv (albertBase_le_closure59 K bK hb)

omit [FiniteDimensional F L] [IsGalois F L]
    [FiniteDimensional F K] [IsGalois F K] in
set_option maxHeartbeats 800000 in
theorem albertOverfieldEquivClosure59_commutes_base
    (bK : Kˣ)
    (hb : ∀ c : K, c ^ 59 ≠ (bK : K))
    (x : K) :
    albertOverfieldEquivClosure59 bK K.val hb
        (algebraMap K (albertOverfield59 bK) x) =
      algebraMap (albertBaseInsideClosure59 K bK hb)
        (albertClosureField59 bK K.val hb)
        (albertBaseEquivInsideClosure59 K bK hb x) := by
  apply Subtype.ext
  change albertClosureEmbedding59 bK K.val hb
      (algebraMap K (albertOverfield59 bK) x) = x
  have hres := albertClosureEmbedding59_restrictDomain bK K.val hb
  exact DFunLike.congr_fun hres x

/-- Genuine tower restriction from the Albert closure image to the original
intermediate field. -/
def albertConcreteRestriction59
    (bK : Kˣ)
    (hb : ∀ c : K, c ^ 59 ≠ (bK : K)) :
    (albertClosureField59 bK K.val hb ≃ₐ[F]
      albertClosureField59 bK K.val hb) →* (K ≃ₐ[F] K) := by
  let B := albertBaseInsideClosure59 K bK hb
  let eB := albertBaseEquivInsideClosure59 K bK hb
  letI : IsGalois F B := IsGalois.of_algEquiv eB
  exact (AlgEquiv.autCongr eB).symm.toMonoidHom.comp
    (AlgEquiv.restrictNormalHom B)

set_option maxHeartbeats 800000 in
theorem albertConcreteRestriction59_generator
    (bK : Kˣ) (sigmaK : K ≃ₐ[F] K) (betaK : K)
    (hratio : sigmaK (bK : K) / (bK : K) = betaK ^ 59)
    (hb : ∀ c : K, c ^ 59 ≠ (bK : K)) :
    albertConcreteRestriction59 K bK hb
      (albertClosureGenerator59 bK sigmaK betaK K.val hratio hb) = sigmaK := by
  let B := albertBaseInsideClosure59 K bK hb
  let eB := albertBaseEquivInsideClosure59 K bK hb
  let eM := albertOverfieldEquivClosure59 bK K.val hb
  let tau := albertLiftAlgEquiv59 sigmaK betaK bK hratio hb
  let tauN := albertClosureGenerator59 bK sigmaK betaK K.val hratio hb
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
  apply (algebraMap B (albertClosureField59 bK K.val hb)).injective
  change (↑((AlgEquiv.restrictNormalHom B tauN) (eB x)) :
      albertClosureField59 bK K.val hb) = _
  rw [AlgEquiv.restrictNormalHom_apply]
  change tauN
      (algebraMap B (albertClosureField59 bK K.val hb) (eB x)) =
    algebraMap B (albertClosureField59 bK K.val hb)
      ((AlgEquiv.autCongr eB sigmaK) (eB x))
  rw [← albertOverfieldEquivClosure59_commutes_base K bK hb x]
  change (AlgEquiv.autCongr eM tau)
      (eM (algebraMap K (albertOverfield59 bK) x)) = _
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply]
  dsimp [tau]
  change eM (albertLiftAlgEquiv59 sigmaK betaK bK hratio hb
      (algebraMap K (albertOverfield59 bK) x)) = _
  rw [albertLiftAlgEquiv59_algebraMap]
  rw [albertOverfieldEquivClosure59_commutes_base K bK hb (sigmaK x)]
  rfl

theorem albertConcreteFiniteCyclicCompatibility59
    (bK : Kˣ) (sigmaK : K ≃ₐ[F] K) (betaK : K)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (hratio : sigmaK (bK : K) / (bK : K) = betaK ^ 59)
    (hb : ∀ c : K, c ^ 59 ≠ (bK : K))
    (hsigma : ∀ rho : K ≃ₐ[F] K, rho ∈ Subgroup.zpowers sigmaK)
    (hfinrank : Module.finrank F K = 59)
    (hbeta : Algebra.norm F betaK = zeta) :
    cyclicReduction3481To59.toMonoidHom.comp
        (albertClosureGalEquiv3481 bK sigmaK betaK K.val zeta hzeta
          hratio hb hsigma hfinrank hbeta).toMulEquiv.toMonoidHom =
      (generatorGalEquiv59 sigmaK hsigma hfinrank).toMulEquiv.toMonoidHom.comp
        (albertConcreteRestriction59 K bK hb) := by
  let tau := albertClosureGenerator59 bK sigmaK betaK K.val hratio hb
  have htau : ∀ rho, rho ∈ Subgroup.zpowers tau := by
    intro rho
    rw [albertClosureGenerator59_zpowers_eq_top bK sigmaK betaK K.val zeta hzeta
      hratio hb hsigma hfinrank hbeta]
    exact Subgroup.mem_top rho
  apply (MonoidHom.eq_iff_eq_on_generator htau _ _).mpr
  simp only [MonoidHom.comp_apply]
  dsimp [tau]
  change cyclicReduction3481To59
      (albertClosureGalEquiv3481 bK sigmaK betaK K.val zeta hzeta
        hratio hb hsigma hfinrank hbeta
        (albertClosureGenerator59 bK sigmaK betaK K.val hratio hb)) =
    generatorGalEquiv59 sigmaK hsigma hfinrank
      (albertConcreteRestriction59 K bK hb
        (albertClosureGenerator59 bK sigmaK betaK K.val hratio hb))
  rw [albertClosureGalEquiv3481_apply_generator bK sigmaK betaK K.val zeta hzeta
      hratio hb hsigma hfinrank hbeta,
    cyclicReduction3481To59_ofAdd_one,
    albertConcreteRestriction59_generator K bK sigmaK betaK hratio hb,
    generatorGalEquiv59_apply_generator sigmaK hsigma hfinrank]

set_option maxHeartbeats 1000000 in
theorem albertConcreteRestriction59_absoluteGalois
    (bK : Kˣ) (sigmaK : K ≃ₐ[F] K) (betaK : K)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (hratio : sigmaK (bK : K) / (bK : K) = betaK ^ 59)
    (hb : ∀ c : K, c ^ 59 ≠ (bK : K))
    (hsigma : ∀ rho : K ≃ₐ[F] K, rho ∈ Subgroup.zpowers sigmaK)
    (hfinrank : Module.finrank F K = 59)
    (hbeta : Algebra.norm F betaK = zeta)
    (g : Field.absoluteGaloisGroup F) :
    letI : IsGalois F (albertClosureField59 bK K.val hb) :=
      albertClosureField59_isGalois bK sigmaK betaK K.val zeta hzeta
        hratio hb hsigma hfinrank hbeta
    albertConcreteRestriction59 K bK hb
        (ContinuousCyclicQuotient.absoluteGaloisRestriction F
          (albertClosureField59 bK K.val hb) g) =
      ContinuousCyclicQuotient.absoluteGaloisRestriction F K g := by
  let N := albertClosureField59 bK K.val hb
  let B := albertBaseInsideClosure59 K bK hb
  let eB := albertBaseEquivInsideClosure59 K bK hb
  letI : IsGalois F N :=
    albertClosureField59_isGalois bK sigmaK betaK K.val zeta hzeta
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

/-- The original order-59 absolute-Galois quotient in the cyclic coordinate
which sends `sigmaK` to one. -/
def generatorCharacter59
    (sigmaK : K ≃ₐ[F] K)
    (hsigma : ∀ rho : K ≃ₐ[F] K, rho ∈ Subgroup.zpowers sigmaK)
    (hfinrank : Module.finrank F K = 59) :
    Field.absoluteGaloisGroup F →ₜ* CyclicGroup59 :=
  ContinuousCyclicQuotient.cyclicQuotient F 59 K
    (generatorGalEquiv59 sigmaK hsigma hfinrank)

set_option maxHeartbeats 1000000 in
/-- Exact Albert compatibility on the absolute Galois group: reduction
modulo 59 of the constructed order-3481 character is the original
generator-oriented order-59 quotient. -/
theorem albertCharacter3481_reduction_eq_generatorCharacter59
    (bK : Kˣ) (sigmaK : K ≃ₐ[F] K) (betaK : K)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (hratio : sigmaK (bK : K) / (bK : K) = betaK ^ 59)
    (hb : ∀ c : K, c ^ 59 ≠ (bK : K))
    (hsigma : ∀ rho : K ≃ₐ[F] K, rho ∈ Subgroup.zpowers sigmaK)
    (hfinrank : Module.finrank F K = 59)
    (hbeta : Algebra.norm F betaK = zeta) :
    cyclicReduction3481To59.comp
        (albertCharacter3481 bK sigmaK betaK K.val zeta hzeta
          hratio hb hsigma hfinrank hbeta) =
      generatorCharacter59 K sigmaK hsigma hfinrank := by
  letI : IsGalois F (albertClosureField59 bK K.val hb) :=
    albertClosureField59_isGalois bK sigmaK betaK K.val zeta hzeta
      hratio hb hsigma hfinrank hbeta
  apply ContinuousMonoidHom.ext
  intro g
  change cyclicReduction3481To59
      (albertClosureGalEquiv3481 bK sigmaK betaK K.val zeta hzeta
        hratio hb hsigma hfinrank hbeta
        (ContinuousCyclicQuotient.absoluteGaloisRestriction F
          (albertClosureField59 bK K.val hb) g)) =
    generatorGalEquiv59 sigmaK hsigma hfinrank
      (ContinuousCyclicQuotient.absoluteGaloisRestriction F K g)
  have hfinite := DFunLike.congr_fun
    (albertConcreteFiniteCyclicCompatibility59 K bK sigmaK betaK zeta hzeta
      hratio hb hsigma hfinrank hbeta)
    (ContinuousCyclicQuotient.absoluteGaloisRestriction F
      (albertClosureField59 bK K.val hb) g)
  simp only [MonoidHom.comp_apply] at hfinite
  rw [albertConcreteRestriction59_absoluteGalois K bK sigmaK betaK zeta hzeta
    hratio hb hsigma hfinrank hbeta g] at hfinite
  exact hfinite

end ConcreteIntermediateField

section ConcreteKummer

open AlbertDescentDatum59 KummerCyclicQuotient59

variable (F : Type) [Field F]
variable (zeta a : F)
variable (hzeta : IsPrimitiveRoot zeta 59)
variable (ha : ∀ x : F, x ^ 59 ≠ a)

private theorem concreteKummerGenerator59_ne_one :
    concreteKummerGenerator59 F zeta a hzeta ha ≠ 1 := by
  letI : Fact (1 < 59) := ⟨by decide⟩
  intro h
  have himage := congrArg
    (fun rho ↦ kummerGalEquiv59 F zeta a hzeta ha rho) h
  simp [concreteKummerGenerator59] at himage

theorem generatorGalEquiv59_eq_kummerGalEquiv59
    (hsigma : ∀ rho : kummerExtension59 F a ≃ₐ[F] kummerExtension59 F a,
      rho ∈ Subgroup.zpowers
        (concreteKummerGenerator59 F zeta a hzeta ha))
    (hfinrank : Module.finrank F (kummerExtension59 F a) = 59) :
    letI : IsSplittingField F (kummerExtension59 F a)
        (kummerPolynomial59 F a) :=
      kummerExtension59_isSplittingField F a
    letI : FiniteDimensional F (kummerExtension59 F a) :=
      Polynomial.IsSplittingField.finiteDimensional
        (kummerExtension59 F a) (kummerPolynomial59 F a)
    letI : IsGalois F (kummerExtension59 F a) :=
      isGalois_of_isSplittingField_X_pow_sub_C
        ⟨zeta, (mem_primitiveRoots (by decide : 0 < 59)).2 hzeta⟩
        (kummerPolynomial59_irreducible F a ha)
        (kummerExtension59 F a)
    generatorGalEquiv59
        (concreteKummerGenerator59 F zeta a hzeta ha) hsigma hfinrank =
      kummerGalEquiv59 F zeta a hzeta ha := by
  letI : IsSplittingField F (kummerExtension59 F a)
      (kummerPolynomial59 F a) :=
    kummerExtension59_isSplittingField F a
  letI : FiniteDimensional F (kummerExtension59 F a) :=
    Polynomial.IsSplittingField.finiteDimensional
      (kummerExtension59 F a) (kummerPolynomial59 F a)
  letI : IsGalois F (kummerExtension59 F a) :=
    isGalois_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (by decide : 0 < 59)).2 hzeta⟩
      (kummerPolynomial59_irreducible F a ha)
      (kummerExtension59 F a)
  apply ContinuousMulEquiv.ext
  have heq :
      (generatorGalEquiv59
        (concreteKummerGenerator59 F zeta a hzeta ha)
        hsigma hfinrank).toMulEquiv =
      (kummerGalEquiv59 F zeta a hzeta ha).toMulEquiv := by
    apply (MulEquiv.eq_iff_eq_on_generator hsigma _ _).mpr
    change generatorGalEquiv59
        (concreteKummerGenerator59 F zeta a hzeta ha) hsigma hfinrank
          (concreteKummerGenerator59 F zeta a hzeta ha) =
      kummerGalEquiv59 F zeta a hzeta ha
        (concreteKummerGenerator59 F zeta a hzeta ha)
    rw [generatorGalEquiv59_apply_generator]
    simp [concreteKummerGenerator59]
  intro rho
  exact DFunLike.congr_fun heq rho

set_option maxHeartbeats 1200000 in
/-- Constructive Albert direction for the concrete Kummer character: a norm
witness produces a continuous order-3481 character whose reduction modulo
59 is exactly the existing order-59 Kummer character. -/
theorem concreteKummer_exists_albertCharacter3481
    (beta : kummerExtension59 F a)
    (hbeta : Algebra.norm F beta = zeta) :
    ∃ psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481,
      cyclicReduction3481To59.comp psi =
        kummerCharacter59 F zeta a hzeta ha := by
  letI : Fact (Nat.Prime 59) := ⟨by decide⟩
  letI : IsSplittingField F (kummerExtension59 F a)
      (kummerPolynomial59 F a) :=
    kummerExtension59_isSplittingField F a
  letI : FiniteDimensional F (kummerExtension59 F a) :=
    Polynomial.IsSplittingField.finiteDimensional
      (kummerExtension59 F a) (kummerPolynomial59 F a)
  letI : IsGalois F (kummerExtension59 F a) :=
    isGalois_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (by decide : 0 < 59)).2 hzeta⟩
      (kummerPolynomial59_irreducible F a ha)
      (kummerExtension59 F a)
  let sigma := concreteKummerGenerator59 F zeta a hzeta ha
  have hfinrank : Module.finrank F (kummerExtension59 F a) = 59 :=
    finrank_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (by decide : 0 < 59)).2 hzeta⟩
      (kummerPolynomial59_irreducible F a ha)
      (kummerExtension59 F a)
  have hcard : Nat.card
      (kummerExtension59 F a ≃ₐ[F] kummerExtension59 F a) = 59 := by
    rw [IsGalois.card_aut_eq_finrank, hfinrank]
  have hsigma : ∀ rho : kummerExtension59 F a ≃ₐ[F] kummerExtension59 F a,
      rho ∈ Subgroup.zpowers sigma := by
    intro rho
    exact mem_zpowers_of_prime_card hcard
      (concreteKummerGenerator59_ne_one F zeta a hzeta ha)
  obtain ⟨bK, hratio, hb⟩ :=
    concreteKummer_exists_albert_descent_datum59 F zeta a hzeta ha beta hbeta
  let psi := albertCharacter3481 bK sigma beta
    (kummerExtension59 F a).val zeta hzeta
      hratio hb hsigma hfinrank hbeta
  refine ⟨psi, ?_⟩
  calc
    cyclicReduction3481To59.comp psi =
        generatorCharacter59 (kummerExtension59 F a)
          sigma hsigma hfinrank :=
      albertCharacter3481_reduction_eq_generatorCharacter59
        (kummerExtension59 F a) bK sigma beta zeta hzeta
          hratio hb hsigma hfinrank hbeta
    _ = kummerCharacter59 F zeta a hzeta ha := by
      unfold generatorCharacter59
      rw [generatorGalEquiv59_eq_kummerGalEquiv59 F zeta a hzeta ha
        hsigma hfinrank]
      rfl

/-- The exact Albert lift produced by a norm witness is automatically
surjective: its reduction is the already-surjective concrete Kummer
character, and surjectivity lifts across `C3481 → C59`. -/
theorem concreteKummer_exists_surjective_albertCharacter3481
    (beta : kummerExtension59 F a)
    (hbeta : Algebra.norm F beta = zeta) :
    ∃ psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481,
      Function.Surjective psi ∧
      cyclicReduction3481To59.comp psi =
        kummerCharacter59 F zeta a hzeta ha := by
  obtain ⟨psi, hpsi⟩ :=
    concreteKummer_exists_albertCharacter3481 F zeta a hzeta ha beta hbeta
  refine ⟨psi, ?_, hpsi⟩
  apply continuous_surjective_of_cyclicReduction3481To59_comp_surjective psi
  rw [hpsi]
  exact kummerCharacter59_surjective F zeta a hzeta ha

end ConcreteKummer

end Fermat.Conservation.AlbertCyclicCompatibility59
