import Fermat.Irregular.TakagiFurtwangler491
import Fermat.Irregular.CyclotomicDiscriminantPrime
import Mathlib.NumberTheory.NumberField.CMField

/-!
# Conjugation descent for degree-491 Kummer extensions

This file records the extra symmetry needed to descend a Kummer extension
of the full `491`th cyclotomic field to its maximal real subfield.

For a radicand `a`, the relevant condition is anti-invariance modulo
`491`th powers.  We use the convenient exact form

`a * conj(a) = b ^ 491`, with `conj(b) = b`.

If `α ^ 491 = a`, this identity lets complex conjugation lift by
`α ↦ b / α`.  The lift is an involution.  The historical radicand
`x * conj(x) ^ 490` has this form with real norm root `x * conj(x)`.
-/

open scoped NumberField

namespace Fermat.Irregular.KummerConjugationDescent491

noncomputable section

open Polynomial AdjoinRoot
open Fermat.Irregular.TakagiFurtwangler491

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {491} ℚ K]

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 491) K (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Exact anti-invariance data for a degree-`491` Kummer radicand.

The equation says that the class of `a` in `Kˣ / (Kˣ)⁵⁸⁷` is sent to its
inverse by complex conjugation.  Requiring the displayed root `b` to be
real makes the lifted conjugation literally involutive. -/
structure ConjugationAntiInvariantWitness491 (a : 𝓞 K) where
  realNormRoot : K
  realNormRoot_fixed :
    NumberField.IsCMField.complexConj K realNormRoot = realNormRoot
  norm_eq :
    (a : K) * NumberField.IsCMField.complexConj K (a : K) =
      realNormRoot ^ 491

/-- The conjugate-pair radicand occurring in Vandiver's equation (7a). -/
noncomputable def conjugatePairRadicand491 (x : 𝓞 K) : 𝓞 K :=
  x * NumberField.IsCMField.ringOfIntegersComplexConj K x ^ 490

/-- A conjugate-pair radicand is anti-invariant, with real norm root
`x * conj(x)`. -/
noncomputable def conjugatePairAntiInvariantWitness491 (x : 𝓞 K) :
    ConjugationAntiInvariantWitness491 (conjugatePairRadicand491 x) where
  realNormRoot :=
    (x : K) * NumberField.IsCMField.complexConj K (x : K)
  realNormRoot_fixed := by
    rw [map_mul, NumberField.IsCMField.complexConj_apply_apply]
    ring
  norm_eq := by
    change
      ((x : K) * NumberField.IsCMField.complexConj K (x : K) ^ 490) *
          NumberField.IsCMField.complexConj K
            ((x : K) * NumberField.IsCMField.complexConj K (x : K) ^ 490) =
        ((x : K) * NumberField.IsCMField.complexConj K (x : K)) ^ 491
    rw [map_mul, map_pow,
      NumberField.IsCMField.complexConj_apply_apply]
    ring

/-- The historical radicand satisfies the exact anti-invariance identity,
displayed separately for later proof generators to reuse. -/
theorem conjugatePairRadicand491_norm_eq (x : 𝓞 K) :
    (conjugatePairRadicand491 x : K) *
        NumberField.IsCMField.complexConj K
          (conjugatePairRadicand491 x : K) =
      (((x : K) * NumberField.IsCMField.complexConj K (x : K)) ^ 491) :=
  (conjugatePairAntiInvariantWitness491 x).norm_eq

section Lift

variable {a : 𝓞 K}
  [hirr : Fact (Irreducible (X ^ 491 - C (a : K)))]

local notation3 "L" => KummerExtension491 K a

local instance : Field L := AdjoinRoot.instField
local instance : Algebra K L := inferInstance
local instance : Algebra K⁺ L := Algebra.restrictScalars K⁺ K L

omit [NumberField K] [IsCyclotomicExtension {491} ℚ K] in
/-- Irreducibility of the Kummer polynomial forces a nonzero radicand. -/
lemma radicand_ne_zero_of_irreducible491 : (a : K) ≠ 0 := by
  intro ha
  have hnotpow :=
    (X_pow_sub_C_irreducible_iff_of_prime
      (show Nat.Prime 491 by norm_num)).mp hirr.out
  exact hnotpow 0 (by simp [ha])

/-- The coefficient embedding obtained by applying complex conjugation
before embedding `K` into its Kummer extension. -/
noncomputable def conjugationCoefficientHom491 :
    K →ₐ[K⁺] L where
  toRingHom :=
    (algebraMap K L).comp
      (NumberField.IsCMField.complexConj K).toRingEquiv.toRingHom
  commutes' x := by
    change algebraMap K L
      (NumberField.IsCMField.complexConj K (algebraMap K⁺ K x)) =
        algebraMap K L (algebraMap K⁺ K x)
    rw [(NumberField.IsCMField.complexConj K).commutes]

@[simp]
lemma conjugationCoefficientHom491_apply (x : K) :
    conjugationCoefficientHom491 (a := a) x =
      algebraMap K L (NumberField.IsCMField.complexConj K x) :=
  rfl

/-- The desired image `b / α` of the distinguished Kummer root. -/
noncomputable def conjugationRootImage491
    (hanti : ConjugationAntiInvariantWitness491 a) : L :=
  algebraMap K L hanti.realNormRoot /
    root (X ^ 491 - C (a : K))

lemma realNormRoot_ne_zero491
    (hanti : ConjugationAntiInvariantWitness491 a) :
    hanti.realNormRoot ≠ 0 := by
  intro hb
  have hprod :
      (a : K) * NumberField.IsCMField.complexConj K (a : K) ≠ 0 :=
    mul_ne_zero (radicand_ne_zero_of_irreducible491 (a := a))
      ((map_ne_zero (NumberField.IsCMField.complexConj K)).mpr
        (radicand_ne_zero_of_irreducible491 (a := a)))
  apply hprod
  rw [hanti.norm_eq, hb, zero_pow (by norm_num : 491 ≠ 0)]

lemma conjugationRootImage491_pow
    (hanti : ConjugationAntiInvariantWitness491 a) :
    conjugationRootImage491 hanti ^ 491 =
      algebraMap K L
        (NumberField.IsCMField.complexConj K (a : K)) := by
  rw [conjugationRootImage491, div_pow, ← map_pow, ← hanti.norm_eq,
    map_mul, kummerExtension491_root_pow]
  exact mul_div_cancel_left₀ _
    ((map_ne_zero (algebraMap K L)).mpr
      (radicand_ne_zero_of_irreducible491 (a := a)))

lemma conjugationRootImage491_isRoot
    (hanti : ConjugationAntiInvariantWitness491 a) :
    (X ^ 491 - C (a : K)).eval₂
        (conjugationCoefficientHom491 (a := a))
        (conjugationRootImage491 hanti) = 0 := by
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
    conjugationRootImage491_pow (a := a)]
  change
    algebraMap K L (NumberField.IsCMField.complexConj K (a : K)) -
        algebraMap K L (NumberField.IsCMField.complexConj K (a : K)) = 0
  exact sub_self _

/-- The semilinear lift of complex conjugation to the Kummer extension.
It is first constructed as a `K⁺`-algebra endomorphism; involutivity below
upgrades it to an automorphism. -/
noncomputable def conjugationLiftAlgHom491
    (hanti : ConjugationAntiInvariantWitness491 a) :
    L →ₐ[K⁺] L :=
  AdjoinRoot.liftAlgHom (X ^ 491 - C (a : K))
    (conjugationCoefficientHom491 (a := a))
    (conjugationRootImage491 hanti)
    (conjugationRootImage491_isRoot (a := a) hanti)

@[simp]
lemma conjugationLiftAlgHom491_algebraMap
    (hanti : ConjugationAntiInvariantWitness491 a) (x : K) :
    conjugationLiftAlgHom491 hanti (algebraMap K L x) =
      algebraMap K L (NumberField.IsCMField.complexConj K x) := by
  exact AdjoinRoot.liftAlgHom_of
    (X ^ 491 - C (a : K))
    (conjugationCoefficientHom491 (a := a))
    (conjugationRootImage491 hanti)
    (conjugationRootImage491_isRoot (a := a) hanti) x

@[simp]
lemma conjugationLiftAlgHom491_root
    (hanti : ConjugationAntiInvariantWitness491 a) :
    conjugationLiftAlgHom491 hanti
        (root (X ^ 491 - C (a : K))) =
      conjugationRootImage491 hanti := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

theorem conjugationLiftAlgHom491_apply_apply
    (hanti : ConjugationAntiInvariantWitness491 a) (x : L) :
    conjugationLiftAlgHom491 hanti
        (conjugationLiftAlgHom491 hanti x) = x := by
  have hsq :
      (conjugationLiftAlgHom491 hanti).comp
          (conjugationLiftAlgHom491 hanti) =
        AlgHom.id K⁺ L := by
    apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro y
      change
        conjugationLiftAlgHom491 hanti
            (conjugationLiftAlgHom491 hanti (algebraMap K L y)) =
          algebraMap K L y
      rw [conjugationLiftAlgHom491_algebraMap,
        conjugationLiftAlgHom491_algebraMap,
        NumberField.IsCMField.complexConj_apply_apply]
    · change
        conjugationLiftAlgHom491 hanti
            (conjugationLiftAlgHom491 hanti
              (root (X ^ 491 - C (a : K)))) =
          root (X ^ 491 - C (a : K))
      rw [conjugationLiftAlgHom491_root,
        conjugationRootImage491, map_div₀,
        conjugationLiftAlgHom491_algebraMap,
        conjugationLiftAlgHom491_root,
        conjugationRootImage491,
        hanti.realNormRoot_fixed]
      exact div_div_cancel₀
        ((map_ne_zero (algebraMap K L)).mpr
          (realNormRoot_ne_zero491 (a := a) hanti))
  exact DFunLike.congr_fun hsq x

/-- The involutive `K⁺`-automorphism of the Kummer extension extending
complex conjugation and sending `α` to `b / α`. -/
noncomputable def conjugationLift491
    (hanti : ConjugationAntiInvariantWitness491 a) :
    L ≃ₐ[K⁺] L :=
  AlgEquiv.ofBijective (conjugationLiftAlgHom491 hanti)
    (Function.Involutive.bijective
      (conjugationLiftAlgHom491_apply_apply (a := a) hanti))

@[simp]
theorem conjugationLift491_algebraMap
    (hanti : ConjugationAntiInvariantWitness491 a) (x : K) :
    conjugationLift491 hanti (algebraMap K L x) =
      algebraMap K L (NumberField.IsCMField.complexConj K x) :=
  conjugationLiftAlgHom491_algebraMap (a := a) hanti x

@[simp]
theorem conjugationLift491_root
    (hanti : ConjugationAntiInvariantWitness491 a) :
    conjugationLift491 hanti
        (root (X ^ 491 - C (a : K))) =
      algebraMap K L hanti.realNormRoot /
        root (X ^ 491 - C (a : K)) :=
  conjugationLiftAlgHom491_root (a := a) hanti

@[simp]
theorem conjugationLift491_apply_apply
    (hanti : ConjugationAntiInvariantWitness491 a) (x : L) :
    conjugationLift491 hanti
        (conjugationLift491 hanti x) = x :=
  conjugationLiftAlgHom491_apply_apply (a := a) hanti x

theorem conjugationLift491_sq
    (hanti : ConjugationAntiInvariantWitness491 a) :
    conjugationLift491 hanti ^ 2 = 1 := by
  ext x
  exact conjugationLift491_apply_apply (a := a) hanti x

/-- Regard a `K`-automorphism of the Kummer extension as an automorphism
over the maximal real subfield.  This explicit wrapper avoids imposing a
particular `IsScalarTower` instance on downstream files. -/
noncomputable def restrictKAutToReal491 (σ : L ≃ₐ[K] L) : L ≃ₐ[K⁺] L where
  __ := σ
  commutes' x := by
    change σ (algebraMap K L (algebraMap K⁺ K x)) =
      algebraMap K L (algebraMap K⁺ K x)
    exact σ.commutes _

omit [NumberField K] [IsCyclotomicExtension {491} ℚ K] in
@[simp]
theorem restrictKAutToReal491_apply (σ : L ≃ₐ[K] L) (x : L) :
    restrictKAutToReal491 σ x = σ x :=
  rfl

/-- Complex conjugation inverts every `491`th root of unity in the
cyclotomic coefficient field. -/
theorem complexConj_eq_inv_of_pow_eq_one491
    {ζ η : K} (hζ : IsPrimitiveRoot ζ 491) (hη : η ^ 491 = 1) :
    NumberField.IsCMField.complexConj K η = η⁻¹ := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
  rw [map_pow,
    Fermat.Irregular.CyclotomicDiscriminantPrime.complexConj_zeta_inv hζ]
  exact inv_pow ζ i

/-- The lifted conjugation commutes pointwise with a Kummer deck
transformation whose root multiplier is inverted by conjugation. -/
theorem conjugationLift491_apply_kAut_of_root_eq
    (hanti : ConjugationAntiInvariantWitness491 a)
    {η : K}
    (hconjη : NumberField.IsCMField.complexConj K η = η⁻¹)
    (σ : L ≃ₐ[K] L)
    (hσroot :
      σ (root (X ^ 491 - C (a : K))) =
        algebraMap K L η * root (X ^ 491 - C (a : K)))
    (x : L) :
    conjugationLift491 hanti (σ x) =
      σ (conjugationLift491 hanti x) := by
  have hcomp :
      (conjugationLift491 hanti).toAlgHom.comp
          (restrictKAutToReal491 σ).toAlgHom =
        (restrictKAutToReal491 σ).toAlgHom.comp
          (conjugationLift491 hanti).toAlgHom := by
    apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro y
      change
        conjugationLift491 hanti
            (σ (algebraMap K L y)) =
          σ (conjugationLift491 hanti (algebraMap K L y))
      simp only [σ.commutes, conjugationLift491_algebraMap]
    · change
        conjugationLift491 hanti
            (σ (root (X ^ 491 - C (a : K)))) =
          σ (conjugationLift491 hanti
            (root (X ^ 491 - C (a : K))))
      rw [hσroot, map_mul, conjugationLift491_algebraMap,
        conjugationLift491_root, hconjη, map_div₀, σ.commutes, hσroot]
      simp only [map_inv₀, div_eq_mul_inv, mul_inv_rev]
      ring
  exact DFunLike.congr_fun hcomp x

/-- Group-theoretic form of
`conjugationLift491_apply_kAut_of_root_eq`. -/
theorem conjugationLift491_commute_kAut_of_root_eq
    (hanti : ConjugationAntiInvariantWitness491 a)
    {η : K}
    (hconjη : NumberField.IsCMField.complexConj K η = η⁻¹)
    (σ : L ≃ₐ[K] L)
    (hσroot :
      σ (root (X ^ 491 - C (a : K))) =
        algebraMap K L η * root (X ^ 491 - C (a : K))) :
    Commute (conjugationLift491 hanti) (restrictKAutToReal491 σ) := by
  apply DFunLike.ext _ _
  intro x
  exact conjugationLift491_apply_kAut_of_root_eq
    (a := a) hanti hconjη σ hσroot x

/-- The lifted conjugation commutes with every deck transformation of the
degree-`491` Kummer extension. -/
theorem conjugationLift491_commute_kAut
    (hanti : ConjugationAntiInvariantWitness491 a)
    (σ : L ≃ₐ[K] L) :
    Commute (conjugationLift491 hanti) (restrictKAutToReal491 σ) := by
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot ℚ K
      (show 491 ∈ ({491} : Set ℕ) by simp)
      (by norm_num : 491 ≠ 0)
  have hroots : (primitiveRoots 491 K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by norm_num : 0 < 491)).2 hζ⟩
  let η : rootsOfUnity 491 K :=
    (autAdjoinRootXPowSubCEquiv hroots hirr.out).symm σ
  have hηpow : (((η : Kˣ) : K)) ^ 491 = 1 :=
    by simpa using (mem_rootsOfUnity' _ _).mp η.prop
  have hσroot :
      σ (root (X ^ 491 - C (a : K))) =
        algebraMap K L (((η : Kˣ) : K)) *
          root (X ^ 491 - C (a : K)) := by
    simpa only [η, Units.smul_def, Algebra.smul_def] using
      (autAdjoinRootXPowSubCEquiv_symm_smul hroots hirr.out σ).symm
  exact conjugationLift491_commute_kAut_of_root_eq
    (a := a) hanti
    (complexConj_eq_inv_of_pow_eq_one491 hζ hηpow)
    σ hσroot

end Lift

end

end Fermat.Irregular.KummerConjugationDescent491
