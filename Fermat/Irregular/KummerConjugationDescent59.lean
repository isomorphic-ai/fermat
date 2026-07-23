import Fermat.Irregular.TakagiFurtwangler59
import Fermat.Irregular.CyclotomicDiscriminantPrime
import Mathlib.NumberTheory.NumberField.CMField

/-!
# Conjugation descent for degree-59 Kummer extensions

This file records the extra symmetry needed to descend a Kummer extension
of the full `59`th cyclotomic field to its maximal real subfield.

For a radicand `a`, the relevant condition is anti-invariance modulo
`59`th powers.  We use the convenient exact form

`a * conj(a) = b ^ 59`, with `conj(b) = b`.

If `α ^ 59 = a`, this identity lets complex conjugation lift by
`α ↦ b / α`.  The lift is an involution.  The historical radicand
`x * conj(x) ^ 58` has this form with real norm root `x * conj(x)`.
-/

open scoped NumberField

namespace Fermat.Irregular.KummerConjugationDescent59

noncomputable section

open Polynomial AdjoinRoot
open Fermat.Irregular.TakagiFurtwangler59

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 59) K (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Exact anti-invariance data for a degree-`59` Kummer radicand.

The equation says that the class of `a` in `Kˣ / (Kˣ)³⁷` is sent to its
inverse by complex conjugation.  Requiring the displayed root `b` to be
real makes the lifted conjugation literally involutive. -/
structure ConjugationAntiInvariantWitness59 (a : 𝓞 K) where
  realNormRoot : K
  realNormRoot_fixed :
    NumberField.IsCMField.complexConj K realNormRoot = realNormRoot
  norm_eq :
    (a : K) * NumberField.IsCMField.complexConj K (a : K) =
      realNormRoot ^ 59

/-- The conjugate-pair radicand occurring in Vandiver's equation (7a). -/
noncomputable def conjugatePairRadicand59 (x : 𝓞 K) : 𝓞 K :=
  x * NumberField.IsCMField.ringOfIntegersComplexConj K x ^ 58

/-- A conjugate-pair radicand is anti-invariant, with real norm root
`x * conj(x)`. -/
noncomputable def conjugatePairAntiInvariantWitness59 (x : 𝓞 K) :
    ConjugationAntiInvariantWitness59 (conjugatePairRadicand59 x) where
  realNormRoot :=
    (x : K) * NumberField.IsCMField.complexConj K (x : K)
  realNormRoot_fixed := by
    rw [map_mul, NumberField.IsCMField.complexConj_apply_apply]
    ring
  norm_eq := by
    change
      ((x : K) * NumberField.IsCMField.complexConj K (x : K) ^ 58) *
          NumberField.IsCMField.complexConj K
            ((x : K) * NumberField.IsCMField.complexConj K (x : K) ^ 58) =
        ((x : K) * NumberField.IsCMField.complexConj K (x : K)) ^ 59
    rw [map_mul, map_pow,
      NumberField.IsCMField.complexConj_apply_apply]
    ring

/-- The historical radicand satisfies the exact anti-invariance identity,
displayed separately for later proof generators to reuse. -/
theorem conjugatePairRadicand59_norm_eq (x : 𝓞 K) :
    (conjugatePairRadicand59 x : K) *
        NumberField.IsCMField.complexConj K
          (conjugatePairRadicand59 x : K) =
      (((x : K) * NumberField.IsCMField.complexConj K (x : K)) ^ 59) :=
  (conjugatePairAntiInvariantWitness59 x).norm_eq

section Lift

variable {a : 𝓞 K}
  [hirr : Fact (Irreducible (X ^ 59 - C (a : K)))]

local notation3 "L" => KummerExtension59 K a

local instance : Field L := AdjoinRoot.instField
local instance : Algebra K L := inferInstance
local instance : Algebra K⁺ L := Algebra.restrictScalars K⁺ K L

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
/-- Irreducibility of the Kummer polynomial forces a nonzero radicand. -/
lemma radicand_ne_zero_of_irreducible59 : (a : K) ≠ 0 := by
  intro ha
  have hnotpow :=
    (X_pow_sub_C_irreducible_iff_of_prime
      (show Nat.Prime 59 by norm_num)).mp hirr.out
  exact hnotpow 0 (by simp [ha])

/-- The coefficient embedding obtained by applying complex conjugation
before embedding `K` into its Kummer extension. -/
noncomputable def conjugationCoefficientHom59 :
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
lemma conjugationCoefficientHom59_apply (x : K) :
    conjugationCoefficientHom59 (a := a) x =
      algebraMap K L (NumberField.IsCMField.complexConj K x) :=
  rfl

/-- The desired image `b / α` of the distinguished Kummer root. -/
noncomputable def conjugationRootImage59
    (hanti : ConjugationAntiInvariantWitness59 a) : L :=
  algebraMap K L hanti.realNormRoot /
    root (X ^ 59 - C (a : K))

lemma realNormRoot_ne_zero59
    (hanti : ConjugationAntiInvariantWitness59 a) :
    hanti.realNormRoot ≠ 0 := by
  intro hb
  have hprod :
      (a : K) * NumberField.IsCMField.complexConj K (a : K) ≠ 0 :=
    mul_ne_zero (radicand_ne_zero_of_irreducible59 (a := a))
      ((map_ne_zero (NumberField.IsCMField.complexConj K)).mpr
        (radicand_ne_zero_of_irreducible59 (a := a)))
  apply hprod
  rw [hanti.norm_eq, hb, zero_pow (by norm_num : 59 ≠ 0)]

lemma conjugationRootImage59_pow
    (hanti : ConjugationAntiInvariantWitness59 a) :
    conjugationRootImage59 hanti ^ 59 =
      algebraMap K L
        (NumberField.IsCMField.complexConj K (a : K)) := by
  rw [conjugationRootImage59, div_pow, ← map_pow, ← hanti.norm_eq,
    map_mul, kummerExtension59_root_pow]
  exact mul_div_cancel_left₀ _
    ((map_ne_zero (algebraMap K L)).mpr
      (radicand_ne_zero_of_irreducible59 (a := a)))

lemma conjugationRootImage59_isRoot
    (hanti : ConjugationAntiInvariantWitness59 a) :
    (X ^ 59 - C (a : K)).eval₂
        (conjugationCoefficientHom59 (a := a))
        (conjugationRootImage59 hanti) = 0 := by
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
    conjugationRootImage59_pow (a := a)]
  change
    algebraMap K L (NumberField.IsCMField.complexConj K (a : K)) -
        algebraMap K L (NumberField.IsCMField.complexConj K (a : K)) = 0
  exact sub_self _

/-- The semilinear lift of complex conjugation to the Kummer extension.
It is first constructed as a `K⁺`-algebra endomorphism; involutivity below
upgrades it to an automorphism. -/
noncomputable def conjugationLiftAlgHom59
    (hanti : ConjugationAntiInvariantWitness59 a) :
    L →ₐ[K⁺] L :=
  AdjoinRoot.liftAlgHom (X ^ 59 - C (a : K))
    (conjugationCoefficientHom59 (a := a))
    (conjugationRootImage59 hanti)
    (conjugationRootImage59_isRoot (a := a) hanti)

@[simp]
lemma conjugationLiftAlgHom59_algebraMap
    (hanti : ConjugationAntiInvariantWitness59 a) (x : K) :
    conjugationLiftAlgHom59 hanti (algebraMap K L x) =
      algebraMap K L (NumberField.IsCMField.complexConj K x) := by
  exact AdjoinRoot.liftAlgHom_of
    (X ^ 59 - C (a : K))
    (conjugationCoefficientHom59 (a := a))
    (conjugationRootImage59 hanti)
    (conjugationRootImage59_isRoot (a := a) hanti) x

@[simp]
lemma conjugationLiftAlgHom59_root
    (hanti : ConjugationAntiInvariantWitness59 a) :
    conjugationLiftAlgHom59 hanti
        (root (X ^ 59 - C (a : K))) =
      conjugationRootImage59 hanti := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

theorem conjugationLiftAlgHom59_apply_apply
    (hanti : ConjugationAntiInvariantWitness59 a) (x : L) :
    conjugationLiftAlgHom59 hanti
        (conjugationLiftAlgHom59 hanti x) = x := by
  have hsq :
      (conjugationLiftAlgHom59 hanti).comp
          (conjugationLiftAlgHom59 hanti) =
        AlgHom.id K⁺ L := by
    apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro y
      change
        conjugationLiftAlgHom59 hanti
            (conjugationLiftAlgHom59 hanti (algebraMap K L y)) =
          algebraMap K L y
      rw [conjugationLiftAlgHom59_algebraMap,
        conjugationLiftAlgHom59_algebraMap,
        NumberField.IsCMField.complexConj_apply_apply]
    · change
        conjugationLiftAlgHom59 hanti
            (conjugationLiftAlgHom59 hanti
              (root (X ^ 59 - C (a : K)))) =
          root (X ^ 59 - C (a : K))
      rw [conjugationLiftAlgHom59_root,
        conjugationRootImage59, map_div₀,
        conjugationLiftAlgHom59_algebraMap,
        conjugationLiftAlgHom59_root,
        conjugationRootImage59,
        hanti.realNormRoot_fixed]
      exact div_div_cancel₀
        ((map_ne_zero (algebraMap K L)).mpr
          (realNormRoot_ne_zero59 (a := a) hanti))
  exact DFunLike.congr_fun hsq x

/-- The involutive `K⁺`-automorphism of the Kummer extension extending
complex conjugation and sending `α` to `b / α`. -/
noncomputable def conjugationLift59
    (hanti : ConjugationAntiInvariantWitness59 a) :
    L ≃ₐ[K⁺] L :=
  AlgEquiv.ofBijective (conjugationLiftAlgHom59 hanti)
    (Function.Involutive.bijective
      (conjugationLiftAlgHom59_apply_apply (a := a) hanti))

@[simp]
theorem conjugationLift59_algebraMap
    (hanti : ConjugationAntiInvariantWitness59 a) (x : K) :
    conjugationLift59 hanti (algebraMap K L x) =
      algebraMap K L (NumberField.IsCMField.complexConj K x) :=
  conjugationLiftAlgHom59_algebraMap (a := a) hanti x

@[simp]
theorem conjugationLift59_root
    (hanti : ConjugationAntiInvariantWitness59 a) :
    conjugationLift59 hanti
        (root (X ^ 59 - C (a : K))) =
      algebraMap K L hanti.realNormRoot /
        root (X ^ 59 - C (a : K)) :=
  conjugationLiftAlgHom59_root (a := a) hanti

@[simp]
theorem conjugationLift59_apply_apply
    (hanti : ConjugationAntiInvariantWitness59 a) (x : L) :
    conjugationLift59 hanti
        (conjugationLift59 hanti x) = x :=
  conjugationLiftAlgHom59_apply_apply (a := a) hanti x

theorem conjugationLift59_sq
    (hanti : ConjugationAntiInvariantWitness59 a) :
    conjugationLift59 hanti ^ 2 = 1 := by
  ext x
  exact conjugationLift59_apply_apply (a := a) hanti x

/-- Regard a `K`-automorphism of the Kummer extension as an automorphism
over the maximal real subfield.  This explicit wrapper avoids imposing a
particular `IsScalarTower` instance on downstream files. -/
noncomputable def restrictKAutToReal59 (σ : L ≃ₐ[K] L) : L ≃ₐ[K⁺] L where
  __ := σ
  commutes' x := by
    change σ (algebraMap K L (algebraMap K⁺ K x)) =
      algebraMap K L (algebraMap K⁺ K x)
    exact σ.commutes _

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
@[simp]
theorem restrictKAutToReal59_apply (σ : L ≃ₐ[K] L) (x : L) :
    restrictKAutToReal59 σ x = σ x :=
  rfl

/-- Complex conjugation inverts every `59`th root of unity in the
cyclotomic coefficient field. -/
theorem complexConj_eq_inv_of_pow_eq_one59
    {ζ η : K} (hζ : IsPrimitiveRoot ζ 59) (hη : η ^ 59 = 1) :
    NumberField.IsCMField.complexConj K η = η⁻¹ := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
  rw [map_pow,
    Fermat.Irregular.CyclotomicDiscriminantPrime.complexConj_zeta_inv hζ]
  exact inv_pow ζ i

/-- The lifted conjugation commutes pointwise with a Kummer deck
transformation whose root multiplier is inverted by conjugation. -/
theorem conjugationLift59_apply_kAut_of_root_eq
    (hanti : ConjugationAntiInvariantWitness59 a)
    {η : K}
    (hconjη : NumberField.IsCMField.complexConj K η = η⁻¹)
    (σ : L ≃ₐ[K] L)
    (hσroot :
      σ (root (X ^ 59 - C (a : K))) =
        algebraMap K L η * root (X ^ 59 - C (a : K)))
    (x : L) :
    conjugationLift59 hanti (σ x) =
      σ (conjugationLift59 hanti x) := by
  have hcomp :
      (conjugationLift59 hanti).toAlgHom.comp
          (restrictKAutToReal59 σ).toAlgHom =
        (restrictKAutToReal59 σ).toAlgHom.comp
          (conjugationLift59 hanti).toAlgHom := by
    apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro y
      change
        conjugationLift59 hanti
            (σ (algebraMap K L y)) =
          σ (conjugationLift59 hanti (algebraMap K L y))
      simp only [σ.commutes, conjugationLift59_algebraMap]
    · change
        conjugationLift59 hanti
            (σ (root (X ^ 59 - C (a : K)))) =
          σ (conjugationLift59 hanti
            (root (X ^ 59 - C (a : K))))
      rw [hσroot, map_mul, conjugationLift59_algebraMap,
        conjugationLift59_root, hconjη, map_div₀, σ.commutes, hσroot]
      simp only [map_inv₀, div_eq_mul_inv, mul_inv_rev]
      ring
  exact DFunLike.congr_fun hcomp x

/-- Group-theoretic form of
`conjugationLift59_apply_kAut_of_root_eq`. -/
theorem conjugationLift59_commute_kAut_of_root_eq
    (hanti : ConjugationAntiInvariantWitness59 a)
    {η : K}
    (hconjη : NumberField.IsCMField.complexConj K η = η⁻¹)
    (σ : L ≃ₐ[K] L)
    (hσroot :
      σ (root (X ^ 59 - C (a : K))) =
        algebraMap K L η * root (X ^ 59 - C (a : K))) :
    Commute (conjugationLift59 hanti) (restrictKAutToReal59 σ) := by
  apply DFunLike.ext _ _
  intro x
  exact conjugationLift59_apply_kAut_of_root_eq
    (a := a) hanti hconjη σ hσroot x

/-- The lifted conjugation commutes with every deck transformation of the
degree-`59` Kummer extension. -/
theorem conjugationLift59_commute_kAut
    (hanti : ConjugationAntiInvariantWitness59 a)
    (σ : L ≃ₐ[K] L) :
    Commute (conjugationLift59 hanti) (restrictKAutToReal59 σ) := by
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot ℚ K
      (show 59 ∈ ({59} : Set ℕ) by simp)
      (by norm_num : 59 ≠ 0)
  have hroots : (primitiveRoots 59 K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by norm_num : 0 < 59)).2 hζ⟩
  let η : rootsOfUnity 59 K :=
    (autAdjoinRootXPowSubCEquiv hroots hirr.out).symm σ
  have hηpow : (((η : Kˣ) : K)) ^ 59 = 1 :=
    by simpa using (mem_rootsOfUnity' _ _).mp η.prop
  have hσroot :
      σ (root (X ^ 59 - C (a : K))) =
        algebraMap K L (((η : Kˣ) : K)) *
          root (X ^ 59 - C (a : K)) := by
    simpa only [η, Units.smul_def, Algebra.smul_def] using
      (autAdjoinRootXPowSubCEquiv_symm_smul hroots hirr.out σ).symm
  exact conjugationLift59_commute_kAut_of_root_eq
    (a := a) hanti
    (complexConj_eq_inv_of_pow_eq_one59 hζ hηpow)
    σ hσroot

end Lift

end

end Fermat.Irregular.KummerConjugationDescent59
