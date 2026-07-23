import Fermat.Irregular.TakagiFurtwangler587
import Fermat.Irregular.CyclotomicDiscriminantPrime
import Mathlib.NumberTheory.NumberField.CMField

/-!
# Conjugation descent for degree-587 Kummer extensions

This file records the extra symmetry needed to descend a Kummer extension
of the full `587`th cyclotomic field to its maximal real subfield.

For a radicand `a`, the relevant condition is anti-invariance modulo
`587`th powers.  We use the convenient exact form

`a * conj(a) = b ^ 587`, with `conj(b) = b`.

If `α ^ 587 = a`, this identity lets complex conjugation lift by
`α ↦ b / α`.  The lift is an involution.  The historical radicand
`x * conj(x) ^ 586` has this form with real norm root `x * conj(x)`.
-/

open scoped NumberField

namespace Fermat.Irregular.KummerConjugationDescent587

noncomputable section

open Polynomial AdjoinRoot
open Fermat.Irregular.TakagiFurtwangler587

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {587} ℚ K]

local instance : Fact (Nat.Prime 587) := ⟨by norm_num⟩

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 587) K (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Exact anti-invariance data for a degree-`587` Kummer radicand.

The equation says that the class of `a` in `Kˣ / (Kˣ)⁵⁸⁷` is sent to its
inverse by complex conjugation.  Requiring the displayed root `b` to be
real makes the lifted conjugation literally involutive. -/
structure ConjugationAntiInvariantWitness587 (a : 𝓞 K) where
  realNormRoot : K
  realNormRoot_fixed :
    NumberField.IsCMField.complexConj K realNormRoot = realNormRoot
  norm_eq :
    (a : K) * NumberField.IsCMField.complexConj K (a : K) =
      realNormRoot ^ 587

/-- The conjugate-pair radicand occurring in Vandiver's equation (7a). -/
noncomputable def conjugatePairRadicand587 (x : 𝓞 K) : 𝓞 K :=
  x * NumberField.IsCMField.ringOfIntegersComplexConj K x ^ 586

/-- A conjugate-pair radicand is anti-invariant, with real norm root
`x * conj(x)`. -/
noncomputable def conjugatePairAntiInvariantWitness587 (x : 𝓞 K) :
    ConjugationAntiInvariantWitness587 (conjugatePairRadicand587 x) where
  realNormRoot :=
    (x : K) * NumberField.IsCMField.complexConj K (x : K)
  realNormRoot_fixed := by
    rw [map_mul, NumberField.IsCMField.complexConj_apply_apply]
    ring
  norm_eq := by
    change
      ((x : K) * NumberField.IsCMField.complexConj K (x : K) ^ 586) *
          NumberField.IsCMField.complexConj K
            ((x : K) * NumberField.IsCMField.complexConj K (x : K) ^ 586) =
        ((x : K) * NumberField.IsCMField.complexConj K (x : K)) ^ 587
    rw [map_mul, map_pow,
      NumberField.IsCMField.complexConj_apply_apply]
    ring

/-- The historical radicand satisfies the exact anti-invariance identity,
displayed separately for later proof generators to reuse. -/
theorem conjugatePairRadicand587_norm_eq (x : 𝓞 K) :
    (conjugatePairRadicand587 x : K) *
        NumberField.IsCMField.complexConj K
          (conjugatePairRadicand587 x : K) =
      (((x : K) * NumberField.IsCMField.complexConj K (x : K)) ^ 587) :=
  (conjugatePairAntiInvariantWitness587 x).norm_eq

section Lift

variable {a : 𝓞 K}
  [hirr : Fact (Irreducible (X ^ 587 - C (a : K)))]

local notation3 "L" => KummerExtension587 K a

local instance : Field L := AdjoinRoot.instField
local instance : Algebra K L := inferInstance
local instance : Algebra K⁺ L := Algebra.restrictScalars K⁺ K L

omit [NumberField K] [IsCyclotomicExtension {587} ℚ K] in
/-- Irreducibility of the Kummer polynomial forces a nonzero radicand. -/
lemma radicand_ne_zero_of_irreducible587 : (a : K) ≠ 0 := by
  intro ha
  have hnotpow :=
    (X_pow_sub_C_irreducible_iff_of_prime
      (show Nat.Prime 587 by norm_num)).mp hirr.out
  exact hnotpow 0 (by simp [ha])

/-- The coefficient embedding obtained by applying complex conjugation
before embedding `K` into its Kummer extension. -/
noncomputable def conjugationCoefficientHom587 :
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
lemma conjugationCoefficientHom587_apply (x : K) :
    conjugationCoefficientHom587 (a := a) x =
      algebraMap K L (NumberField.IsCMField.complexConj K x) :=
  rfl

/-- The desired image `b / α` of the distinguished Kummer root. -/
noncomputable def conjugationRootImage587
    (hanti : ConjugationAntiInvariantWitness587 a) : L :=
  algebraMap K L hanti.realNormRoot /
    root (X ^ 587 - C (a : K))

lemma realNormRoot_ne_zero587
    (hanti : ConjugationAntiInvariantWitness587 a) :
    hanti.realNormRoot ≠ 0 := by
  intro hb
  have hprod :
      (a : K) * NumberField.IsCMField.complexConj K (a : K) ≠ 0 :=
    mul_ne_zero (radicand_ne_zero_of_irreducible587 (a := a))
      ((map_ne_zero (NumberField.IsCMField.complexConj K)).mpr
        (radicand_ne_zero_of_irreducible587 (a := a)))
  apply hprod
  rw [hanti.norm_eq, hb, zero_pow (by norm_num : 587 ≠ 0)]

lemma conjugationRootImage587_pow
    (hanti : ConjugationAntiInvariantWitness587 a) :
    conjugationRootImage587 hanti ^ 587 =
      algebraMap K L
        (NumberField.IsCMField.complexConj K (a : K)) := by
  rw [conjugationRootImage587, div_pow, ← map_pow, ← hanti.norm_eq,
    map_mul, kummerExtension587_root_pow]
  exact mul_div_cancel_left₀ _
    ((map_ne_zero (algebraMap K L)).mpr
      (radicand_ne_zero_of_irreducible587 (a := a)))

lemma conjugationRootImage587_isRoot
    (hanti : ConjugationAntiInvariantWitness587 a) :
    (X ^ 587 - C (a : K)).eval₂
        (conjugationCoefficientHom587 (a := a))
        (conjugationRootImage587 hanti) = 0 := by
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
    conjugationRootImage587_pow (a := a)]
  change
    algebraMap K L (NumberField.IsCMField.complexConj K (a : K)) -
        algebraMap K L (NumberField.IsCMField.complexConj K (a : K)) = 0
  exact sub_self _

/-- The semilinear lift of complex conjugation to the Kummer extension.
It is first constructed as a `K⁺`-algebra endomorphism; involutivity below
upgrades it to an automorphism. -/
noncomputable def conjugationLiftAlgHom587
    (hanti : ConjugationAntiInvariantWitness587 a) :
    L →ₐ[K⁺] L :=
  AdjoinRoot.liftAlgHom (X ^ 587 - C (a : K))
    (conjugationCoefficientHom587 (a := a))
    (conjugationRootImage587 hanti)
    (conjugationRootImage587_isRoot (a := a) hanti)

@[simp]
lemma conjugationLiftAlgHom587_algebraMap
    (hanti : ConjugationAntiInvariantWitness587 a) (x : K) :
    conjugationLiftAlgHom587 hanti (algebraMap K L x) =
      algebraMap K L (NumberField.IsCMField.complexConj K x) := by
  exact AdjoinRoot.liftAlgHom_of
    (X ^ 587 - C (a : K))
    (conjugationCoefficientHom587 (a := a))
    (conjugationRootImage587 hanti)
    (conjugationRootImage587_isRoot (a := a) hanti) x

@[simp]
lemma conjugationLiftAlgHom587_root
    (hanti : ConjugationAntiInvariantWitness587 a) :
    conjugationLiftAlgHom587 hanti
        (root (X ^ 587 - C (a : K))) =
      conjugationRootImage587 hanti := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

theorem conjugationLiftAlgHom587_apply_apply
    (hanti : ConjugationAntiInvariantWitness587 a) (x : L) :
    conjugationLiftAlgHom587 hanti
        (conjugationLiftAlgHom587 hanti x) = x := by
  have hsq :
      (conjugationLiftAlgHom587 hanti).comp
          (conjugationLiftAlgHom587 hanti) =
        AlgHom.id K⁺ L := by
    apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro y
      change
        conjugationLiftAlgHom587 hanti
            (conjugationLiftAlgHom587 hanti (algebraMap K L y)) =
          algebraMap K L y
      rw [conjugationLiftAlgHom587_algebraMap,
        conjugationLiftAlgHom587_algebraMap,
        NumberField.IsCMField.complexConj_apply_apply]
    · change
        conjugationLiftAlgHom587 hanti
            (conjugationLiftAlgHom587 hanti
              (root (X ^ 587 - C (a : K)))) =
          root (X ^ 587 - C (a : K))
      rw [conjugationLiftAlgHom587_root,
        conjugationRootImage587, map_div₀,
        conjugationLiftAlgHom587_algebraMap,
        conjugationLiftAlgHom587_root,
        conjugationRootImage587,
        hanti.realNormRoot_fixed]
      exact div_div_cancel₀
        ((map_ne_zero (algebraMap K L)).mpr
          (realNormRoot_ne_zero587 (a := a) hanti))
  exact DFunLike.congr_fun hsq x

/-- The involutive `K⁺`-automorphism of the Kummer extension extending
complex conjugation and sending `α` to `b / α`. -/
noncomputable def conjugationLift587
    (hanti : ConjugationAntiInvariantWitness587 a) :
    L ≃ₐ[K⁺] L :=
  AlgEquiv.ofBijective (conjugationLiftAlgHom587 hanti)
    (Function.Involutive.bijective
      (conjugationLiftAlgHom587_apply_apply (a := a) hanti))

@[simp]
theorem conjugationLift587_algebraMap
    (hanti : ConjugationAntiInvariantWitness587 a) (x : K) :
    conjugationLift587 hanti (algebraMap K L x) =
      algebraMap K L (NumberField.IsCMField.complexConj K x) :=
  conjugationLiftAlgHom587_algebraMap (a := a) hanti x

@[simp]
theorem conjugationLift587_root
    (hanti : ConjugationAntiInvariantWitness587 a) :
    conjugationLift587 hanti
        (root (X ^ 587 - C (a : K))) =
      algebraMap K L hanti.realNormRoot /
        root (X ^ 587 - C (a : K)) :=
  conjugationLiftAlgHom587_root (a := a) hanti

@[simp]
theorem conjugationLift587_apply_apply
    (hanti : ConjugationAntiInvariantWitness587 a) (x : L) :
    conjugationLift587 hanti
        (conjugationLift587 hanti x) = x :=
  conjugationLiftAlgHom587_apply_apply (a := a) hanti x

theorem conjugationLift587_sq
    (hanti : ConjugationAntiInvariantWitness587 a) :
    conjugationLift587 hanti ^ 2 = 1 := by
  ext x
  exact conjugationLift587_apply_apply (a := a) hanti x

/-- Regard a `K`-automorphism of the Kummer extension as an automorphism
over the maximal real subfield.  This explicit wrapper avoids imposing a
particular `IsScalarTower` instance on downstream files. -/
noncomputable def restrictKAutToReal587 (σ : L ≃ₐ[K] L) : L ≃ₐ[K⁺] L where
  __ := σ
  commutes' x := by
    change σ (algebraMap K L (algebraMap K⁺ K x)) =
      algebraMap K L (algebraMap K⁺ K x)
    exact σ.commutes _

omit [NumberField K] [IsCyclotomicExtension {587} ℚ K] in
@[simp]
theorem restrictKAutToReal587_apply (σ : L ≃ₐ[K] L) (x : L) :
    restrictKAutToReal587 σ x = σ x :=
  rfl

/-- Complex conjugation inverts every `587`th root of unity in the
cyclotomic coefficient field. -/
theorem complexConj_eq_inv_of_pow_eq_one587
    {ζ η : K} (hζ : IsPrimitiveRoot ζ 587) (hη : η ^ 587 = 1) :
    NumberField.IsCMField.complexConj K η = η⁻¹ := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
  rw [map_pow,
    Fermat.Irregular.CyclotomicDiscriminantPrime.complexConj_zeta_inv hζ]
  exact inv_pow ζ i

/-- The lifted conjugation commutes pointwise with a Kummer deck
transformation whose root multiplier is inverted by conjugation. -/
theorem conjugationLift587_apply_kAut_of_root_eq
    (hanti : ConjugationAntiInvariantWitness587 a)
    {η : K}
    (hconjη : NumberField.IsCMField.complexConj K η = η⁻¹)
    (σ : L ≃ₐ[K] L)
    (hσroot :
      σ (root (X ^ 587 - C (a : K))) =
        algebraMap K L η * root (X ^ 587 - C (a : K)))
    (x : L) :
    conjugationLift587 hanti (σ x) =
      σ (conjugationLift587 hanti x) := by
  have hcomp :
      (conjugationLift587 hanti).toAlgHom.comp
          (restrictKAutToReal587 σ).toAlgHom =
        (restrictKAutToReal587 σ).toAlgHom.comp
          (conjugationLift587 hanti).toAlgHom := by
    apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro y
      change
        conjugationLift587 hanti
            (σ (algebraMap K L y)) =
          σ (conjugationLift587 hanti (algebraMap K L y))
      simp only [σ.commutes, conjugationLift587_algebraMap]
    · change
        conjugationLift587 hanti
            (σ (root (X ^ 587 - C (a : K)))) =
          σ (conjugationLift587 hanti
            (root (X ^ 587 - C (a : K))))
      rw [hσroot, map_mul, conjugationLift587_algebraMap,
        conjugationLift587_root, hconjη, map_div₀, σ.commutes, hσroot]
      simp only [map_inv₀, div_eq_mul_inv, mul_inv_rev]
      ring
  exact DFunLike.congr_fun hcomp x

/-- Group-theoretic form of
`conjugationLift587_apply_kAut_of_root_eq`. -/
theorem conjugationLift587_commute_kAut_of_root_eq
    (hanti : ConjugationAntiInvariantWitness587 a)
    {η : K}
    (hconjη : NumberField.IsCMField.complexConj K η = η⁻¹)
    (σ : L ≃ₐ[K] L)
    (hσroot :
      σ (root (X ^ 587 - C (a : K))) =
        algebraMap K L η * root (X ^ 587 - C (a : K))) :
    Commute (conjugationLift587 hanti) (restrictKAutToReal587 σ) := by
  apply DFunLike.ext _ _
  intro x
  exact conjugationLift587_apply_kAut_of_root_eq
    (a := a) hanti hconjη σ hσroot x

/-- The lifted conjugation commutes with every deck transformation of the
degree-`587` Kummer extension. -/
theorem conjugationLift587_commute_kAut
    (hanti : ConjugationAntiInvariantWitness587 a)
    (σ : L ≃ₐ[K] L) :
    Commute (conjugationLift587 hanti) (restrictKAutToReal587 σ) := by
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot ℚ K
      (show 587 ∈ ({587} : Set ℕ) by simp)
      (by norm_num : 587 ≠ 0)
  have hroots : (primitiveRoots 587 K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by norm_num : 0 < 587)).2 hζ⟩
  let η : rootsOfUnity 587 K :=
    (autAdjoinRootXPowSubCEquiv hroots hirr.out).symm σ
  have hηpow : (((η : Kˣ) : K)) ^ 587 = 1 :=
    by simpa using (mem_rootsOfUnity' _ _).mp η.prop
  have hσroot :
      σ (root (X ^ 587 - C (a : K))) =
        algebraMap K L (((η : Kˣ) : K)) *
          root (X ^ 587 - C (a : K)) := by
    simpa only [η, Units.smul_def, Algebra.smul_def] using
      (autAdjoinRootXPowSubCEquiv_symm_smul hroots hirr.out σ).symm
  exact conjugationLift587_commute_kAut_of_root_eq
    (a := a) hanti
    (complexConj_eq_inv_of_pow_eq_one587 hζ hηpow)
    σ hσroot

end Lift

end

end Fermat.Irregular.KummerConjugationDescent587
