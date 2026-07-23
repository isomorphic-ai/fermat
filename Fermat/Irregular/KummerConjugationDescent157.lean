import Fermat.Irregular.TakagiFurtwangler157
import Fermat.Irregular.CyclotomicDiscriminantPrime
import Mathlib.NumberTheory.NumberField.CMField

/-!
# Conjugation descent for degree-157 Kummer extensions

This file records the extra symmetry needed to descend a Kummer extension
of the full `157`th cyclotomic field to its maximal real subfield.

For a radicand `a`, the relevant condition is anti-invariance modulo
`157`th powers.  We use the convenient exact form

`a * conj(a) = b ^ 157`, with `conj(b) = b`.

If `α ^ 157 = a`, this identity lets complex conjugation lift by
`α ↦ b / α`.  The lift is an involution.  The historical radicand
`x * conj(x) ^ 156` has this form with real norm root `x * conj(x)`.
-/

open scoped NumberField

namespace Fermat.Irregular.KummerConjugationDescent157

noncomputable section

open Polynomial AdjoinRoot
open Fermat.Irregular.TakagiFurtwangler157

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {157} ℚ K]

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 157) K (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Exact anti-invariance data for a degree-`157` Kummer radicand.

The equation says that the class of `a` in `Kˣ / (Kˣ)³⁷` is sent to its
inverse by complex conjugation.  Requiring the displayed root `b` to be
real makes the lifted conjugation literally involutive. -/
structure ConjugationAntiInvariantWitness157 (a : 𝓞 K) where
  realNormRoot : K
  realNormRoot_fixed :
    NumberField.IsCMField.complexConj K realNormRoot = realNormRoot
  norm_eq :
    (a : K) * NumberField.IsCMField.complexConj K (a : K) =
      realNormRoot ^ 157

/-- The conjugate-pair radicand occurring in Vandiver's equation (7a). -/
noncomputable def conjugatePairRadicand157 (x : 𝓞 K) : 𝓞 K :=
  x * NumberField.IsCMField.ringOfIntegersComplexConj K x ^ 156

/-- A conjugate-pair radicand is anti-invariant, with real norm root
`x * conj(x)`. -/
noncomputable def conjugatePairAntiInvariantWitness157 (x : 𝓞 K) :
    ConjugationAntiInvariantWitness157 (conjugatePairRadicand157 x) where
  realNormRoot :=
    (x : K) * NumberField.IsCMField.complexConj K (x : K)
  realNormRoot_fixed := by
    rw [map_mul, NumberField.IsCMField.complexConj_apply_apply]
    ring
  norm_eq := by
    change
      ((x : K) * NumberField.IsCMField.complexConj K (x : K) ^ 156) *
          NumberField.IsCMField.complexConj K
            ((x : K) * NumberField.IsCMField.complexConj K (x : K) ^ 156) =
        ((x : K) * NumberField.IsCMField.complexConj K (x : K)) ^ 157
    rw [map_mul, map_pow,
      NumberField.IsCMField.complexConj_apply_apply]
    ring

/-- The historical radicand satisfies the exact anti-invariance identity,
displayed separately for later proof generators to reuse. -/
theorem conjugatePairRadicand157_norm_eq (x : 𝓞 K) :
    (conjugatePairRadicand157 x : K) *
        NumberField.IsCMField.complexConj K
          (conjugatePairRadicand157 x : K) =
      (((x : K) * NumberField.IsCMField.complexConj K (x : K)) ^ 157) :=
  (conjugatePairAntiInvariantWitness157 x).norm_eq

section Lift

variable {a : 𝓞 K}
  [hirr : Fact (Irreducible (X ^ 157 - C (a : K)))]

local notation3 "L" => KummerExtension157 K a

local instance : Field L := AdjoinRoot.instField
local instance : Algebra K L := inferInstance
local instance : Algebra K⁺ L := Algebra.restrictScalars K⁺ K L

omit [NumberField K] [IsCyclotomicExtension {157} ℚ K] in
/-- Irreducibility of the Kummer polynomial forces a nonzero radicand. -/
lemma radicand_ne_zero_of_irreducible157 : (a : K) ≠ 0 := by
  intro ha
  have hnotpow :=
    (X_pow_sub_C_irreducible_iff_of_prime
      (show Nat.Prime 157 by norm_num)).mp hirr.out
  exact hnotpow 0 (by simp [ha])

/-- The coefficient embedding obtained by applying complex conjugation
before embedding `K` into its Kummer extension. -/
noncomputable def conjugationCoefficientHom157 :
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
lemma conjugationCoefficientHom157_apply (x : K) :
    conjugationCoefficientHom157 (a := a) x =
      algebraMap K L (NumberField.IsCMField.complexConj K x) :=
  rfl

/-- The desired image `b / α` of the distinguished Kummer root. -/
noncomputable def conjugationRootImage157
    (hanti : ConjugationAntiInvariantWitness157 a) : L :=
  algebraMap K L hanti.realNormRoot /
    root (X ^ 157 - C (a : K))

lemma realNormRoot_ne_zero157
    (hanti : ConjugationAntiInvariantWitness157 a) :
    hanti.realNormRoot ≠ 0 := by
  intro hb
  have hprod :
      (a : K) * NumberField.IsCMField.complexConj K (a : K) ≠ 0 :=
    mul_ne_zero (radicand_ne_zero_of_irreducible157 (a := a))
      ((map_ne_zero (NumberField.IsCMField.complexConj K)).mpr
        (radicand_ne_zero_of_irreducible157 (a := a)))
  apply hprod
  rw [hanti.norm_eq, hb, zero_pow (by norm_num : 157 ≠ 0)]

lemma conjugationRootImage157_pow
    (hanti : ConjugationAntiInvariantWitness157 a) :
    conjugationRootImage157 hanti ^ 157 =
      algebraMap K L
        (NumberField.IsCMField.complexConj K (a : K)) := by
  rw [conjugationRootImage157, div_pow, ← map_pow, ← hanti.norm_eq,
    map_mul, kummerExtension157_root_pow]
  exact mul_div_cancel_left₀ _
    ((map_ne_zero (algebraMap K L)).mpr
      (radicand_ne_zero_of_irreducible157 (a := a)))

lemma conjugationRootImage157_isRoot
    (hanti : ConjugationAntiInvariantWitness157 a) :
    (X ^ 157 - C (a : K)).eval₂
        (conjugationCoefficientHom157 (a := a))
        (conjugationRootImage157 hanti) = 0 := by
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
    conjugationRootImage157_pow (a := a)]
  change
    algebraMap K L (NumberField.IsCMField.complexConj K (a : K)) -
        algebraMap K L (NumberField.IsCMField.complexConj K (a : K)) = 0
  exact sub_self _

/-- The semilinear lift of complex conjugation to the Kummer extension.
It is first constructed as a `K⁺`-algebra endomorphism; involutivity below
upgrades it to an automorphism. -/
noncomputable def conjugationLiftAlgHom157
    (hanti : ConjugationAntiInvariantWitness157 a) :
    L →ₐ[K⁺] L :=
  AdjoinRoot.liftAlgHom (X ^ 157 - C (a : K))
    (conjugationCoefficientHom157 (a := a))
    (conjugationRootImage157 hanti)
    (conjugationRootImage157_isRoot (a := a) hanti)

@[simp]
lemma conjugationLiftAlgHom157_algebraMap
    (hanti : ConjugationAntiInvariantWitness157 a) (x : K) :
    conjugationLiftAlgHom157 hanti (algebraMap K L x) =
      algebraMap K L (NumberField.IsCMField.complexConj K x) := by
  exact AdjoinRoot.liftAlgHom_of
    (X ^ 157 - C (a : K))
    (conjugationCoefficientHom157 (a := a))
    (conjugationRootImage157 hanti)
    (conjugationRootImage157_isRoot (a := a) hanti) x

@[simp]
lemma conjugationLiftAlgHom157_root
    (hanti : ConjugationAntiInvariantWitness157 a) :
    conjugationLiftAlgHom157 hanti
        (root (X ^ 157 - C (a : K))) =
      conjugationRootImage157 hanti := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

theorem conjugationLiftAlgHom157_apply_apply
    (hanti : ConjugationAntiInvariantWitness157 a) (x : L) :
    conjugationLiftAlgHom157 hanti
        (conjugationLiftAlgHom157 hanti x) = x := by
  have hsq :
      (conjugationLiftAlgHom157 hanti).comp
          (conjugationLiftAlgHom157 hanti) =
        AlgHom.id K⁺ L := by
    apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro y
      change
        conjugationLiftAlgHom157 hanti
            (conjugationLiftAlgHom157 hanti (algebraMap K L y)) =
          algebraMap K L y
      rw [conjugationLiftAlgHom157_algebraMap,
        conjugationLiftAlgHom157_algebraMap,
        NumberField.IsCMField.complexConj_apply_apply]
    · change
        conjugationLiftAlgHom157 hanti
            (conjugationLiftAlgHom157 hanti
              (root (X ^ 157 - C (a : K)))) =
          root (X ^ 157 - C (a : K))
      rw [conjugationLiftAlgHom157_root,
        conjugationRootImage157, map_div₀,
        conjugationLiftAlgHom157_algebraMap,
        conjugationLiftAlgHom157_root,
        conjugationRootImage157,
        hanti.realNormRoot_fixed]
      exact div_div_cancel₀
        ((map_ne_zero (algebraMap K L)).mpr
          (realNormRoot_ne_zero157 (a := a) hanti))
  exact DFunLike.congr_fun hsq x

/-- The involutive `K⁺`-automorphism of the Kummer extension extending
complex conjugation and sending `α` to `b / α`. -/
noncomputable def conjugationLift157
    (hanti : ConjugationAntiInvariantWitness157 a) :
    L ≃ₐ[K⁺] L :=
  AlgEquiv.ofBijective (conjugationLiftAlgHom157 hanti)
    (Function.Involutive.bijective
      (conjugationLiftAlgHom157_apply_apply (a := a) hanti))

@[simp]
theorem conjugationLift157_algebraMap
    (hanti : ConjugationAntiInvariantWitness157 a) (x : K) :
    conjugationLift157 hanti (algebraMap K L x) =
      algebraMap K L (NumberField.IsCMField.complexConj K x) :=
  conjugationLiftAlgHom157_algebraMap (a := a) hanti x

@[simp]
theorem conjugationLift157_root
    (hanti : ConjugationAntiInvariantWitness157 a) :
    conjugationLift157 hanti
        (root (X ^ 157 - C (a : K))) =
      algebraMap K L hanti.realNormRoot /
        root (X ^ 157 - C (a : K)) :=
  conjugationLiftAlgHom157_root (a := a) hanti

@[simp]
theorem conjugationLift157_apply_apply
    (hanti : ConjugationAntiInvariantWitness157 a) (x : L) :
    conjugationLift157 hanti
        (conjugationLift157 hanti x) = x :=
  conjugationLiftAlgHom157_apply_apply (a := a) hanti x

theorem conjugationLift157_sq
    (hanti : ConjugationAntiInvariantWitness157 a) :
    conjugationLift157 hanti ^ 2 = 1 := by
  ext x
  exact conjugationLift157_apply_apply (a := a) hanti x

/-- Regard a `K`-automorphism of the Kummer extension as an automorphism
over the maximal real subfield.  This explicit wrapper avoids imposing a
particular `IsScalarTower` instance on downstream files. -/
noncomputable def restrictKAutToReal157 (σ : L ≃ₐ[K] L) : L ≃ₐ[K⁺] L where
  __ := σ
  commutes' x := by
    change σ (algebraMap K L (algebraMap K⁺ K x)) =
      algebraMap K L (algebraMap K⁺ K x)
    exact σ.commutes _

omit [NumberField K] [IsCyclotomicExtension {157} ℚ K] in
@[simp]
theorem restrictKAutToReal157_apply (σ : L ≃ₐ[K] L) (x : L) :
    restrictKAutToReal157 σ x = σ x :=
  rfl

/-- Complex conjugation inverts every `157`th root of unity in the
cyclotomic coefficient field. -/
theorem complexConj_eq_inv_of_pow_eq_one157
    {ζ η : K} (hζ : IsPrimitiveRoot ζ 157) (hη : η ^ 157 = 1) :
    NumberField.IsCMField.complexConj K η = η⁻¹ := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
  rw [map_pow,
    Fermat.Irregular.CyclotomicDiscriminantPrime.complexConj_zeta_inv hζ]
  exact inv_pow ζ i

/-- The lifted conjugation commutes pointwise with a Kummer deck
transformation whose root multiplier is inverted by conjugation. -/
theorem conjugationLift157_apply_kAut_of_root_eq
    (hanti : ConjugationAntiInvariantWitness157 a)
    {η : K}
    (hconjη : NumberField.IsCMField.complexConj K η = η⁻¹)
    (σ : L ≃ₐ[K] L)
    (hσroot :
      σ (root (X ^ 157 - C (a : K))) =
        algebraMap K L η * root (X ^ 157 - C (a : K)))
    (x : L) :
    conjugationLift157 hanti (σ x) =
      σ (conjugationLift157 hanti x) := by
  have hcomp :
      (conjugationLift157 hanti).toAlgHom.comp
          (restrictKAutToReal157 σ).toAlgHom =
        (restrictKAutToReal157 σ).toAlgHom.comp
          (conjugationLift157 hanti).toAlgHom := by
    apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro y
      change
        conjugationLift157 hanti
            (σ (algebraMap K L y)) =
          σ (conjugationLift157 hanti (algebraMap K L y))
      simp only [σ.commutes, conjugationLift157_algebraMap]
    · change
        conjugationLift157 hanti
            (σ (root (X ^ 157 - C (a : K)))) =
          σ (conjugationLift157 hanti
            (root (X ^ 157 - C (a : K))))
      rw [hσroot, map_mul, conjugationLift157_algebraMap,
        conjugationLift157_root, hconjη, map_div₀, σ.commutes, hσroot]
      simp only [map_inv₀, div_eq_mul_inv, mul_inv_rev]
      ring
  exact DFunLike.congr_fun hcomp x

/-- Group-theoretic form of
`conjugationLift157_apply_kAut_of_root_eq`. -/
theorem conjugationLift157_commute_kAut_of_root_eq
    (hanti : ConjugationAntiInvariantWitness157 a)
    {η : K}
    (hconjη : NumberField.IsCMField.complexConj K η = η⁻¹)
    (σ : L ≃ₐ[K] L)
    (hσroot :
      σ (root (X ^ 157 - C (a : K))) =
        algebraMap K L η * root (X ^ 157 - C (a : K))) :
    Commute (conjugationLift157 hanti) (restrictKAutToReal157 σ) := by
  apply DFunLike.ext _ _
  intro x
  exact conjugationLift157_apply_kAut_of_root_eq
    (a := a) hanti hconjη σ hσroot x

/-- The lifted conjugation commutes with every deck transformation of the
degree-`157` Kummer extension. -/
theorem conjugationLift157_commute_kAut
    (hanti : ConjugationAntiInvariantWitness157 a)
    (σ : L ≃ₐ[K] L) :
    Commute (conjugationLift157 hanti) (restrictKAutToReal157 σ) := by
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot ℚ K
      (show 157 ∈ ({157} : Set ℕ) by simp)
      (by norm_num : 157 ≠ 0)
  have hroots : (primitiveRoots 157 K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by norm_num : 0 < 157)).2 hζ⟩
  let η : rootsOfUnity 157 K :=
    (autAdjoinRootXPowSubCEquiv hroots hirr.out).symm σ
  have hηpow : (((η : Kˣ) : K)) ^ 157 = 1 :=
    by simpa using (mem_rootsOfUnity' _ _).mp η.prop
  have hσroot :
      σ (root (X ^ 157 - C (a : K))) =
        algebraMap K L (((η : Kˣ) : K)) *
          root (X ^ 157 - C (a : K)) := by
    simpa only [η, Units.smul_def, Algebra.smul_def] using
      (autAdjoinRootXPowSubCEquiv_symm_smul hroots hirr.out σ).symm
  exact conjugationLift157_commute_kAut_of_root_eq
    (a := a) hanti
    (complexConj_eq_inv_of_pow_eq_one157 hζ hηpow)
    σ hσroot

end Lift

end

end Fermat.Irregular.KummerConjugationDescent157
