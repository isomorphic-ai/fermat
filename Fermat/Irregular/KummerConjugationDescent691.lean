import Fermat.Irregular.TakagiFurtwangler691
import Fermat.Irregular.CyclotomicDiscriminantPrime
import Mathlib.NumberTheory.NumberField.CMField

/-!
# Conjugation descent for degree-691 Kummer extensions

This file records the extra symmetry needed to descend a Kummer extension
of the full `691`th cyclotomic field to its maximal real subfield.

For a radicand `a`, the relevant condition is anti-invariance modulo
`691`th powers.  We use the convenient exact form

`a * conj(a) = b ^ 691`, with `conj(b) = b`.

If `α ^ 691 = a`, this identity lets complex conjugation lift by
`α ↦ b / α`.  The lift is an involution.  The historical radicand
`x * conj(x) ^ 690` has this form with real norm root `x * conj(x)`.
-/

open scoped NumberField

namespace Fermat.Irregular.KummerConjugationDescent691

noncomputable section

open Polynomial AdjoinRoot
open Fermat.Irregular.TakagiFurtwangler691

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {691} ℚ K]

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 691) K (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Exact anti-invariance data for a degree-`691` Kummer radicand.

The equation says that the class of `a` in `Kˣ / (Kˣ)⁵⁸⁷` is sent to its
inverse by complex conjugation.  Requiring the displayed root `b` to be
real makes the lifted conjugation literally involutive. -/
structure ConjugationAntiInvariantWitness691 (a : 𝓞 K) where
  realNormRoot : K
  realNormRoot_fixed :
    NumberField.IsCMField.complexConj K realNormRoot = realNormRoot
  norm_eq :
    (a : K) * NumberField.IsCMField.complexConj K (a : K) =
      realNormRoot ^ 691

/-- The conjugate-pair radicand occurring in Vandiver's equation (7a). -/
noncomputable def conjugatePairRadicand691 (x : 𝓞 K) : 𝓞 K :=
  x * NumberField.IsCMField.ringOfIntegersComplexConj K x ^ 690

/-- A conjugate-pair radicand is anti-invariant, with real norm root
`x * conj(x)`. -/
noncomputable def conjugatePairAntiInvariantWitness691 (x : 𝓞 K) :
    ConjugationAntiInvariantWitness691 (conjugatePairRadicand691 x) where
  realNormRoot :=
    (x : K) * NumberField.IsCMField.complexConj K (x : K)
  realNormRoot_fixed := by
    rw [map_mul, NumberField.IsCMField.complexConj_apply_apply]
    ring
  norm_eq := by
    change
      ((x : K) * NumberField.IsCMField.complexConj K (x : K) ^ 690) *
          NumberField.IsCMField.complexConj K
            ((x : K) * NumberField.IsCMField.complexConj K (x : K) ^ 690) =
        ((x : K) * NumberField.IsCMField.complexConj K (x : K)) ^ 691
    rw [map_mul, map_pow,
      NumberField.IsCMField.complexConj_apply_apply]
    ring

/-- The historical radicand satisfies the exact anti-invariance identity,
displayed separately for later proof generators to reuse. -/
theorem conjugatePairRadicand691_norm_eq (x : 𝓞 K) :
    (conjugatePairRadicand691 x : K) *
        NumberField.IsCMField.complexConj K
          (conjugatePairRadicand691 x : K) =
      (((x : K) * NumberField.IsCMField.complexConj K (x : K)) ^ 691) :=
  (conjugatePairAntiInvariantWitness691 x).norm_eq

section Lift

variable {a : 𝓞 K}
  [hirr : Fact (Irreducible (X ^ 691 - C (a : K)))]

local notation3 "L" => KummerExtension691 K a

local instance : Field L := AdjoinRoot.instField
local instance : Algebra K L := inferInstance
local instance : Algebra K⁺ L := Algebra.restrictScalars K⁺ K L

omit [NumberField K] [IsCyclotomicExtension {691} ℚ K] in
/-- Irreducibility of the Kummer polynomial forces a nonzero radicand. -/
lemma radicand_ne_zero_of_irreducible691 : (a : K) ≠ 0 := by
  intro ha
  have hnotpow :=
    (X_pow_sub_C_irreducible_iff_of_prime
      (show Nat.Prime 691 by norm_num)).mp hirr.out
  exact hnotpow 0 (by simp [ha])

/-- The coefficient embedding obtained by applying complex conjugation
before embedding `K` into its Kummer extension. -/
noncomputable def conjugationCoefficientHom691 :
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
lemma conjugationCoefficientHom691_apply (x : K) :
    conjugationCoefficientHom691 (a := a) x =
      algebraMap K L (NumberField.IsCMField.complexConj K x) :=
  rfl

/-- The desired image `b / α` of the distinguished Kummer root. -/
noncomputable def conjugationRootImage691
    (hanti : ConjugationAntiInvariantWitness691 a) : L :=
  algebraMap K L hanti.realNormRoot /
    root (X ^ 691 - C (a : K))

lemma realNormRoot_ne_zero691
    (hanti : ConjugationAntiInvariantWitness691 a) :
    hanti.realNormRoot ≠ 0 := by
  intro hb
  have hprod :
      (a : K) * NumberField.IsCMField.complexConj K (a : K) ≠ 0 :=
    mul_ne_zero (radicand_ne_zero_of_irreducible691 (a := a))
      ((map_ne_zero (NumberField.IsCMField.complexConj K)).mpr
        (radicand_ne_zero_of_irreducible691 (a := a)))
  apply hprod
  rw [hanti.norm_eq, hb, zero_pow (by norm_num : 691 ≠ 0)]

lemma conjugationRootImage691_pow
    (hanti : ConjugationAntiInvariantWitness691 a) :
    conjugationRootImage691 hanti ^ 691 =
      algebraMap K L
        (NumberField.IsCMField.complexConj K (a : K)) := by
  rw [conjugationRootImage691, div_pow, ← map_pow, ← hanti.norm_eq,
    map_mul, kummerExtension691_root_pow]
  exact mul_div_cancel_left₀ _
    ((map_ne_zero (algebraMap K L)).mpr
      (radicand_ne_zero_of_irreducible691 (a := a)))

lemma conjugationRootImage691_isRoot
    (hanti : ConjugationAntiInvariantWitness691 a) :
    (X ^ 691 - C (a : K)).eval₂
        (conjugationCoefficientHom691 (a := a))
        (conjugationRootImage691 hanti) = 0 := by
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
    conjugationRootImage691_pow (a := a)]
  change
    algebraMap K L (NumberField.IsCMField.complexConj K (a : K)) -
        algebraMap K L (NumberField.IsCMField.complexConj K (a : K)) = 0
  exact sub_self _

/-- The semilinear lift of complex conjugation to the Kummer extension.
It is first constructed as a `K⁺`-algebra endomorphism; involutivity below
upgrades it to an automorphism. -/
noncomputable def conjugationLiftAlgHom691
    (hanti : ConjugationAntiInvariantWitness691 a) :
    L →ₐ[K⁺] L :=
  AdjoinRoot.liftAlgHom (X ^ 691 - C (a : K))
    (conjugationCoefficientHom691 (a := a))
    (conjugationRootImage691 hanti)
    (conjugationRootImage691_isRoot (a := a) hanti)

@[simp]
lemma conjugationLiftAlgHom691_algebraMap
    (hanti : ConjugationAntiInvariantWitness691 a) (x : K) :
    conjugationLiftAlgHom691 hanti (algebraMap K L x) =
      algebraMap K L (NumberField.IsCMField.complexConj K x) := by
  exact AdjoinRoot.liftAlgHom_of
    (X ^ 691 - C (a : K))
    (conjugationCoefficientHom691 (a := a))
    (conjugationRootImage691 hanti)
    (conjugationRootImage691_isRoot (a := a) hanti) x

@[simp]
lemma conjugationLiftAlgHom691_root
    (hanti : ConjugationAntiInvariantWitness691 a) :
    conjugationLiftAlgHom691 hanti
        (root (X ^ 691 - C (a : K))) =
      conjugationRootImage691 hanti := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

theorem conjugationLiftAlgHom691_apply_apply
    (hanti : ConjugationAntiInvariantWitness691 a) (x : L) :
    conjugationLiftAlgHom691 hanti
        (conjugationLiftAlgHom691 hanti x) = x := by
  have hsq :
      (conjugationLiftAlgHom691 hanti).comp
          (conjugationLiftAlgHom691 hanti) =
        AlgHom.id K⁺ L := by
    apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro y
      change
        conjugationLiftAlgHom691 hanti
            (conjugationLiftAlgHom691 hanti (algebraMap K L y)) =
          algebraMap K L y
      rw [conjugationLiftAlgHom691_algebraMap,
        conjugationLiftAlgHom691_algebraMap,
        NumberField.IsCMField.complexConj_apply_apply]
    · change
        conjugationLiftAlgHom691 hanti
            (conjugationLiftAlgHom691 hanti
              (root (X ^ 691 - C (a : K)))) =
          root (X ^ 691 - C (a : K))
      rw [conjugationLiftAlgHom691_root,
        conjugationRootImage691, map_div₀,
        conjugationLiftAlgHom691_algebraMap,
        conjugationLiftAlgHom691_root,
        conjugationRootImage691,
        hanti.realNormRoot_fixed]
      exact div_div_cancel₀
        ((map_ne_zero (algebraMap K L)).mpr
          (realNormRoot_ne_zero691 (a := a) hanti))
  exact DFunLike.congr_fun hsq x

/-- The involutive `K⁺`-automorphism of the Kummer extension extending
complex conjugation and sending `α` to `b / α`. -/
noncomputable def conjugationLift691
    (hanti : ConjugationAntiInvariantWitness691 a) :
    L ≃ₐ[K⁺] L :=
  AlgEquiv.ofBijective (conjugationLiftAlgHom691 hanti)
    (Function.Involutive.bijective
      (conjugationLiftAlgHom691_apply_apply (a := a) hanti))

@[simp]
theorem conjugationLift691_algebraMap
    (hanti : ConjugationAntiInvariantWitness691 a) (x : K) :
    conjugationLift691 hanti (algebraMap K L x) =
      algebraMap K L (NumberField.IsCMField.complexConj K x) :=
  conjugationLiftAlgHom691_algebraMap (a := a) hanti x

@[simp]
theorem conjugationLift691_root
    (hanti : ConjugationAntiInvariantWitness691 a) :
    conjugationLift691 hanti
        (root (X ^ 691 - C (a : K))) =
      algebraMap K L hanti.realNormRoot /
        root (X ^ 691 - C (a : K)) :=
  conjugationLiftAlgHom691_root (a := a) hanti

@[simp]
theorem conjugationLift691_apply_apply
    (hanti : ConjugationAntiInvariantWitness691 a) (x : L) :
    conjugationLift691 hanti
        (conjugationLift691 hanti x) = x :=
  conjugationLiftAlgHom691_apply_apply (a := a) hanti x

theorem conjugationLift691_sq
    (hanti : ConjugationAntiInvariantWitness691 a) :
    conjugationLift691 hanti ^ 2 = 1 := by
  ext x
  exact conjugationLift691_apply_apply (a := a) hanti x

/-- Regard a `K`-automorphism of the Kummer extension as an automorphism
over the maximal real subfield.  This explicit wrapper avoids imposing a
particular `IsScalarTower` instance on downstream files. -/
noncomputable def restrictKAutToReal691 (σ : L ≃ₐ[K] L) : L ≃ₐ[K⁺] L where
  __ := σ
  commutes' x := by
    change σ (algebraMap K L (algebraMap K⁺ K x)) =
      algebraMap K L (algebraMap K⁺ K x)
    exact σ.commutes _

omit [NumberField K] [IsCyclotomicExtension {691} ℚ K] in
@[simp]
theorem restrictKAutToReal691_apply (σ : L ≃ₐ[K] L) (x : L) :
    restrictKAutToReal691 σ x = σ x :=
  rfl

/-- Complex conjugation inverts every `691`th root of unity in the
cyclotomic coefficient field. -/
theorem complexConj_eq_inv_of_pow_eq_one691
    {ζ η : K} (hζ : IsPrimitiveRoot ζ 691) (hη : η ^ 691 = 1) :
    NumberField.IsCMField.complexConj K η = η⁻¹ := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
  rw [map_pow,
    Fermat.Irregular.CyclotomicDiscriminantPrime.complexConj_zeta_inv hζ]
  exact inv_pow ζ i

/-- The lifted conjugation commutes pointwise with a Kummer deck
transformation whose root multiplier is inverted by conjugation. -/
theorem conjugationLift691_apply_kAut_of_root_eq
    (hanti : ConjugationAntiInvariantWitness691 a)
    {η : K}
    (hconjη : NumberField.IsCMField.complexConj K η = η⁻¹)
    (σ : L ≃ₐ[K] L)
    (hσroot :
      σ (root (X ^ 691 - C (a : K))) =
        algebraMap K L η * root (X ^ 691 - C (a : K)))
    (x : L) :
    conjugationLift691 hanti (σ x) =
      σ (conjugationLift691 hanti x) := by
  have hcomp :
      (conjugationLift691 hanti).toAlgHom.comp
          (restrictKAutToReal691 σ).toAlgHom =
        (restrictKAutToReal691 σ).toAlgHom.comp
          (conjugationLift691 hanti).toAlgHom := by
    apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro y
      change
        conjugationLift691 hanti
            (σ (algebraMap K L y)) =
          σ (conjugationLift691 hanti (algebraMap K L y))
      simp only [σ.commutes, conjugationLift691_algebraMap]
    · change
        conjugationLift691 hanti
            (σ (root (X ^ 691 - C (a : K)))) =
          σ (conjugationLift691 hanti
            (root (X ^ 691 - C (a : K))))
      rw [hσroot, map_mul, conjugationLift691_algebraMap,
        conjugationLift691_root, hconjη, map_div₀, σ.commutes, hσroot]
      simp only [map_inv₀, div_eq_mul_inv, mul_inv_rev]
      ring
  exact DFunLike.congr_fun hcomp x

/-- Group-theoretic form of
`conjugationLift691_apply_kAut_of_root_eq`. -/
theorem conjugationLift691_commute_kAut_of_root_eq
    (hanti : ConjugationAntiInvariantWitness691 a)
    {η : K}
    (hconjη : NumberField.IsCMField.complexConj K η = η⁻¹)
    (σ : L ≃ₐ[K] L)
    (hσroot :
      σ (root (X ^ 691 - C (a : K))) =
        algebraMap K L η * root (X ^ 691 - C (a : K))) :
    Commute (conjugationLift691 hanti) (restrictKAutToReal691 σ) := by
  apply DFunLike.ext _ _
  intro x
  exact conjugationLift691_apply_kAut_of_root_eq
    (a := a) hanti hconjη σ hσroot x

/-- The lifted conjugation commutes with every deck transformation of the
degree-`691` Kummer extension. -/
theorem conjugationLift691_commute_kAut
    (hanti : ConjugationAntiInvariantWitness691 a)
    (σ : L ≃ₐ[K] L) :
    Commute (conjugationLift691 hanti) (restrictKAutToReal691 σ) := by
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot ℚ K
      (show 691 ∈ ({691} : Set ℕ) by simp)
      (by norm_num : 691 ≠ 0)
  have hroots : (primitiveRoots 691 K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by norm_num : 0 < 691)).2 hζ⟩
  let η : rootsOfUnity 691 K :=
    (autAdjoinRootXPowSubCEquiv hroots hirr.out).symm σ
  have hηpow : (((η : Kˣ) : K)) ^ 691 = 1 :=
    by simpa using (mem_rootsOfUnity' _ _).mp η.prop
  have hσroot :
      σ (root (X ^ 691 - C (a : K))) =
        algebraMap K L (((η : Kˣ) : K)) *
          root (X ^ 691 - C (a : K)) := by
    simpa only [η, Units.smul_def, Algebra.smul_def] using
      (autAdjoinRootXPowSubCEquiv_symm_smul hroots hirr.out σ).symm
  exact conjugationLift691_commute_kAut_of_root_eq
    (a := a) hanti
    (complexConj_eq_inv_of_pow_eq_one691 hζ hηpow)
    σ hσroot

end Lift

end

end Fermat.Irregular.KummerConjugationDescent691
