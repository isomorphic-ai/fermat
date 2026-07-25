import Fermat.Irregular.TakagiFurtwanglerPrime
import Fermat.Irregular.CyclotomicDiscriminantPrime
import Mathlib.NumberTheory.NumberField.CMField

/-!
# Prime-generic conjugation descent for Kummer extensions

For a Kummer radicand `a`, exact anti-invariance means

`a * conj(a) = b ^ p`, with `conj(b) = b`.

If `α ^ p = a`, this identity lifts complex conjugation by
`α ↦ b / α`.  The lift is involutive and commutes with every Kummer
deck transformation.  The conjugate-pair radicand
`x * conj(x) ^ (p - 1)` supplies the canonical witness.
-/

open scoped NumberField

namespace Fermat.Irregular.KummerConjugationDescentPrime

noncomputable section

open Polynomial AdjoinRoot
open Fermat.Irregular.TakagiFurtwanglerPrime

variable {K : Type*} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Exact anti-invariance data for a degree-`p` Kummer radicand.

The equation says that the class of `a` modulo `p`-th powers is sent to its
inverse by complex conjugation.  Requiring the displayed root `b` to be
real makes the lifted conjugation literally involutive. -/
structure ConjugationAntiInvariantWitness (a : 𝓞 K) where
  realNormRoot : K
  realNormRoot_fixed :
    NumberField.IsCMField.complexConj K realNormRoot = realNormRoot
  norm_eq :
    (a : K) * NumberField.IsCMField.complexConj K (a : K) =
      realNormRoot ^ p

/-- The conjugate-pair radicand occurring in Vandiver's equation (7a). -/
noncomputable def conjugatePairRadicand (x : 𝓞 K) : 𝓞 K :=
  x * NumberField.IsCMField.ringOfIntegersComplexConj K x ^ (p - 1)

/-- A conjugate-pair radicand is anti-invariant, with real norm root
`x * conj(x)`. -/
noncomputable def conjugatePairAntiInvariantWitness (x : 𝓞 K) :
    ConjugationAntiInvariantWitness (p := p)
      (conjugatePairRadicand (p := p) x) where
  realNormRoot :=
    (x : K) * NumberField.IsCMField.complexConj K (x : K)
  realNormRoot_fixed := by
    rw [map_mul, NumberField.IsCMField.complexConj_apply_apply]
    ring
  norm_eq := by
    change
      ((x : K) * NumberField.IsCMField.complexConj K (x : K) ^ (p - 1)) *
          NumberField.IsCMField.complexConj K
            ((x : K) * NumberField.IsCMField.complexConj K (x : K) ^ (p - 1)) =
        ((x : K) * NumberField.IsCMField.complexConj K (x : K)) ^ p
    rw [map_mul, map_pow,
      NumberField.IsCMField.complexConj_apply_apply]
    rw [mul_pow]
    rw [show (x : K) ^ p = (x : K) ^ (p - 1) * (x : K) by
      rw [← pow_succ]
      congr 1
      exact (Nat.sub_add_cancel (Fact.out : Nat.Prime p).one_le).symm]
    rw [show NumberField.IsCMField.complexConj K (x : K) ^ p =
        NumberField.IsCMField.complexConj K (x : K) ^ (p - 1) *
          NumberField.IsCMField.complexConj K (x : K) by
      rw [← pow_succ]
      congr 1
      exact (Nat.sub_add_cancel (Fact.out : Nat.Prime p).one_le).symm]
    ring

/-- The historical radicand satisfies the exact anti-invariance identity,
displayed separately for later proof generators to reuse. -/
theorem conjugatePairRadicand_norm_eq (x : 𝓞 K) :
    (conjugatePairRadicand (p := p) x : K) *
        NumberField.IsCMField.complexConj K
          (conjugatePairRadicand (p := p) x : K) =
      (((x : K) * NumberField.IsCMField.complexConj K (x : K)) ^ p) :=
  (conjugatePairAntiInvariantWitness (p := p) x).norm_eq

section Lift

variable {a : 𝓞 K}
  [hirr : Fact (Irreducible (X ^ p - C (a : K)))]

local notation3 "L" => KummerExtension (p := p) K a

local instance : Field L := AdjoinRoot.instField
local instance : Algebra K L := inferInstance
local instance : Algebra K⁺ L := Algebra.restrictScalars K⁺ K L

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
include hirr in
/-- Irreducibility of the Kummer polynomial forces a nonzero radicand. -/
lemma radicand_ne_zero_of_irreducible : (a : K) ≠ 0 := by
  intro ha
  have hnotpow :=
    (X_pow_sub_C_irreducible_iff_of_prime
      (Fact.out : Nat.Prime p)).mp hirr.out
  exact hnotpow 0 (by
    rw [zero_pow (Fact.out : Nat.Prime p).ne_zero, ha])

/-- The coefficient embedding obtained by applying complex conjugation
before embedding `K` into its Kummer extension. -/
noncomputable def conjugationCoefficientHom :
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
lemma conjugationCoefficientHom_apply (x : K) :
    conjugationCoefficientHom (a := a) x =
      algebraMap K L (NumberField.IsCMField.complexConj K x) :=
  rfl

/-- The desired image `b / α` of the distinguished Kummer root. -/
noncomputable def conjugationRootImage
    (hanti : ConjugationAntiInvariantWitness (p := p) a) : L :=
  algebraMap K L hanti.realNormRoot /
    root (X ^ p - C (a : K))

lemma realNormRoot_ne_zero
    (hanti : ConjugationAntiInvariantWitness (p := p) a) :
    hanti.realNormRoot ≠ 0 := by
  intro hb
  have hprod :
      (a : K) * NumberField.IsCMField.complexConj K (a : K) ≠ 0 :=
    mul_ne_zero (radicand_ne_zero_of_irreducible (p := p) (a := a))
      ((map_ne_zero (NumberField.IsCMField.complexConj K)).mpr
        (radicand_ne_zero_of_irreducible (p := p) (a := a)))
  apply hprod
  rw [hanti.norm_eq, hb,
    zero_pow (Fact.out : Nat.Prime p).ne_zero]

lemma conjugationRootImage_pow
    (hanti : ConjugationAntiInvariantWitness (p := p) a) :
    conjugationRootImage hanti ^ p =
      algebraMap K L
        (NumberField.IsCMField.complexConj K (a : K)) := by
  rw [conjugationRootImage, div_pow, ← map_pow, ← hanti.norm_eq,
    map_mul, kummerExtension_root_pow]
  exact mul_div_cancel_left₀ _
    ((map_ne_zero (algebraMap K L)).mpr
      (radicand_ne_zero_of_irreducible (p := p) (a := a)))

lemma conjugationRootImage_isRoot
    (hanti : ConjugationAntiInvariantWitness (p := p) a) :
    (X ^ p - C (a : K)).eval₂
        (conjugationCoefficientHom (a := a)).toRingHom
        (conjugationRootImage hanti) = 0 := by
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
    conjugationRootImage_pow (a := a)]
  change
    algebraMap K L (NumberField.IsCMField.complexConj K (a : K)) -
        algebraMap K L (NumberField.IsCMField.complexConj K (a : K)) = 0
  exact sub_self _

/-- The semilinear lift of complex conjugation to the Kummer extension.
It is first constructed as a `K⁺`-algebra endomorphism; involutivity below
upgrades it to an automorphism. -/
noncomputable def conjugationLiftAlgHom
    (hanti : ConjugationAntiInvariantWitness (p := p) a) :
    L →ₐ[K⁺] L :=
  AdjoinRoot.liftAlgHom (X ^ p - C (a : K))
    (conjugationCoefficientHom (a := a))
    (conjugationRootImage hanti)
    (conjugationRootImage_isRoot (a := a) hanti)

@[simp]
lemma conjugationLiftAlgHom_algebraMap
    (hanti : ConjugationAntiInvariantWitness (p := p) a) (x : K) :
    conjugationLiftAlgHom hanti (algebraMap K L x) =
      algebraMap K L (NumberField.IsCMField.complexConj K x) := by
  exact AdjoinRoot.liftAlgHom_of
    (X ^ p - C (a : K))
    (conjugationCoefficientHom (a := a))
    (conjugationRootImage hanti)
    (conjugationRootImage_isRoot (a := a) hanti) x

@[simp]
lemma conjugationLiftAlgHom_root
    (hanti : ConjugationAntiInvariantWitness (p := p) a) :
    conjugationLiftAlgHom hanti
        (root (X ^ p - C (a : K))) =
      conjugationRootImage hanti := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

theorem conjugationLiftAlgHom_apply_apply
    (hanti : ConjugationAntiInvariantWitness (p := p) a) (x : L) :
    conjugationLiftAlgHom hanti
        (conjugationLiftAlgHom hanti x) = x := by
  have hsq :
      (conjugationLiftAlgHom hanti).comp
          (conjugationLiftAlgHom hanti) =
        AlgHom.id K⁺ L := by
    apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro y
      change
        conjugationLiftAlgHom hanti
            (conjugationLiftAlgHom hanti (algebraMap K L y)) =
          algebraMap K L y
      rw [conjugationLiftAlgHom_algebraMap,
        conjugationLiftAlgHom_algebraMap,
        NumberField.IsCMField.complexConj_apply_apply]
    · change
        conjugationLiftAlgHom hanti
            (conjugationLiftAlgHom hanti
              (root (X ^ p - C (a : K)))) =
          root (X ^ p - C (a : K))
      rw [conjugationLiftAlgHom_root,
        conjugationRootImage, map_div₀,
        conjugationLiftAlgHom_algebraMap,
        conjugationLiftAlgHom_root,
        conjugationRootImage,
        hanti.realNormRoot_fixed]
      exact div_div_cancel₀
        ((map_ne_zero (algebraMap K L)).mpr
          (realNormRoot_ne_zero (a := a) hanti))
  exact DFunLike.congr_fun hsq x

/-- The involutive `K⁺`-automorphism of the Kummer extension extending
complex conjugation and sending `α` to `b / α`. -/
noncomputable def conjugationLift
    (hanti : ConjugationAntiInvariantWitness (p := p) a) :
    L ≃ₐ[K⁺] L :=
  AlgEquiv.ofBijective (conjugationLiftAlgHom hanti)
    (Function.Involutive.bijective
      (conjugationLiftAlgHom_apply_apply (a := a) hanti))

@[simp]
theorem conjugationLift_algebraMap
    (hanti : ConjugationAntiInvariantWitness (p := p) a) (x : K) :
    conjugationLift hanti (algebraMap K L x) =
      algebraMap K L (NumberField.IsCMField.complexConj K x) :=
  conjugationLiftAlgHom_algebraMap (a := a) hanti x

@[simp]
theorem conjugationLift_root
    (hanti : ConjugationAntiInvariantWitness (p := p) a) :
    conjugationLift hanti
        (root (X ^ p - C (a : K))) =
      algebraMap K L hanti.realNormRoot /
        root (X ^ p - C (a : K)) :=
  conjugationLiftAlgHom_root (a := a) hanti

@[simp]
theorem conjugationLift_apply_apply
    (hanti : ConjugationAntiInvariantWitness (p := p) a) (x : L) :
    conjugationLift hanti
        (conjugationLift hanti x) = x :=
  conjugationLiftAlgHom_apply_apply (a := a) hanti x

theorem conjugationLift_sq
    (hanti : ConjugationAntiInvariantWitness (p := p) a) :
    conjugationLift hanti ^ 2 = 1 := by
  ext x
  exact conjugationLift_apply_apply (a := a) hanti x

/-- Regard a `K`-automorphism of the Kummer extension as an automorphism
over the maximal real subfield.  This explicit wrapper avoids imposing a
particular `IsScalarTower` instance on downstream files. -/
noncomputable def restrictKAutToReal (σ : L ≃ₐ[K] L) : L ≃ₐ[K⁺] L where
  __ := σ
  commutes' x := by
    change σ (algebraMap K L (algebraMap K⁺ K x)) =
      algebraMap K L (algebraMap K⁺ K x)
    exact σ.commutes _

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
@[simp]
theorem restrictKAutToReal_apply (σ : L ≃ₐ[K] L) (x : L) :
    restrictKAutToReal σ x = σ x :=
  rfl

/-- Complex conjugation inverts every `p`th root of unity in the
cyclotomic coefficient field. -/
theorem complexConj_eq_inv_of_pow_eq_one
    {ζ η : K} (hζ : IsPrimitiveRoot ζ p) (hη : η ^ p = 1) :
    NumberField.IsCMField.complexConj K η = η⁻¹ := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
  rw [map_pow,
    Fermat.Irregular.CyclotomicDiscriminantPrime.complexConj_zeta_inv hζ]
  exact inv_pow ζ i

/-- The lifted conjugation commutes pointwise with a Kummer deck
transformation whose root multiplier is inverted by conjugation. -/
theorem conjugationLift_apply_kAut_of_root_eq
    (hanti : ConjugationAntiInvariantWitness (p := p) a)
    {η : K}
    (hconjη : NumberField.IsCMField.complexConj K η = η⁻¹)
    (σ : L ≃ₐ[K] L)
    (hσroot :
      σ (root (X ^ p - C (a : K))) =
        algebraMap K L η * root (X ^ p - C (a : K)))
    (x : L) :
    conjugationLift hanti (σ x) =
      σ (conjugationLift hanti x) := by
  have hcomp :
      (conjugationLift hanti).toAlgHom.comp
          (restrictKAutToReal σ).toAlgHom =
        (restrictKAutToReal σ).toAlgHom.comp
          (conjugationLift hanti).toAlgHom := by
    apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro y
      change
        conjugationLift hanti
            (σ (algebraMap K L y)) =
          σ (conjugationLift hanti (algebraMap K L y))
      simp only [σ.commutes, conjugationLift_algebraMap]
    · change
        conjugationLift hanti
            (σ (root (X ^ p - C (a : K)))) =
          σ (conjugationLift hanti
            (root (X ^ p - C (a : K))))
      rw [hσroot, map_mul, conjugationLift_algebraMap,
        conjugationLift_root, hconjη, map_div₀, σ.commutes, hσroot]
      simp only [map_inv₀, div_eq_mul_inv, mul_inv_rev]
      ring
  exact DFunLike.congr_fun hcomp x

/-- Group-theoretic form of
`conjugationLift_apply_kAut_of_root_eq`. -/
theorem conjugationLift_commute_kAut_of_root_eq
    (hanti : ConjugationAntiInvariantWitness (p := p) a)
    {η : K}
    (hconjη : NumberField.IsCMField.complexConj K η = η⁻¹)
    (σ : L ≃ₐ[K] L)
    (hσroot :
      σ (root (X ^ p - C (a : K))) =
        algebraMap K L η * root (X ^ p - C (a : K))) :
    Commute (conjugationLift hanti) (restrictKAutToReal σ) := by
  apply DFunLike.ext _ _
  intro x
  exact conjugationLift_apply_kAut_of_root_eq
    (a := a) hanti hconjη σ hσroot x

/-- The lifted conjugation commutes with every deck transformation of the
degree-`p` Kummer extension. -/
theorem conjugationLift_commute_kAut
    (hanti : ConjugationAntiInvariantWitness (p := p) a)
    (σ : L ≃ₐ[K] L) :
    Commute (conjugationLift hanti) (restrictKAutToReal σ) := by
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot ℚ K
      (show p ∈ ({p} : Set ℕ) by simp)
      (Fact.out : Nat.Prime p).ne_zero
  have hroots : (primitiveRoots p K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (Fact.out : Nat.Prime p).pos).2 hζ⟩
  let η : rootsOfUnity p K :=
    (autAdjoinRootXPowSubCEquiv hroots hirr.out).symm σ
  have hηpow : (((η : Kˣ) : K)) ^ p = 1 :=
    by simpa using (mem_rootsOfUnity' _ _).mp η.prop
  have hσroot :
      σ (root (X ^ p - C (a : K))) =
        algebraMap K L (((η : Kˣ) : K)) *
          root (X ^ p - C (a : K)) := by
    simpa only [η, Units.smul_def, Algebra.smul_def] using
      (autAdjoinRootXPowSubCEquiv_symm_smul hroots hirr.out σ).symm
  exact conjugationLift_commute_kAut_of_root_eq
    (a := a) hanti
    (complexConj_eq_inv_of_pow_eq_one hζ hηpow)
    σ hσroot

end Lift

end

end Fermat.Irregular.KummerConjugationDescentPrime
