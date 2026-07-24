import Fermat.Irregular.VandiverLemmaOne
import Fermat.SixtySeven.SinnottKummer
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.Integral

/-!
# The Takagi--Furtwängler boundary for Vandiver's Lemma 1 at exponent 67

This file separates the elementary class-group part of Vandiver's Lemma 1
from its class-field-theoretic input.  For a prime `p`, divisibility of a
number field's class number by `p` is equivalent to the existence of a
nonprincipal integral ideal whose `p`th power is principal.  We prove that
equivalence here.

At `p = 67` we construct the Kummer extension attached to a hypothetical
nonprincipal ideal root.  The radicand is not a `67`th power, so
`X ^ 67 - a` is irreducible; its adjoining-root field is a cyclic Galois
extension of degree `67`, with Galois group explicitly equivalent to
`ZMod 67`.  A different-ideal calculation also proves unramifiedness at
every prime containing neither `67` nor `a`.

This exposes two genuinely class-field-theoretic inputs.  The local Kummer
ramification theorem says that the ideal-power identity and primary
congruence make the extension unramified at every finite prime.  The global
Takagi--Furtwängler reflection law sends such a nontrivial primary
unramified Kummer extension to `67`-torsion in the real class group.
Mathlib currently contains neither theorem.  We state them separately and
prove that together they imply the former end-to-end reciprocity boundary.
Sinnott--Kummer's proved nondivisibility `67 ∤ h⁺` then proves
`LemmaOne K 67`.
-/

open scoped NumberField

namespace Fermat.Irregular.TakagiFurtwangler67

noncomputable section

open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverLemmaOne
open Polynomial AdjoinRoot

/-- An integral ideal representing nontrivial `p`-torsion in the class
group: the ideal is nonprincipal, while its `p`th power is principal. -/
def HasNonprincipalIdealWithPrincipalPower
    (F : Type*) [Field F] [NumberField F] (p : ℕ) : Prop :=
  ∃ I : Ideal (𝓞 F),
    ¬ Submodule.IsPrincipal (I : Ideal (𝓞 F)) ∧
      Submodule.IsPrincipal (I ^ p : Ideal (𝓞 F))

theorem hasNonprincipalIdealWithPrincipalPower_iff_dvd_classNumber
    {F : Type*} [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime) :
    HasNonprincipalIdealWithPrincipalPower F p ↔
      p ∣ NumberField.classNumber F := by
  constructor
  · rintro ⟨I, hI, hIpow⟩
    by_contra hclass
    exact hI <|
      ideal_isPrincipal_of_pow_of_not_dvd_classNumber hp hclass I hIpow
  · intro hclass
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card
      (G := ClassGroup (𝓞 F)) p (by
        simpa only [NumberField.classNumber] using hclass)
    obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c
    have hInonprincipal :
        ¬ Submodule.IsPrincipal (I.1 : Ideal (𝓞 F)) := by
      intro hprincipal
      have hc_one : c = 1 := by
        rw [← hI]
        exact (ClassGroup.mk0_eq_one_iff I.2).mpr hprincipal
      have hp_one : p = 1 := by
        rw [← hc, orderOf_eq_one_iff]
        exact hc_one
      exact hp.ne_one hp_one
    have hcpow : c ^ p = 1 := by
      rw [← hc]
      exact pow_orderOf_eq_one c
    have hmkpow : ClassGroup.mk0 (I ^ p) = 1 := by
      rw [map_pow, hI, hcpow]
    have hIpow : Submodule.IsPrincipal (I.1 ^ p : Ideal (𝓞 F)) := by
      exact (ClassGroup.mk0_eq_one_iff (I ^ p).2).mp hmkpow
    exact ⟨I.1, hInonprincipal, hIpow⟩

/-! ## From a nonprincipal ideal root to a Kummer extension -/

/-- If `I ^ p = (a)` with `I` nonprincipal, then `a` is not a `p`th
power in the number field.

Indeed, a field element `b` with `b ^ p = a` is integral because its
`p`th power is integral.  It therefore defines an algebraic integer
`bO`.  Injectivity of the `p`th-power map on integral ideals then gives
`I = (bO)`, a contradiction. -/
theorem not_pow_eq_of_nonprincipal_idealRoot
    {F : Type*} [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime)
    {a : 𝓞 F} {I : Ideal (𝓞 F)}
    (hpow : I ^ p = Ideal.span {a})
    (hnonprincipal : ¬ Submodule.IsPrincipal (I : Ideal (𝓞 F))) :
    ∀ b : F, b ^ p ≠ (a : F) := by
  intro b hb
  apply hnonprincipal
  have hbint : IsIntegral ℤ b := by
    apply IsIntegral.of_pow hp.pos
    rw [hb]
    exact NumberField.RingOfIntegers.isIntegral_coe a
  let bO : 𝓞 F := ⟨b, hbint⟩
  have hbO : bO ^ p = a := by
    apply NumberField.RingOfIntegers.ext
    exact hb
  have hIeq : I = Ideal.span {bO} := by
    apply pow_left_injective (M := Ideal (𝓞 F)) hp.ne_zero
    calc
      I ^ p = Ideal.span {a} := hpow
      _ = Ideal.span {bO ^ p} := by rw [hbO]
      _ = (Ideal.span {bO}) ^ p :=
        (Ideal.span_singleton_pow bO p).symm
  rw [hIeq]
  infer_instance

/-- The Kummer polynomial belonging to a nonprincipal ideal root is
irreducible. -/
theorem irreducible_kummerPolynomial_of_nonprincipal_idealRoot
    {F : Type*} [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime)
    {a : 𝓞 F} {I : Ideal (𝓞 F)}
    (hpow : I ^ p = Ideal.span {a})
    (hnonprincipal : ¬ Submodule.IsPrincipal (I : Ideal (𝓞 F))) :
    Irreducible (X ^ p - C (a : F)) :=
  (X_pow_sub_C_irreducible_iff_of_prime hp).2
    (not_pow_eq_of_nonprincipal_idealRoot hp hpow hnonprincipal)

/-- The generator of a nonprincipal ideal root is nonzero. -/
theorem radicand_ne_zero_of_nonprincipal_idealRoot
    {F : Type*} [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime)
    {a : 𝓞 F} {I : Ideal (𝓞 F)}
    (hpow : I ^ p = Ideal.span {a})
    (hnonprincipal : ¬ Submodule.IsPrincipal (I : Ideal (𝓞 F))) :
    a ≠ 0 := by
  intro ha
  subst a
  exact (not_pow_eq_of_nonprincipal_idealRoot hp hpow hnonprincipal 0)
    (by simp [hp.ne_zero])

/-! ## The canonical degree-67 Kummer extension -/

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {67} ℚ K]

local instance : Fact (Nat.Prime 67) := ⟨by norm_num⟩

/-- The canonical extension obtained by adjoining a `67`th root of `a`. -/
abbrev KummerExtension67 (K : Type*) [Field K] (a : 𝓞 K) :=
  AdjoinRoot (X ^ 67 - C (a : K))

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K] in
/-- The distinguished root in `KummerExtension67 K a` has `67`th power
equal to `a`. -/
theorem kummerExtension67_root_pow (a : 𝓞 K) :
    (root (X ^ 67 - C (a : K)) : KummerExtension67 K a) ^ 67 =
      algebraMap K (KummerExtension67 K a) (a : K) := by
  simpa only [KummerExtension67, AdjoinRoot.algebraMap_eq] using
    (root_X_pow_sub_C_pow 67 (a : K))

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K] in
/-- An irreducible Kummer polynomial at `67` produces an extension of
degree exactly `67`. -/
theorem kummerExtension67_finrank
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 67 - C (a : K))) :
    letI := Fact.mk hirr
    letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension67 K a) := inferInstance
    Module.finrank K (KummerExtension67 K a) = 67 := by
  letI := Fact.mk hirr
  letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
  letI : Algebra K (KummerExtension67 K a) := inferInstance
  have hroots : (primitiveRoots 67 K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by norm_num : 0 < 67)).2 hζ⟩
  letI : IsSplittingField K (KummerExtension67 K a)
      (X ^ 67 - C (a : K)) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C hroots hirr
  exact finrank_of_isSplittingField_X_pow_sub_C hroots hirr _

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K] in
/-- The canonical irreducible Kummer extension at `67` is Galois. -/
theorem kummerExtension67_isGalois
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 67 - C (a : K))) :
    letI := Fact.mk hirr
    letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension67 K a) := inferInstance
    IsGalois K (KummerExtension67 K a) := by
  letI := Fact.mk hirr
  letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
  letI : Algebra K (KummerExtension67 K a) := inferInstance
  have hroots : (primitiveRoots 67 K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by norm_num : 0 < 67)).2 hζ⟩
  letI : IsSplittingField K (KummerExtension67 K a)
      (X ^ 67 - C (a : K)) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C hroots hirr
  exact isGalois_of_isSplittingField_X_pow_sub_C hroots hirr _

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K] in
/-- The Galois group of the canonical irreducible Kummer extension at
`67` is cyclic. -/
theorem kummerExtension67_isCyclic
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 67 - C (a : K))) :
    letI := Fact.mk hirr
    letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension67 K a) := inferInstance
    IsCyclic ((KummerExtension67 K a) ≃ₐ[K] (KummerExtension67 K a)) := by
  letI := Fact.mk hirr
  letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
  letI : Algebra K (KummerExtension67 K a) := inferInstance
  have hroots : (primitiveRoots 67 K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by norm_num : 0 < 67)).2 hζ⟩
  letI : IsSplittingField K (KummerExtension67 K a)
      (X ^ 67 - C (a : K)) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C hroots hirr
  letI : NeZero 67 := ⟨by norm_num⟩
  exact isCyclic_of_isSplittingField_X_pow_sub_C hroots hirr _

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K] in
/-- Explicitly, the Galois group is the multiplicative form of
`ZMod 67`. -/
noncomputable def kummerExtension67_autEquivZmod
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 67 - C (a : K))) :
    letI := Fact.mk hirr
    letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension67 K a) := inferInstance
    ((KummerExtension67 K a) ≃ₐ[K] (KummerExtension67 K a)) ≃*
      Multiplicative (ZMod 67) := by
  letI := Fact.mk hirr
  letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
  letI : Algebra K (KummerExtension67 K a) := inferInstance
  have hroots : (primitiveRoots 67 K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by norm_num : 0 < 67)).2 hζ⟩
  letI : IsSplittingField K (KummerExtension67 K a)
      (X ^ 67 - C (a : K)) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C hroots hirr
  letI : NeZero 67 := ⟨by norm_num⟩
  exact autEquivZmod hirr _ hζ

omit [IsCyclotomicExtension {67} ℚ K] in
/-- The canonical irreducible Kummer extension is again a number field. -/
theorem kummerExtension67_numberField
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 67 - C (a : K))) :
    letI := Fact.mk hirr
    letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension67 K a) := inferInstance
    letI : Module.Finite K (KummerExtension67 K a) :=
      (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
    NumberField (KummerExtension67 K a) := by
  letI := Fact.mk hirr
  letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
  letI : Algebra K (KummerExtension67 K a) := inferInstance
  letI : Module.Finite K (KummerExtension67 K a) :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
  exact NumberField.of_module_finite K (KummerExtension67 K a)

/-! ## The integral Kummer root and its ideal -/

omit [IsCyclotomicExtension {67} ℚ K] in
/-- The distinguished Kummer root, regarded as an algebraic integer. -/
noncomputable def kummerRootInteger67
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 67 - C (a : K))) :
    letI := Fact.mk hirr
    letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension67 K a) := inferInstance
    letI : Module.Finite K (KummerExtension67 K a) :=
      (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
    letI : NumberField (KummerExtension67 K a) :=
      NumberField.of_module_finite K (KummerExtension67 K a)
    𝓞 (KummerExtension67 K a) := by
  letI := Fact.mk hirr
  let L := KummerExtension67 K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  let α : L := root (X ^ 67 - C (a : K))
  have hαintZ : IsIntegral ℤ α := by
    apply IsIntegral.of_pow (by norm_num : 0 < 67)
    rw [show α ^ 67 = algebraMap K L (a : K) by
      exact kummerExtension67_root_pow a]
    exact (NumberField.RingOfIntegers.isIntegral_coe a).map
      (IsScalarTower.toAlgHom ℤ K L)
  exact ⟨α, hαintZ⟩

/-- The integral Kummer root still satisfies its defining equation. -/
theorem kummerRootInteger67_pow
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 67 - C (a : K))) :
    letI := Fact.mk hirr
    letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension67 K a) := inferInstance
    letI : Module.Finite K (KummerExtension67 K a) :=
      (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
    letI : NumberField (KummerExtension67 K a) :=
      NumberField.of_module_finite K (KummerExtension67 K a)
    kummerRootInteger67 hirr ^ 67 =
      algebraMap (𝓞 K) (𝓞 (KummerExtension67 K a)) a := by
  letI := Fact.mk hirr
  let L := KummerExtension67 K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  apply NumberField.RingOfIntegers.ext
  exact kummerExtension67_root_pow a

set_option maxRecDepth 3000 in
/-- If `(a) = I ^ 67`, the principal ideal of the integral Kummer root is
exactly the extension of `I` to the Kummer field.

Both ideals have the same `67`th power; injectivity of powers in the
Dedekind ideal monoid gives the result.  This identity is the starting
point for the local rescaling at primes in the support of `a`. -/
theorem span_kummerRootInteger67_eq_map_of_idealPower
    {a : 𝓞 K} {I : Ideal (𝓞 K)}
    (hpow : I ^ 67 = Ideal.span {a})
    (hnonprincipal : ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K))) :
    let hirr :=
      irreducible_kummerPolynomial_of_nonprincipal_idealRoot
        (by norm_num : Nat.Prime 67) hpow hnonprincipal
    letI := Fact.mk hirr
    letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension67 K a) := inferInstance
    letI : Module.Finite K (KummerExtension67 K a) :=
      (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
    letI : NumberField (KummerExtension67 K a) :=
      NumberField.of_module_finite K (KummerExtension67 K a)
    Ideal.span {kummerRootInteger67 hirr} =
      I.map (algebraMap (𝓞 K) (𝓞 (KummerExtension67 K a))) := by
  let hirr :=
    irreducible_kummerPolynomial_of_nonprincipal_idealRoot
      (by norm_num : Nat.Prime 67) hpow hnonprincipal
  letI := Fact.mk hirr
  let L := KummerExtension67 K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  apply pow_left_injective (M := Ideal (𝓞 L)) (by norm_num : 67 ≠ 0)
  calc
    Ideal.span {kummerRootInteger67 hirr} ^ 67 =
        Ideal.span {kummerRootInteger67 hirr ^ 67} :=
      Ideal.span_singleton_pow _ _
    _ = Ideal.span {algebraMap (𝓞 K) (𝓞 L) a} := by
      rw [kummerRootInteger67_pow hirr]
    _ = (Ideal.span {a}).map (algebraMap (𝓞 K) (𝓞 L)) := by
      rw [Ideal.map_span]
      simp
    _ = (I ^ 67).map (algebraMap (𝓞 K) (𝓞 L)) := by rw [hpow]
    _ = (I.map (algebraMap (𝓞 K) (𝓞 L))) ^ 67 :=
      Ideal.map_pow _ _ _

/-! ## Local rescaling away from `67` -/

set_option maxRecDepth 1500 in
/-- At a nonzero upper prime, the Kummer root is a local generator of
the extension of `I`.

The localization of the lower Dedekind domain is a discrete valuation
ring, so the localized ideal `I` has a generator `t`.  Mapping
`(√[67]{a}) = I O_L` into the corresponding semilocal localization shows
that the Kummer root and `t` differ by a unit. -/
theorem exists_local_unit_rescaling67
    {a : 𝓞 K} {I : Ideal (𝓞 K)}
    (hpow : I ^ 67 = Ideal.span {a})
    (hnonprincipal : ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K))) :
    let hirr :=
      irreducible_kummerPolynomial_of_nonprincipal_idealRoot
        (by norm_num : Nat.Prime 67) hpow hnonprincipal
    letI := Fact.mk hirr
    letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension67 K a) := inferInstance
    letI : Module.Finite K (KummerExtension67 K a) :=
      (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
    letI : NumberField (KummerExtension67 K a) :=
      NumberField.of_module_finite K (KummerExtension67 K a)
    ∀ (Q : PrimeSpectrum (𝓞 (KummerExtension67 K a))),
      Q.asIdeal ≠ ⊥ →
      let P := Q.asIdeal.under (𝓞 K)
      let Aₚ := Localization.AtPrime P
      let Bₚ := Localization
        (Algebra.algebraMapSubmonoid
          (𝓞 (KummerExtension67 K a)) P.primeCompl)
      ∃ u : Bₚˣ,
        algebraMap (𝓞 (KummerExtension67 K a)) Bₚ
            (kummerRootInteger67 hirr) =
          algebraMap Aₚ Bₚ
            (Submodule.IsPrincipal.generator
              (I.map (algebraMap (𝓞 K) Aₚ))) * u := by
  let hirr :=
    irreducible_kummerPolynomial_of_nonprincipal_idealRoot
      (by norm_num : Nat.Prime 67) hpow hnonprincipal
  letI := Fact.mk hirr
  let L := KummerExtension67 K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  change ∀ (Q : PrimeSpectrum (𝓞 L)), Q.asIdeal ≠ ⊥ →
    let P := Q.asIdeal.under (𝓞 K)
    let Aₚ := Localization.AtPrime P
    let Bₚ := Localization
      (Algebra.algebraMapSubmonoid (𝓞 L) P.primeCompl)
    ∃ u : Bₚˣ,
      algebraMap (𝓞 L) Bₚ (kummerRootInteger67 hirr) =
        algebraMap Aₚ Bₚ
          (Submodule.IsPrincipal.generator
            (I.map (algebraMap (𝓞 K) Aₚ))) * u
  intro Q hQ0
  let P := Q.asIdeal.under (𝓞 K)
  letI : P.IsPrime := inferInstance
  have hP0 : P ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hQ0
  let Aₚ := Localization.AtPrime P
  letI : IsDiscreteValuationRing Aₚ :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K) hP0 Aₚ
  let Bₚ := Localization
    (Algebra.algebraMapSubmonoid (𝓞 L) P.primeCompl)
  let J : Ideal Aₚ := I.map (algebraMap (𝓞 K) Aₚ)
  let t : Aₚ := Submodule.IsPrincipal.generator J
  have ht : Ideal.span {t} = J :=
    Ideal.span_singleton_generator J
  have hα :
      Ideal.span
          {algebraMap (𝓞 L) Bₚ (kummerRootInteger67 hirr)} =
        I.map (algebraMap (𝓞 K) Bₚ) := by
    calc
      Ideal.span
          {algebraMap (𝓞 L) Bₚ (kummerRootInteger67 hirr)} =
          (Ideal.span {kummerRootInteger67 hirr}).map
            (algebraMap (𝓞 L) Bₚ) := by
              rw [Ideal.map_span]
              simp
      _ = (I.map (algebraMap (𝓞 K) (𝓞 L))).map
            (algebraMap (𝓞 L) Bₚ) := by
              rw [span_kummerRootInteger67_eq_map_of_idealPower
                hpow hnonprincipal]
      _ = I.map (algebraMap (𝓞 K) Bₚ) := by
        rw [Ideal.map_map,
          IsScalarTower.algebraMap_eq (𝓞 K) (𝓞 L) Bₚ]
  have ht' :
      Ideal.span {algebraMap Aₚ Bₚ t} =
        I.map (algebraMap (𝓞 K) Bₚ) := by
    calc
      Ideal.span {algebraMap Aₚ Bₚ t} =
          (Ideal.span {t}).map (algebraMap Aₚ Bₚ) := by
            rw [Ideal.map_span]
            simp
      _ = J.map (algebraMap Aₚ Bₚ) := by rw [ht]
      _ = (I.map (algebraMap (𝓞 K) Aₚ)).map
          (algebraMap Aₚ Bₚ) := rfl
      _ = I.map (algebraMap (𝓞 K) Bₚ) := by
        rw [Ideal.map_map,
          IsScalarTower.algebraMap_eq (𝓞 K) Aₚ Bₚ]
  have hassoc :
      Associated
        (algebraMap (𝓞 L) Bₚ (kummerRootInteger67 hirr))
        (algebraMap Aₚ Bₚ t) :=
    Ideal.span_singleton_eq_span_singleton.mp (hα.trans ht'.symm)
  rcases hassoc with ⟨u, hu⟩
  refine ⟨u⁻¹, ?_⟩
  rw [← hu]
  simp
  rfl

set_option maxRecDepth 1500 in
/-- The local unit rescaling can be represented by a global integer
`b ∈ O_L` which remains a unit at the chosen upper prime.

More precisely, there are nonzero `c d ∈ O_K` with
`√[67]{a} * d = c * b`.  Thus `b` is a base-field rescaling of the
Kummer root, remains a primitive element of the extension, and is a unit
at `Q`. -/
theorem exists_global_tame_rescaling67
    {a : 𝓞 K} {I : Ideal (𝓞 K)}
    (hpow : I ^ 67 = Ideal.span {a})
    (hnonprincipal : ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K))) :
    let hirr :=
      irreducible_kummerPolynomial_of_nonprincipal_idealRoot
        (by norm_num : Nat.Prime 67) hpow hnonprincipal
    letI := Fact.mk hirr
    letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension67 K a) := inferInstance
    letI : Module.Finite K (KummerExtension67 K a) :=
      (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
    letI : NumberField (KummerExtension67 K a) :=
      NumberField.of_module_finite K (KummerExtension67 K a)
    ∀ (Q : PrimeSpectrum (𝓞 (KummerExtension67 K a))),
      Q.asIdeal ≠ ⊥ →
      ∃ b : 𝓞 (KummerExtension67 K a),
        b ∉ Q.asIdeal ∧
        ∃ c d : 𝓞 K, c ≠ 0 ∧ d ≠ 0 ∧
          kummerRootInteger67 hirr *
              algebraMap (𝓞 K)
                (𝓞 (KummerExtension67 K a)) d =
            algebraMap (𝓞 K)
                (𝓞 (KummerExtension67 K a)) c * b := by
  let hirr :=
    irreducible_kummerPolynomial_of_nonprincipal_idealRoot
      (by norm_num : Nat.Prime 67) hpow hnonprincipal
  letI := Fact.mk hirr
  let L := KummerExtension67 K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  change ∀ (Q : PrimeSpectrum (𝓞 L)), Q.asIdeal ≠ ⊥ →
    ∃ b : 𝓞 L, b ∉ Q.asIdeal ∧
      ∃ c d : 𝓞 K, c ≠ 0 ∧ d ≠ 0 ∧
        kummerRootInteger67 hirr *
            algebraMap (𝓞 K) (𝓞 L) d =
          algebraMap (𝓞 K) (𝓞 L) c * b
  intro Q hQ0
  let P := Q.asIdeal.under (𝓞 K)
  letI : P.IsPrime := inferInstance
  letI : Q.asIdeal.LiesOver P := Ideal.LiesOver.mk rfl
  have hP0 : P ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hQ0
  let Aₚ := Localization.AtPrime P
  letI : IsDiscreteValuationRing Aₚ :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K) hP0 Aₚ
  let Bₚ := Localization
    (Algebra.algebraMapSubmonoid (𝓞 L) P.primeCompl)
  let J : Ideal Aₚ := I.map (algebraMap (𝓞 K) Aₚ)
  let t : Aₚ := Submodule.IsPrincipal.generator J
  obtain ⟨u, hαu⟩ :=
    exists_local_unit_rescaling67 hpow hnonprincipal Q hQ0
  obtain ⟨c, dc, hct⟩ :=
    IsLocalization.exists_mk'_eq P.primeCompl t
  have hI0 : I ≠ ⊥ := by
    intro hI
    apply hnonprincipal
    rw [hI]
    infer_instance
  have hAinj : Function.Injective (algebraMap (𝓞 K) Aₚ) :=
    IsLocalization.injective Aₚ P.primeCompl_le_nonZeroDivisors
  have hJ0 : J ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hAinj).not.mpr hI0
  have ht0 : t ≠ 0 := by
    intro ht0
    apply hJ0
    change Submodule.IsPrincipal.generator J = 0 at ht0
    rw [← Ideal.span_singleton_generator J, ht0]
    simp
  have hc0 : c ≠ 0 := by
    intro hc0
    apply ht0
    rw [← hct, hc0]
    simp
  obtain ⟨b, sb, hbu⟩ :=
    IsLocalization.exists_mk'_eq
      (Algebra.algebraMapSubmonoid (𝓞 L) P.primeCompl) (u : Bₚ)
  rcases sb with ⟨sb, hsb⟩
  rcases hsb with ⟨s, hs, hsb⟩
  subst sb
  have hbunit : IsUnit (algebraMap (𝓞 L) Bₚ b) := by
    rw [← IsLocalization.mk'_spec' Bₚ b
      ⟨algebraMap (𝓞 K) (𝓞 L) s,
        Algebra.mem_algebraMapSubmonoid_of_mem ⟨s, hs⟩⟩,
      hbu]
    exact
      (IsLocalization.map_units Bₚ
        ⟨algebraMap (𝓞 K) (𝓞 L) s,
          Algebra.mem_algebraMapSubmonoid_of_mem ⟨s, hs⟩⟩).mul u.isUnit
  have hdisj :
      Disjoint
        ((Algebra.algebraMapSubmonoid
          (𝓞 L) P.primeCompl : Submonoid (𝓞 L)) : Set (𝓞 L))
        (Q.asIdeal : Set (𝓞 L)) :=
    Ideal.disjoint_primeCompl_of_liesOver Q.asIdeal P
  have hmapQ :
      Q.asIdeal.map (algebraMap (𝓞 L) Bₚ) ≠ ⊤ :=
    (IsLocalization.map_algebraMap_ne_top_iff_disjoint
      (Algebra.algebraMapSubmonoid (𝓞 L) P.primeCompl)
      Bₚ Q.asIdeal).mpr hdisj
  have hbQ : b ∉ Q.asIdeal := by
    intro hb
    apply hmapQ
    exact Ideal.eq_top_of_isUnit_mem _
      (Ideal.mem_map_of_mem (algebraMap (𝓞 L) Bₚ) hb) hbunit
  have htclear :
      algebraMap Aₚ Bₚ t *
          algebraMap (𝓞 K) Bₚ (dc : 𝓞 K) =
        algebraMap (𝓞 K) Bₚ c := by
    calc
      algebraMap Aₚ Bₚ t *
          algebraMap (𝓞 K) Bₚ (dc : 𝓞 K) =
          algebraMap Aₚ Bₚ
            (t * algebraMap (𝓞 K) Aₚ (dc : 𝓞 K)) := by
              rw [map_mul,
                IsScalarTower.algebraMap_apply (𝓞 K) Aₚ Bₚ]
      _ = algebraMap Aₚ Bₚ
          (IsLocalization.mk' Aₚ c dc *
            algebraMap (𝓞 K) Aₚ (dc : 𝓞 K)) := by rw [hct]
      _ = algebraMap Aₚ Bₚ (algebraMap (𝓞 K) Aₚ c) := by
        rw [IsLocalization.mk'_spec]
      _ = algebraMap (𝓞 K) Bₚ c :=
        (IsScalarTower.algebraMap_apply (𝓞 K) Aₚ Bₚ c).symm
  have huclear :
      algebraMap (𝓞 K) Bₚ s * (u : Bₚ) =
        algebraMap (𝓞 L) Bₚ b := by
    simpa only [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) Bₚ]
      using
        (show
          algebraMap (𝓞 L) Bₚ
                (algebraMap (𝓞 K) (𝓞 L) s) *
              (u : Bₚ) =
            algebraMap (𝓞 L) Bₚ b by
          rw [← hbu]
          exact IsLocalization.mk'_spec' Bₚ b
            ⟨algebraMap (𝓞 K) (𝓞 L) s,
              Algebra.mem_algebraMapSubmonoid_of_mem ⟨s, hs⟩⟩)
  have hrelLoc :
      algebraMap (𝓞 L) Bₚ (kummerRootInteger67 hirr) *
          algebraMap (𝓞 K) Bₚ ((dc : 𝓞 K) * s) =
        algebraMap (𝓞 K) Bₚ c *
          algebraMap (𝓞 L) Bₚ b := by
    rw [map_mul, hαu]
    calc
      (algebraMap Aₚ Bₚ t * (u : Bₚ)) *
          (algebraMap (𝓞 K) Bₚ (dc : 𝓞 K) *
            algebraMap (𝓞 K) Bₚ s) =
          (algebraMap Aₚ Bₚ t *
            algebraMap (𝓞 K) Bₚ (dc : 𝓞 K)) *
          (algebraMap (𝓞 K) Bₚ s * (u : Bₚ)) := by ring
      _ = algebraMap (𝓞 K) Bₚ c *
          algebraMap (𝓞 L) Bₚ b := by rw [htclear, huclear]
  have hM :
      Algebra.algebraMapSubmonoid (𝓞 L) P.primeCompl ≤
        nonZeroDivisors (𝓞 L) :=
    Submonoid.map_le_of_le_comap _ <|
      P.primeCompl_le_nonZeroDivisors.trans <|
        nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
          (algebraMap (𝓞 K) (𝓞 L))
          (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))
  have hBinj : Function.Injective (algebraMap (𝓞 L) Bₚ) :=
    IsLocalization.injective Bₚ hM
  have hrel :
      kummerRootInteger67 hirr *
          algebraMap (𝓞 K) (𝓞 L) ((dc : 𝓞 K) * s) =
        algebraMap (𝓞 K) (𝓞 L) c * b := by
    apply hBinj
    simpa only [map_mul,
      IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) Bₚ] using hrelLoc
  have hdc0 : (dc : 𝓞 K) ≠ 0 := by
    intro h
    exact dc.2 (h ▸ P.zero_mem)
  have hs0 : s ≠ 0 := by
    intro h
    exact hs (h ▸ P.zero_mem)
  exact ⟨b, hbQ, c, (dc : 𝓞 K) * s, hc0,
    mul_ne_zero hdc0 hs0, hrel⟩

set_option maxRecDepth 1800 in
/-- The ideal-power identity eliminates every finite ramification prime
away from `67`.

At an upper prime `Q`, choose the global rescaling `b` above.  It is a
unit at `Q`, still generates the Kummer field, and satisfies
`b ^ 67 ∈ K`.  Its minimal polynomial therefore has the form
`X ^ 67 - k`, whose derivative is `67 * b ^ 66`.  If `Q` does not lie
above `67`, this derivative is a unit at `Q`; the different criterion
then proves unramifiedness. -/
theorem kummerExtension67_unramifiedAt_of_idealPower_awayFrom67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {a : 𝓞 K} {I : Ideal (𝓞 K)}
    (hpow : I ^ 67 = Ideal.span {a})
    (hnonprincipal : ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K))) :
    let hirr :=
      irreducible_kummerPolynomial_of_nonprincipal_idealRoot
        (by norm_num : Nat.Prime 67) hpow hnonprincipal
    letI := Fact.mk hirr
    letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension67 K a) := inferInstance
    letI : Module.Finite K (KummerExtension67 K a) :=
      (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
    letI : NumberField (KummerExtension67 K a) :=
      NumberField.of_module_finite K (KummerExtension67 K a)
    ∀ (Q : PrimeSpectrum (𝓞 (KummerExtension67 K a))),
      Q.asIdeal ≠ ⊥ →
      algebraMap (𝓞 K) (𝓞 (KummerExtension67 K a))
          (67 : 𝓞 K) ∉ Q.asIdeal →
      Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal := by
  let hirr :=
    irreducible_kummerPolynomial_of_nonprincipal_idealRoot
      (by norm_num : Nat.Prime 67) hpow hnonprincipal
  letI := Fact.mk hirr
  let L := KummerExtension67 K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  change ∀ (Q : PrimeSpectrum (𝓞 L)), Q.asIdeal ≠ ⊥ →
    algebraMap (𝓞 K) (𝓞 L) (67 : 𝓞 K) ∉ Q.asIdeal →
      Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal
  intro Q hQ0 h67
  obtain ⟨b, hbQ, c, d, hc0, hd0, hrel⟩ :=
    exists_global_tame_rescaling67 hpow hnonprincipal Q hQ0
  let α : L := root (X ^ 67 - C (a : K))
  let β : L := algebraMap (𝓞 L) L b
  have hrelL :
      α * algebraMap K L (d : K) =
        algebraMap K L (c : K) * β := by
    have h := congrArg (algebraMap (𝓞 L) L) hrel
    have hαOcoe :
        algebraMap (𝓞 L) L (kummerRootInteger67 hirr) = α := rfl
    rw [map_mul, map_mul] at h
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L d,
      ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L c] at h
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) K L d,
      ← IsScalarTower.algebraMap_apply (𝓞 K) K L c]
    simpa only [β, hαOcoe] using h
  have hcL : algebraMap K L (c : K) ≠ 0 := by
    simpa using
      (algebraMap K L).injective.ne
        (NumberField.RingOfIntegers.coe_injective.ne hc0)
  have hdL : algebraMap K L (d : K) ≠ 0 := by
    simpa using
      (algebraMap K L).injective.ne
        (NumberField.RingOfIntegers.coe_injective.ne hd0)
  have hβeq :
      β = algebraMap K L ((d : K) / (c : K)) * α := by
    rw [map_div₀ (algebraMap K L) (d : K) (c : K)]
    field_simp
    simpa only [mul_comm] using hrelL.symm
  have hαeq :
      α = algebraMap K L ((c : K) / (d : K)) * β := by
    rw [map_div₀ (algebraMap K L) (c : K) (d : K)]
    field_simp
    simpa only [mul_comm] using hrelL
  have hαgen : Algebra.adjoin K {α} = ⊤ := by
    simpa only [α, L, KummerExtension67] using
      (AdjoinRoot.adjoinRoot_eq_top (R := K)
        (f := X ^ 67 - C (a : K)))
  have hαmem : α ∈ Algebra.adjoin K {β} := by
    rw [hαeq]
    exact (Algebra.adjoin K {β}).mul_mem
      ((Algebra.adjoin K {β}).algebraMap_mem ((c : K) / (d : K)))
      (Algebra.subset_adjoin (Set.mem_singleton β))
  have hgen : Algebra.adjoin K {β} = ⊤ := by
    apply top_unique
    rw [← hαgen]
    exact Algebra.adjoin_le (by
      intro x hx
      have hx' : x = α := by
        simpa only [Set.mem_singleton_iff] using hx
      subst x
      exact hαmem)
  have hgenIF : IntermediateField.adjoin K {β} = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (IsIntegral.isAlgebraic (IsIntegral.of_finite K β))]
    exact hgen
  let k : K := ((d : K) / (c : K)) ^ 67 * (a : K)
  have hβpow : β ^ 67 = algebraMap K L k := by
    calc
      β ^ 67 =
          (algebraMap K L ((d : K) / (c : K)) * α) ^ 67 := by
            rw [hβeq]
      _ = algebraMap K L ((d : K) / (c : K)) ^ 67 * α ^ 67 := by
        rw [mul_pow]
      _ = algebraMap K L ((d : K) / (c : K)) ^ 67 *
          algebraMap K L (a : K) := by
        rw [show α ^ 67 = algebraMap K L (a : K) by
          exact kummerExtension67_root_pow a]
      _ = algebraMap K L k := by simp [k]
  have hfin : Module.finrank K L = 67 :=
    kummerExtension67_finrank hζ hirr
  have hβpow' :
      β ^ Module.finrank K L = algebraMap K L k := by
    simpa only [hfin] using hβpow
  have hirrβ :
      Irreducible (X ^ 67 - C k) := by
    simpa only [hfin] using
      (irreducible_X_pow_sub_C_of_root_adjoin_eq_top hβpow' hgenIF)
  have hβroot : aeval β (X ^ 67 - C k) = 0 := by
    simp [hβpow]
  have hminpolyK : minpoly K β = X ^ 67 - C k := by
    symm
    simpa using minpoly.eq_of_irreducible hirrβ hβroot
  have hkintL : IsIntegral ℤ (algebraMap K L k) := by
    rw [← hβpow]
    exact (NumberField.RingOfIntegers.isIntegral_coe b).pow 67
  have hkint : IsIntegral ℤ k :=
    (isIntegral_algebraMap_iff (algebraMap K L).injective).mp hkintL
  let kO : 𝓞 K := ⟨k, hkint⟩
  let g : (𝓞 K)[X] := X ^ 67 - C kO
  have hminpoly :
      minpoly (𝓞 K) b = g := by
    apply Polynomial.map_injective (algebraMap (𝓞 K) K)
      NumberField.RingOfIntegers.coe_injective
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L
      (IsIntegralClosure.isIntegral (𝓞 K) L b)]
    change minpoly K β =
      Polynomial.map (algebraMap (𝓞 K) K) g
    rw [hminpolyK]
    simp [g, kO]
  rw [← not_dvd_differentIdeal_iff]
  intro hQdiff
  have hderiv :
      aeval b (derivative (minpoly (𝓞 K) b)) ∈
        differentIdeal (𝓞 K) (𝓞 L) :=
    aeval_derivative_mem_differentIdeal
      (A := 𝓞 K) (K := K) (L := L) b hgen
  have hderivQ :
      aeval b (derivative (minpoly (𝓞 K) b)) ∈ Q.asIdeal :=
    (Ideal.dvd_iff_le.mp hQdiff) hderiv
  have hcoef :
      algebraMap (𝓞 K) (𝓞 L) (66 : 𝓞 K) + 1 =
        (67 : 𝓞 L) := by
    rw [map_ofNat]
    norm_num
  have hderivQ'' :
      (algebraMap (𝓞 K) (𝓞 L) (66 : 𝓞 K) + 1) *
          b ^ 66 ∈ Q.asIdeal := by
    simpa [hminpoly, g] using hderivQ
  have hderivQ' : (67 : 𝓞 L) * b ^ 66 ∈ Q.asIdeal := by
    rw [← hcoef]
    exact hderivQ''
  rcases Q.isPrime.mem_or_mem hderivQ' with h | h
  · exact h67 (by simpa only [map_ofNat] using h)
  · exact hbQ (Q.isPrime.mem_of_pow_mem 66 h)

/-! ## Wild rescaling above `67` -/

/-- Kummer's primary congruence produces the monic polynomial of the
wildly rescaled generator

`(√[67]{a} - c) / (ζ - 1)`.

Writing `π = ζ - 1`, substitute `πX + c` into `X^67 - a`.  Every
coefficient is divisible by `π^67`: the constant coefficient by the
primary congruence, and each mixed coefficient by
`67 ∣ choose 67 i` together with `π^66 ∣ 67`.  Dividing by `π^67`
therefore leaves a monic polynomial of degree exactly `67`. -/
theorem exists_primary_shift_polynomial67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {a : 𝓞 K}
    (hprimary : IsKummerPrimary hζ a) :
    ∃ (c : ℤ) (g : (𝓞 K)[X]),
      g.Monic ∧ g.natDegree = 67 ∧
      let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
      let cA : 𝓞 K := c
      let f : (𝓞 K)[X] := X ^ 67 - C a
      let F : (𝓞 K)[X] :=
        (taylor cA f).comp (C π * X)
      F = C (π ^ 67) * g := by
  rcases hprimary.2 with ⟨c, hc⟩
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  let cA : 𝓞 K := c
  let f : (𝓞 K)[X] := X ^ 67 - C a
  let F : (𝓞 K)[X] :=
    (taylor cA f).comp (C π * X)
  have hdiv : C (π ^ 67) ∣ F := by
    dsimp only [F, f, cA, π]
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [comp_C_mul_X_coeff, taylor_apply]
    simp only [sub_comp, pow_comp, X_comp, C_comp]
    rw [coeff_sub, coeff_X_add_C_pow]
    by_cases hi0 : i = 0
    · subst i
      simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one,
        mul_one, coeff_C_zero, pow_zero, mul_one]
      convert dvd_neg.mpr hc using 1
      ring
    by_cases hi67 : i < 67
    · have hchoose : 67 ∣ Nat.choose 67 i :=
        Nat.Prime.dvd_choose_self (by norm_num) hi0 hi67
      obtain ⟨m, hm⟩ := hchoose
      have hπ66 : π ^ 66 ∣ (67 : 𝓞 K) := by
        simpa only [π, Nat.reduceSub, Nat.cast_ofNat] using
          (associated_zeta_sub_one_pow_prime hζ).dvd
      obtain ⟨u, hu⟩ := hπ66
      refine ⟨cA ^ (67 - i) * (m : 𝓞 K) * u * π ^ (i - 1), ?_⟩
      have hcast : (Nat.choose 67 i : 𝓞 K) =
          (67 : 𝓞 K) * (m : 𝓞 K) := by
        rw [hm]
        norm_num
      have hpi : π ^ i = π ^ (i - 1) * π := by
        rw [← pow_succ]
        congr 1
        omega
      have hpi67 : π ^ 67 = π ^ 66 * π := by
        simpa using pow_succ π 66
      rw [coeff_C, if_neg hi0, sub_zero, hcast, hu, hpi, hpi67]
      ring
    · have hi : 67 ≤ i := Nat.le_of_not_gt hi67
      by_cases heq : i = 67
      · subst i
        norm_num
      · have hlt : 67 < i := lt_of_le_of_ne hi (Ne.symm heq)
        rw [Nat.choose_eq_zero_of_lt hlt]
        simp [coeff_C, hi0]
  rcases hdiv with ⟨g, hg⟩
  have hπ0 : π ≠ 0 := by
    exact hζ.unit'_coe.sub_one_ne_zero (by norm_num)
  have hπ670 : π ^ 67 ≠ 0 := pow_ne_zero 67 hπ0
  have hF67 : F.coeff 67 = π ^ 67 := by
    dsimp only [F, f, cA]
    rw [comp_C_mul_X_coeff, taylor_apply]
    simp only [sub_comp, pow_comp, X_comp, C_comp]
    rw [coeff_sub, coeff_X_add_C_pow]
    norm_num
  have hg67 : g.coeff 67 = 1 := by
    have h := congrArg (fun q : (𝓞 K)[X] => q.coeff 67) hg
    change F.coeff 67 = (C (π ^ 67) * g).coeff 67 at h
    rw [hF67, coeff_C_mul] at h
    have h' : π ^ 67 * 1 = π ^ 67 * g.coeff 67 := by
      simpa using h
    exact (mul_left_cancel₀ hπ670 h').symm
  have hgdeg : g.natDegree ≤ 67 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hF0 : F.coeff N = 0 := by
      dsimp only [F, f, cA]
      rw [comp_C_mul_X_coeff, taylor_apply]
      simp only [sub_comp, pow_comp, X_comp, C_comp]
      rw [coeff_sub, coeff_X_add_C_pow,
        Nat.choose_eq_zero_of_lt hN]
      have hN0 : N ≠ 0 := by omega
      rw [Nat.cast_zero, mul_zero, coeff_C, if_neg hN0,
        sub_zero, zero_mul]
    have h := congrArg (fun q : (𝓞 K)[X] => q.coeff N) hg
    change F.coeff N = (C (π ^ 67) * g).coeff N at h
    rw [hF0, coeff_C_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hπ670
  have hgeq : g.natDegree = 67 :=
    le_antisymm hgdeg
      (le_natDegree_of_ne_zero (by simpa only [hg67] using
        (one_ne_zero : (1 : 𝓞 K) ≠ 0)))
  refine ⟨c, g, monic_of_natDegree_le_of_coeff_eq_one 67 hgdeg hg67,
    hgeq, ?_⟩
  simpa only [π, cA, f, F] using hg

set_option maxRecDepth 2000 in
/-- A Kummer-primary radicand eliminates the remaining wild
ramification above `67`.

For an upper prime `Q` above `67`, cyclotomic ramification identifies its
lower prime with `(ζ - 1)`.  The primary congruence gives the integral
generator `β = (√[67]{a} - c)/(ζ - 1)` and the monic polynomial produced
above.  Differentiating its defining identity gives

`g'(β) = u * √[67]{a} ^ 66`

for a unit `u`.  The radicand is prime to `ζ - 1`, so the right-hand side
is a unit at `Q`; the different criterion proves unramifiedness. -/
theorem kummerExtension67_unramifiedAt_of_primary_above67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {a : 𝓞 K} {I : Ideal (𝓞 K)}
    (hprimary : IsKummerPrimary hζ a)
    (hpow : I ^ 67 = Ideal.span {a})
    (hnonprincipal : ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K))) :
    let hirr :=
      irreducible_kummerPolynomial_of_nonprincipal_idealRoot
        (by norm_num : Nat.Prime 67) hpow hnonprincipal
    letI := Fact.mk hirr
    letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension67 K a) := inferInstance
    letI : Module.Finite K (KummerExtension67 K a) :=
      (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
    letI : NumberField (KummerExtension67 K a) :=
      NumberField.of_module_finite K (KummerExtension67 K a)
    ∀ (Q : PrimeSpectrum (𝓞 (KummerExtension67 K a))),
      Q.asIdeal ≠ ⊥ →
      algebraMap (𝓞 K) (𝓞 (KummerExtension67 K a))
          (67 : 𝓞 K) ∈ Q.asIdeal →
      Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal := by
  let hirr :=
    irreducible_kummerPolynomial_of_nonprincipal_idealRoot
      (by norm_num : Nat.Prime 67) hpow hnonprincipal
  letI := Fact.mk hirr
  let L := KummerExtension67 K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  change ∀ (Q : PrimeSpectrum (𝓞 L)), Q.asIdeal ≠ ⊥ →
    algebraMap (𝓞 K) (𝓞 L) (67 : 𝓞 K) ∈ Q.asIdeal →
      Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal
  intro Q hQ0 h67Q
  let P := Q.asIdeal.under (𝓞 K)
  letI : P.IsPrime := inferInstance
  letI : Q.asIdeal.LiesOver P := Ideal.LiesOver.mk rfl
  have hP0 : P ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hQ0
  have h67P : (67 : 𝓞 K) ∈ P := by
    exact h67Q
  have hPover :
      Ideal.span {(67 : ℤ)} = P.under ℤ := by
    refine Ideal.IsMaximal.eq_of_le
      (Int.ideal_span_isMaximal_of_prime 67) Ideal.IsPrime.ne_top' ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    have hmap67 :
        algebraMap ℤ (𝓞 K) (67 : ℤ) = (67 : 𝓞 K) := by
      norm_num
    rw [hmap67]
    exact h67P
  letI : P.LiesOver (Ideal.span {(67 : ℤ)}) :=
    Ideal.LiesOver.mk hPover
  have hPeq :
      P = Ideal.span {hζ.toInteger - 1} :=
    IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver'
      67 K hζ P
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  have htoInteger : hζ.toInteger = (hζ.unit' : 𝓞 K) := by
    apply NumberField.RingOfIntegers.ext
    rfl
  have hPeqπ : P = Ideal.span {π} := by
    simpa only [π, htoInteger] using hPeq
  have haP : a ∉ P := by
    rw [hPeqπ]
    simpa only [Ideal.mem_span_singleton] using hprimary.1
  obtain ⟨c, g, hgmonic, hgdegree, hFg⟩ :=
    exists_primary_shift_polynomial67 hζ hprimary
  let cA : 𝓞 K := c
  let f : (𝓞 K)[X] := X ^ 67 - C a
  let F : (𝓞 K)[X] :=
    (taylor cA f).comp (C π * X)
  let α : L := root (X ^ 67 - C (a : K))
  let β : L :=
    (α - algebraMap (𝓞 K) L cA) /
      algebraMap (𝓞 K) L π
  have hπ0 : π ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero (by norm_num)
  have hπL0 : algebraMap (𝓞 K) L π ≠ 0 := by
    simpa using
      (FaithfulSMul.algebraMap_injective (𝓞 K) L).ne hπ0
  have haffine :
      algebraMap (𝓞 K) L π * β +
        algebraMap (𝓞 K) L cA = α := by
    dsimp only [β]
    field_simp
    ring_nf
  have hEvalF : aeval β F = 0 := by
    dsimp only [F]
    rw [aeval_comp]
    simp only [map_mul, aeval_C, aeval_X]
    rw [taylor_apply, aeval_comp]
    simp only [map_add, aeval_X, aeval_C]
    rw [haffine]
    dsimp only [f]
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [show α ^ 67 = algebraMap K L (a : K) by
      exact kummerExtension67_root_pow a]
    change algebraMap K L (algebraMap (𝓞 K) K a) -
      algebraMap K L (algebraMap (𝓞 K) K a) = 0
    ring
  have hEvalG : aeval β g = 0 := by
    have h := congrArg (fun q : (𝓞 K)[X] => aeval β q) hFg
    change aeval β F = aeval β (C (π ^ 67) * g) at h
    rw [hEvalF] at h
    simp only [map_mul, aeval_C] at h
    have hπpowL0 : algebraMap (𝓞 K) L (π ^ 67) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero 67 hπL0
    exact (mul_eq_zero.mp h.symm).resolve_left hπpowL0
  have hβintA : IsIntegral (𝓞 K) β :=
    ⟨g, hgmonic, hEvalG⟩
  letI : IsScalarTower ℤ (𝓞 K) L :=
    IsScalarTower.of_algebraMap_eq fun z => by
      change (z : L) =
        algebraMap (𝓞 K) L (z : 𝓞 K)
      simp only [IsScalarTower.algebraMap_apply (𝓞 K) K L]
      simp
  have htowerCheck : IsScalarTower ℤ (𝓞 K) L :=
    inferInstance
  have hβintZ : IsIntegral ℤ β :=
    @isIntegral_trans ℤ (𝓞 K) L _ _ _ _ _ _ htowerCheck _ β hβintA
  let βO : 𝓞 L := ⟨β, hβintZ⟩
  have hβOcoe : algebraMap (𝓞 L) L βO = β := rfl
  have hαgen : Algebra.adjoin K {α} = ⊤ := by
    simpa only [α, L, KummerExtension67] using
      (AdjoinRoot.adjoinRoot_eq_top (R := K)
        (f := X ^ 67 - C (a : K)))
  have hαmem : α ∈ Algebra.adjoin K {β} := by
    rw [← haffine]
    apply (Algebra.adjoin K {β}).add_mem
    · apply (Algebra.adjoin K {β}).mul_mem
      · simpa only [IsScalarTower.algebraMap_apply (𝓞 K) K L] using
          (Algebra.adjoin K {β}).algebraMap_mem (π : K)
      · exact Algebra.subset_adjoin (Set.mem_singleton β)
    · simpa only [IsScalarTower.algebraMap_apply (𝓞 K) K L] using
        (Algebra.adjoin K {β}).algebraMap_mem (cA : K)
  have hgen : Algebra.adjoin K {β} = ⊤ := by
    apply top_unique
    rw [← hαgen]
    exact Algebra.adjoin_le (by
      intro x hx
      have hx' : x = α := by
        simpa only [Set.mem_singleton_iff] using hx
      subst x
      exact hαmem)
  have hgenIF : IntermediateField.adjoin K {β} = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (IsIntegral.isAlgebraic (IsIntegral.of_finite K β))]
    exact hgen
  have hfin : Module.finrank K L = 67 :=
    kummerExtension67_finrank hζ hirr
  have hminDegree :
      (minpoly K β).natDegree = 67 := by
    rw [← hfin]
    exact (Field.primitive_element_iff_minpoly_natDegree_eq K β).mp hgenIF
  let gK : K[X] := g.map (algebraMap (𝓞 K) K)
  have hgKmonic : gK.Monic := hgmonic.map _
  have hgKdegree : gK.natDegree = 67 := by
    exact hgmonic.natDegree_map (algebraMap (𝓞 K) K) |>.trans hgdegree
  have hEvalGK : aeval β gK = 0 := by
    dsimp only [gK]
    simp only [aeval_def, eval₂_map]
    exact hEvalG
  have hminpolyK : minpoly K β = gK := by
    have hdvd : minpoly K β ∣ gK := minpoly.dvd K β hEvalGK
    symm
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (IsIntegral.of_finite K β))
      hgKmonic hdvd
    rw [hgKdegree, hminDegree]
  have hminpoly :
      minpoly (𝓞 K) βO = g := by
    apply Polynomial.map_injective (algebraMap (𝓞 K) K)
      NumberField.RingOfIntegers.coe_injective
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L
      (IsIntegralClosure.isIntegral (𝓞 K) L βO)]
    change minpoly K β = Polynomial.map (algebraMap (𝓞 K) K) g
    exact hminpolyK
  have hEvalDerivF :
      aeval β (derivative F) =
        algebraMap (𝓞 K) L π *
          algebraMap (𝓞 K) L (67 : 𝓞 K) * α ^ 66 := by
    dsimp only [F]
    rw [derivative_comp]
    simp only [derivative_mul, derivative_C, zero_mul, derivative_X,
      mul_one, zero_add, map_mul, aeval_C]
    rw [taylor_apply]
    simp only [sub_comp, pow_comp, X_comp, C_comp,
      derivative_sub, derivative_C, sub_zero, f]
    rw [derivative_X_add_C_pow, aeval_comp]
    simp only [map_mul, map_pow, map_add, aeval_C, aeval_X]
    rw [haffine]
    ring_nf
  obtain ⟨u, hπu⟩ :=
    associated_zeta_sub_one_pow_prime hζ
  have hπu' : π ^ 66 * (u : 𝓞 K) = (67 : 𝓞 K) := by
    simpa only [π, Nat.reduceSub, Nat.cast_ofNat] using hπu
  have hEvalDerivG :
      aeval β (derivative g) =
        algebraMap (𝓞 K) L (u : 𝓞 K) * α ^ 66 := by
    have h := congrArg derivative hFg
    have heval :=
      congrArg (fun q : (𝓞 K)[X] => aeval β q) h
    change aeval β (derivative F) =
      aeval β (derivative (C (π ^ 67) * g)) at heval
    rw [hEvalDerivF] at heval
    simp only [derivative_mul, derivative_C, zero_mul,
      zero_add, map_mul, aeval_C] at heval
    have hπ67L0 :
        algebraMap (𝓞 K) L (π ^ 67) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero 67 hπL0
    have hπ67 : π ^ 67 = π * π ^ 66 := by
      simpa using pow_succ' π 66
    have hbase : π * (67 : 𝓞 K) = π ^ 67 * (u : 𝓞 K) := by
      rw [← hπu', hπ67]
      ring
    have hfactor :
        algebraMap (𝓞 K) L π *
              algebraMap (𝓞 K) L (67 : 𝓞 K) * α ^ 66 =
          algebraMap (𝓞 K) L (π ^ 67) *
            (algebraMap (𝓞 K) L (u : 𝓞 K) * α ^ 66) := by
      rw [← map_mul, hbase, map_mul]
      ring
    rw [hfactor] at heval
    exact (mul_left_cancel₀ hπ67L0 heval).symm
  let αO : 𝓞 L := kummerRootInteger67 hirr
  have hαOcoe : algebraMap (𝓞 L) L αO = α := rfl
  have hEvalDerivGO :
      aeval βO (derivative g) =
        algebraMap (𝓞 K) (𝓞 L) (u : 𝓞 K) * αO ^ 66 := by
    apply NumberField.RingOfIntegers.ext
    change algebraMap (𝓞 L) L (aeval βO (derivative g)) =
      algebraMap (𝓞 L) L
        (algebraMap (𝓞 K) (𝓞 L) (u : 𝓞 K) * αO ^ 66)
    have hmapEval :
        algebraMap (𝓞 L) L (aeval βO (derivative g)) =
          aeval β (derivative g) := by
      simp only [aeval_def]
      rw [hom_eval₂]
      simp only [hβOcoe]
      rw [IsScalarTower.algebraMap_eq (𝓞 K) (𝓞 L) L]
    rw [hmapEval, hEvalDerivG]
    simp only [map_mul, map_pow, hαOcoe,
      IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L]
  have hαOQ : αO ∉ Q.asIdeal := by
    intro hαQ
    apply haP
    have hpowmem :=
      Q.asIdeal.pow_mem_of_mem hαQ 67 (by norm_num)
    change kummerRootInteger67 hirr ^ 67 ∈ Q.asIdeal at hpowmem
    rw [kummerRootInteger67_pow hirr] at hpowmem
    exact hpowmem
  have huQ :
      algebraMap (𝓞 K) (𝓞 L) (u : 𝓞 K) ∉ Q.asIdeal := by
    intro huMem
    exact Q.isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem Q.asIdeal huMem
        (u.isUnit.map (algebraMap (𝓞 K) (𝓞 L))))
  have hderivNot :
      aeval βO (derivative g) ∉ Q.asIdeal := by
    rw [hEvalDerivGO]
    intro hprod
    rcases Q.isPrime.mem_or_mem hprod with huMem | hαpow
    · exact huQ huMem
    · exact hαOQ (Q.isPrime.mem_of_pow_mem 66 hαpow)
  have hgenO :
      Algebra.adjoin K {algebraMap (𝓞 L) L βO} = ⊤ := by
    simpa only [hβOcoe] using hgen
  rw [← not_dvd_differentIdeal_iff]
  intro hQdiff
  have hderiv :
      aeval βO (derivative (minpoly (𝓞 K) βO)) ∈
        differentIdeal (𝓞 K) (𝓞 L) :=
    aeval_derivative_mem_differentIdeal
      (A := 𝓞 K) (K := K) (L := L) βO hgenO
  have hderivQ :
      aeval βO (derivative (minpoly (𝓞 K) βO)) ∈
        Q.asIdeal :=
    (Ideal.dvd_iff_le.mp hQdiff) hderiv
  rw [hminpoly] at hderivQ
  exact hderivNot hderivQ

/-! ## Finite-prime ramification and the reciprocity boundary -/

/-- The concrete Kummer extension is unramified at every prime which
contains neither `67` nor the radicand.

This predicate is deliberately stated using the actual upper prime ideal,
so it records the precise result furnished by the different-ideal
calculation below. -/
def KummerExtension67UnramifiedAwayFrom67AndRadicand
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 67 - C (a : K))) : Prop :=
  letI := Fact.mk hirr
  letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
  letI : Algebra K (KummerExtension67 K a) := inferInstance
  letI : Module.Finite K (KummerExtension67 K a) :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
  letI : NumberField (KummerExtension67 K a) :=
    NumberField.of_module_finite K (KummerExtension67 K a)
  ∀ Q : PrimeSpectrum (𝓞 (KummerExtension67 K a)),
    algebraMap (𝓞 K) (𝓞 (KummerExtension67 K a)) (67 : 𝓞 K) ∉ Q.asIdeal →
    algebraMap (𝓞 K) (𝓞 (KummerExtension67 K a)) a ∉ Q.asIdeal →
      Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal

omit [IsCyclotomicExtension {67} ℚ K] in
/-- Ramification in `K(√[67]{a})/K` can occur only above `67` or at a
prime containing `a`.

Let `α = √[67]{a}`.  The element `α` is an algebraic integer, generates
the extension, and has minimal polynomial `X ^ 67 - a` over `𝓞 K`.
Consequently `67 * α ^ 66` belongs to the relative different.  If an
upper prime contains neither `67` nor `a = α ^ 67`, it cannot contain
this derivative, hence cannot divide the different and is unramified. -/
theorem kummerExtension67_unramifiedAwayFrom67AndRadicand
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 67 - C (a : K))) :
    KummerExtension67UnramifiedAwayFrom67AndRadicand hirr := by
  letI := Fact.mk hirr
  let L := KummerExtension67 K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  intro Q h67 ha
  let α : L := root (X ^ 67 - C (a : K))
  let g : (𝓞 K)[X] := X ^ 67 - C a
  have hαintZ : IsIntegral ℤ α := by
    apply IsIntegral.of_pow (by norm_num : 0 < 67)
    rw [show α ^ 67 = algebraMap K L (a : K) by
      exact kummerExtension67_root_pow a]
    exact (NumberField.RingOfIntegers.isIntegral_coe a).map
      (IsScalarTower.toAlgHom ℤ K L)
  let αO : 𝓞 L := ⟨α, hαintZ⟩
  have hαOcoe : algebraMap (𝓞 L) L αO = α := rfl
  have hαOpow :
      αO ^ 67 = algebraMap (𝓞 K) (𝓞 L) a := by
    apply NumberField.RingOfIntegers.ext
    exact kummerExtension67_root_pow a
  have hgen : Algebra.adjoin K {algebraMap (𝓞 L) L αO} = ⊤ := by
    simpa only [hαOcoe, α, L, KummerExtension67] using
      (AdjoinRoot.adjoinRoot_eq_top (R := K)
        (f := X ^ 67 - C (a : K)))
  have hminpolyK :
      minpoly K α = X ^ 67 - C (a : K) := by
    change minpoly K (root (X ^ 67 - C (a : K))) =
      X ^ 67 - C (a : K)
    rw [← AdjoinRoot.powerBasis_gen
      (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).ne_zero]
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic
      (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0))
  have hminpoly :
      minpoly (𝓞 K) αO = g := by
    apply Polynomial.map_injective (algebraMap (𝓞 K) K)
      (NumberField.RingOfIntegers.coe_injective (K := K))
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L
      (IsIntegralClosure.isIntegral (𝓞 K) L αO)]
    simp [hαOcoe, hminpolyK, g]
  rw [← not_dvd_differentIdeal_iff]
  intro hQdiff
  have hderiv :
      aeval αO (derivative (minpoly (𝓞 K) αO)) ∈
        differentIdeal (𝓞 K) (𝓞 L) :=
    aeval_derivative_mem_differentIdeal
      (A := 𝓞 K) (K := K) (L := L) αO hgen
  have hderivQ : aeval αO (derivative (minpoly (𝓞 K) αO)) ∈ Q.asIdeal :=
    (Ideal.dvd_iff_le.mp hQdiff) hderiv
  have hcoef :
      algebraMap (𝓞 K) (𝓞 L) (66 : 𝓞 K) + 1 = (67 : 𝓞 L) := by
    rw [map_ofNat]
    norm_num
  have hderivQ' : (67 : 𝓞 L) * αO ^ 66 ∈ Q.asIdeal := by
    simpa [hminpoly, g, hcoef] using hderivQ
  have hαO : αO ∉ Q.asIdeal := by
    intro hα
    apply ha
    have hp := Q.asIdeal.pow_mem_of_mem hα 67 (by norm_num)
    rwa [hαOpow] at hp
  rcases Q.isPrime.mem_or_mem hderivQ' with h | h
  · exact h67 (by simpa only [map_ofNat] using h)
  · exact hαO (Q.isPrime.mem_of_pow_mem 66 h)

/-- A finite extension of number fields is unramified at every finite
place if it is unramified at every nonzero prime of the upper ring of
integers. -/
def IsUnramifiedAtFinitePlaces
    (k L : Type*) [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] : Prop :=
  ∀ Q : PrimeSpectrum (𝓞 L), Q.asIdeal ≠ ⊥ →
    Algebra.IsUnramifiedAt (𝓞 k) Q.asIdeal

/-- Formal unramifiedness of the full integer-ring extension implies
unramifiedness at every finite place. -/
theorem isUnramifiedAtFinitePlaces_of_formallyUnramified
    {k L : Type*} [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L]
    (h : Algebra.FormallyUnramified (𝓞 k) (𝓞 L)) :
    IsUnramifiedAtFinitePlaces k L := by
  intro Q _
  exact Algebra.formallyUnramified_iff_forall.mp h Q

/-- The canonical Kummer extension is unramified at all finite primes.
The irreducibility proof is an explicit parameter because it supplies the
field structure on `AdjoinRoot`. -/
def KummerExtension67Unramified
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 67 - C (a : K))) : Prop :=
  letI := Fact.mk hirr
  letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
  letI : Algebra K (KummerExtension67 K a) := inferInstance
  letI : Module.Finite K (KummerExtension67 K a) :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
  letI : NumberField (KummerExtension67 K a) :=
    NumberField.of_module_finite K (KummerExtension67 K a)
  IsUnramifiedAtFinitePlaces K (KummerExtension67 K a)

/-- The restriction of finite-prime unramifiedness to the only primes not
already covered by
`kummerExtension67_unramifiedAwayFrom67AndRadicand`: primes containing
`67` or the radicand. -/
def KummerExtension67UnramifiedAtPotentiallyRamifiedPrimes
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 67 - C (a : K))) : Prop :=
  letI := Fact.mk hirr
  letI : Field (KummerExtension67 K a) := AdjoinRoot.instField
  letI : Algebra K (KummerExtension67 K a) := inferInstance
  letI : Module.Finite K (KummerExtension67 K a) :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
  letI : NumberField (KummerExtension67 K a) :=
    NumberField.of_module_finite K (KummerExtension67 K a)
  ∀ Q : PrimeSpectrum (𝓞 (KummerExtension67 K a)),
    Q.asIdeal ≠ ⊥ →
    (algebraMap (𝓞 K) (𝓞 (KummerExtension67 K a)) (67 : 𝓞 K) ∈ Q.asIdeal ∨
      algebraMap (𝓞 K) (𝓞 (KummerExtension67 K a)) a ∈ Q.asIdeal) →
      Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal

omit [IsCyclotomicExtension {67} ℚ K] in
/-- For the canonical degree-`67` Kummer extension, proving
unramifiedness at every finite prime is equivalent to treating only the
primes containing `67` or `a`.  The complementary primes are discharged
unconditionally by the different-ideal calculation above. -/
theorem kummerExtension67_unramified_iff_atPotentiallyRamifiedPrimes
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 67 - C (a : K))) :
    KummerExtension67Unramified hirr ↔
      KummerExtension67UnramifiedAtPotentiallyRamifiedPrimes hirr := by
  letI := Fact.mk hirr
  let L := KummerExtension67 K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  change
    (∀ Q : PrimeSpectrum (𝓞 L), Q.asIdeal ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal) ↔
    (∀ Q : PrimeSpectrum (𝓞 L), Q.asIdeal ≠ ⊥ →
      (algebraMap (𝓞 K) (𝓞 L) (67 : 𝓞 K) ∈ Q.asIdeal ∨
        algebraMap (𝓞 K) (𝓞 L) a ∈ Q.asIdeal) →
      Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal)
  constructor
  · intro hall Q hQ _
    exact hall Q hQ
  · intro hbad Q hQ
    by_cases h67 :
        algebraMap (𝓞 K) (𝓞 L) (67 : 𝓞 K) ∈ Q.asIdeal
    · exact hbad Q hQ (Or.inl h67)
    by_cases ha : algebraMap (𝓞 K) (𝓞 L) a ∈ Q.asIdeal
    · exact hbad Q hQ (Or.inr ha)
    exact kummerExtension67_unramifiedAwayFrom67AndRadicand hirr Q h67 ha

/-- The exact real-class-group output of the Takagi--Furtwängler step at
exponent `67`.

If a Kummer-primary integer generates the `67`th power of a nonprincipal
ideal, global reciprocity constructs nontrivial `67`-torsion in the class
group of the maximal real subfield.  Unlike `LemmaOne`, this proposition
does not assume or conclude that the original ideal is principal: its
conclusion is a separate ideal of `K⁺` witnessing real class-group torsion.

This is retained as the convenient end-to-end interface used by
`lemmaOne_of_primaryNonprincipalProducesRealTorsion67`.  The definitions
below factor it through the actual Kummer extension, separating local
ramification from global reflection. -/
def PrimaryNonprincipalProducesRealTorsion67 (K : Type*)
    [Field K] [NumberField K] [IsCyclotomicExtension {67} ℚ K] : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {a : 𝓞 K} {I : Ideal (𝓞 K)},
    IsKummerPrimary hζ a →
      I ^ 67 = Ideal.span {a} →
        ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K)) →
          HasNonprincipalIdealWithPrincipalPower
            (NumberField.maximalRealSubfield K) 67

/-- The local Kummer ramification input.

Away from `67`, the ideal identity `(a) = I ^ 67` makes every valuation of
`a` a multiple of `67`.  At the unique prime above `67`, the Kummer-primary
congruence removes the remaining possible wild ramification.  Together
these assertions say that the concrete extension `K(√[67]{a})/K` is
unramified at every finite prime. -/
def PrimaryIdealRootGivesUnramifiedKummer67 (K : Type*)
    [Field K] [NumberField K] [IsCyclotomicExtension {67} ℚ K] : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {a : 𝓞 K} {I : Ideal (𝓞 K)},
    ∀ (_hprimary : IsKummerPrimary hζ a)
      (hpow : I ^ 67 = Ideal.span {a})
      (hnonprincipal : ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K))),
      KummerExtension67Unramified
        (irreducible_kummerPolynomial_of_nonprincipal_idealRoot
          (by norm_num) hpow hnonprincipal)

set_option maxRecDepth 2000 in
/-- The complete local Takagi--Furtwängler ramification theorem at `67`.

At primes above `67` this is
`kummerExtension67_unramifiedAt_of_primary_above67`; at every other
prime it is
`kummerExtension67_unramifiedAt_of_idealPower_awayFrom67`. -/
theorem primaryIdealRootGivesUnramifiedKummer67 :
    PrimaryIdealRootGivesUnramifiedKummer67 K := by
  intro ζ hζ a I hprimary hpow hnonprincipal
  let hirr :=
    irreducible_kummerPolynomial_of_nonprincipal_idealRoot
      (by norm_num : Nat.Prime 67) hpow hnonprincipal
  letI := Fact.mk hirr
  let L := KummerExtension67 K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  change ∀ (Q : PrimeSpectrum (𝓞 L)), Q.asIdeal ≠ ⊥ →
    Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal
  intro Q hQ0
  by_cases h67 :
      algebraMap (𝓞 K) (𝓞 L) (67 : 𝓞 K) ∈ Q.asIdeal
  · exact kummerExtension67_unramifiedAt_of_primary_above67
      hζ hprimary hpow hnonprincipal Q hQ0 h67
  · exact kummerExtension67_unramifiedAt_of_idealPower_awayFrom67
      hζ hpow hnonprincipal Q hQ0 h67

/-- The remaining local ramification statement after the checked
different-ideal calculation.

For primes containing `a`, one must use `(a) = I ^ 67` to rescale the
Kummer root by a local generator of `I`.  For primes containing `67`, one
must use the primary congruence to eliminate wild ramification. -/
def PrimaryIdealRootPotentialRamificationResolved67 (K : Type*)
    [Field K] [NumberField K] [IsCyclotomicExtension {67} ℚ K] : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {a : 𝓞 K} {I : Ideal (𝓞 K)},
    ∀ (_hprimary : IsKummerPrimary hζ a)
      (hpow : I ^ 67 = Ideal.span {a})
      (hnonprincipal : ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K))),
      KummerExtension67UnramifiedAtPotentiallyRamifiedPrimes
        (irreducible_kummerPolynomial_of_nonprincipal_idealRoot
          (by norm_num) hpow hnonprincipal)

set_option maxRecDepth 3000 in
/-- The local Kummer boundary is equivalent to resolving only primes
containing `67` or the radicand. -/
theorem primaryIdealRootGivesUnramifiedKummer67_iff_potentialRamificationResolved :
    PrimaryIdealRootGivesUnramifiedKummer67 K ↔
      PrimaryIdealRootPotentialRamificationResolved67 K := by
  constructor
  · intro h ζ hζ a I hprimary hpow hnonprincipal
    exact
      (kummerExtension67_unramified_iff_atPotentiallyRamifiedPrimes
        (irreducible_kummerPolynomial_of_nonprincipal_idealRoot
          (by norm_num) hpow hnonprincipal)).mp
        (h hζ hprimary hpow hnonprincipal)
  · intro h ζ hζ a I hprimary hpow hnonprincipal
    exact
      (kummerExtension67_unramified_iff_atPotentiallyRamifiedPrimes
        (irreducible_kummerPolynomial_of_nonprincipal_idealRoot
          (by norm_num) hpow hnonprincipal)).mpr
        (h hζ hprimary hpow hnonprincipal)

/-- The global Takagi--Furtwängler reflection input, stated on the actual
unramified Kummer extension rather than on the original principalization
conclusion.

The irreducibility parameter makes this a nontrivial extension; the
theorems above prove that it is Galois, cyclic, and has degree `67`.
Global reciprocity/reflection sends a primary unramified extension of this
form to nontrivial `67`-torsion in the real class group.  This is the
remaining Hilbert-class-field/Artin-reciprocity theorem absent from
Mathlib. -/
def PrimaryUnramifiedKummerReflection67 (K : Type*)
    [Field K] [NumberField K] [IsCyclotomicExtension {67} ℚ K] : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {a : 𝓞 K},
    IsKummerPrimary hζ a →
      ∀ hirr : Irreducible (X ^ 67 - C (a : K)),
        KummerExtension67Unramified hirr →
          HasNonprincipalIdealWithPrincipalPower
            (NumberField.maximalRealSubfield K) 67

set_option maxRecDepth 3000 in
/-- The local unramified-Kummer theorem and the global primary-reflection
law together imply the former end-to-end Takagi--Furtwängler boundary. -/
theorem primaryNonprincipalProducesRealTorsion67_of_kummerTheory
    (hunramified : PrimaryIdealRootGivesUnramifiedKummer67 K)
    (hreflection : PrimaryUnramifiedKummerReflection67 K) :
    PrimaryNonprincipalProducesRealTorsion67 K := by
  intro ζ hζ a I hprimary hpow hnonprincipal
  let hirr : Irreducible (X ^ 67 - C (a : K)) :=
    irreducible_kummerPolynomial_of_nonprincipal_idealRoot
      (by norm_num) hpow hnonprincipal
  exact hreflection hζ hprimary hirr
    (hunramified hζ hprimary hpow hnonprincipal)

/-- Equivalent numerical form of the exact missing reciprocity statement:
a primary nonprincipal ideal root forces `67 ∣ h⁺`. -/
theorem primaryNonprincipalProducesRealTorsion67_iff_forces_dvd_classNumber :
    PrimaryNonprincipalProducesRealTorsion67 K ↔
      ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
        {a : 𝓞 K} {I : Ideal (𝓞 K)},
        IsKummerPrimary hζ a →
          I ^ 67 = Ideal.span {a} →
            ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K)) →
              67 ∣ NumberField.classNumber
                (NumberField.maximalRealSubfield K) := by
  simp only [PrimaryNonprincipalProducesRealTorsion67]
  constructor
  · intro h ζ hζ a I hprimary hpow hnonprincipal
    exact (hasNonprincipalIdealWithPrincipalPower_iff_dvd_classNumber
      (F := NumberField.maximalRealSubfield K) (p := 67) (by norm_num)).mp
        (h hζ hprimary hpow hnonprincipal)
  · intro h ζ hζ a I hprimary hpow hnonprincipal
    exact (hasNonprincipalIdealWithPrincipalPower_iff_dvd_classNumber
      (F := NumberField.maximalRealSubfield K) (p := 67) (by norm_num)).mpr
        (h hζ hprimary hpow hnonprincipal)

set_option maxRecDepth 3000 in
/-- Once the Takagi--Furtwängler real-torsion construction is available,
the unconditional Sinnott--Kummer computation `67 ∤ h⁺` proves
Vandiver's Lemma 1 at exponent `67`. -/
theorem lemmaOne_of_primaryNonprincipalProducesRealTorsion67
    (hTF : PrimaryNonprincipalProducesRealTorsion67 K) :
    LemmaOne K 67 := by
  have hTF' : ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
      {a : 𝓞 K} {I : Ideal (𝓞 K)},
      IsKummerPrimary hζ a →
        I ^ 67 = Ideal.span {a} →
          ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K)) →
            67 ∣ NumberField.classNumber
              (NumberField.maximalRealSubfield K) :=
    (primaryNonprincipalProducesRealTorsion67_iff_forces_dvd_classNumber
      (K := K)).mp hTF
  unfold LemmaOne
  intro ζ hζ a I hprimary hpow
  by_contra hnonprincipal
  have hdvd : 67 ∣ NumberField.classNumber
      (NumberField.maximalRealSubfield K) :=
    hTF' hζ hprimary hpow hnonprincipal
  exact Fermat.SixtySeven.SinnottKummer.not_dvd_classNumber hζ hdvd

end

end Fermat.Irregular.TakagiFurtwangler67
