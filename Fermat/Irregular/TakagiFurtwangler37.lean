import Fermat.Irregular.VandiverLemmaOne
import Fermat.ThirtySeven.SinnottKummer
import Mathlib.FieldTheory.KummerExtension
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# The Takagi--Furtwängler boundary for Vandiver's Lemma 1 at exponent 37

This file separates the elementary class-group part of Vandiver's Lemma 1
from its class-field-theoretic input.  For a prime `p`, divisibility of a
number field's class number by `p` is equivalent to the existence of a
nonprincipal integral ideal whose `p`th power is principal.  We prove that
equivalence here.

At `p = 37` we construct the Kummer extension attached to a hypothetical
nonprincipal ideal root.  The radicand is not a `37`th power, so
`X ^ 37 - a` is irreducible; its adjoining-root field is a cyclic Galois
extension of degree `37`, with Galois group explicitly equivalent to
`ZMod 37`.  A different-ideal calculation also proves unramifiedness at
every prime containing neither `37` nor `a`.

This exposes two genuinely class-field-theoretic inputs.  The local Kummer
ramification theorem says that the ideal-power identity and primary
congruence make the extension unramified at every finite prime.  The global
Takagi--Furtwängler reflection law sends such a nontrivial primary
unramified Kummer extension to `37`-torsion in the real class group.
Mathlib currently contains neither theorem.  We state them separately and
prove that together they imply the former end-to-end reciprocity boundary.
Sinnott--Kummer's proved nondivisibility `37 ∤ h⁺` then proves
`LemmaOne K 37`.
-/

open scoped NumberField

namespace Fermat.Irregular.TakagiFurtwangler37

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

/-! ## The canonical degree-37 Kummer extension -/

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- The canonical extension obtained by adjoining a `37`th root of `a`. -/
abbrev KummerExtension37 (K : Type*) [Field K] (a : 𝓞 K) :=
  AdjoinRoot (X ^ 37 - C (a : K))

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] in
/-- The distinguished root in `KummerExtension37 K a` has `37`th power
equal to `a`. -/
theorem kummerExtension37_root_pow (a : 𝓞 K) :
    (root (X ^ 37 - C (a : K)) : KummerExtension37 K a) ^ 37 =
      algebraMap K (KummerExtension37 K a) (a : K) := by
  simpa only [KummerExtension37, AdjoinRoot.algebraMap_eq] using
    (root_X_pow_sub_C_pow 37 (a : K))

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] in
/-- An irreducible Kummer polynomial at `37` produces an extension of
degree exactly `37`. -/
theorem kummerExtension37_finrank
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 37 - C (a : K))) :
    letI := Fact.mk hirr
    letI : Field (KummerExtension37 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension37 K a) := inferInstance
    Module.finrank K (KummerExtension37 K a) = 37 := by
  letI := Fact.mk hirr
  letI : Field (KummerExtension37 K a) := AdjoinRoot.instField
  letI : Algebra K (KummerExtension37 K a) := inferInstance
  have hroots : (primitiveRoots 37 K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by norm_num : 0 < 37)).2 hζ⟩
  letI : IsSplittingField K (KummerExtension37 K a)
      (X ^ 37 - C (a : K)) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C hroots hirr
  exact finrank_of_isSplittingField_X_pow_sub_C hroots hirr _

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] in
/-- The canonical irreducible Kummer extension at `37` is Galois. -/
theorem kummerExtension37_isGalois
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 37 - C (a : K))) :
    letI := Fact.mk hirr
    letI : Field (KummerExtension37 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension37 K a) := inferInstance
    IsGalois K (KummerExtension37 K a) := by
  letI := Fact.mk hirr
  letI : Field (KummerExtension37 K a) := AdjoinRoot.instField
  letI : Algebra K (KummerExtension37 K a) := inferInstance
  have hroots : (primitiveRoots 37 K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by norm_num : 0 < 37)).2 hζ⟩
  letI : IsSplittingField K (KummerExtension37 K a)
      (X ^ 37 - C (a : K)) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C hroots hirr
  exact isGalois_of_isSplittingField_X_pow_sub_C hroots hirr _

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] in
/-- The Galois group of the canonical irreducible Kummer extension at
`37` is cyclic. -/
theorem kummerExtension37_isCyclic
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 37 - C (a : K))) :
    letI := Fact.mk hirr
    letI : Field (KummerExtension37 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension37 K a) := inferInstance
    IsCyclic ((KummerExtension37 K a) ≃ₐ[K] (KummerExtension37 K a)) := by
  letI := Fact.mk hirr
  letI : Field (KummerExtension37 K a) := AdjoinRoot.instField
  letI : Algebra K (KummerExtension37 K a) := inferInstance
  have hroots : (primitiveRoots 37 K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by norm_num : 0 < 37)).2 hζ⟩
  letI : IsSplittingField K (KummerExtension37 K a)
      (X ^ 37 - C (a : K)) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C hroots hirr
  letI : NeZero 37 := ⟨by norm_num⟩
  exact isCyclic_of_isSplittingField_X_pow_sub_C hroots hirr _

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] in
/-- Explicitly, the Galois group is the multiplicative form of
`ZMod 37`. -/
noncomputable def kummerExtension37_autEquivZmod
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 37 - C (a : K))) :
    letI := Fact.mk hirr
    letI : Field (KummerExtension37 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension37 K a) := inferInstance
    ((KummerExtension37 K a) ≃ₐ[K] (KummerExtension37 K a)) ≃*
      Multiplicative (ZMod 37) := by
  letI := Fact.mk hirr
  letI : Field (KummerExtension37 K a) := AdjoinRoot.instField
  letI : Algebra K (KummerExtension37 K a) := inferInstance
  have hroots : (primitiveRoots 37 K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by norm_num : 0 < 37)).2 hζ⟩
  letI : IsSplittingField K (KummerExtension37 K a)
      (X ^ 37 - C (a : K)) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C hroots hirr
  letI : NeZero 37 := ⟨by norm_num⟩
  exact autEquivZmod hirr _ hζ

omit [IsCyclotomicExtension {37} ℚ K] in
/-- The canonical irreducible Kummer extension is again a number field. -/
theorem kummerExtension37_numberField
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 37 - C (a : K))) :
    letI := Fact.mk hirr
    letI : Field (KummerExtension37 K a) := AdjoinRoot.instField
    letI : Algebra K (KummerExtension37 K a) := inferInstance
    letI : Module.Finite K (KummerExtension37 K a) :=
      (monic_X_pow_sub_C (a : K) (by norm_num : 37 ≠ 0)).finite_adjoinRoot
    NumberField (KummerExtension37 K a) := by
  letI := Fact.mk hirr
  letI : Field (KummerExtension37 K a) := AdjoinRoot.instField
  letI : Algebra K (KummerExtension37 K a) := inferInstance
  letI : Module.Finite K (KummerExtension37 K a) :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 37 ≠ 0)).finite_adjoinRoot
  exact NumberField.of_module_finite K (KummerExtension37 K a)

/-! ## Finite-prime ramification and the reciprocity boundary -/

/-- The concrete Kummer extension is unramified at every prime which
contains neither `37` nor the radicand.

This predicate is deliberately stated using the actual upper prime ideal,
so it records the precise result furnished by the different-ideal
calculation below. -/
def KummerExtension37UnramifiedAwayFrom37AndRadicand
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 37 - C (a : K))) : Prop :=
  letI := Fact.mk hirr
  letI : Field (KummerExtension37 K a) := AdjoinRoot.instField
  letI : Algebra K (KummerExtension37 K a) := inferInstance
  letI : Module.Finite K (KummerExtension37 K a) :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 37 ≠ 0)).finite_adjoinRoot
  letI : NumberField (KummerExtension37 K a) :=
    NumberField.of_module_finite K (KummerExtension37 K a)
  ∀ Q : PrimeSpectrum (𝓞 (KummerExtension37 K a)),
    algebraMap (𝓞 K) (𝓞 (KummerExtension37 K a)) (37 : 𝓞 K) ∉ Q.asIdeal →
    algebraMap (𝓞 K) (𝓞 (KummerExtension37 K a)) a ∉ Q.asIdeal →
      Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal

omit [IsCyclotomicExtension {37} ℚ K] in
/-- Ramification in `K(√[37]{a})/K` can occur only above `37` or at a
prime containing `a`.

Let `α = √[37]{a}`.  The element `α` is an algebraic integer, generates
the extension, and has minimal polynomial `X ^ 37 - a` over `𝓞 K`.
Consequently `37 * α ^ 36` belongs to the relative different.  If an
upper prime contains neither `37` nor `a = α ^ 37`, it cannot contain
this derivative, hence cannot divide the different and is unramified. -/
theorem kummerExtension37_unramifiedAwayFrom37AndRadicand
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 37 - C (a : K))) :
    KummerExtension37UnramifiedAwayFrom37AndRadicand hirr := by
  letI := Fact.mk hirr
  let L := KummerExtension37 K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 37 ≠ 0)).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  intro Q h37 ha
  let α : L := root (X ^ 37 - C (a : K))
  let g : (𝓞 K)[X] := X ^ 37 - C a
  have hαintZ : IsIntegral ℤ α := by
    apply IsIntegral.of_pow (by norm_num : 0 < 37)
    rw [show α ^ 37 = algebraMap K L (a : K) by
      exact kummerExtension37_root_pow a]
    exact (NumberField.RingOfIntegers.isIntegral_coe a).map
      (IsScalarTower.toAlgHom ℤ K L)
  let αO : 𝓞 L := ⟨α, hαintZ⟩
  have hαOcoe : algebraMap (𝓞 L) L αO = α := rfl
  have hαOpow :
      αO ^ 37 = algebraMap (𝓞 K) (𝓞 L) a := by
    apply NumberField.RingOfIntegers.ext
    exact kummerExtension37_root_pow a
  have hgen : Algebra.adjoin K {algebraMap (𝓞 L) L αO} = ⊤ := by
    simpa only [hαOcoe, α, L, KummerExtension37] using
      (AdjoinRoot.adjoinRoot_eq_top (R := K)
        (f := X ^ 37 - C (a : K)))
  have hminpolyK :
      minpoly K α = X ^ 37 - C (a : K) := by
    simpa only [α, L, KummerExtension37] using
      (AdjoinRoot.minpoly_powerBasis_gen_of_monic
        (monic_X_pow_sub_C (a : K) (by norm_num : 37 ≠ 0)))
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
      algebraMap (𝓞 K) (𝓞 L) (36 : 𝓞 K) + 1 = (37 : 𝓞 L) := by
    rw [map_ofNat]
    norm_num
  have hderivQ' : (37 : 𝓞 L) * αO ^ 36 ∈ Q.asIdeal := by
    simpa [hminpoly, g, hcoef] using hderivQ
  have hαO : αO ∉ Q.asIdeal := by
    intro hα
    apply ha
    have hp := Q.asIdeal.pow_mem_of_mem hα 37 (by norm_num)
    rwa [hαOpow] at hp
  rcases Q.isPrime.mem_or_mem hderivQ' with h | h
  · exact h37 (by simpa using h)
  · exact hαO (Q.isPrime.mem_of_pow_mem 36 h)

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
def KummerExtension37Unramified
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 37 - C (a : K))) : Prop :=
  letI := Fact.mk hirr
  letI : Field (KummerExtension37 K a) := AdjoinRoot.instField
  letI : Algebra K (KummerExtension37 K a) := inferInstance
  letI : Module.Finite K (KummerExtension37 K a) :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 37 ≠ 0)).finite_adjoinRoot
  letI : NumberField (KummerExtension37 K a) :=
    NumberField.of_module_finite K (KummerExtension37 K a)
  IsUnramifiedAtFinitePlaces K (KummerExtension37 K a)

/-- The restriction of finite-prime unramifiedness to the only primes not
already covered by
`kummerExtension37_unramifiedAwayFrom37AndRadicand`: primes containing
`37` or the radicand. -/
def KummerExtension37UnramifiedAtPotentiallyRamifiedPrimes
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 37 - C (a : K))) : Prop :=
  letI := Fact.mk hirr
  letI : Field (KummerExtension37 K a) := AdjoinRoot.instField
  letI : Algebra K (KummerExtension37 K a) := inferInstance
  letI : Module.Finite K (KummerExtension37 K a) :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 37 ≠ 0)).finite_adjoinRoot
  letI : NumberField (KummerExtension37 K a) :=
    NumberField.of_module_finite K (KummerExtension37 K a)
  ∀ Q : PrimeSpectrum (𝓞 (KummerExtension37 K a)),
    Q.asIdeal ≠ ⊥ →
    (algebraMap (𝓞 K) (𝓞 (KummerExtension37 K a)) (37 : 𝓞 K) ∈ Q.asIdeal ∨
      algebraMap (𝓞 K) (𝓞 (KummerExtension37 K a)) a ∈ Q.asIdeal) →
      Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal

omit [IsCyclotomicExtension {37} ℚ K] in
/-- For the canonical degree-`37` Kummer extension, proving
unramifiedness at every finite prime is equivalent to treating only the
primes containing `37` or `a`.  The complementary primes are discharged
unconditionally by the different-ideal calculation above. -/
theorem kummerExtension37_unramified_iff_atPotentiallyRamifiedPrimes
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 37 - C (a : K))) :
    KummerExtension37Unramified hirr ↔
      KummerExtension37UnramifiedAtPotentiallyRamifiedPrimes hirr := by
  letI := Fact.mk hirr
  let L := KummerExtension37 K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 37 ≠ 0)).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  change
    (∀ Q : PrimeSpectrum (𝓞 L), Q.asIdeal ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal) ↔
    (∀ Q : PrimeSpectrum (𝓞 L), Q.asIdeal ≠ ⊥ →
      (algebraMap (𝓞 K) (𝓞 L) (37 : 𝓞 K) ∈ Q.asIdeal ∨
        algebraMap (𝓞 K) (𝓞 L) a ∈ Q.asIdeal) →
      Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal)
  constructor
  · intro hall Q hQ _
    exact hall Q hQ
  · intro hbad Q hQ
    by_cases h37 :
        algebraMap (𝓞 K) (𝓞 L) (37 : 𝓞 K) ∈ Q.asIdeal
    · exact hbad Q hQ (Or.inl h37)
    by_cases ha : algebraMap (𝓞 K) (𝓞 L) a ∈ Q.asIdeal
    · exact hbad Q hQ (Or.inr ha)
    exact kummerExtension37_unramifiedAwayFrom37AndRadicand hirr Q h37 ha

/-- The exact real-class-group output of the Takagi--Furtwängler step at
exponent `37`.

If a Kummer-primary integer generates the `37`th power of a nonprincipal
ideal, global reciprocity constructs nontrivial `37`-torsion in the class
group of the maximal real subfield.  Unlike `LemmaOne`, this proposition
does not assume or conclude that the original ideal is principal: its
conclusion is a separate ideal of `K⁺` witnessing real class-group torsion.

This is retained as the convenient end-to-end interface used by
`lemmaOne_of_primaryNonprincipalProducesRealTorsion37`.  The definitions
below factor it through the actual Kummer extension, separating local
ramification from global reflection. -/
def PrimaryNonprincipalProducesRealTorsion37 (K : Type*)
    [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K] : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {a : 𝓞 K} {I : Ideal (𝓞 K)},
    IsKummerPrimary hζ a →
      I ^ 37 = Ideal.span {a} →
        ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K)) →
          HasNonprincipalIdealWithPrincipalPower
            (NumberField.maximalRealSubfield K) 37

/-- The local Kummer ramification input.

Away from `37`, the ideal identity `(a) = I ^ 37` makes every valuation of
`a` a multiple of `37`.  At the unique prime above `37`, the Kummer-primary
congruence removes the remaining possible wild ramification.  Together
these assertions say that the concrete extension `K(√[37]{a})/K` is
unramified at every finite prime.

This is not presently derivable from Mathlib: its Kummer-extension API has
no local ramification theorem for `X ^ p - a`. -/
def PrimaryIdealRootGivesUnramifiedKummer37 (K : Type*)
    [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K] : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {a : 𝓞 K} {I : Ideal (𝓞 K)},
    ∀ (_hprimary : IsKummerPrimary hζ a)
      (hpow : I ^ 37 = Ideal.span {a})
      (hnonprincipal : ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K))),
      KummerExtension37Unramified
        (irreducible_kummerPolynomial_of_nonprincipal_idealRoot
          (by norm_num) hpow hnonprincipal)

/-- The remaining local ramification statement after the checked
different-ideal calculation.

For primes containing `a`, one must use `(a) = I ^ 37` to rescale the
Kummer root by a local generator of `I`.  For primes containing `37`, one
must use the primary congruence to eliminate wild ramification. -/
def PrimaryIdealRootPotentialRamificationResolved37 (K : Type*)
    [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K] : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {a : 𝓞 K} {I : Ideal (𝓞 K)},
    ∀ (_hprimary : IsKummerPrimary hζ a)
      (hpow : I ^ 37 = Ideal.span {a})
      (hnonprincipal : ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K))),
      KummerExtension37UnramifiedAtPotentiallyRamifiedPrimes
        (irreducible_kummerPolynomial_of_nonprincipal_idealRoot
          (by norm_num) hpow hnonprincipal)

set_option maxRecDepth 1000 in
/-- The local Kummer boundary is equivalent to resolving only primes
containing `37` or the radicand. -/
theorem primaryIdealRootGivesUnramifiedKummer37_iff_potentialRamificationResolved :
    PrimaryIdealRootGivesUnramifiedKummer37 K ↔
      PrimaryIdealRootPotentialRamificationResolved37 K := by
  constructor
  · intro h ζ hζ a I hprimary hpow hnonprincipal
    exact
      (kummerExtension37_unramified_iff_atPotentiallyRamifiedPrimes
        (irreducible_kummerPolynomial_of_nonprincipal_idealRoot
          (by norm_num) hpow hnonprincipal)).mp
        (h hζ hprimary hpow hnonprincipal)
  · intro h ζ hζ a I hprimary hpow hnonprincipal
    exact
      (kummerExtension37_unramified_iff_atPotentiallyRamifiedPrimes
        (irreducible_kummerPolynomial_of_nonprincipal_idealRoot
          (by norm_num) hpow hnonprincipal)).mpr
        (h hζ hprimary hpow hnonprincipal)

/-- The global Takagi--Furtwängler reflection input, stated on the actual
unramified Kummer extension rather than on the original principalization
conclusion.

The irreducibility parameter makes this a nontrivial extension; the
theorems above prove that it is Galois, cyclic, and has degree `37`.
Global reciprocity/reflection sends a primary unramified extension of this
form to nontrivial `37`-torsion in the real class group.  This is the
remaining Hilbert-class-field/Artin-reciprocity theorem absent from
Mathlib. -/
def PrimaryUnramifiedKummerReflection37 (K : Type*)
    [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K] : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {a : 𝓞 K},
    IsKummerPrimary hζ a →
      ∀ hirr : Irreducible (X ^ 37 - C (a : K)),
        KummerExtension37Unramified hirr →
          HasNonprincipalIdealWithPrincipalPower
            (NumberField.maximalRealSubfield K) 37

set_option maxRecDepth 1000 in
/-- The local unramified-Kummer theorem and the global primary-reflection
law together imply the former end-to-end Takagi--Furtwängler boundary. -/
theorem primaryNonprincipalProducesRealTorsion37_of_kummerTheory
    (hunramified : PrimaryIdealRootGivesUnramifiedKummer37 K)
    (hreflection : PrimaryUnramifiedKummerReflection37 K) :
    PrimaryNonprincipalProducesRealTorsion37 K := by
  intro ζ hζ a I hprimary hpow hnonprincipal
  let hirr : Irreducible (X ^ 37 - C (a : K)) :=
    irreducible_kummerPolynomial_of_nonprincipal_idealRoot
      (by norm_num) hpow hnonprincipal
  exact hreflection hζ hprimary hirr
    (hunramified hζ hprimary hpow hnonprincipal)

/-- Equivalent numerical form of the exact missing reciprocity statement:
a primary nonprincipal ideal root forces `37 ∣ h⁺`. -/
theorem primaryNonprincipalProducesRealTorsion37_iff_forces_dvd_classNumber :
    PrimaryNonprincipalProducesRealTorsion37 K ↔
      ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
        {a : 𝓞 K} {I : Ideal (𝓞 K)},
        IsKummerPrimary hζ a →
          I ^ 37 = Ideal.span {a} →
            ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K)) →
              37 ∣ NumberField.classNumber
                (NumberField.maximalRealSubfield K) := by
  simp only [PrimaryNonprincipalProducesRealTorsion37]
  constructor
  · intro h ζ hζ a I hprimary hpow hnonprincipal
    exact (hasNonprincipalIdealWithPrincipalPower_iff_dvd_classNumber
      (F := NumberField.maximalRealSubfield K) (p := 37) (by norm_num)).mp
        (h hζ hprimary hpow hnonprincipal)
  · intro h ζ hζ a I hprimary hpow hnonprincipal
    exact (hasNonprincipalIdealWithPrincipalPower_iff_dvd_classNumber
      (F := NumberField.maximalRealSubfield K) (p := 37) (by norm_num)).mpr
        (h hζ hprimary hpow hnonprincipal)

set_option maxRecDepth 1000 in
/-- Once the Takagi--Furtwängler real-torsion construction is available,
the unconditional Sinnott--Kummer computation `37 ∤ h⁺` proves
Vandiver's Lemma 1 at exponent `37`. -/
theorem lemmaOne_of_primaryNonprincipalProducesRealTorsion37
    (hTF : PrimaryNonprincipalProducesRealTorsion37 K) :
    LemmaOne K 37 := by
  have hTF' : ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
      {a : 𝓞 K} {I : Ideal (𝓞 K)},
      IsKummerPrimary hζ a →
        I ^ 37 = Ideal.span {a} →
          ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K)) →
            37 ∣ NumberField.classNumber
              (NumberField.maximalRealSubfield K) :=
    (primaryNonprincipalProducesRealTorsion37_iff_forces_dvd_classNumber
      (K := K)).mp hTF
  unfold LemmaOne
  intro ζ hζ a I hprimary hpow
  by_contra hnonprincipal
  have hdvd : 37 ∣ NumberField.classNumber
      (NumberField.maximalRealSubfield K) :=
    hTF' hζ hprimary hpow hnonprincipal
  exact Fermat.ThirtySeven.SinnottKummer.not_dvd_classNumber hζ hdvd

end

end Fermat.Irregular.TakagiFurtwangler37
