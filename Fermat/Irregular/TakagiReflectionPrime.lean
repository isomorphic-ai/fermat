import Fermat.Irregular.TakagiFurtwanglerPrime
import Fermat.Irregular.KummerRealFixedFieldPrime
import FltRegular.NumberTheory.Hilbert94
import Mathlib.NumberTheory.RamificationInertia.Galois

set_option maxRecDepth 50000

/-!
# Prime-generic Takagi--Furtwängler reflection infrastructure

This module connects finite-prime unramifiedness to the ramification-index
interface used by Hilbert's Theorem 94.  It proves coprime-degree descent
from a quadratic/cyclic degree-`p` compositum, packages cyclic unramified
degree-`p` extensions, and extracts their explicit class-group torsion.

The conjugation-fixed real extension and the resulting conjugate-pair
principalization are also prime-generic.  The concrete reflection modules
need supply only their checked nondivisibility certificate for the real
class number.
-/

open scoped NumberField

namespace Fermat.Irregular.TakagiReflectionPrime

noncomputable section

open Polynomial
open Fermat.Irregular.TakagiFurtwanglerPrime
open Fermat.Irregular.VandiverLemmaOne
open Fermat.Irregular.KummerConjugationDescentPrime
open Fermat.Irregular.KummerRealFixedFieldPrime

/-! ## Comparing the two finite-prime unramifiedness interfaces -/

/-- If every nonzero upper prime is unramified in the commutative-algebra
sense, then the ramification index is one at every finite prime.  This is
the exact bridge from `KummerExtensionUnramified` to the `IsUnramified`
class used by Hilbert 94. -/
theorem isUnramified_of_isUnramifiedAtFinitePlaces
    {k L : Type*} [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L]
    (hfinite : IsUnramifiedAtFinitePlaces k L) :
    IsUnramified (𝓞 k) (𝓞 L) := by
  constructor
  intro p hp hp0 P hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver p := hP.2
  have hP0 : P ≠ ⊥ :=
    Ideal.ne_bot_of_mem_primesOver hp0 hP
  have hlocal : Algebra.IsUnramifiedAt (𝓞 k) P :=
    hfinite ⟨P, hP.1⟩ hP0
  letI : Algebra.IsUnramifiedAt (𝓞 k) P := hlocal
  have hindex :=
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
      (R := 𝓞 k) hP0
  have hover : P.under (𝓞 k) = p :=
    (Ideal.over_def P p).symm
  simpa only [hover] using hindex

/-- Coprime-degree descent of finite-prime unramifiedness in the
degree-`2`/degree-`p` compositum configuration.

Suppose `K/F` is Galois of degree `2`, `E/F` is Galois of degree `p`,
and both fields embed compatibly into `L`.  If `L/K` is unramified at
every finite prime, then so is `E/F`.

For a prime of `E`, extend it to `L`.  Multiplicativity of ramification
indices in the two towers shows that its ramification index over `F` is
at most the corresponding index in `K/F`, hence at most `2`.  Galois
ramification theory for `E/F` also makes that index divide `p`; primality
then forces it to equal `1`. -/
theorem isUnramifiedAtFinitePlaces_of_degreeTwo_degreePrime
    {p : ℕ} [Fact p.Prime]
    {F K E L : Type}
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Field L] [NumberField L]
    [Algebra F K] [Algebra F E] [Algebra F L]
    [Algebra K L] [Algebra E L]
    [IsScalarTower F K L] [IsScalarTower F E L]
    [FiniteDimensional F K] [FiniteDimensional F E]
    [FiniteDimensional K L] [FiniteDimensional E L]
    [IsGalois F K] [IsGalois F E]
    (hp2 : p ≠ 2)
    (hFK : Module.finrank F K = 2)
    (hFE : Module.finrank F E = p)
    (hLK : IsUnramifiedAtFinitePlaces K L) :
    IsUnramifiedAtFinitePlaces F E := by
  intro R hR0
  letI : R.asIdeal.IsPrime := R.isPrime
  obtain ⟨Q⟩ := R.asIdeal.nonempty_primesOver (S := 𝓞 L)
  letI : Q.1.IsPrime := Q.2.1
  letI : Q.1.LiesOver R.asIdeal := Q.2.2
  have hQ0 : Q.1 ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hR0 Q.1
  let P : Ideal (𝓞 K) := Q.1.under (𝓞 K)
  let q : Ideal (𝓞 F) := Q.1.under (𝓞 F)
  letI : P.IsPrime := Ideal.IsPrime.under (𝓞 K) Q.1
  letI : q.IsPrime := Ideal.IsPrime.under (𝓞 F) Q.1
  letI : Q.1.LiesOver P := by
    change Q.1.LiesOver (Q.1.under (𝓞 K))
    infer_instance
  letI : Q.1.LiesOver q := by
    change Q.1.LiesOver (Q.1.under (𝓞 F))
    infer_instance
  letI : R.asIdeal.LiesOver q :=
    Ideal.LiesOver.tower_bot Q.1 R.asIdeal q
  letI : P.LiesOver q :=
    Ideal.LiesOver.tower_bot Q.1 P q
  have hlocalLK : Algebra.IsUnramifiedAt (𝓞 K) Q.1 :=
    hLK ⟨Q.1, Q.2.1⟩ hQ0
  letI : Algebra.IsUnramifiedAt (𝓞 K) Q.1 := hlocalLK
  have hePQ : Ideal.ramificationIdx P Q.1 = 1 := by
    simpa only [P] using
      Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
        (R := 𝓞 K) hQ0
  have htowerK :
      Ideal.ramificationIdx q Q.1 =
        Ideal.ramificationIdx q P *
          Ideal.ramificationIdx P Q.1 :=
    Ideal.ramificationIdx_algebra_tower' q P Q.1
  have htowerE :
      Ideal.ramificationIdx q Q.1 =
        Ideal.ramificationIdx q R.asIdeal *
          Ideal.ramificationIdx R.asIdeal Q.1 :=
    Ideal.ramificationIdx_algebra_tower' q R.asIdeal Q.1
  have hq0 : q ≠ ⊥ := by
    rw [Ideal.over_def R.asIdeal q]
    exact Ideal.under_ne_bot (𝓞 F) hR0
  letI : q.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hq0 inferInstance
  have heP_le : Ideal.ramificationIdx q P ≤ 2 := by
    have hfundK :=
      Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
        hq0 (𝓞 K) Gal(K/F)
    have hePIn :
        Ideal.ramificationIdxIn q (𝓞 K) =
          Ideal.ramificationIdx q P :=
      Ideal.ramificationIdxIn_eq_ramificationIdx q P Gal(K/F)
    have hcardK : Nat.card Gal(K/F) = 2 := by
      rw [IsGalois.card_aut_eq_finrank, hFK]
    have hdvdP : Ideal.ramificationIdx q P ∣ 2 := by
      rw [hcardK] at hfundK
      rw [← hePIn]
      exact ⟨
        (q.primesOver (𝓞 K)).ncard *
          q.inertiaDegIn (𝓞 K),
        by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hfundK.symm⟩
    exact Nat.le_of_dvd (by norm_num) hdvdP
  have heR_le : Ideal.ramificationIdx q R.asIdeal ≤ 2 := by
    have hQ_le : Ideal.ramificationIdx q Q.1 ≤ 2 := by
      rw [htowerK, hePQ, mul_one]
      exact heP_le
    rw [htowerE] at hQ_le
    exact
      (Nat.le_mul_of_pos_right _
        (Nat.pos_iff_ne_zero.mpr
          (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver
            Q.1 hR0))).trans hQ_le
  have hfundE :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      hq0 (𝓞 E) Gal(E/F)
  have heIn_eq :
      Ideal.ramificationIdxIn q (𝓞 E) =
        Ideal.ramificationIdx q R.asIdeal :=
    Ideal.ramificationIdxIn_eq_ramificationIdx q R.asIdeal Gal(E/F)
  have hcardE : Nat.card Gal(E/F) = p := by
    rw [IsGalois.card_aut_eq_finrank, hFE]
  have hdvd : Ideal.ramificationIdx q R.asIdeal ∣ p := by
    rw [hcardE] at hfundE
    rw [← heIn_eq]
    exact ⟨
      (q.primesOver (𝓞 E)).ncard *
        q.inertiaDegIn (𝓞 E),
      by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hfundE.symm⟩
  have heR : Ideal.ramificationIdx q R.asIdeal = 1 := by
    rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hdvd with h | h
    · exact h
    · have hpLower := (Fact.out : Nat.Prime p).two_le
      omega
  exact
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hR0).mpr
      (by simpa only [q, Ideal.over_def R.asIdeal q] using heR)

/-! ## The direct Hilbert-94 consequence over the cyclotomic field -/

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K]

/-- The actual cyclic degree-p Kummer extension, once unramified at every
finite prime, contributes `p`-torsion to the full cyclotomic class group.

This is the strongest conclusion supplied directly by Hilbert 94.  The
passage from the full class group to the maximal-real class group is the
separate Takagi--Furtwängler reflection step below. -/
theorem prime_dvd_classNumber_of_kummerExtensionUnramified
    (hp2 : p ≠ 2)
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ p - C (a : K)))
    (hunramified : KummerExtensionUnramified hirr) :
    p ∣ NumberField.classNumber K := by
  letI := Fact.mk hirr
  let L := KummerExtension (p := p) K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K)
      (Fact.out : Nat.Prime p).ne_zero).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  letI : IsGalois K L :=
    kummerExtension_isGalois hzeta hirr
  letI : IsCyclic (L ≃ₐ[K] L) :=
    kummerExtension_isCyclic hzeta hirr
  letI : IsUnramified (𝓞 K) (𝓞 L) :=
    isUnramified_of_isUnramifiedAtFinitePlaces hunramified
  have hdegree : Module.finrank K L = p :=
    kummerExtension_finrank hzeta hirr
  have hdvd :=
    dvd_card_classGroup_of_isUnramified_isCyclic
      (K := K) (L := L)
      (hdegree.symm ▸ (Fact.out : Nat.Prime p))
      (hdegree.symm ▸ hp2)
  simpa only [hdegree, NumberField.classNumber] using hdvd

/-! ## Hilbert 94 over the maximal real field -/

/-- Concrete data for a cyclic unramified extension of degree `p`.

The typeclass fields make this structure directly consumable by the
existing formalization of Hilbert's Theorem 94. -/
structure UnramifiedCyclicExtension
    (F : Type) [Field F] [NumberField F] where
  L : Type
  [fieldL : Field L]
  [numberFieldL : NumberField L]
  [algebraFL : Algebra F L]
  [finiteDimensionalFL : FiniteDimensional F L]
  [galoisFL : IsGalois F L]
  [unramifiedFL : IsUnramified (𝓞 F) (𝓞 L)]
  [cyclicFL : IsCyclic (L ≃ₐ[F] L)]
  finrank_eq : Module.finrank F L = p

/-- Package field-theoretic data and upper-prime unramifiedness into the
form consumed by Hilbert 94. -/
def UnramifiedCyclicExtension.ofIsUnramifiedAtFinitePlaces
    {F L : Type} [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L]
    [IsGalois F L] [IsCyclic (L ≃ₐ[F] L)]
    (hdegree : Module.finrank F L = p)
    (hunramified : IsUnramifiedAtFinitePlaces F L) :
    UnramifiedCyclicExtension (p := p) F where
  L := L
  fieldL := inferInstance
  numberFieldL := inferInstance
  algebraFL := inferInstance
  finiteDimensionalFL := inferInstance
  galoisFL := inferInstance
  unramifiedFL :=
    isUnramified_of_isUnramifiedAtFinitePlaces hunramified
  cyclicFL := inferInstance
  finrank_eq := hdegree

/-- Hilbert 94 turns a cyclic unramified degree-`p` extension into an
explicit nonprincipal ideal whose `p`-th power is principal. -/
theorem hasNonprincipalIdealWithPrincipalPower_of_unramifiedCyclicExtension
    (hp2 : p ≠ 2)
    {F : Type} [Field F] [NumberField F]
    (E : UnramifiedCyclicExtension (p := p) F) :
    HasNonprincipalIdealWithPrincipalPower F p := by
  letI := E.fieldL
  letI := E.numberFieldL
  letI := E.algebraFL
  letI := E.finiteDimensionalFL
  letI := E.galoisFL
  letI := E.unramifiedFL
  letI := E.cyclicFL
  have hprime : Nat.Prime (Module.finrank F E.L) := by
    rw [E.finrank_eq]
    exact Fact.out
  have hne : Module.finrank F E.L ≠ 2 := by
    rw [E.finrank_eq]
    exact hp2
  have hdvd :
      p ∣ Fintype.card (ClassGroup (𝓞 F)) := by
    simpa only [E.finrank_eq] using
      dvd_card_classGroup_of_isUnramified_isCyclic
        (K := F) (L := E.L) hprime hne
  apply
    (hasNonprincipalIdealWithPrincipalPower_iff_dvd_classNumber
      (F := F) (p := p) (Fact.out : Nat.Prime p)).mpr
  simpa only [NumberField.classNumber] using hdvd

/-! ## The explicit conjugation-fixed real extension -/

section RealReflection

variable [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The fixed field of the lifted conjugation is an everywhere-unramified
cyclic extension of degree `p` over the maximal real subfield.

Finite-prime unramifiedness descends from the given unramified Kummer
extension: every ramification index in the real extension divides both
the quadratic degree and `p`. -/
noncomputable def realFixedFieldUnramifiedCyclicExtension
    (hp2 : p ≠ 2)
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ p - C (a : K)))
    (hanti : ConjugationAntiInvariantWitness (p := p) a)
    (hunramified : KummerExtensionUnramified hirr) :
    UnramifiedCyclicExtension (p := p) K⁺ := by
  letI : Fact (Irreducible (X ^ p - C (a : K))) := ⟨hirr⟩
  let L := KummerExtension (p := p) K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K)
      (Fact.out : Nat.Prime p).ne_zero).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  letI : Algebra K⁺ L :=
    algebraKummerOverReal (K := K) (a := a)
  letI : IsScalarTower K⁺ K L :=
    scalarTowerKummerOverReal (K := K) (a := a)
  letI : FiniteDimensional K⁺ L :=
    finiteDimensionalKummerOverReal (K := K) (a := a)
  let E := realFixedField hanti
  letI : Field E := inferInstance
  letI : Algebra K⁺ E := inferInstance
  letI : Algebra E L := inferInstance
  letI : IsScalarTower K⁺ E L :=
    IntermediateField.isScalarTower_mid' E
  letI : FiniteDimensional K⁺ E :=
    FiniteDimensional.of_finrank_pos <| by
      rw [show Module.finrank K⁺ E = p by
        exact finrank_realFixedField (a := a) hanti]
      exact (Fact.out : Nat.Prime p).pos
  letI : FiniteDimensional E L :=
    FiniteDimensional.right K⁺ E L
  letI : NumberField E := NumberField.of_module_finite K⁺ E
  letI : IsGalois K⁺ E :=
    isGalois_realFixedField (a := a) hanti
  letI : IsCyclic (E ≃ₐ[K⁺] E) :=
    isCyclic_realFixedFieldAut (a := a) hanti
  have hrealUnramified : IsUnramifiedAtFinitePlaces K⁺ E := by
    let hKLTower : IsScalarTower K⁺ K L :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact
      @isUnramifiedAtFinitePlaces_of_degreeTwo_degreePrime
      p (inferInstance : Fact p.Prime)
      K⁺ K E L
      (inferInstance : Field K⁺) (inferInstance : NumberField K⁺)
      (inferInstance : Field K) (inferInstance : NumberField K)
      (inferInstance : Field E) (inferInstance : NumberField E)
      (inferInstance : Field L) (inferInstance : NumberField L)
      (inferInstance : Algebra K⁺ K) (inferInstance : Algebra K⁺ E)
      (algebraKummerOverReal (p := p) (K := K) (a := a))
      (inferInstance : Algebra K L) (inferInstance : Algebra E L)
      hKLTower (IntermediateField.isScalarTower_mid' E)
      (inferInstance : FiniteDimensional K⁺ K)
      (inferInstance : FiniteDimensional K⁺ E)
      (inferInstance : FiniteDimensional K L)
      (inferInstance : FiniteDimensional E L)
      (inferInstance : IsGalois K⁺ K) (inferInstance : IsGalois K⁺ E)
      hp2
      (Algebra.IsQuadraticExtension.finrank_eq_two K⁺ K)
      (finrank_realFixedField (a := a) hanti)
      hunramified
  exact
    UnramifiedCyclicExtension.ofIsUnramifiedAtFinitePlaces
      (p := p)
      (finrank_realFixedField (a := a) hanti)
      hrealUnramified

/-- Hilbert 94 applied to the explicit conjugation-fixed field: an
anti-invariant, everywhere-unramified degree-`p` Kummer extension gives
nontrivial `p`-torsion in the maximal-real class group. -/
theorem antiInvariantKummerReflection
    (hp2 : p ≠ 2)
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ p - C (a : K)))
    (hanti : ConjugationAntiInvariantWitness (p := p) a)
    (hunramified : KummerExtensionUnramified hirr) :
    HasNonprincipalIdealWithPrincipalPower K⁺ p :=
  hasNonprincipalIdealWithPrincipalPower_of_unramifiedCyclicExtension
    hp2
    (realFixedFieldUnramifiedCyclicExtension
      hp2 hirr hanti hunramified)

set_option maxRecDepth 50000 in
/-- The conjugate-pair instance of Vandiver's Lemma 1 at a prime exponent.

The real-class-number nondivisibility certificate is an explicit
parameter.  It is the sole checked exponent-specific input to this
prime-generic principalization argument. -/
theorem conjugatePairIdealRoot_isPrincipal
    (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hnot : ¬ p ∣ NumberField.classNumber K⁺)
    {x : 𝓞 K} {I : Ideal (𝓞 K)}
    (hprimary :
      IsKummerPrimary hζ (conjugatePairRadicand (p := p) x))
    (hpow :
      I ^ p = Ideal.span {conjugatePairRadicand (p := p) x}) :
    Submodule.IsPrincipal (I : Ideal (𝓞 K)) := by
  by_contra hnonprincipal
  let hirr :
      Irreducible
        (X ^ p - C (conjugatePairRadicand (p := p) x : K)) :=
    irreducible_kummerPolynomial_of_nonprincipal_idealRoot
      (Fact.out : Nat.Prime p) hpow hnonprincipal
  have hunramified : KummerExtensionUnramified hirr :=
    primaryIdealRootGivesUnramifiedKummer
      hζ hprimary hpow hnonprincipal
  have htorsion :
      HasNonprincipalIdealWithPrincipalPower K⁺ p :=
    antiInvariantKummerReflection hp2 hirr
      (conjugatePairAntiInvariantWitness (p := p) x)
      hunramified
  have hdvd : p ∣ NumberField.classNumber K⁺ :=
    (hasNonprincipalIdealWithPrincipalPower_iff_dvd_classNumber
      (F := K⁺) (p := p) (Fact.out : Nat.Prime p)).mp htorsion
  exact hnot hdvd

set_option maxRecDepth 50000 in
/-- Equation (7a) for a conjugate pair, without assuming the universal
form of Vandiver's Lemma 1.

If `I^p = (x)`, `J^p = (conj(x))`, and the normalized product
`x * conj(x)^(p - 1)` is primary, real fixed-field reflection
principalizes `I * J^(p - 1)`. -/
theorem exists_conjugatePairEquationSevenAGenerator
    (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hnot : ¬ p ∣ NumberField.classNumber K⁺)
    (I J : Ideal (𝓞 K)) (x y : 𝓞 K)
    (hIpow : I ^ p = Ideal.span {x})
    (hJpow : J ^ p = Ideal.span {y})
    (hconj :
      NumberField.IsCMField.ringOfIntegersComplexConj K x = y)
    (hprimary : IsKummerPrimary hζ (x * y ^ (p - 1))) :
    ∃ r : 𝓞 K, I * J ^ (p - 1) = Ideal.span {r} := by
  have hradicand :
      conjugatePairRadicand (p := p) x = x * y ^ (p - 1) := by
    simp only [conjugatePairRadicand, hconj]
  have hpow :
      (I * J ^ (p - 1)) ^ p =
        Ideal.span {conjugatePairRadicand (p := p) x} := by
    calc
      (I * J ^ (p - 1)) ^ p =
          I ^ p * (J ^ p) ^ (p - 1) := by
        rw [mul_pow, ← pow_mul, ← pow_mul,
          Nat.mul_comm (p - 1) p]
      _ = Ideal.span {x} * (Ideal.span {y}) ^ (p - 1) := by
        rw [hIpow, hJpow]
      _ = Ideal.span {x * y ^ (p - 1)} := by
        rw [Ideal.span_singleton_pow,
          Ideal.span_singleton_mul_span_singleton]
      _ = Ideal.span {conjugatePairRadicand (p := p) x} := by
        rw [hradicand]
  have hprimary' :
      IsKummerPrimary hζ (conjugatePairRadicand (p := p) x) := by
    rw [hradicand]
    exact hprimary
  obtain ⟨r, hr⟩ :=
    (conjugatePairIdealRoot_isPrincipal
      hp2 hζ hnot hprimary' hpow).principal
  exact ⟨r, hr⟩

/-- The exact global existence theorem needed after the concrete Kummer
extension has been constructed and proved unramified: Takagi reflection
must produce a cyclic unramified degree-`p` extension of the maximal real
subfield.

This is deliberately extension-valued, rather than assuming the desired
class-group torsion conclusion. -/
def PrimaryKummerProducesRealUnramifiedExtension
    (K : Type) [Field K] [NumberField K] [NumberField.IsCMField K]
    [IsCyclotomicExtension {p} ℚ K] : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {a : 𝓞 K},
    IsKummerPrimary hζ a →
      ∀ hirr : Irreducible (X ^ p - C (a : K)),
        KummerExtensionUnramified hirr →
          Nonempty
            (UnramifiedCyclicExtension (p := p)
              (NumberField.maximalRealSubfield K))

/-- Once Takagi's global construction supplies the real unramified
extension, Hilbert 94 proves the exact reflection predicate used by the
prime-generic Takagi--Furtwängler interface. -/
theorem primaryUnramifiedKummerReflection_of_realExtension
    (hp2 : p ≠ 2)
    (hreal : PrimaryKummerProducesRealUnramifiedExtension (p := p) K) :
    PrimaryUnramifiedKummerReflection (p := p) K := by
  intro ζ hζ a hprimary hirr hunramified
  obtain ⟨E⟩ := hreal hζ hprimary hirr hunramified
  exact
    hasNonprincipalIdealWithPrincipalPower_of_unramifiedCyclicExtension
      hp2 E

end RealReflection


end

end Fermat.Irregular.TakagiReflectionPrime
