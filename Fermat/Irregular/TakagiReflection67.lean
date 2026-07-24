import Fermat.Irregular.TakagiFurtwangler67
import Fermat.Irregular.KummerRealFixedField67
import FltRegular.NumberTheory.Hilbert94
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# The global Takagi--Furtwängler reflection layer at exponent 67

This file connects the finite-prime unramifiedness predicate used by the
concrete Kummer construction to the ramification-index interface consumed
by Hilbert's Theorem 94.  It then isolates the genuinely global reflection
step: construction of an unramified cyclic degree-67 extension of the
maximal real subfield.
-/

open scoped NumberField

namespace Fermat.Irregular.TakagiReflection67

noncomputable section

open Polynomial
open Fermat.Irregular.TakagiFurtwangler67
open Fermat.Irregular.VandiverLemmaOne
open Fermat.Irregular.KummerConjugationDescent67
open Fermat.Irregular.KummerRealFixedField67

/-! ## Comparing the two finite-prime unramifiedness interfaces -/

/-- If every nonzero upper prime is unramified in the commutative-algebra
sense, then the ramification index is one at every finite prime.  This is
the exact bridge from `KummerExtension67Unramified` to the `IsUnramified`
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
degree-`2`/degree-`67` compositum configuration.

Suppose `K/F` is Galois of degree `2`, `E/F` is Galois of degree `67`,
and both fields embed compatibly into `L`.  If `L/K` is unramified at
every finite prime, then so is `E/F`.

For a prime of `E`, extend it to `L`.  Multiplicativity of ramification
indices in the two towers shows that its ramification index over `F` is
at most the corresponding index in `K/F`, hence at most `2`.  Galois
ramification theory for `E/F` also makes that index divide `67`; primality
then forces it to equal `1`. -/
theorem isUnramifiedAtFinitePlaces_of_degreeTwo_degreeSixtySeven
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
    (hFK : Module.finrank F K = 2)
    (hFE : Module.finrank F E = 67)
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
  have hcardE : Nat.card Gal(E/F) = 67 := by
    rw [IsGalois.card_aut_eq_finrank, hFE]
  have hdvd : Ideal.ramificationIdx q R.asIdeal ∣ 67 := by
    rw [hcardE] at hfundE
    rw [← heIn_eq]
    exact ⟨
      (q.primesOver (𝓞 E)).ncard *
        q.inertiaDegIn (𝓞 E),
      by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hfundE.symm⟩
  have heR : Ideal.ramificationIdx q R.asIdeal = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 67)).mp hdvd with h | h
    · exact h
    · omega
  exact
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hR0).mpr
      (by simpa only [q, Ideal.over_def R.asIdeal q] using heR)

/-! ## The direct Hilbert-94 consequence over the cyclotomic field -/

local instance : Fact (Nat.Prime 67) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {67} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 67) K (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The actual cyclic degree-67 Kummer extension, once unramified at every
finite prime, contributes `67`-torsion to the full cyclotomic class group.

This is the strongest conclusion supplied directly by Hilbert 94.  The
passage from the full class group to the maximal-real class group is the
separate Takagi--Furtwängler reflection step below. -/
theorem sixtySeven_dvd_classNumber_of_kummerExtensionUnramified
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 67 - C (a : K)))
    (hunramified : KummerExtension67Unramified hirr) :
    67 ∣ NumberField.classNumber K := by
  letI := Fact.mk hirr
  let L := KummerExtension67 K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 67 ≠ 0)).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  letI : IsGalois K L :=
    kummerExtension67_isGalois hzeta hirr
  letI : IsCyclic (L ≃ₐ[K] L) :=
    kummerExtension67_isCyclic hzeta hirr
  letI : IsUnramified (𝓞 K) (𝓞 L) :=
    isUnramified_of_isUnramifiedAtFinitePlaces hunramified
  have hdegree : Module.finrank K L = 67 :=
    kummerExtension67_finrank hzeta hirr
  have hdvd :=
    dvd_card_classGroup_of_isUnramified_isCyclic
      (K := K) (L := L)
      (hdegree.symm ▸ (show Nat.Prime 67 by norm_num))
      (hdegree.symm ▸ (show 67 ≠ 2 by norm_num))
  simpa only [hdegree, NumberField.classNumber] using hdvd

/-! ## Hilbert 94 over the maximal real field -/

/-- Concrete data for a cyclic unramified extension of degree `67`.

The typeclass fields make this structure directly consumable by the
existing formalization of Hilbert's Theorem 94. -/
structure UnramifiedCyclicExtension67
    (F : Type) [Field F] [NumberField F] where
  L : Type
  [fieldL : Field L]
  [numberFieldL : NumberField L]
  [algebraFL : Algebra F L]
  [finiteDimensionalFL : FiniteDimensional F L]
  [galoisFL : IsGalois F L]
  [unramifiedFL : IsUnramified (𝓞 F) (𝓞 L)]
  [cyclicFL : IsCyclic (L ≃ₐ[F] L)]
  finrank_eq : Module.finrank F L = 67

/-- Package field-theoretic data and upper-prime unramifiedness into the
form consumed by Hilbert 94. -/
def UnramifiedCyclicExtension67.ofIsUnramifiedAtFinitePlaces
    {F L : Type} [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L]
    [IsGalois F L] [IsCyclic (L ≃ₐ[F] L)]
    (hdegree : Module.finrank F L = 67)
    (hunramified : IsUnramifiedAtFinitePlaces F L) :
    UnramifiedCyclicExtension67 F where
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

/-- Hilbert 94 turns a cyclic unramified degree-67 extension into an
explicit nonprincipal ideal whose 67th power is principal. -/
theorem hasNonprincipalIdealWithPrincipalPower_of_unramifiedCyclicExtension67
    {F : Type} [Field F] [NumberField F]
    (E : UnramifiedCyclicExtension67 F) :
    HasNonprincipalIdealWithPrincipalPower F 67 := by
  letI := E.fieldL
  letI := E.numberFieldL
  letI := E.algebraFL
  letI := E.finiteDimensionalFL
  letI := E.galoisFL
  letI := E.unramifiedFL
  letI := E.cyclicFL
  have hprime : Nat.Prime (Module.finrank F E.L) := by
    rw [E.finrank_eq]
    decide
  have hne : Module.finrank F E.L ≠ 2 := by
    rw [E.finrank_eq]
    norm_num
  have hdvd :
      67 ∣ Fintype.card (ClassGroup (𝓞 F)) := by
    simpa only [E.finrank_eq] using
      dvd_card_classGroup_of_isUnramified_isCyclic
        (K := F) (L := E.L) hprime hne
  apply
    (hasNonprincipalIdealWithPrincipalPower_iff_dvd_classNumber
      (F := F) (p := 67) (by norm_num)).mpr
  simpa only [NumberField.classNumber] using hdvd

/-! ## The explicit conjugation-fixed real extension -/

/-- The fixed field of the lifted conjugation is an everywhere-unramified
cyclic extension of degree `67` over the maximal real subfield.

The algebraic fixed-field package comes from
`KummerRealFixedField67`.  Finite-prime unramifiedness descends from the
given unramified Kummer extension by the coprime-degree theorem above:
each ramification index divides both `2` and `67`. -/
noncomputable def realFixedFieldUnramifiedCyclicExtension67
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 67 - C (a : K)))
    (hanti : ConjugationAntiInvariantWitness67 a)
    (hunramified : KummerExtension67Unramified hirr) :
    UnramifiedCyclicExtension67 K⁺ := by
  letI : Fact (Irreducible (X ^ 67 - C (a : K))) := ⟨hirr⟩
  let L := KummerExtension67 K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K)
      (by norm_num : 67 ≠ 0)).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  letI : Algebra K⁺ L :=
    algebraKummerOverReal67 (K := K) (a := a)
  letI : IsScalarTower K⁺ K L :=
    scalarTowerKummerOverReal67 (K := K) (a := a)
  letI : FiniteDimensional K⁺ L :=
    finiteDimensionalKummerOverReal67 (K := K) (a := a)
  let E := realFixedField67 hanti
  letI : Field E := inferInstance
  letI : Algebra K⁺ E := inferInstance
  letI : Algebra E L := inferInstance
  letI : IsScalarTower K⁺ E L :=
    IntermediateField.isScalarTower_mid' E
  letI : FiniteDimensional K⁺ E :=
    FiniteDimensional.of_finrank_pos <| by
      rw [show Module.finrank K⁺ E = 67 by
        exact finrank_realFixedField67 (a := a) hanti]
      norm_num
  letI : FiniteDimensional E L :=
    FiniteDimensional.right K⁺ E L
  letI : NumberField E := NumberField.of_module_finite K⁺ E
  letI : IsGalois K⁺ E :=
    isGalois_realFixedField67 (a := a) hanti
  letI : IsCyclic (E ≃ₐ[K⁺] E) :=
    isCyclic_realFixedFieldAut67 (a := a) hanti
  have hrealUnramified : IsUnramifiedAtFinitePlaces K⁺ E :=
    @isUnramifiedAtFinitePlaces_of_degreeTwo_degreeSixtySeven
      K⁺ K E L
      inferInstance inferInstance
      inferInstance inferInstance
      inferInstance inferInstance
      inferInstance inferInstance
      inferInstance inferInstance
      (algebraKummerOverReal67 (K := K) (a := a))
      inferInstance inferInstance
      (scalarTowerKummerOverReal67 (K := K) (a := a))
      inferInstance
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance
      (Algebra.IsQuadraticExtension.finrank_eq_two K⁺ K)
      (finrank_realFixedField67 (a := a) hanti)
      hunramified
  exact UnramifiedCyclicExtension67.ofIsUnramifiedAtFinitePlaces
    (finrank_realFixedField67 (a := a) hanti)
    hrealUnramified

/-- Hilbert 94 applied to the explicit conjugation-fixed field: an
anti-invariant, everywhere-unramified degree-`67` Kummer extension gives
nontrivial `67`-torsion in the maximal-real class group. -/
theorem antiInvariantKummerReflection67
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 67 - C (a : K)))
    (hanti : ConjugationAntiInvariantWitness67 a)
    (hunramified : KummerExtension67Unramified hirr) :
    HasNonprincipalIdealWithPrincipalPower K⁺ 67 :=
  hasNonprincipalIdealWithPrincipalPower_of_unramifiedCyclicExtension67
    (realFixedFieldUnramifiedCyclicExtension67
      hirr hanti hunramified)

set_option maxRecDepth 2000 in
/-- The conjugate-pair instance of Vandiver's Lemma 1 at exponent `67`.

If the ideal root were nonprincipal, the local Kummer theorem would make
the corresponding extension everywhere unramified.  The exact identity
for `x * conj(x)^66` supplies the lifted conjugation, so the theorem above
would force `67` to divide the maximal-real class number, contradicting
the checked Sinnott--Kummer computation. -/
theorem conjugatePairIdealRoot_isPrincipal67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {x : 𝓞 K} {I : Ideal (𝓞 K)}
    (hprimary : IsKummerPrimary hζ (conjugatePairRadicand67 x))
    (hpow :
      I ^ 67 = Ideal.span {conjugatePairRadicand67 x}) :
    Submodule.IsPrincipal (I : Ideal (𝓞 K)) := by
  by_contra hnonprincipal
  let hirr :
      Irreducible
        (X ^ 67 - C (conjugatePairRadicand67 x : K)) :=
    irreducible_kummerPolynomial_of_nonprincipal_idealRoot
      (by norm_num : Nat.Prime 67) hpow hnonprincipal
  have hunramified : KummerExtension67Unramified hirr :=
    primaryIdealRootGivesUnramifiedKummer67
      hζ hprimary hpow hnonprincipal
  have htorsion :
      HasNonprincipalIdealWithPrincipalPower K⁺ 67 :=
    antiInvariantKummerReflection67 hirr
      (conjugatePairAntiInvariantWitness67 x)
      hunramified
  have hdvd : 67 ∣ NumberField.classNumber K⁺ :=
    (hasNonprincipalIdealWithPrincipalPower_iff_dvd_classNumber
      (F := K⁺) (p := 67) (by norm_num)).mp htorsion
  exact Fermat.SixtySeven.SinnottKummer.not_dvd_classNumber hζ hdvd

set_option maxRecDepth 2000 in
/-- Equation (7a) for a conjugate pair, without assuming the universal
form of Vandiver's Lemma 1.

If `I^67 = (x)`, `J^67 = (conj(x))`, and the normalized product
`x * conj(x)^66` is primary, the explicit real fixed-field reflection
principalizes `I * J^66`. -/
theorem exists_conjugatePairEquationSevenAGenerator67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (I J : Ideal (𝓞 K)) (x y : 𝓞 K)
    (hIpow : I ^ 67 = Ideal.span {x})
    (hJpow : J ^ 67 = Ideal.span {y})
    (hconj :
      NumberField.IsCMField.ringOfIntegersComplexConj K x = y)
    (hprimary : IsKummerPrimary hζ (x * y ^ 66)) :
    ∃ r : 𝓞 K, I * J ^ 66 = Ideal.span {r} := by
  have hradicand :
      conjugatePairRadicand67 x = x * y ^ 66 := by
    simp only [conjugatePairRadicand67, hconj]
  have hpow :
      (I * J ^ 66) ^ 67 =
        Ideal.span {conjugatePairRadicand67 x} := by
    calc
      (I * J ^ 66) ^ 67 =
          I ^ 67 * (J ^ 67) ^ 66 := by
        rw [mul_pow, ← pow_mul, ← pow_mul,
          Nat.mul_comm 66 67]
      _ = Ideal.span {x} * (Ideal.span {y}) ^ 66 := by
        rw [hIpow, hJpow]
      _ = Ideal.span {x * y ^ 66} := by
        rw [Ideal.span_singleton_pow,
          Ideal.span_singleton_mul_span_singleton]
      _ = Ideal.span {conjugatePairRadicand67 x} := by
        rw [hradicand]
  have hprimary' :
      IsKummerPrimary hζ (conjugatePairRadicand67 x) := by
    rw [hradicand]
    exact hprimary
  obtain ⟨r, hr⟩ :=
    (conjugatePairIdealRoot_isPrincipal67
      hζ hprimary' hpow).principal
  exact ⟨r, hr⟩

/-- The exact global existence theorem needed after the concrete Kummer
extension has been constructed and proved unramified: Takagi reflection
must produce a cyclic unramified degree-67 extension of the maximal real
subfield.

This is deliberately an extension-valued statement, rather than assuming
the desired class-group torsion conclusion. -/
def PrimaryKummerProducesRealUnramifiedExtension67
    (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {67} ℚ K] : Prop :=
  ∀ {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    {a : 𝓞 K},
    Fermat.Irregular.VandiverLemmaOne.IsKummerPrimary hzeta a →
      ∀ hirr : Irreducible (X ^ 67 - C (a : K)),
        KummerExtension67Unramified hirr →
          Nonempty
            (UnramifiedCyclicExtension67
              (NumberField.maximalRealSubfield K))

/-- Once Takagi's global construction supplies the real unramified
extension, Hilbert 94 proves the exact reflection predicate used by
`TakagiFurtwangler67`. -/
theorem primaryUnramifiedKummerReflection67_of_realExtension
    (hreal : PrimaryKummerProducesRealUnramifiedExtension67 K) :
    PrimaryUnramifiedKummerReflection67 K := by
  intro zeta hzeta a hprimary hirr hunramified
  obtain ⟨E⟩ := hreal hzeta hprimary hirr hunramified
  exact
    hasNonprincipalIdealWithPrincipalPower_of_unramifiedCyclicExtension67 E

end

end Fermat.Irregular.TakagiReflection67
