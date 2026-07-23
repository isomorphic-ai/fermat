import Fermat.Irregular.TakagiFurtwangler37
import FltRegular.NumberTheory.Hilbert94

/-!
# The global Takagi--Furtwängler reflection layer at exponent 37

This file connects the finite-prime unramifiedness predicate used by the
concrete Kummer construction to the ramification-index interface consumed
by Hilbert's Theorem 94.  It then isolates the genuinely global reflection
step: construction of an unramified cyclic degree-37 extension of the
maximal real subfield.
-/

open scoped NumberField

namespace Fermat.Irregular.TakagiReflection37

noncomputable section

open Polynomial
open Fermat.Irregular.TakagiFurtwangler37

/-! ## Comparing the two finite-prime unramifiedness interfaces -/

/-- If every nonzero upper prime is unramified in the commutative-algebra
sense, then the ramification index is one at every finite prime.  This is
the exact bridge from `KummerExtension37Unramified` to the `IsUnramified`
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

/-! ## The direct Hilbert-94 consequence over the cyclotomic field -/

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

/-- The actual cyclic degree-37 Kummer extension, once unramified at every
finite prime, contributes `37`-torsion to the full cyclotomic class group.

This is the strongest conclusion supplied directly by Hilbert 94.  The
passage from the full class group to the maximal-real class group is the
separate Takagi--Furtwängler reflection step below. -/
theorem thirtySeven_dvd_classNumber_of_kummerExtensionUnramified
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    {a : 𝓞 K}
    (hirr : Irreducible (X ^ 37 - C (a : K)))
    (hunramified : KummerExtension37Unramified hirr) :
    37 ∣ NumberField.classNumber K := by
  letI := Fact.mk hirr
  let L := KummerExtension37 K a
  letI : Field L := AdjoinRoot.instField
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L :=
    (monic_X_pow_sub_C (a : K) (by norm_num : 37 ≠ 0)).finite_adjoinRoot
  letI : NumberField L := NumberField.of_module_finite K L
  letI : IsGalois K L :=
    kummerExtension37_isGalois hzeta hirr
  letI : IsCyclic (L ≃ₐ[K] L) :=
    kummerExtension37_isCyclic hzeta hirr
  letI : IsUnramified (𝓞 K) (𝓞 L) :=
    isUnramified_of_isUnramifiedAtFinitePlaces hunramified
  have hdegree : Module.finrank K L = 37 :=
    kummerExtension37_finrank hzeta hirr
  have hdvd :=
    dvd_card_classGroup_of_isUnramified_isCyclic
      (K := K) (L := L)
      (hdegree.symm ▸ (show Nat.Prime 37 by norm_num))
      (hdegree.symm ▸ (show 37 ≠ 2 by norm_num))
  simpa only [hdegree, NumberField.classNumber] using hdvd

/-! ## Hilbert 94 over the maximal real field -/

/-- Concrete data for a cyclic unramified extension of degree `37`.

The typeclass fields make this structure directly consumable by the
existing formalization of Hilbert's Theorem 94. -/
structure UnramifiedCyclicExtension37
    (F : Type) [Field F] [NumberField F] where
  L : Type
  [fieldL : Field L]
  [numberFieldL : NumberField L]
  [algebraFL : Algebra F L]
  [finiteDimensionalFL : FiniteDimensional F L]
  [galoisFL : IsGalois F L]
  [unramifiedFL : IsUnramified (𝓞 F) (𝓞 L)]
  [cyclicFL : IsCyclic (L ≃ₐ[F] L)]
  finrank_eq : Module.finrank F L = 37

/-- Hilbert 94 turns a cyclic unramified degree-37 extension into an
explicit nonprincipal ideal whose 37th power is principal. -/
theorem hasNonprincipalIdealWithPrincipalPower_of_unramifiedCyclicExtension37
    {F : Type} [Field F] [NumberField F]
    (E : UnramifiedCyclicExtension37 F) :
    HasNonprincipalIdealWithPrincipalPower F 37 := by
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
      37 ∣ Fintype.card (ClassGroup (𝓞 F)) := by
    simpa only [E.finrank_eq] using
      dvd_card_classGroup_of_isUnramified_isCyclic
        (K := F) (L := E.L) hprime hne
  apply
    (hasNonprincipalIdealWithPrincipalPower_iff_dvd_classNumber
      (F := F) (p := 37) (by norm_num)).mpr
  simpa only [NumberField.classNumber] using hdvd

/-- The exact global existence theorem needed after the concrete Kummer
extension has been constructed and proved unramified: Takagi reflection
must produce a cyclic unramified degree-37 extension of the maximal real
subfield.

This is deliberately an extension-valued statement, rather than assuming
the desired class-group torsion conclusion. -/
def PrimaryKummerProducesRealUnramifiedExtension37
    (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {37} ℚ K] : Prop :=
  ∀ {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    {a : 𝓞 K},
    Fermat.Irregular.VandiverLemmaOne.IsKummerPrimary hzeta a →
      ∀ hirr : Irreducible (X ^ 37 - C (a : K)),
        KummerExtension37Unramified hirr →
          Nonempty
            (UnramifiedCyclicExtension37
              (NumberField.maximalRealSubfield K))

/-- Once Takagi's global construction supplies the real unramified
extension, Hilbert 94 proves the exact reflection predicate used by
`TakagiFurtwangler37`. -/
theorem primaryUnramifiedKummerReflection37_of_realExtension
    (hreal : PrimaryKummerProducesRealUnramifiedExtension37 K) :
    PrimaryUnramifiedKummerReflection37 K := by
  intro zeta hzeta a hprimary hirr hunramified
  obtain ⟨E⟩ := hreal hzeta hprimary hirr hunramified
  exact
    hasNonprincipalIdealWithPrincipalPower_of_unramifiedCyclicExtension37 E

end

end Fermat.Irregular.TakagiReflection37
