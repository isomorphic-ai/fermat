import Fermat.Descent.Irregular.CircularUnitResidues
import KummerCriterion.UnitQuotient.DeltaAction

/-!
# Cyclotomic evaluation naturality at a split finite-field root

Evaluation of the canonical cyclotomic integer at powers of a primitive
p-th root gives the complete finite-field embedding orbit. Precomposing an
evaluation with the cyclotomic automorphism indexed by tau multiplies its
root index by tau.

The final section also proves that, when `q - 1 = m * p`, these evaluation
kernels exhaust all primes above `q`. Thus changing the chosen reduction
prime is exactly a reindexing of this explicit Galois orbit.
-/

open scoped NumberField

namespace Fermat.Irregular.CyclotomicEvaluationNaturality

noncomputable section

open Polynomial

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

private abbrev zeta : K := IsCyclotomicExtension.zeta p ℚ K

private abbrev zeta_isPrimitive :
    IsPrimitiveRoot (zeta (p := p) (K := K)) p :=
  IsCyclotomicExtension.zeta_spec p ℚ K

private theorem minpoly_zetaInteger_eq_cyclotomic :
    minpoly ℤ (zeta_isPrimitive (p := p) (K := K)).toInteger =
      cyclotomic p ℤ := by
  apply Polynomial.map_injective (algebraMap ℤ ℚ)
    (RingHom.injective_int (algebraMap ℤ ℚ))
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions ℚ K,
    show algebraMap (NumberField.RingOfIntegers K) K
        (zeta_isPrimitive (p := p) (K := K)).toInteger =
      zeta (p := p) (K := K) from rfl,
    ← cyclotomic_eq_minpoly_rat (zeta_isPrimitive (p := p) (K := K))
      (Fact.out : p.Prime).pos,
    map_cyclotomic]
  exact IsIntegralClosure.isIntegral _ K _

/-- The finite-field primitive root at cyclotomic Galois index sigma. -/
def orbitRoot (root : ZMod q)
    (sigma : KummerCriterion.CyclotomicUnitDelta p) : ZMod q :=
  root ^ (sigma : ZMod p).val

theorem orbitRoot_isPrimitive {root : ZMod q}
    (hroot : IsPrimitiveRoot root p)
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    IsPrimitiveRoot (orbitRoot root sigma) p := by
  exact hroot.pow_of_coprime (sigma : ZMod p).val
    (ZMod.val_coe_unit_coprime sigma)

/-- Evaluation of the cyclotomic integral power basis at one root in the
finite-field orbit. -/
def evaluationHom (root : ZMod q) (hroot : IsPrimitiveRoot root p)
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    NumberField.RingOfIntegers K →+* ZMod q :=
  ((zeta_isPrimitive (p := p) (K := K)).integralPowerBasis.lift
    (orbitRoot root sigma) (by
      rw [(zeta_isPrimitive (p := p) (K := K)).integralPowerBasis_gen,
        minpoly_zetaInteger_eq_cyclotomic]
      simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
        Polynomial.map_cyclotomic, IsRoot.def] using
        (orbitRoot_isPrimitive hroot sigma).isRoot_cyclotomic
          (Fact.out : p.Prime).pos)).toRingHom

@[simp]
theorem evaluationHom_zetaInteger (root : ZMod q)
    (hroot : IsPrimitiveRoot root p)
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    evaluationHom (K := K) root hroot sigma
        (zeta_isPrimitive (p := p) (K := K)).toInteger =
      orbitRoot root sigma := by
  rw [evaluationHom,
    ← (zeta_isPrimitive (p := p) (K := K)).integralPowerBasis_gen]
  exact PowerBasis.lift_gen _ _ _

theorem orbitRoot_mul (root : ZMod q) (hroot : IsPrimitiveRoot root p)
    (sigma tau : KummerCriterion.CyclotomicUnitDelta p) :
    orbitRoot root sigma ^ (tau : ZMod p).val =
      orbitRoot root (sigma * tau) := by
  rw [orbitRoot, orbitRoot, ← pow_mul]
  apply pow_eq_pow_of_modEq _ hroot.pow_eq_one
  rw [← ZMod.natCast_eq_natCast_iff]
  calc
    (((sigma : ZMod p).val * (tau : ZMod p).val : ℕ) : ZMod p) =
        (sigma : ZMod p) * (tau : ZMod p) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    _ = ((sigma * tau : KummerCriterion.CyclotomicUnitDelta p) :
        ZMod p) := rfl
    _ = ((((sigma * tau : KummerCriterion.CyclotomicUnitDelta p) :
        ZMod p).val : ℕ) : ZMod p) := by
      rw [ZMod.natCast_zmod_val]

/-- Replacing the base root by its alpha-th power reindexes the evaluation
orbit by left multiplication with alpha. -/
theorem orbitRoot_root_pow (root : ZMod q)
    (hroot : IsPrimitiveRoot root p)
    (alpha sigma : KummerCriterion.CyclotomicUnitDelta p) :
    orbitRoot (root ^ (alpha : ZMod p).val) sigma =
      orbitRoot root (alpha * sigma) :=
  orbitRoot_mul root hroot alpha sigma

theorem evaluationHom_root_pow (root : ZMod q)
    (hroot : IsPrimitiveRoot root p)
    (alpha sigma : KummerCriterion.CyclotomicUnitDelta p) :
    evaluationHom (K := K) (root ^ (alpha : ZMod p).val)
        (hroot.pow_of_coprime (alpha : ZMod p).val
          (ZMod.val_coe_unit_coprime alpha)) sigma =
      evaluationHom (K := K) root hroot (alpha * sigma) := by
  apply RingHom.ext
  intro x
  let leftAlg :=
    (evaluationHom (K := K) (root ^ (alpha : ZMod p).val)
      (hroot.pow_of_coprime (alpha : ZMod p).val
        (ZMod.val_coe_unit_coprime alpha)) sigma).toIntAlgHom
  let rightAlg :=
    (evaluationHom (K := K) root hroot (alpha * sigma)).toIntAlgHom
  have heq : leftAlg = rightAlg := by
    apply (zeta_isPrimitive (p := p) (K := K)).integralPowerBasis.algHom_ext
    rw [(zeta_isPrimitive (p := p) (K := K)).integralPowerBasis_gen]
    dsimp only [leftAlg, rightAlg]
    change evaluationHom (K := K) (root ^ (alpha : ZMod p).val)
        (hroot.pow_of_coprime (alpha : ZMod p).val
          (ZMod.val_coe_unit_coprime alpha)) sigma
          (zeta_isPrimitive (p := p) (K := K)).toInteger =
      evaluationHom (K := K) root hroot (alpha * sigma)
        (zeta_isPrimitive (p := p) (K := K)).toInteger
    rw [evaluationHom_zetaInteger, evaluationHom_zetaInteger]
    exact orbitRoot_root_pow root hroot alpha sigma
  exact DFunLike.congr_fun heq x

theorem evaluationKernel_root_pow (root : ZMod q)
    (hroot : IsPrimitiveRoot root p)
    (alpha sigma : KummerCriterion.CyclotomicUnitDelta p) :
    RingHom.ker
        (evaluationHom (K := K) (root ^ (alpha : ZMod p).val)
          (hroot.pow_of_coprime (alpha : ZMod p).val
            (ZMod.val_coe_unit_coprime alpha)) sigma) =
      RingHom.ker
        (evaluationHom (K := K) root hroot (alpha * sigma)) := by
  rw [evaluationHom_root_pow]

/-- Precomposition by a cyclotomic automorphism is multiplication of the
finite-field root index. -/
theorem evaluationHom_comp_cyclotomicRingOfIntegersEquiv
    (root : ZMod q) (hroot : IsPrimitiveRoot root p)
    (sigma tau : KummerCriterion.CyclotomicUnitDelta p) :
    (evaluationHom (K := K) root hroot sigma).comp
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := p) K tau).toRingHom =
      evaluationHom (K := K) root hroot (sigma * tau) := by
  apply RingHom.ext
  intro x
  let leftAlg := ((evaluationHom (K := K) root hroot sigma).comp
    (KummerCriterion.cyclotomicRingOfIntegersEquiv
      (p := p) K tau).toRingHom).toIntAlgHom
  let rightAlg :=
    (evaluationHom (K := K) root hroot (sigma * tau)).toIntAlgHom
  have heq : leftAlg = rightAlg := by
    apply (zeta_isPrimitive (p := p) (K := K)).integralPowerBasis.algHom_ext
    dsimp [leftAlg, rightAlg]
    rw [(zeta_isPrimitive (p := p) (K := K)).integralPowerBasis_gen]
    change evaluationHom (K := K) root hroot sigma
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := p) K tau
            (zeta_isPrimitive (p := p) (K := K)).toInteger) =
      evaluationHom (K := K) root hroot (sigma * tau)
        (zeta_isPrimitive (p := p) (K := K)).toInteger
    have hzeta :
        KummerCriterion.cyclotomicRingOfIntegersEquiv
            (p := p) K tau
              (zeta_isPrimitive (p := p) (K := K)).toInteger =
          (zeta_isPrimitive (p := p) (K := K)).toInteger ^
            (tau : ZMod p).val := by
      exact KummerCriterion.cyclotomicSigmaOfUnit_smul_zetaInteger
        (p := p) K tau
    rw [hzeta, map_pow, evaluationHom_zetaInteger,
      evaluationHom_zetaInteger]
    exact orbitRoot_mul root hroot sigma tau
  exact DFunLike.congr_fun heq x

/-- The corresponding evaluation kernels transform contragrediently by
ideal comap. -/
theorem evaluationKernel_comap_cyclotomicRingOfIntegersEquiv
    (root : ZMod q) (hroot : IsPrimitiveRoot root p)
    (sigma tau : KummerCriterion.CyclotomicUnitDelta p) :
    (RingHom.ker (evaluationHom (K := K) root hroot sigma)).comap
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := p) K tau).toRingHom =
      RingHom.ker (evaluationHom (K := K) root hroot (sigma * tau)) := by
  rw [RingHom.comap_ker,
    evaluationHom_comp_cyclotomicRingOfIntegersEquiv]

theorem orbitRoot_injective (root : ZMod q)
    (hroot : IsPrimitiveRoot root p) :
    Function.Injective (orbitRoot (p := p) root) := by
  intro sigma tau hroots
  have hval : (sigma : ZMod p).val = (tau : ZMod p).val :=
    hroot.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hroots
  apply Units.ext
  exact ZMod.val_injective p hval

theorem evaluationHom_surjective (root : ZMod q)
    (hroot : IsPrimitiveRoot root p)
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    Function.Surjective (evaluationHom (K := K) root hroot sigma) :=
  ZMod.ringHom_surjective _

/-- Distinct finite-field root indices give distinct evaluation kernels. -/
theorem evaluationKernel_injective (root : ZMod q)
    (hroot : IsPrimitiveRoot root p) :
    Function.Injective
      (fun sigma : KummerCriterion.CyclotomicUnitDelta p ↦
        RingHom.ker (evaluationHom (K := K) root hroot sigma)) := by
  intro sigma tau hkernels
  have hhoms :
      evaluationHom (K := K) root hroot sigma =
        evaluationHom (K := K) root hroot tau :=
    ZMod.ringHom_eq_of_ker_eq _ _ hkernels
  apply orbitRoot_injective (p := p) root hroot
  rw [← evaluationHom_zetaInteger (K := K) root hroot sigma,
    ← evaluationHom_zetaInteger (K := K) root hroot tau, hhoms]

/-! ## Exhaustion at a completely split rational prime -/

def rationalPrimeIdeal (q : ℕ) : Ideal ℤ :=
  Ideal.span ({(q : ℤ)} : Set ℤ)

theorem rationalPrimeIdeal_ne_bot :
    rationalPrimeIdeal q ≠ ⊥ := by
  simp [rationalPrimeIdeal, (Fact.out : q.Prime).ne_zero]

theorem rationalPrimeIdeal_isMaximal :
    (rationalPrimeIdeal q).IsMaximal := by
  rw [rationalPrimeIdeal]
  have hq0 : (q : ℤ) ≠ 0 := by
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hqprime : Prime (q : ℤ) :=
    Nat.prime_iff_prime_int.mp (Fact.out : q.Prime)
  exact
    ((Ideal.span_singleton_prime hq0).mpr hqprime).isMaximal
      (by simpa using hq0)

omit [Fact p.Prime] in
theorem auxiliaryPrime_eq (m : ℕ) (hq : q - 1 = m * p) :
    q = m * p + 1 := by
  have hqpos := (Fact.out : q.Prime).pos
  omega

theorem auxiliaryPrime_not_dvd_exponent
    (m : ℕ) (hq : q - 1 = m * p) :
    ¬q ∣ p := by
  have hpq : p < q := by
    have hpgt := (Fact.out : p.Prime).one_lt
    have hqne := (Fact.out : q.Prime).ne_one
    have hqeq := auxiliaryPrime_eq m hq
    have hm : 0 < m := by
      by_contra hm
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      rw [hm0, zero_mul, zero_add] at hqeq
      exact hqne hqeq
    have hpm : p ≤ m * p := Nat.le_mul_of_pos_left p hm
    omega
  exact Nat.not_dvd_of_pos_of_lt (Fact.out : p.Prime).pos hpq

theorem orderOf_auxiliaryPrime_zmod
    (m : ℕ) (hq : q - 1 = m * p) :
    orderOf (q : ZMod p) = 1 := by
  have hqcast : (q : ZMod p) = 1 := by
    rw [auxiliaryPrime_eq m hq]
    simp
  rw [hqcast, orderOf_one]

theorem gal_ncard_eq_exponent_sub_one :
    Nat.card Gal(K/ℚ) = p - 1 := by
  calc
    Nat.card Gal(K/ℚ) = Nat.card (ZMod p)ˣ :=
      Nat.card_congr
        (IsCyclotomicExtension.Rat.galEquivZMod p K).toEquiv
    _ = p - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime (Fact.out : p.Prime)]

/-- The congruence q = 1 mod p makes q split into exactly p-1 primes in the
full p-th cyclotomic field. -/
theorem primesOver_ncard_eq_exponent_sub_one
    (m : ℕ) (hq : q - 1 = m * p) :
    ((rationalPrimeIdeal q).primesOver
      (NumberField.RingOfIntegers K)).ncard = p - 1 := by
  letI : (rationalPrimeIdeal q).IsMaximal :=
    rationalPrimeIdeal_isMaximal
  letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  letI : MulSemiringAction Gal(K/ℚ)
      (NumberField.RingOfIntegers K) :=
    IsIntegralClosure.MulSemiringAction ℤ ℚ K
      (NumberField.RingOfIntegers K)
  haveI : IsGaloisGroup Gal(K/ℚ) ℤ
      (NumberField.RingOfIntegers K) :=
    IsGaloisGroup.of_isFractionRing Gal(K/ℚ) ℤ
      (NumberField.RingOfIntegers K) ℚ K
  have hcount :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (G := Gal(K/ℚ)) (rationalPrimeIdeal_ne_bot (q := q))
        (NumberField.RingOfIntegers K)
  unfold rationalPrimeIdeal at hcount
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd
        q K (auxiliaryPrime_not_dvd_exponent m hq),
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd
        q K (auxiliaryPrime_not_dvd_exponent m hq),
      orderOf_auxiliaryPrime_zmod m hq, mul_one, mul_one] at hcount
  unfold rationalPrimeIdeal
  rw [hcount]
  exact gal_ncard_eq_exponent_sub_one

theorem evaluationHom_comp_algebraMap (root : ZMod q)
    (hroot : IsPrimitiveRoot root p)
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    (evaluationHom (K := K) root hroot sigma).comp
        (algebraMap ℤ (NumberField.RingOfIntegers K)) =
      Int.castRingHom (ZMod q) := by
  ext z
  simp

theorem evaluationKernel_under_int (root : ZMod q)
    (hroot : IsPrimitiveRoot root p)
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    (RingHom.ker (evaluationHom (K := K) root hroot sigma)).under ℤ =
      rationalPrimeIdeal q := by
  rw [Ideal.under_def, rationalPrimeIdeal]
  rw [← ZMod.ker_intCastRingHom q]
  rw [← evaluationHom_comp_algebraMap (K := K) root hroot sigma]
  ext z
  rfl

/-- Each explicit evaluation kernel is a prime over the rational auxiliary
prime. -/
def evaluationPrime (root : ZMod q) (hroot : IsPrimitiveRoot root p)
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    (rationalPrimeIdeal q).primesOver
      (NumberField.RingOfIntegers K) :=
  ⟨RingHom.ker (evaluationHom (K := K) root hroot sigma),
    RingHom.ker_isPrime _,
    ⟨(evaluationKernel_under_int (K := K) root hroot sigma).symm⟩⟩

theorem evaluationPrime_injective (root : ZMod q)
    (hroot : IsPrimitiveRoot root p) :
    Function.Injective (evaluationPrime (K := K) root hroot) := by
  intro sigma tau hprimes
  apply evaluationKernel_injective (K := K) root hroot
  exact congrArg Subtype.val hprimes

/-- The explicit finite-field evaluation kernels exhaust every prime above
q. -/
def evaluationPrimeEquiv (m : ℕ) (hq : q - 1 = m * p)
    (root : ZMod q) (hroot : IsPrimitiveRoot root p) :
    KummerCriterion.CyclotomicUnitDelta p ≃
      (rationalPrimeIdeal q).primesOver
        (NumberField.RingOfIntegers K) := by
  letI : (rationalPrimeIdeal q).IsMaximal :=
    rationalPrimeIdeal_isMaximal
  refine Equiv.ofBijective (evaluationPrime (K := K) root hroot) ?_
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · exact evaluationPrime_injective (K := K) root hroot
  · rw [ZMod.card_units_eq_totient,
      Nat.totient_prime (Fact.out : p.Prime)]
    have hcard :=
      primesOver_ncard_eq_exponent_sub_one (K := K) m hq
    change Nat.card ((rationalPrimeIdeal q).primesOver
      (NumberField.RingOfIntegers K)) = p - 1 at hcard
    simpa only [Nat.card_eq_fintype_card] using hcard.symm

/-- Every prime above q is the kernel of exactly one evaluation in the
finite-field root orbit. -/
theorem exists_evaluationKernel_eq_of_mem_primesOver
    (m : ℕ) (hq : q - 1 = m * p)
    (root : ZMod q) (hroot : IsPrimitiveRoot root p)
    (P : (rationalPrimeIdeal q).primesOver
      (NumberField.RingOfIntegers K)) :
    ∃ sigma : KummerCriterion.CyclotomicUnitDelta p,
      RingHom.ker (evaluationHom (K := K) root hroot sigma) = P.1 := by
  obtain ⟨sigma, hsigma⟩ :=
    (evaluationPrimeEquiv (K := K) m hq root hroot).surjective P
  exact ⟨sigma, congrArg Subtype.val hsigma⟩

end

end Fermat.Irregular.CyclotomicEvaluationNaturality
