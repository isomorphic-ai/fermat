import Fermat.Descent.Irregular.VandiverPostEquationNinePrime
import Fermat.Descent.Irregular.TakagiHistoricalPrime

/-!
# Prime-generic prepared conjugate equation-(8) pairs

Starting from an explicitly supplied `ConjugateEquationEightPair`, this
module performs the algebra from the paired equation (8) through the
normalized equation (9a).  It absorbs the real quotient unit into both
roots and packages the resulting common real `p`-th-power approximation.

The deep inputs remain visible:

* the caller supplies the conjugate equation-(8) pair (hence no
  unconditional Takagi theorem is assumed);
* coprimality of the two generators is derived from the supplied pair and
  the historical state's source coprimality; and
* the caller either supplies `RealEquationNineGeneratorExtraction` or
  discharges it from explicit plus-class nondivisibility.
-/

namespace Fermat.Irregular.VandiverPreparedPairPrime

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverHistoricalPrime
open Fermat.Irregular.VandiverHistoricalStatePrime
open Fermat.Irregular.VandiverTakagiPairPrime
open Fermat.Irregular.VandiverPostEquationNinePrime
open Fermat.Irregular.VandiverGeneratorSupportPrime
open Fermat.Irregular.TakagiHistoricalPrime
open Fermat.Irregular.VandiverEquationTenPrime
open Fermat.Irregular.VandiverEquationEightAFactorizationPrime

noncomputable section

variable {K : Type} {p r : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

/-! ## Historical Takagi pairs constructed from plus-class data -/

/-- The canonical prepared historical factors give the conjugate
equation-(8) pair at `ζ,ζ⁻¹`. -/
theorem exists_historicalEquationEightPair_one_of_plusClass
    (hp5 : 5 ≤ p)
    (hplus : PlusClassNondivisibility K p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    Nonempty
      (ConjugateEquationEightPair
        hζ s.omega s.theta hζ.unit') := by
  let d : PreparedHistoricalEquationData hζ :=
    preparedHistoricalEquationData hp5 hζ s hs
  have hfactor :
      d.plusFactor * ((hζ.unit' : 𝓞 K) - 1) =
        s.omega + s.theta * (hζ.unit' : 𝓞 K) := by
    change
      historicalZetaFactor (by omega : p ≠ 2) hζ s *
          ((hζ.unit' : 𝓞 K) - 1) =
        s.omega + s.theta * (hζ.unit' : 𝓞 K)
    exact historicalZetaFactor_mul_zeta_sub_one
      (by omega : p ≠ 2) hζ s
  exact
    d.exists_conjugateEquationEightPair hζ hp5 hplus
      hs.1 hs.2.1 hfactor

/-- The transported historical state at primitive root `ζ²` gives the
second conjugate equation-(8) pair without any new global input. -/
theorem exists_historicalEquationEightPair_two_of_plusClass
    (hp5 : 5 ≤ p)
    (hplus : PlusClassNondivisibility K p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    Nonempty
      (ConjugateEquationEightPair
        hζ s.omega s.theta (hζ.unit' ^ 2)) := by
  let hζtwo :=
    hζ.pow_of_coprime 2 (coprime_two_prime hp5)
  let stwo := historicalStateAtTwo hp5 hζ s
  have hstwo : RealSourceAdmissible hζtwo stwo := by
    simpa only [hζtwo, stwo] using
      historicalStateAtTwo_admissible hp5 hζ s hs
  obtain ⟨pair⟩ :=
    exists_historicalEquationEightPair_one_of_plusClass
      hp5 hplus hζtwo stwo hstwo
  have hassoc :
      Associated ((hζ.unit' : 𝓞 K) - 1)
        ((hζtwo.unit' : 𝓞 K) - 1) := by
    simpa only [hζtwo, powTwoPrimitiveRoot_unit hp5 hζ,
      Units.val_pow_eq_pow_val] using
      hζ.unit'_coe.associated_sub_one_pow_sub_one_of_coprime
        (coprime_two_prime hp5)
  refine
    ⟨{ rplus := pair.rplus
       rminus := pair.rminus
       coefficient := pair.coefficient
       coefficient_real := pair.coefficient_real
       equation_plus := ?_
       equation_minus := ?_
       conjugate := pair.conjugate
       rplus_not_ramified := ?_
       rminus_not_ramified := ?_ }⟩
  · simpa only [hζtwo, stwo, historicalStateAtTwo,
      powTwoPrimitiveRoot_unit hp5 hζ,
      Units.val_pow_eq_pow_val] using pair.equation_plus
  · simpa only [hζtwo, stwo, historicalStateAtTwo,
      powTwoPrimitiveRoot_unit hp5 hζ] using pair.equation_minus
  · exact fun h ↦
      pair.rplus_not_ramified
        ((hassoc.dvd_iff_dvd_left).mp h)
  · exact fun h ↦
      pair.rminus_not_ramified
        ((hassoc.dvd_iff_dvd_left).mp h)

/-- A normalized conjugate equation-(8) pair after equation (9), with
the quotient unit absorbed into both roots. -/
structure PreparedEquationEightPair
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (s : HistoricalState hζ) (t : (𝓞 K)ˣ)
    extends
      ConjugateEquationEightPair hζ s.omega s.theta t where
  mu : 𝓞 K
  mu_real :
    NumberField.IsCMField.ringOfIntegersComplexConj K mu = mu
  mu_not_ramified :
    ¬ (hζ.unit' : 𝓞 K) - 1 ∣ mu
  close_plus :
    ((hζ.unit' : 𝓞 K) - 1) ^ ((2 * s.m - 2) * p) ∣
      rplus - mu ^ p
  close_minus :
    ((hζ.unit' : 𝓞 K) - 1) ^ ((2 * s.m - 2) * p) ∣
      rminus - mu ^ p

namespace PreparedEquationEightPair

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
  (s : HistoricalState hζ) (t : (𝓞 K)ˣ)
  (d : PreparedEquationEightPair hζ s t)

/-- The prepared pair retains the universal quadratic equation. -/
lemma quadraticEquation :
    s.omega ^ 2 +
        ((t : 𝓞 K) + (t⁻¹ : (𝓞 K)ˣ)) *
          (s.omega * s.theta) +
        s.theta ^ 2 =
      ((1 - (t : 𝓞 K)) * (1 - (t⁻¹ : (𝓞 K)ˣ))) *
        ((d.coefficient ^ 2 : (𝓞 K)ˣ) *
          (d.rplus * d.rminus) ^ p) :=
  d.toConjugateEquationEightPair.quadraticEquation
    hζ s.omega s.theta t

/-- The product of the two prepared roots is literally real. -/
lemma product_real :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (d.rplus * d.rminus) =
      d.rplus * d.rminus :=
  d.toConjugateEquationEightPair.product_real
    hζ s.omega s.theta t

/-- Quadratic equation (10) for the prepared pair at `ζ,ζ⁻¹`. -/
lemma quadraticEquation_one
    (d : PreparedEquationEightPair hζ s hζ.unit') :
    s.omega ^ 2 +
        equationTenTraceOne hζ * (s.omega * s.theta) +
        s.theta ^ 2 =
      kappa hζ *
        ((d.coefficient ^ 2 : (𝓞 K)ˣ) *
          (d.rplus * d.rminus) ^ p) := by
  simpa only [equationTenTraceOne, kappa] using
    d.quadraticEquation hζ s hζ.unit'

/-- Quadratic equation (10) for the prepared pair at `ζ²,ζ⁻²`. -/
lemma quadraticEquation_two
    (hp5 : 5 ≤ p)
    (d : PreparedEquationEightPair hζ s (hζ.unit' ^ 2)) :
    s.omega ^ 2 +
        equationTenTraceTwo hζ * (s.omega * s.theta) +
        s.theta ^ 2 =
      kappa hζ *
        ((equationTenTraceTwoUnit hp5 hζ * d.coefficient ^ 2 :
            (𝓞 K)ˣ) *
          (d.rplus * d.rminus) ^ p) := by
  have htrace :
      (((hζ.unit' ^ 2 : (𝓞 K)ˣ) : 𝓞 K) +
          (((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) =
        equationTenTraceTwo hζ := by
    simp only [equationTenTraceTwo, Units.val_pow_eq_pow_val]
    congr 1
  have hden :
      (1 - ((hζ.unit' ^ 2 : (𝓞 K)ˣ) : 𝓞 K)) *
          (1 - (((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) =
        kappa hζ *
          (equationTenTraceTwoUnit hp5 hζ : 𝓞 K) := by
    calc
      _ =
          kappa
            (hζ.pow_of_coprime 2
              (coprime_two_prime hp5)) := by
        simp only [kappa, powTwoPrimitiveRoot_unit hp5 hζ]
      _ = _ := kappa_powTwoPrimitiveRoot hp5 hζ
  have hq := d.quadraticEquation hζ s (hζ.unit' ^ 2)
  rw [htrace, hden] at hq
  calc
    s.omega ^ 2 +
          equationTenTraceTwo hζ * (s.omega * s.theta) +
          s.theta ^ 2 =
        (kappa hζ *
            (equationTenTraceTwoUnit hp5 hζ : 𝓞 K)) *
          ((d.coefficient ^ 2 : (𝓞 K)ˣ) *
            (d.rplus * d.rminus) ^ p) := hq
    _ = kappa hζ *
        ((equationTenTraceTwoUnit hp5 hζ * d.coefficient ^ 2 :
            (𝓞 K)ˣ) *
          (d.rplus * d.rminus) ^ p) := by
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      ring

end PreparedEquationEightPair

/-- Equations (8) at `a,-a`, together with (8a), give the exact
difference equation used before (9).  The statement is uniform for
`p = 2*r+1`; no class-number input occurs. -/
theorem exists_equationEight_difference
    (hcop2 : Nat.Coprime 2 p) (hr : p = 2 * r + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (a m : ℕ) (ha : a.Coprime p) (hm : 1 < m)
    (omega theta rhoPlus rhoMinus rhoZero : 𝓞 K)
    (eta etaZero : (𝓞 K)ˣ)
    (hplus :
      omega + (hζ.unit' ^ a : (𝓞 K)ˣ) * theta =
        (1 - (hζ.unit' ^ a : (𝓞 K)ˣ)) *
          eta * rhoPlus ^ p)
    (hminus :
      omega + ((hζ.unit' ^ a)⁻¹ : (𝓞 K)ˣ) * theta =
        (1 - ((hζ.unit' ^ a)⁻¹ : (𝓞 K)ˣ)) *
          eta * rhoMinus ^ p)
    (hzero :
      omega + theta =
        etaZero * kappa hζ ^ (p * m - r) * rhoZero ^ p) :
    ∃ epsilon : (𝓞 K)ˣ,
      rhoPlus ^ p - rhoMinus ^ p =
        epsilon *
          (((hζ.unit' : 𝓞 K) - 1) ^ (2 * m - 1) *
            rhoZero) ^ p := by
  let t : (𝓞 K)ˣ := hζ.unit' ^ a
  have htprim : IsPrimitiveRoot (t : 𝓞 K) p :=
    hζ.unit'_coe.pow_of_coprime a ha
  let htplus : IsUnit ((1 : 𝓞 K) + t) := by
    simpa [add_comm] using
      htprim.geom_sum_isUnit
        (Fact.out : Nat.Prime p).two_le hcop2
  let uplus : (𝓞 K)ˣ := htplus.unit
  have huplus : (uplus : 𝓞 K) = 1 + (t : 𝓞 K) :=
    htplus.unit_spec
  obtain ⟨u, hu⟩ :=
    hζ.unit'_coe.associated_sub_one_pow_sub_one_of_coprime ha
  let uden : (𝓞 K)ˣ := -u
  have huden :
      (1 : 𝓞 K) - (t : 𝓞 K) =
        (uden : 𝓞 K) * ((hζ.unit' : 𝓞 K) - 1) := by
    dsimp [t, uden]
    calc
      (1 : 𝓞 K) - (hζ.unit' : 𝓞 K) ^ a =
          -((hζ.unit' : 𝓞 K) ^ a - 1) := by ring
      _ = -(((hζ.unit' : 𝓞 K) - 1) * (u : 𝓞 K)) := by
        rw [hu]
      _ = (-(u : 𝓞 K)) *
          ((hζ.unit' : 𝓞 K) - 1) := by ring
  have helim :=
    equationEight_pair_difference p t eta
      omega theta rhoPlus rhoMinus
      (by simpa only [t] using hplus)
      (by simpa only [t] using hminus)
  let E : ℕ := p * m - r
  let N : ℕ := (2 * m - 1) * p
  have hexp : 2 * E = N + 1 := by
    dsimp [E, N]
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
    simp only [one_mul]
    rw [show 2 * (p * m) = 2 * m * p by ring]
    have hlarge : p ≤ 2 * m * p := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right p (show 1 ≤ 2 * m by omega)
    omega
  have hkappa :
      kappa hζ ^ E =
        ((kappaUnit hζ ^ E : (𝓞 K)ˣ) : 𝓞 K) *
          ((hζ.unit' : 𝓞 K) - 1) ^ (N + 1) := by
    rw [kappa_pow_eq_kappaUnit_pow_mul, hexp]
  have hkappa' :
      kappa hζ ^ E =
        ((kappaUnit hζ ^ E : (𝓞 K)ˣ) : 𝓞 K) *
          ((hζ.unit' : 𝓞 K) - 1) *
            ((hζ.unit' : 𝓞 K) - 1) ^ N := by
    rw [hkappa, pow_succ']
    ring
  let leftUnit : (𝓞 K)ˣ := uden * eta
  let rightUnit : (𝓞 K)ˣ :=
    uplus * etaZero * kappaUnit hζ ^ E
  have hpi : (hζ.unit' : 𝓞 K) - 1 ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero
      (Fact.out : Nat.Prime p).one_lt
  have hcancel :
      (leftUnit : 𝓞 K) *
          (rhoPlus ^ p - rhoMinus ^ p) =
        (rightUnit : 𝓞 K) *
          ((hζ.unit' : 𝓞 K) - 1) ^ N * rhoZero ^ p := by
    apply mul_left_cancel₀ hpi
    calc
      ((hζ.unit' : 𝓞 K) - 1) *
            ((leftUnit : 𝓞 K) *
              (rhoPlus ^ p - rhoMinus ^ p)) =
          (1 - (t : 𝓞 K)) * eta *
            (rhoPlus ^ p - rhoMinus ^ p) := by
        dsimp [leftUnit]
        rw [huden]
        ring
      _ = (1 + (t : 𝓞 K)) * (omega + theta) := helim
      _ = ((hζ.unit' : 𝓞 K) - 1) *
          ((rightUnit : 𝓞 K) *
            ((hζ.unit' : 𝓞 K) - 1) ^ N *
              rhoZero ^ p) := by
        have hzero' :
            omega + theta =
              etaZero * kappa hζ ^ E * rhoZero ^ p := by
          simpa only [E] using hzero
        rw [← huplus, hzero', hkappa']
        dsimp [rightUnit]
        ring
  let epsilon : (𝓞 K)ˣ := leftUnit⁻¹ * rightUnit
  refine ⟨epsilon, ?_⟩
  have hdiff :
      rhoPlus ^ p - rhoMinus ^ p =
        (epsilon : 𝓞 K) *
          ((hζ.unit' : 𝓞 K) - 1) ^ N * rhoZero ^ p := by
    calc
      rhoPlus ^ p - rhoMinus ^ p =
          (leftUnit⁻¹ : (𝓞 K)ˣ) *
            ((leftUnit : 𝓞 K) *
              (rhoPlus ^ p - rhoMinus ^ p)) := by
        rw [← mul_assoc, ← Units.val_mul]
        simp
      _ = (leftUnit⁻¹ : (𝓞 K)ˣ) *
          ((rightUnit : 𝓞 K) *
            ((hζ.unit' : 𝓞 K) - 1) ^ N *
              rhoZero ^ p) := by rw [hcancel]
      _ = (epsilon : 𝓞 K) *
          ((hζ.unit' : 𝓞 K) - 1) ^ N * rhoZero ^ p := by
        dsimp [epsilon]
        ring
  rw [hdiff]
  dsimp [N]
  rw [mul_pow, ← pow_mul]
  ring

/-- The two generators in any supplied conjugate equation-(8) pair at
`ζ ^ a, ζ ^ (-a)` are coprime when `a` is prime to the odd prime `p`.

This is the prime-generic form of the separate historical lemmas at
`a = 1` and `a = 2`. -/
theorem equationEight_pair_generators_coprime
    (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (s : HistoricalState hζ)
    (a : ℕ) (ha : a.Coprime p)
    (pair :
      ConjugateEquationEightPair hζ s.omega s.theta
        (hζ.unit' ^ a)) :
    IsCoprime pair.rplus pair.rminus := by
  let t : (𝓞 K)ˣ := hζ.unit' ^ a
  let pi : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  have hpgt2 : 2 < p := by
    have hpOne := (Fact.out : Nat.Prime p).one_lt
    omega
  have hpi0 : pi ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero
      (Fact.out : Nat.Prime p).one_lt
  have htprim : IsPrimitiveRoot (t : 𝓞 K) p := by
    dsimp [t]
    exact hζ.unit'_coe.pow_of_coprime a ha
  have htneone : (t : 𝓞 K) ≠ 1 :=
    htprim.ne_one (Fact.out : Nat.Prime p).one_lt
  have htPow : (t : 𝓞 K) ^ p = 1 :=
    htprim.pow_eq_one
  have htUnitPow : t ^ p = 1 := by
    apply Units.ext
    exact htPow
  have htInvPow : ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, htUnitPow]
    simp
  have hrootOne :
      (1 : 𝓞 K) ∈
        Polynomial.nthRootsFinset p (1 : 𝓞 K) :=
    Polynomial.one_mem_nthRootsFinset
      (Fact.out : Nat.Prime p).pos
  have hrootT :
      (t : 𝓞 K) ∈
        Polynomial.nthRootsFinset p (1 : 𝓞 K) := by
    rw [Polynomial.mem_nthRootsFinset
      (Fact.out : Nat.Prime p).pos]
    exact htPow
  have hrootTInv :
      ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ∈
        Polynomial.nthRootsFinset p (1 : 𝓞 K) := by
    rw [Polynomial.mem_nthRootsFinset
      (Fact.out : Nat.Prime p).pos]
    exact htInvPow
  have htInvNeOne : ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ≠ 1 := by
    intro hinv
    apply htneone
    have hinvUnit : t⁻¹ = 1 := Units.ext hinv
    exact congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K)
      (inv_eq_one.mp hinvUnit)
  have htDistinct :
      (t : 𝓞 K) ≠ ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
    intro heq
    have htSq : (t : 𝓞 K) ^ 2 = 1 := by
      calc
        (t : 𝓞 K) ^ 2 =
            (t : 𝓞 K) * (t : 𝓞 K) := pow_two _
        _ = (t : 𝓞 K) *
            ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) :=
          congrArg ((t : 𝓞 K) * ·) heq
        _ = 1 := by
          rw [← Units.val_mul]
          simp
    have hpDvdTwo : p ∣ 2 :=
      (htprim.pow_eq_one_iff_dvd 2).mp htSq
    have hpLeTwo : p ≤ 2 :=
      Nat.le_of_dvd (by norm_num) hpDvdTwo
    omega
  have hcPlusBase :
      Associated (1 - (t : 𝓞 K)) pi := by
    exact
      (hζ.unit'_coe.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
          (Fact.out : Nat.Prime p)
          hrootOne hrootT htneone.symm).symm
  have hcMinusBase :
      Associated
        (1 - ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) pi := by
    exact
      (hζ.unit'_coe.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
          (Fact.out : Nat.Prime p)
          hrootOne hrootTInv htInvNeOne.symm).symm
  have hcPlus :
      Associated
        ((1 - (t : 𝓞 K)) * (pair.coefficient : 𝓞 K)) pi :=
    associated_mul_unit_left_iff.mpr hcPlusBase
  have hcMinus :
      Associated
        ((1 - ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) *
          (pair.coefficient : 𝓞 K)) pi :=
    associated_mul_unit_left_iff.mpr hcMinusBase
  have ht :
      Associated
        ((t : 𝓞 K) - ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) pi := by
    exact
      (hζ.unit'_coe.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
          (Fact.out : Nat.Prime p)
          hrootT hrootTInv htDistinct).symm
  exact coprime_generators_of_distinct_linearEquations
    hpi0 s.coprime_omega_theta hcPlus hcMinus ht
    (by simpa only [t, mul_assoc] using pair.equation_plus)
    (by simpa only [t, mul_assoc] using pair.equation_minus)

set_option maxRecDepth 50000 in
/-- Prepare an already-supplied conjugate equation-(8) pair.

No theorem constructing `pair` is invoked here. -/
theorem exists_preparedEquationEightPair
    (hp2 : p ≠ 2) (hcop2 : Nat.Coprime 2 p)
    (hr : p = 2 * r + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (s : HistoricalState hζ)
    (a : ℕ) (ha : a.Coprime p)
    (pair :
      ConjugateEquationEightPair hζ s.omega s.theta
        (hζ.unit' ^ a))
    (rhoZero : 𝓞 K) (etaZero : (𝓞 K)ˣ)
    (hzero :
      s.omega + s.theta =
        etaZero * kappa hζ ^ (p * s.m - r) * rhoZero ^ p)
    (hextract : RealEquationNineGeneratorExtraction hζ) :
    Nonempty
      (PreparedEquationEightPair hζ s (hζ.unit' ^ a)) := by
  classical
  have hpair : IsCoprime pair.rplus pair.rminus :=
    equationEight_pair_generators_coprime hp2 hζ s a ha pair
  obtain ⟨epsilon, hdifference⟩ :=
    exists_equationEight_difference hcop2 hr
      hζ a s.m ha s.one_lt_m
      s.omega s.theta pair.rplus pair.rminus rhoZero
      pair.coefficient etaZero
      pair.equation_plus pair.equation_minus hzero
  obtain ⟨normalizedPlus, normalizedMinus,
      hnplus, hnminus, hclose, hnconj, hnminusNot⟩ :=
    Fermat.Irregular.VandiverEquationNinePrime.equationNineA_normalized_conjugate
      hp2 hr hζ s.m s.one_lt_m
      pair.rplus pair.rminus rhoZero epsilon
      hdifference pair.conjugate pair.rminus_not_ramified
  have hnormalizedPair :
      IsCoprime normalizedPlus normalizedMinus := by
    have hpowers :
        IsCoprime (normalizedPlus ^ p) (normalizedMinus ^ p) := by
      rw [hnplus, hnminus]
      exact hpair.pow_left.pow_right
    exact
      (IsCoprime.pow_left_iff (Fact.out : Nat.Prime p).pos).mp
        ((IsCoprime.pow_right_iff
          (Fact.out : Nat.Prime p).pos).mp hpowers)
  let D : ℕ := (2 * s.m - 2) * p
  let post : PostEquationNineNormalizedData hζ :=
    { m := s.m
      one_lt_m := s.one_lt_m
      rplus := normalizedPlus
      rminus := normalizedMinus
      rzero := rhoZero
      epsilon := epsilon
      equation := by
        rw [hnplus, hnminus]
        exact hdifference
      conjugate := hnconj
      coprime := hnormalizedPair
      rminus_not_ramified := hnminusNot
      depth := D + 1
      two_le_depth := by
        have hm : 1 < s.m := s.one_lt_m
        have hcoefficient : 1 ≤ 2 * s.m - 2 := by
          omega
        have hproduct : 2 ≤ (2 * s.m - 2) * p := by
          simpa only [one_mul] using
            Nat.mul_le_mul hcoefficient
              (Fact.out : Nat.Prime p).two_le
        dsimp [D]
        omega
      close := by
        simpa only [D] using hclose }
  obtain ⟨mu, delta, -, hmureal, hquotient, hmuNot,
      hminusQ, hplusQ⟩ :=
    post.exists_real_generator hζ hp2 hextract
  have hdeltaReal :
      NumberField.IsCMField.unitsComplexConj K delta = delta :=
    post.generator_unit_real hζ hp2
      mu delta hmureal hmuNot hquotient
  let rplus : 𝓞 K :=
    (delta⁻¹ : (𝓞 K)ˣ) * normalizedPlus
  let rminus : 𝓞 K :=
    (delta⁻¹ : (𝓞 K)ˣ) * normalizedMinus
  let coefficient : (𝓞 K)ˣ :=
    pair.coefficient * delta ^ p
  have hcoefficientReal :
      NumberField.IsCMField.unitsComplexConj K coefficient =
        coefficient := by
    dsimp [coefficient]
    rw [map_mul, map_pow, pair.coefficient_real, hdeltaReal]
  have hdeltaCancel :
      (delta : 𝓞 K) ^ p *
          ((delta⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ p = 1 := by
    rw [← mul_pow, ← Units.val_mul]
    simp
  have hequationPlus :
      s.omega + (hζ.unit' ^ a : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit' ^ a : (𝓞 K)ˣ)) *
          coefficient * rplus ^ p := by
    have hscaled :
        (coefficient : 𝓞 K) * rplus ^ p =
          (pair.coefficient : 𝓞 K) * pair.rplus ^ p := by
      dsimp [coefficient, rplus]
      simp only [mul_pow]
      rw [hnplus]
      calc
        ((pair.coefficient : 𝓞 K) * (delta : 𝓞 K) ^ p) *
            (((delta⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ p *
              pair.rplus ^ p) =
          (pair.coefficient : 𝓞 K) *
            (((delta : 𝓞 K) ^ p *
              ((delta⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ p) *
                pair.rplus ^ p) := by ac_rfl
        _ = (pair.coefficient : 𝓞 K) *
            pair.rplus ^ p := by
          rw [hdeltaCancel, one_mul]
    calc
      s.omega + (hζ.unit' ^ a : (𝓞 K)ˣ) * s.theta =
          (1 - (hζ.unit' ^ a : (𝓞 K)ˣ)) *
            ((pair.coefficient : 𝓞 K) * pair.rplus ^ p) := by
        simpa only [mul_assoc] using pair.equation_plus
      _ = (1 - (hζ.unit' ^ a : (𝓞 K)ˣ)) *
          ((coefficient : 𝓞 K) * rplus ^ p) := by
        rw [hscaled]
      _ = _ := by rw [mul_assoc]
  have hequationMinus :
      s.omega + ((hζ.unit' ^ a)⁻¹ : (𝓞 K)ˣ) * s.theta =
        (1 - ((hζ.unit' ^ a)⁻¹ : (𝓞 K)ˣ)) *
          coefficient * rminus ^ p := by
    have hscaled :
        (coefficient : 𝓞 K) * rminus ^ p =
          (pair.coefficient : 𝓞 K) * pair.rminus ^ p := by
      dsimp [coefficient, rminus]
      simp only [mul_pow]
      rw [hnminus]
      calc
        ((pair.coefficient : 𝓞 K) * (delta : 𝓞 K) ^ p) *
            (((delta⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ p *
              pair.rminus ^ p) =
          (pair.coefficient : 𝓞 K) *
            (((delta : 𝓞 K) ^ p *
              ((delta⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ p) *
                pair.rminus ^ p) := by ac_rfl
        _ = (pair.coefficient : 𝓞 K) *
            pair.rminus ^ p := by
          rw [hdeltaCancel, one_mul]
    calc
      s.omega + ((hζ.unit' ^ a)⁻¹ : (𝓞 K)ˣ) * s.theta =
          (1 - ((hζ.unit' ^ a)⁻¹ : (𝓞 K)ˣ)) *
            ((pair.coefficient : 𝓞 K) * pair.rminus ^ p) := by
        simpa only [mul_assoc] using pair.equation_minus
      _ = (1 - ((hζ.unit' ^ a)⁻¹ : (𝓞 K)ˣ)) *
          ((coefficient : 𝓞 K) * rminus ^ p) := by
        rw [hscaled]
      _ = _ := by rw [mul_assoc]
  have hconjugate :
      NumberField.IsCMField.ringOfIntegersComplexConj K rplus =
        rminus := by
    have hdeltaInvReal :
        NumberField.IsCMField.unitsComplexConj K delta⁻¹ =
          delta⁻¹ := by
      rw [map_inv, hdeltaReal]
    dsimp [rplus, rminus]
    rw [map_mul, hnconj]
    exact congrArg
      (fun u : (𝓞 K)ˣ ↦ (u : 𝓞 K) * normalizedMinus)
      hdeltaInvReal
  have hrplusNot :
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rplus := by
    intro h
    have hn :
        (hζ.unit' : 𝓞 K) - 1 ∣ normalizedPlus := by
      have hscaled := dvd_mul_of_dvd_right h (delta : 𝓞 K)
      convert hscaled using 1
      dsimp [rplus]
      rw [← mul_assoc, ← Units.val_mul]
      simp
    have hc :=
      zeta_sub_one_pow_dvd_conj_of_dvd hζ 1 normalizedPlus
        (by simpa only [pow_one] using hn)
    apply hnminusNot
    simpa only [pow_one, hnconj] using hc
  have hrminusNot :
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rminus := by
    intro h
    apply hnminusNot
    have hscaled := dvd_mul_of_dvd_right h (delta : 𝓞 K)
    convert hscaled using 1
    dsimp [rminus]
    rw [← mul_assoc, ← Units.val_mul]
    simp
  have hcloseMinus :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        rminus - mu ^ p := by
    simpa only [post, D, Nat.add_sub_cancel, rminus] using
      post.pow_pred_dvd_inv_unit_mul_rminus_sub_pow
        hζ hp2 mu delta hquotient
  have hclosePlus :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        rplus - mu ^ p := by
    simpa only [post, D, Nat.add_sub_cancel, rplus] using
      post.pow_pred_dvd_inv_unit_mul_rplus_sub_pow
        hζ mu delta hplusQ
  exact
    ⟨{ toConjugateEquationEightPair :=
        { rplus := rplus
          rminus := rminus
          coefficient := coefficient
          coefficient_real := hcoefficientReal
          equation_plus := hequationPlus
          equation_minus := hequationMinus
          conjugate := hconjugate
          rplus_not_ramified := hrplusNot
          rminus_not_ramified := hrminusNot }
       mu := mu
       mu_real := hmureal
       mu_not_ramified := hmuNot
       close_plus := by simpa only [D] using hclosePlus
       close_minus := by simpa only [D] using hcloseMinus }⟩

set_option maxRecDepth 50000 in
/-- Plus-class form of `exists_preparedEquationEightPair`.

The supplied conjugate equation-(8) pair remains the explicit Takagi
boundary.  Its generator coprimality and the post-(9) real-generator
extraction are both discharged here. -/
theorem exists_preparedEquationEightPair_of_plusClass
    (hplus : PlusClassNondivisibility K p)
    (hp2 : p ≠ 2) (hcop2 : Nat.Coprime 2 p)
    (hr : p = 2 * r + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (s : HistoricalState hζ)
    (a : ℕ) (ha : a.Coprime p)
    (pair :
      ConjugateEquationEightPair hζ s.omega s.theta
        (hζ.unit' ^ a))
    (rhoZero : 𝓞 K) (etaZero : (𝓞 K)ˣ)
    (hzero :
      s.omega + s.theta =
        etaZero * kappa hζ ^ (p * s.m - r) * rhoZero ^ p) :
    Nonempty
      (PreparedEquationEightPair hζ s (hζ.unit' ^ a)) := by
  have hpgt2 : 2 < p := by
    have hpOne := (Fact.out : Nat.Prime p).one_lt
    omega
  exact
    exists_preparedEquationEightPair hp2 hcop2 hr hζ s
      a ha pair rhoZero etaZero hzero
      (realEquationNineGeneratorExtraction
        hplus hpgt2 hcop2 hr hζ)

set_option maxRecDepth 50000 in
/-- The first fully prepared historical pair, with both the Takagi pair
and the post-equation-(9) real generator constructed from the same
plus-class witness. -/
theorem exists_historicalPreparedEquationEightPair_one_of_plusClass
    (hplus : PlusClassNondivisibility K p)
    (hp5 : 5 ≤ p) (hcop2 : Nat.Coprime 2 p)
    (hr : p = 2 * r + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s)
    (rhoZero : 𝓞 K) (etaZero : (𝓞 K)ˣ)
    (hzero :
      s.omega + s.theta =
        etaZero * kappa hζ ^ (p * s.m - r) * rhoZero ^ p) :
    Nonempty
      (PreparedEquationEightPair hζ s hζ.unit') := by
  obtain ⟨pair⟩ :=
    exists_historicalEquationEightPair_one_of_plusClass
      hp5 hplus hζ s hs
  have pair' :
      ConjugateEquationEightPair
        hζ s.omega s.theta (hζ.unit' ^ 1) := by
    simpa only [pow_one] using pair
  have hprepared :=
    exists_preparedEquationEightPair_of_plusClass
      hplus (by omega : p ≠ 2) hcop2 hr hζ s
      1 (by simp) pair' rhoZero etaZero hzero
  simpa only [pow_one] using hprepared

set_option maxRecDepth 50000 in
/-- The second fully prepared historical pair at `ζ²,ζ⁻²`.  The
primitive-root transport is entirely algebraic and introduces no new
class-number hypothesis. -/
theorem exists_historicalPreparedEquationEightPair_two_of_plusClass
    (hplus : PlusClassNondivisibility K p)
    (hp5 : 5 ≤ p) (hcop2 : Nat.Coprime 2 p)
    (hr : p = 2 * r + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s)
    (rhoZero : 𝓞 K) (etaZero : (𝓞 K)ˣ)
    (hzero :
      s.omega + s.theta =
        etaZero * kappa hζ ^ (p * s.m - r) * rhoZero ^ p) :
    Nonempty
      (PreparedEquationEightPair
        hζ s (hζ.unit' ^ 2)) := by
  obtain ⟨pair⟩ :=
    exists_historicalEquationEightPair_two_of_plusClass
      hp5 hplus hζ s hs
  exact
    exists_preparedEquationEightPair_of_plusClass
      hplus (by omega : p ≠ 2) hcop2 hr hζ s
      2 hcop2 pair rhoZero etaZero hzero

end

end Fermat.Irregular.VandiverPreparedPairPrime
