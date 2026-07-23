import Fermat.Irregular.VandiverUnitLemma
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Vandiver's historical second-case descent

This module isolates the source-faithful descent in H. S. Vandiver,
*On Fermat's Last Theorem*, Transactions of the AMS 31 (1929), pp. 621--624.
It is the descent following equations (7b)--(10), and is different from the
`m ↦ m - 1` descent extracted in `VandiverCriterion`.

Vandiver starts from

`ω ^ p + θ ^ p = η * (κ ^ m * ξ) ^ p`, with `1 < m`,

where `κ = (1 - ζ) * (1 - ζ⁻¹)`. Equations (7b)--(9a) produce a unit
congruence initially modulo `(1 - ζ) ^ ((2 * m - 2) * p)`. Since `m > 1`,
this implies the precise depth `(1 - ζ) ^ (2 * p)` required by Vandiver's
Lemma 2. After that unit is recognized as a `p`-th power, equations
(10a)--(10b) produce a new equation of the same form whose `ξ` has fewer
distinct prime-ideal factors.

The library does not yet contain Vandiver's real-subfield conjugation and
ideal-principalization calculation proving those two construction steps.
They are therefore exposed below as two explicit propositions:

* `SecondCaseStartsHistoricalDescent` is the source's reduction from a
  rational second-case solution to equation (6);
* `EquationsSevenToTenReduction` is exactly the witness package constructed
  in (7b)--(10b).

Neither is an axiom, and no theorem below claims that numerical Bernoulli
data proves them. From these source obligations and the exact deep
`KummerUnitPowerConclusion`, the well-founded descent and the final
`Fermat.SecondCaseExcluded` implication are kernel-checked here.
-/

namespace Fermat.Irregular.VandiverHistoricalDescent

open scoped nonZeroDivisors NumberField

open Fermat.Irregular.VandiverCriterion

variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]

/-- Vandiver's real cyclotomic factor
`κ = (1 - ζ) * (1 - ζ⁻¹)` from equation (6). -/
def kappa {ζ : K} (hζ : IsPrimitiveRoot ζ p) : 𝓞 K :=
  ((1 : 𝓞 K) - hζ.unit') * ((1 : 𝓞 K) - (hζ.unit')⁻¹)

/-- The equation and coprimality invariant used in Vandiver's infinite
descent. The real-subfield origin of the entries is needed to construct the
reduction package, but not after that package has been obtained, so it is
kept in the explicit source boundary below rather than postulated here. -/
structure HistoricalState {ζ : K} (hζ : IsPrimitiveRoot ζ p) where
  omega : 𝓞 K
  theta : 𝓞 K
  xi : 𝓞 K
  eta : (𝓞 K)ˣ
  m : ℕ
  one_lt_m : 1 < m
  xi_ne_zero : xi ≠ 0
  coprime_omega_theta : IsCoprime omega theta
  coprime_theta_xi : IsCoprime theta xi
  coprime_omega_xi : IsCoprime omega xi
  equation :
    omega ^ p + theta ^ p = eta * (kappa hζ ^ m * xi) ^ p

/-- An additional source invariant on historical states. In Vandiver's
application this is where one records that `ω`, `θ`, and `ξ` come from the
real cyclotomic subfield, together with any ideal-theoretic conditions needed
to repeat equations (7b)--(10).

Parameterizing the descent by this predicate avoids the unnecessarily strong
claim that the historical construction works for arbitrary non-real states.
The starting boundary produces an admissible state and the reduction boundary
proves admissibility of every successor. -/
abbrev HistoricalAdmissibility {ζ : K} (hζ : IsPrimitiveRoot ζ p) :=
  HistoricalState hζ → Prop

/-- The number of distinct prime-ideal factors of the principal ideal `(x)`.
This is the well-founded measure Vandiver explicitly decreases after
equation (10b). -/
noncomputable def distinctPrimeIdealFactorCount (x : 𝓞 K) : ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {x})).toFinset.card

/-- The output of Vandiver's equations (7b)--(10b) for one historical state.

The field `highCongruence` is exactly the congruence in equation (10), at
depth `2 * p`. The last three fields encode (10b): once the quotient unit has
a `p`-th root, a new state exists with exponent `2 * m - 1` and strictly fewer
distinct prime-ideal factors of `ξ`.

Keeping this as data, rather than a proposition which merely says that some
next state exists, makes the exact invocation of Vandiver's Lemma 2 visible
and prevents the deep local hypothesis from being silently weakened. -/
structure EquationSevenToTenData {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (admissible : HistoricalAdmissibility hζ) (s : HistoricalState hζ) where
  quotientUnit : (𝓞 K)ˣ
  rationalBase : ℤ
  highCongruence :
    ((1 : 𝓞 K) - hζ.unit') ^ (2 * p) ∣
      ((quotientUnit : 𝓞 K) - (rationalBase : 𝓞 K) ^ p)
  nextState :
    (v : (𝓞 K)ˣ) → quotientUnit = v ^ p → HistoricalState hζ
  next_admissible :
    ∀ (v : (𝓞 K)ˣ) (hv : quotientUnit = v ^ p),
      admissible (nextState v hv)
  next_exponent :
    ∀ (v : (𝓞 K)ˣ) (hv : quotientUnit = v ^ p),
      (nextState v hv).m = 2 * s.m - 1
  factorCount_decreases :
    ∀ (v : (𝓞 K)ˣ) (hv : quotientUnit = v ^ p),
      distinctPrimeIdealFactorCount (nextState v hv).xi <
        distinctPrimeIdealFactorCount s.xi

/-- Source boundary for the sentence preceding Vandiver's equation (6): a
primitive rational second-case solution supplies a historical descent state.

This proposition is intentionally stated only for the orientation in which
`p ∣ z`; the final theorem rotates the three variables exactly as in the
standard Case-II assembly. -/
def SecondCaseStartsHistoricalDescent {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (admissible : HistoricalAdmissibility hζ) : Prop :=
  ∀ {x y z : ℤ},
    ({x, y, z} : Finset ℤ).gcd id = 1 →
    (p : ℤ) ∣ z → z ≠ 0 → x ^ p + y ^ p = z ^ p →
      ∃ s : HistoricalState hζ, admissible s

/-- Exact formal boundary for Vandiver's construction in equations
(7b)--(10b). It contains no unit-power conclusion: that conclusion is
obtained below only by applying the deep `KummerUnitPowerConclusion`. -/
def EquationsSevenToTenReduction {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (admissible : HistoricalAdmissibility hζ) : Prop :=
  ∀ s : HistoricalState hζ, admissible s →
    Nonempty (EquationSevenToTenData hζ admissible s)

/-! ## The exact depth in equation (10) -/

/-- The congruence recorded by the reduction data is exactly Vandiver's
equation (10), at depth `(1 - ζ) ^ (2 * p)`. -/
lemma equationTen_deepCongruence {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (admissible : HistoricalAdmissibility hζ)
    (s : HistoricalState hζ)
    (d : EquationSevenToTenData hζ admissible s) :
    ((1 : 𝓞 K) - hζ.unit') ^ (2 * p) ∣
      ((d.quotientUnit : 𝓞 K) - (d.rationalBase : 𝓞 K) ^ p) := by
  exact d.highCongruence

/-! ## Well-founded descent -/

/-- Equations (7b)--(10), together with the exact deep unit lemma, rule out
every historical state. The contradiction is Vandiver's infinite descent on
the number of distinct prime-ideal factors of `ξ`. -/
theorem no_historicalState {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (admissible : HistoricalAdmissibility hζ)
    (hreduce : EquationsSevenToTenReduction hζ admissible)
    (hkummer : KummerUnitPowerConclusion K p) :
    ¬ ∃ s : HistoricalState hζ, admissible s := by
  classical
  rintro ⟨s₀, hs₀⟩
  let P : ℕ → Prop := fun n ↦
    ∃ s : HistoricalState hζ,
      admissible s ∧ distinctPrimeIdealFactorCount s.xi = n
  have hP : ∃ n, P n :=
    ⟨distinctPrimeIdealFactorCount s₀.xi, s₀, hs₀, rfl⟩
  obtain ⟨s, hs_admissible, hs_count⟩ := Nat.find_spec hP
  obtain ⟨d⟩ := hreduce s hs_admissible
  obtain ⟨v, hv⟩ := hkummer hζ d.quotientUnit
    ⟨d.rationalBase, equationTen_deepCongruence hζ admissible s d⟩
  let next := d.nextState v hv
  have hnext : P (distinctPrimeIdealFactorCount next.xi) :=
    ⟨next, d.next_admissible v hv, rfl⟩
  have hminimal := Nat.find_min' hP hnext
  have hdecrease := d.factorCount_decreases v hv
  dsimp only [next] at hminimal hdecrease
  omega

/-- No primitive integer solution exists in the orientation `p ∣ z` once
the source's starting reduction, equations (7b)--(10), and Lemma 2 are
available. -/
theorem not_exists_primitive_int_solution {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (admissible : HistoricalAdmissibility hζ)
    (hstart : SecondCaseStartsHistoricalDescent hζ admissible)
    (hreduce : EquationsSevenToTenReduction hζ admissible)
    (hkummer : KummerUnitPowerConclusion K p) :
    ¬ ∃ (x y z : ℤ),
      ({x, y, z} : Finset ℤ).gcd id = 1 ∧ (p : ℤ) ∣ z ∧ z ≠ 0 ∧
      x ^ p + y ^ p = z ^ p := by
  rintro ⟨x, y, z, hgcd, hz, hz0, e⟩
  exact no_historicalState hζ admissible hreduce hkummer
    (hstart hgcd hz hz0 e)

private lemma int_gcd_left_comm (a b c : ℤ) :
    Int.gcd a (Int.gcd b c) = Int.gcd b (Int.gcd a c) := by
  rw [← Int.gcd_assoc, ← Int.gcd_assoc, Int.gcd_comm a b]

/-- Source-faithful historical Case II: Vandiver's starting reduction and
equations (7b)--(10), combined with the exact `λ ^ (2 * p)` unit conclusion,
imply `Fermat.SecondCaseExcluded p`.

This theorem is an unconditional implication between explicit propositions;
it does not assert either of the two source boundaries. -/
theorem secondCaseExcluded_of_historical_descent {ζ : K}
    (hodd : p ≠ 2) (hζ : IsPrimitiveRoot ζ p)
    (admissible : HistoricalAdmissibility hζ)
    (hstart : SecondCaseStartsHistoricalDescent hζ admissible)
    (hreduce : EquationsSevenToTenReduction hζ admissible)
    (hkummer : KummerUnitPowerConclusion K p) :
    Fermat.SecondCaseExcluded p := by
  intro a b c ha hb hc hgcd hcase e
  have hpodd := hpri.out.odd_of_ne_two hodd
  obtain hab | hpc := (Nat.prime_iff_prime_int.mp hpri.out).dvd_or_dvd hcase
  · obtain hpa | hpb := (Nat.prime_iff_prime_int.mp hpri.out).dvd_or_dvd hab
    · refine not_exists_primitive_int_solution hζ admissible hstart hreduce hkummer
        ⟨b, -c, -a, ?_, ?_, ?_, ?_⟩
      · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd,
          Int.neg_gcd, ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty,
          int_gcd_left_comm _ a]
      · rwa [dvd_neg]
      · rwa [ne_eq, neg_eq_zero]
      · simp [hpodd.neg_pow, ← e]
    · refine not_exists_primitive_int_solution hζ admissible hstart hreduce hkummer
        ⟨-c, a, -b, ?_, ?_, ?_, ?_⟩
      · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd,
          Int.neg_gcd, ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty,
          int_gcd_left_comm _ c]
      · rwa [dvd_neg]
      · rwa [ne_eq, neg_eq_zero]
      · simp [hpodd.neg_pow, ← e]
  · exact not_exists_primitive_int_solution hζ admissible hstart hreduce hkummer
      ⟨a, b, c, hgcd, hpc, hc, e⟩

/-- The historical descent assembled directly with Vandiver's Lemma 2 and
the repository's finite Bernoulli cube condition. The only hypotheses left
are the explicitly named source theorem boundaries: Lemma 2 itself, the
passage to equation (6), and the construction in equations (7b)--(10b). -/
theorem secondCaseExcluded_of_vandiver_lemmaTwo {ζ : K}
    [IsCyclotomicExtension {p} ℚ K]
    (hodd : p ≠ 2) (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot ζ p)
    (admissible : HistoricalAdmissibility hζ)
    (hstart : SecondCaseStartsHistoricalDescent hζ admissible)
    (hreduce : EquationsSevenToTenReduction hζ admissible)
    (hLemmaTwo : Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K p)
    (hB : Fermat.Irregular.VandiverData.BernoulliCubeCondition p) :
    Fermat.SecondCaseExcluded p :=
  secondCaseExcluded_of_historical_descent hodd hζ admissible hstart hreduce
    (Fermat.Irregular.VandiverUnitLemma.kummerUnitPowerConclusion_of_lemmaTwo
      hp5 hLemmaTwo hB)

end Fermat.Irregular.VandiverHistoricalDescent
