import Fermat.Irregular.VandiverCriterion

/-!
# Vandiver's Lemma 1: the singular-primary principalization boundary

Vandiver's Lemma 1 in *On Fermat's Last Theorem*, Transactions AMS 31
(1929), pp. 616 and 622, is the class-field-theoretic input immediately
preceding equation (7a).  In modern notation it says that, when the real
(`second`) factor of the cyclotomic class number is prime to `p`, a primary
generator whose principal ideal is a `p`th ideal power cannot have a
nonprincipal ideal root.

The proof cited by Vandiver uses either Furtwängler reciprocity or Takagi's
existence theorem for class fields.  Neither theorem is currently available
in Mathlib.  This module therefore records the exact conclusion as the named
proposition `LemmaOne`; it is not an axiom.  Everything after that
single boundary—including the chosen generator and the ideal identity used
in equation (7a)—is proved below.

Here `IsKummerPrimary` uses the singular-primary congruence

`a ≡ c^p (mod (zeta - 1)^p)`

together with primeness to the ramified prime.  The weaker congruence modulo
`(zeta - 1)^2` is usually called *semiprimary* in modern treatments.
-/

namespace Fermat.Irregular.VandiverLemmaOne

open scoped NumberField

open Fermat.Irregular.VandiverCriterion

noncomputable section

variable {K : Type*} {p : ℕ} [Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- The local congruence in Kummer's definition of a primary cyclotomic
integer, including primeness to the unique ramified prime above `p`. -/
def IsKummerPrimary {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : 𝓞 K) : Prop :=
  ¬ (hζ.unit' : 𝓞 K) - 1 ∣ a ∧
    ∃ c : ℤ,
      ((hζ.unit' : 𝓞 K) - 1) ^ p ∣
        a - (c : 𝓞 K) ^ p

/-- Every `p`th power is congruent to the `p`th power of a rational
integer modulo `(ζ - 1)^p`.

Choose `c : ℤ` with `a ≡ c (mod ζ - 1)`.  In the binomial expansion of
`(c + (ζ - 1)k)^p`, the last term visibly contains `(ζ - 1)^p`, while
every mixed term contains both `(ζ - 1)` and the rational prime `p`.
The standard cyclotomic association

`p ~ (ζ - 1)^(p-1)`

then supplies the remaining `p - 1` factors. -/
theorem exists_int_pow_congruent_mod_primary
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : 𝓞 K) :
    ∃ c : ℤ,
      ((hζ.unit' : 𝓞 K) - 1) ^ p ∣
        a ^ p - (c : 𝓞 K) ^ p := by
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  obtain ⟨c, k, hk⟩ := exists_zeta_sub_one_dvd_sub_Int hζ a
  have ha : a = (c : 𝓞 K) + π * k := by
    rw [sub_eq_iff_eq_add] at hk
    simpa only [π, add_comm] using hk
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : p.Prime)
      (c : 𝓞 K) (π * k)
  have hpdiv : π ^ (p - 1) ∣ (p : 𝓞 K) := by
    simpa only [π] using (associated_zeta_sub_one_pow_prime hζ).dvd
  obtain ⟨t, ht⟩ := hpdiv
  have hlast : π ^ p ∣ (π * k) ^ p := by
    rw [mul_pow]
    exact dvd_mul_right _ _
  have hmixed : π ^ p ∣
      (p : 𝓞 K) * (c : 𝓞 K) * (π * k) * r := by
    refine ⟨t * (c : 𝓞 K) * k * r, ?_⟩
    rw [ht]
    calc
      π ^ (p - 1) * t * (c : 𝓞 K) * (π * k) * r =
          (π ^ (p - 1) * π) * (t * (c : 𝓞 K) * k * r) := by ring
      _ = π ^ p * (t * (c : 𝓞 K) * k * r) := by
        rw [← pow_succ, Nat.sub_add_cancel
          (Fact.out : p.Prime).one_lt.le]
  refine ⟨c, ?_⟩
  rw [ha, hr]
  convert dvd_add hlast hmixed using 1
  all_goals ring

/-- A pair of nonramified factors that agree modulo `(ζ - 1)^p` gives a
Kummer-primary generator after the standard `a * b^(p-1)` recombination.

The congruence is elementary:

`a * b^(p-1) ≡ b^p ≡ c^p (mod (ζ - 1)^p)`.

This is the local calculation immediately before Vandiver invokes his
global Lemma 1. -/
theorem isKummerPrimary_mul_pow_pred_of_congruent
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a b : 𝓞 K)
    (ha : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ a)
    (hb : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ b)
    (hab : ((hζ.unit' : 𝓞 K) - 1) ^ p ∣ a - b) :
    IsKummerPrimary hζ (a * b ^ (p - 1)) := by
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  have hpred : p - 1 ≠ 0 := by
    have := (Fact.out : p.Prime).one_lt
    omega
  have hbpow : ¬ π ∣ b ^ (p - 1) := by
    intro h
    apply hb
    exact (hζ.zeta_sub_one_prime'.dvd_pow_iff_dvd hpred).mp h
  refine ⟨hζ.zeta_sub_one_prime'.not_dvd_mul ha hbpow, ?_⟩
  obtain ⟨c, hc⟩ := exists_int_pow_congruent_mod_primary hζ b
  refine ⟨c, ?_⟩
  have hfirst : π ^ p ∣ (a - b) * b ^ (p - 1) :=
    dvd_mul_of_dvd_left (by simpa only [π] using hab) _
  have hsum := dvd_add hfirst hc
  have hbpowid : b ^ p = b * b ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel
      (Fact.out : p.Prime).one_lt.le]
  convert hsum using 1
  rw [hbpowid]
  ring

/-- Unit-normalized version of
`isKummerPrimary_mul_pow_pred_of_congruent`.  This is convenient when a
linear factor has first been divided by the fixed uniformizer `ζ - 1` and
must be rescaled to the historically used denominator `ζ^a - 1`. -/
theorem isKummerPrimary_unit_mul_pow_pred_of_congruent
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (u : (𝓞 K)ˣ) (a b : 𝓞 K)
    (ha : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ a)
    (hb : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ b)
    (hab : ((hζ.unit' : 𝓞 K) - 1) ^ p ∣
      (u : 𝓞 K) * a - b) :
    IsKummerPrimary hζ ((u : 𝓞 K) * a * b ^ (p - 1)) := by
  have hu : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ (u : 𝓞 K) := by
    intro h
    exact hζ.zeta_sub_one_prime'.not_unit
      (isUnit_of_dvd_unit h u.isUnit)
  simpa only [mul_assoc] using
    isKummerPrimary_mul_pow_pred_of_congruent hζ
      ((u : 𝓞 K) * a) b
      (hζ.zeta_sub_one_prime'.not_dvd_mul hu ha) hb hab

/-- Exact conclusion of Vandiver's Lemma 1.

At exponent `37`, the numerical hypothesis behind this proposition is the
already-proved nondivisibility `37 ∤ h⁺`.  The remaining implication is
Takagi/Furtwängler's class-field theorem for singular primary integers. -/
def LemmaOne (K : Type*) (p : ℕ)
    [Fact p.Prime] [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ p) {a : 𝓞 K} {I : Ideal (𝓞 K)},
    IsKummerPrimary hζ a →
      I ^ p = Ideal.span {a} →
        Submodule.IsPrincipal (I : Ideal (𝓞 K))

/-- Element-level form of Lemma 1: after principalizing the ideal root, its
chosen generator differs from the displayed primary element by a unit. -/
theorem exists_unit_mul_pow_of_lemmaOne
    (hlemma : LemmaOne K p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (I : Ideal (𝓞 K)) (a : 𝓞 K)
    (hprimary : IsKummerPrimary hζ a)
    (hpow : I ^ p = Ideal.span {a}) :
    ∃ (ρ : 𝓞 K) (ε : (𝓞 K)ˣ),
      I = Ideal.span {ρ} ∧ a = ε * ρ ^ p := by
  exact exists_unit_mul_pow_eq_of_isPrincipal_ideal I a
    (hlemma hζ hprimary hpow) hpow

/-- The literal ideal identity used as Vandiver's equation (7a).

If `I^p = (a)` and `J^p = (b)`, then

`(I * J^(p-1))^p = (a * b^(p-1))`.

When the displayed generator is primary, Lemma 1 supplies a generator of
`I * J^(p-1)`.  This is the only class-field-theoretic step in (7a); the
power calculation and generator extraction are kernel-checked here. -/
theorem exists_equationSevenA_generator
    (hlemma : LemmaOne K p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (I J : Ideal (𝓞 K)) (a b : 𝓞 K)
    (hIpow : I ^ p = Ideal.span {a})
    (hJpow : J ^ p = Ideal.span {b})
    (hprimary : IsKummerPrimary hζ (a * b ^ (p - 1))) :
    ∃ r : 𝓞 K, I * J ^ (p - 1) = Ideal.span {r} := by
  have hpow : (I * J ^ (p - 1)) ^ p =
      Ideal.span {a * b ^ (p - 1)} := by
    calc
      (I * J ^ (p - 1)) ^ p =
          I ^ p * (J ^ p) ^ (p - 1) := by
            rw [mul_pow, ← pow_mul, ← pow_mul,
              Nat.mul_comm (p - 1) p]
      _ = Ideal.span {a} * (Ideal.span {b}) ^ (p - 1) := by
            rw [hIpow, hJpow]
      _ = Ideal.span {a * b ^ (p - 1)} := by
            rw [Ideal.span_singleton_pow,
              Ideal.span_singleton_mul_span_singleton]
  obtain ⟨r, hr⟩ := (hlemma hζ hprimary hpow).principal
  exact ⟨r, hr⟩

/-- Unit-normalized form of equation (7a).

Multiplying the displayed primary generator by a unit does not change its
principal ideal.  This form lets callers normalize conjugate linear factors
so that their local congruence is literal, while retaining the original
factor ideals `I` and `J`. -/
theorem exists_equationSevenA_generator_of_unit
    (hlemma : LemmaOne K p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (u : (𝓞 K)ˣ) (I J : Ideal (𝓞 K)) (a b : 𝓞 K)
    (hIpow : I ^ p = Ideal.span {a})
    (hJpow : J ^ p = Ideal.span {b})
    (hprimary : IsKummerPrimary hζ
      ((u : 𝓞 K) * (a * b ^ (p - 1)))) :
    ∃ r : 𝓞 K, I * J ^ (p - 1) = Ideal.span {r} := by
  have hpow : (I * J ^ (p - 1)) ^ p =
      Ideal.span {(u : 𝓞 K) * (a * b ^ (p - 1))} := by
    calc
      (I * J ^ (p - 1)) ^ p =
          I ^ p * (J ^ p) ^ (p - 1) := by
            rw [mul_pow, ← pow_mul, ← pow_mul,
              Nat.mul_comm (p - 1) p]
      _ = Ideal.span {a} * (Ideal.span {b}) ^ (p - 1) := by
            rw [hIpow, hJpow]
      _ = Ideal.span {a * b ^ (p - 1)} := by
            rw [Ideal.span_singleton_pow,
              Ideal.span_singleton_mul_span_singleton]
      _ = Ideal.span {(u : 𝓞 K) * (a * b ^ (p - 1))} :=
        Ideal.span_singleton_eq_span_singleton.mpr
          (associated_unit_mul_right _ _ u.isUnit)
  obtain ⟨r, hr⟩ := (hlemma hζ hprimary hpow).principal
  exact ⟨r, hr⟩

end

end Fermat.Irregular.VandiverLemmaOne
