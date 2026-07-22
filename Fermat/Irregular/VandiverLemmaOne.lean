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

end

end Fermat.Irregular.VandiverLemmaOne
