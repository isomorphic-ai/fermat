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

/-- The primitive root `ζ`, regarded as an element of the finite set of
`p`th roots of unity in the cyclotomic integers. -/
def zetaNthRoot {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Polynomial.nthRootsFinset p (1 : 𝓞 K) :=
  ⟨hζ.unit', hζ.unit'_coe.mem_nthRootsFinset
    (Fact.out : p.Prime).pos⟩

/-- The inverse primitive root `ζ⁻¹`, regarded as an integral `p`th root
of unity. -/
def inverseZetaNthRoot {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Polynomial.nthRootsFinset p (1 : 𝓞 K) :=
  ⟨(hζ.unit'⁻¹ : (𝓞 K)ˣ), by
    rw [Polynomial.mem_nthRootsFinset (Fact.out : p.Prime).pos]
    rw [← Units.val_pow_eq_pow_val]
    have hz : hζ.unit' ^ p = 1 := by
      apply Units.ext
      apply NumberField.RingOfIntegers.ext
      change ζ ^ p = 1
      exact hζ.pow_eq_one
    rw [inv_pow, hz, inv_one]
    rfl⟩

/-- The root `1`, regarded as an element of the finite set of `p`th roots
of unity in the cyclotomic integers. -/
def oneNthRoot : Polynomial.nthRootsFinset p (1 : 𝓞 K) :=
  ⟨1, Polynomial.one_mem_nthRootsFinset (Fact.out : p.Prime).pos⟩

omit [IsCyclotomicExtension {p} ℚ K] in
/-- A primitive root is distinct from the root `1` inside
`nthRootsFinset`. -/
theorem zetaNthRoot_ne_one {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    zetaNthRoot hζ ≠ oneNthRoot := by
  rw [ne_eq, Subtype.ext_iff]
  exact hζ.unit'_coe.ne_one (Fact.out : p.Prime).one_lt

omit [IsCyclotomicExtension {p} ℚ K] in
/-- The inverse of a primitive root is also distinct from `1`. -/
theorem inverseZetaNthRoot_ne_one {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    inverseZetaNthRoot hζ ≠ oneNthRoot := by
  rw [ne_eq, Subtype.ext_iff]
  intro h
  have h' : hζ.unit'⁻¹ = 1 := Units.ext h
  have hz : hζ.unit' = 1 := by
    rw [← inv_inv hζ.unit', h', inv_one]
  exact hζ.unit'_coe.ne_one (Fact.out : p.Prime).one_lt
    (congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hz)

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

section NormalizedConjugateFactors

variable {L : Type} {q : ℕ} [Fact q.Prime] [Field L] [NumberField L]
  [IsCyclotomicExtension {q} ℚ L]

/-- The exact local comparison of the two conjugate linear factors used in
Vandiver's equation (7a).

Write

`q₊ = (x + y*ζ)/(ζ - 1)` and
`q₋ = (x + y*ζ⁻¹)/(ζ - 1)`.

If `(ζ - 1)^(q+1)` divides the real factor `x + y`, then

`q₊ ≡ (-ζ) q₋ (mod (ζ - 1)^q)`.

Indeed, after multiplying by `ζ - 1`, the difference is exactly
`(1 + ζ) * (x + y)`, and one factor of `ζ - 1` cancels.  The same depth
hypothesis makes the factor at the root `1` ramified.  Injectivity of the
factor residues then proves that the two factors at `ζ` and `ζ⁻¹` are
both prime to `ζ - 1`.

This packages the full elementary local input required by
`isKummerPrimary_mul_pow_pred_of_congruent`; no class-field theorem is
used. -/
theorem normalizedConjugateLinearFactors
    (hq2 : q ≠ 2) {ζ : L} (hζ : IsPrimitiveRoot ζ q)
    {x y z : 𝓞 L} {ε : (𝓞 L)ˣ} {m : ℕ}
    (e : x ^ q + y ^ q = ε *
      ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ q)
    (hy : ¬ (hζ.unit' : 𝓞 L) - 1 ∣ y)
    (hsum : ((hζ.unit' : 𝓞 L) - 1) ^ (q + 1) ∣ x + y) :
    let qplus : 𝓞 L := div_zeta_sub_one hq2 hζ e
      (zetaNthRoot (K := L) (p := q) hζ)
    let qminus : 𝓞 L := div_zeta_sub_one hq2 hζ e
      (inverseZetaNthRoot (K := L) (p := q) hζ)
    ¬ (hζ.unit' : 𝓞 L) - 1 ∣ qplus ∧
    ¬ (hζ.unit' : 𝓞 L) - 1 ∣ qminus ∧
    ((hζ.unit' : 𝓞 L) - 1) ^ q ∣
      qplus - (((-hζ.unit' : (𝓞 L)ˣ) : 𝓞 L) * qminus) := by
  let π : 𝓞 L := (hζ.unit' : 𝓞 L) - 1
  let qplus : 𝓞 L := div_zeta_sub_one hq2 hζ e
    (zetaNthRoot (K := L) (p := q) hζ)
  let qminus : 𝓞 L := div_zeta_sub_one hq2 hζ e
    (inverseZetaNthRoot (K := L) (p := q) hζ)
  let qone : 𝓞 L := div_zeta_sub_one hq2 hζ e
    (oneNthRoot (K := L) (p := q))
  have hπ0 : π ≠ 0 := hζ.unit'_coe.sub_one_ne_zero
    (Fact.out : q.Prime).one_lt
  have hqone_mul : qone * π = x + y := by
    simpa only [qone, oneNthRoot, π, mul_one] using
      div_zeta_sub_one_mul_zeta_sub_one hq2 hζ e
        (oneNthRoot (K := L) (p := q))
  have hqonePow : π ^ q ∣ qone := by
    rw [← mul_dvd_mul_iff_right hπ0]
    rw [← pow_succ, hqone_mul]
    simpa only [π] using hsum
  have hqone : π ∣ qone :=
    (dvd_pow_self π (Fact.out : q.Prime).ne_zero).trans hqonePow
  have hqplus : ¬ π ∣ qplus := by
    intro h
    apply zetaNthRoot_ne_one hζ
    apply div_zeta_sub_one_Injective hq2 hζ e hy
    calc
      Ideal.Quotient.mk (Ideal.span {π}) qplus = 0 :=
        (Ideal.Quotient.eq_zero_iff_dvd π qplus).2 h
      _ = Ideal.Quotient.mk (Ideal.span {π}) qone :=
        ((Ideal.Quotient.eq_zero_iff_dvd π qone).2 hqone).symm
  have hqminus : ¬ π ∣ qminus := by
    intro h
    apply inverseZetaNthRoot_ne_one hζ
    apply div_zeta_sub_one_Injective hq2 hζ e hy
    calc
      Ideal.Quotient.mk (Ideal.span {π}) qminus = 0 :=
        (Ideal.Quotient.eq_zero_iff_dvd π qminus).2 h
      _ = Ideal.Quotient.mk (Ideal.span {π}) qone :=
        ((Ideal.Quotient.eq_zero_iff_dvd π qone).2 hqone).symm
  have hinv : (hζ.unit' : 𝓞 L) * (hζ.unit'⁻¹ : (𝓞 L)ˣ) = 1 := by
    rw [← Units.val_mul]
    simp
  have hpair_mul :
      (qplus - (((-hζ.unit' : (𝓞 L)ˣ) : 𝓞 L) * qminus)) * π =
        (1 + (hζ.unit' : 𝓞 L)) * (x + y) := by
    rw [sub_mul, mul_assoc]
    rw [show qplus * π =
        x + y * (zetaNthRoot (K := L) (p := q) hζ : 𝓞 L) by
      exact div_zeta_sub_one_mul_zeta_sub_one hq2 hζ e
        (zetaNthRoot (K := L) (p := q) hζ)]
    rw [show qminus * π =
        x + y * (inverseZetaNthRoot (K := L) (p := q) hζ : 𝓞 L) by
      exact div_zeta_sub_one_mul_zeta_sub_one hq2 hζ e
        (inverseZetaNthRoot (K := L) (p := q) hζ)]
    dsimp only [zetaNthRoot, inverseZetaNthRoot]
    simp only [Units.val_neg]
    linear_combination y * hinv
  have hpair : π ^ q ∣
      qplus - (((-hζ.unit' : (𝓞 L)ˣ) : 𝓞 L) * qminus) := by
    rw [← mul_dvd_mul_iff_right hπ0]
    rw [← pow_succ, hpair_mul]
    exact dvd_mul_of_dvd_right (by simpa only [π] using hsum) _
  exact ⟨hqplus, hqminus, hpair⟩

/-- The primary-generator conclusion for the normalized conjugate factor
pair.  This is the direct composition of the checked factor comparison
above with the generic Kummer-primary recombination theorem. -/
theorem normalizedConjugateLinearFactor_isKummerPrimary
    (hq2 : q ≠ 2) {ζ : L} (hζ : IsPrimitiveRoot ζ q)
    {x y z : 𝓞 L} {ε : (𝓞 L)ˣ} {m : ℕ}
    (e : x ^ q + y ^ q = ε *
      ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ q)
    (hy : ¬ (hζ.unit' : 𝓞 L) - 1 ∣ y)
    (hsum : ((hζ.unit' : 𝓞 L) - 1) ^ (q + 1) ∣ x + y) :
    let qplus : 𝓞 L := div_zeta_sub_one hq2 hζ e
      (zetaNthRoot (K := L) (p := q) hζ)
    let qminus : 𝓞 L := div_zeta_sub_one hq2 hζ e
      (inverseZetaNthRoot (K := L) (p := q) hζ)
    IsKummerPrimary hζ
      (qplus * (((( -hζ.unit' : (𝓞 L)ˣ) : 𝓞 L) * qminus) ^ (q - 1))) := by
  dsimp only
  obtain ⟨hqplus, hqminus, hpair⟩ :=
    normalizedConjugateLinearFactors hq2 hζ e hy hsum
  have hu : ¬ (hζ.unit' : 𝓞 L) - 1 ∣
      ((-hζ.unit' : (𝓞 L)ˣ) : 𝓞 L) := by
    intro h
    exact hζ.zeta_sub_one_prime'.not_unit
      (isUnit_of_dvd_unit h (-hζ.unit').isUnit)
  exact isKummerPrimary_mul_pow_pred_of_congruent hζ _ _ hqplus
    (hζ.zeta_sub_one_prime'.not_dvd_mul hu hqminus) hpair

end NormalizedConjugateFactors

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
