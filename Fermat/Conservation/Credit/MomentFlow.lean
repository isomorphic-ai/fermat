/-
Generic polynomial moment flow for the generator-derived credit argument.

The module isolates the elementary polynomial and finite-field facts behind
the first-layer and prime-square moment congruences.  Its API is generic in
the prime and contains no instance-specific arithmetic.
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

open scoped BigOperators

namespace Fermat.Conservation.Credit.Flow

open Polynomial

/-- The `N`th exponential moment of an integral polynomial. -/
def exponentialMoment (N : ℕ) (P : ℤ[X]) : ℤ :=
  P.sum fun i a ↦ a * (i : ℤ) ^ N

/-- The exponential moment is additive in the polynomial. -/
def exponentialMomentHom (N : ℕ) : ℤ[X] →+ ℤ where
  toFun := exponentialMoment N
  map_zero' := by simp [exponentialMoment]
  map_add' P Q := by
    exact Polynomial.sum_add_index P Q
      (fun i a ↦ a * (i : ℤ) ^ N)
      (by intro i; simp)
      (by intro i a b; ring)

@[simp]
theorem exponentialMoment_add (N : ℕ) (P Q : ℤ[X]) :
    exponentialMoment N (P + Q) =
      exponentialMoment N P + exponentialMoment N Q :=
  (exponentialMomentHom N).map_add P Q

@[simp]
theorem exponentialMoment_neg (N : ℕ) (P : ℤ[X]) :
    exponentialMoment N (-P) = -exponentialMoment N P :=
  (exponentialMomentHom N).map_neg P

@[simp]
theorem exponentialMoment_sub (N : ℕ) (P Q : ℤ[X]) :
    exponentialMoment N (P - Q) =
      exponentialMoment N P - exponentialMoment N Q :=
  (exponentialMomentHom N).map_sub P Q

@[simp]
theorem exponentialMoment_C_mul_X_pow (N i : ℕ) (a : ℤ) :
    exponentialMoment N (C a * X ^ i) = a * (i : ℤ) ^ N := by
  unfold exponentialMoment
  rw [C_mul_X_pow_eq_monomial, sum_monomial_index]
  simp

@[simp]
theorem exponentialMoment_monomial (N i : ℕ) (a : ℤ) :
    exponentialMoment N (monomial i a) = a * (i : ℤ) ^ N := by
  unfold exponentialMoment
  rw [sum_monomial_index]
  simp

@[simp]
theorem exponentialMoment_X_pow (N i : ℕ) :
    exponentialMoment N (X ^ i : ℤ[X]) = (i : ℤ) ^ N := by
  rw [← one_mul (X ^ i : ℤ[X]), ← C_1,
    exponentialMoment_C_mul_X_pow]
  simp

/-- A scalar constant factors out of every moment. -/
theorem exponentialMoment_C_mul (N : ℕ) (a : ℤ) (P : ℤ[X]) :
    exponentialMoment N (C a * P) = a * exponentialMoment N P := by
  change
    (exponentialMomentHom N) (C a * P) =
      a * (exponentialMomentHom N) P
  simpa [smul_eq_mul] using (exponentialMomentHom N).map_zsmul a P

/-- The complete `N`th power sum modulo `p` vanishes unless `p - 1`
divides `N`. -/
theorem zmod_sum_range_pow_eq_zero {p N : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hnot : ¬(p - 1) ∣ N) :
    (∑ i ∈ Finset.range p, (i : ZMod p) ^ N) = 0 := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.pos.ne'
  letI : NeZero p := ⟨hp0⟩
  have hall : (∑ x : ZMod p, x ^ N) = 0 := by
    let inclusion : (ZMod p)ˣ ↪ ZMod p :=
      ⟨fun x ↦ x, Units.val_injective⟩
    have himage :
        Finset.univ.map inclusion =
          Finset.univ \ {(0 : ZMod p)} := by
      ext x
      simpa only [Finset.mem_map, Finset.mem_univ,
        Function.Embedding.coeFn_mk, true_and, Finset.mem_sdiff,
        Finset.mem_singleton, inclusion] using! isUnit_iff_ne_zero
    calc
      (∑ x : ZMod p, x ^ N) =
          ∑ x ∈ Finset.univ \ {(0 : ZMod p)}, x ^ N := by
            rw [← Finset.sum_sdiff ({0} : Finset (ZMod p)).subset_univ,
              Finset.sum_singleton, zero_pow hN.ne', add_zero]
      _ = ∑ x : (ZMod p)ˣ, (x ^ N : ZMod p) := by
            simp [inclusion, ← himage, Finset.univ.sum_map inclusion]
      _ = 0 := by
            rw [FiniteField.sum_pow_units, ZMod.card, if_neg hnot]
  rw [← Fin.sum_univ_eq_sum_range]
  have hfin (i : Fin p) :
      (ZMod.finEquiv p) i = (i.val : ZMod p) := by
    cases p with
    | zero => exact (hp0 rfl).elim
    | succ p =>
        change (i : ZMod (p + 1)) = (i.val : ZMod (p + 1))
        apply Fin.ext
        exact (Nat.mod_eq_of_lt i.isLt).symm
  calc
    (∑ i : Fin p, ((i.val : ℕ) : ZMod p) ^ N) =
        ∑ i : Fin p, ((ZMod.finEquiv p) i) ^ N := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hfin]
    _ = 0 :=
      ((ZMod.finEquiv p).sum_comp fun x : ZMod p ↦ x ^ N).trans hall

/-- Integral form of the nontrivial finite-field power-sum congruence. -/
theorem prime_dvd_sum_range_pow {p N : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hnot : ¬(p - 1) ∣ N) :
    (p : ℤ) ∣ ∑ i ∈ Finset.range p, (i : ℤ) ^ N := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact zmod_sum_range_pow_eq_zero hN hnot

/-- The cyclotomic moment at a prime is the usual complete power sum. -/
theorem exponentialMoment_cyclotomic_prime {p N : ℕ} [Fact p.Prime] :
    exponentialMoment N (cyclotomic p ℤ) =
      ∑ i ∈ Finset.range p, (i : ℤ) ^ N := by
  rw [cyclotomic_prime]
  change
    (exponentialMomentHom N) (∑ i ∈ Finset.range p, X ^ i) =
      ∑ i ∈ Finset.range p, (i : ℤ) ^ N
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact exponentialMoment_X_pow N i

/-- Translation of an exponent by a multiple of `p` changes its `N`th
power by a multiple of `p²` when `p ∣ N`. -/
theorem prime_sq_dvd_add_pow_sub_pow {p i N : ℕ}
    (hdiv : p ∣ N) :
    ((p : ℤ) ^ 2) ∣
      ((i + p : ℕ) : ℤ) ^ N - (i : ℤ) ^ N := by
  have hfirst :
      ((p : ℤ) ^ 2) ∣
        ((i : ℤ) + (p : ℤ)) ^ N -
          (i : ℤ) ^ (N - 1) * (p : ℤ) * (N : ℤ) -
          (i : ℤ) ^ N :=
    sq_dvd_add_pow_sub_sub (p : ℤ) (i : ℤ) N
  have hdivInt : (p : ℤ) ∣ (N : ℤ) := by
    exact_mod_cast hdiv
  rcases hdivInt with ⟨d, hd⟩
  have hmiddle :
      ((p : ℤ) ^ 2) ∣
        (i : ℤ) ^ (N - 1) * (p : ℤ) * (N : ℤ) := by
    refine ⟨(i : ℤ) ^ (N - 1) * d, ?_⟩
    rw [hd]
    ring
  convert hfirst.add hmiddle using 1
  all_goals push_cast
  all_goals ring

/-- Translation of an exponent by `p` changes every power by a multiple
of `p`. -/
theorem prime_dvd_add_pow_sub_pow {p i N : ℕ} :
    (p : ℤ) ∣
      ((i + p : ℕ) : ℤ) ^ N - (i : ℤ) ^ N := by
  have hshift :=
    sub_dvd_pow_sub_pow (((i + p : ℕ) : ℤ)) (i : ℤ) N
  convert hshift using 1
  all_goals push_cast
  all_goals ring

/-- The moment of every `(X^p - 1)` multiple is divisible by `p²` when
`p ∣ N`. -/
theorem prime_sq_dvd_exponentialMoment_X_pow_sub_one_mul
    {p N : ℕ} (hdiv : p ∣ N) (Q : ℤ[X]) :
    ((p : ℤ) ^ 2) ∣
      exponentialMoment N ((X ^ p - 1) * Q) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [mul_add, exponentialMoment_add]
      exact dvd_add hP hQ
  | monomial i a =>
      rw [sub_mul, one_mul, X_pow_mul_monomial,
        exponentialMoment_sub, exponentialMoment_monomial,
        exponentialMoment_monomial]
      have hshift := prime_sq_dvd_add_pow_sub_pow
        (p := p) (i := i) (N := N) hdiv
      convert dvd_mul_of_dvd_right hshift a using 1
      ring

/-- The moment of every `(X^p - 1)` multiple is divisible by `p`. -/
theorem prime_dvd_exponentialMoment_X_pow_sub_one_mul
    {p N : ℕ} (Q : ℤ[X]) :
    (p : ℤ) ∣ exponentialMoment N ((X ^ p - 1) * Q) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [mul_add, exponentialMoment_add]
      exact dvd_add hP hQ
  | monomial i a =>
      rw [sub_mul, one_mul, X_pow_mul_monomial,
        exponentialMoment_sub, exponentialMoment_monomial,
        exponentialMoment_monomial]
      have hshift := prime_dvd_add_pow_sub_pow
        (p := p) (i := i) (N := N)
      convert dvd_mul_of_dvd_right hshift a using 1
      ring

/-- The cyclotomic summand in the quotient decomposition has
prime-square-divisible moment. -/
theorem prime_sq_dvd_exponentialMoment_scaled_cyclotomic
    {p N : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hnot : ¬(p - 1) ∣ N) (d : ℤ) :
    ((p : ℤ) ^ 2) ∣
      exponentialMoment N (C ((p : ℤ) * d) * cyclotomic p ℤ) := by
  have hsum := prime_dvd_sum_range_pow (p := p) (N := N) hN hnot
  rcases hsum with ⟨e, he⟩
  rw [exponentialMoment_C_mul, exponentialMoment_cyclotomic_prime, he]
  refine ⟨d * e, ?_⟩
  ring

/-- A visibly `p`-scaled cyclotomic summand has moment divisible by `p`
at every index. -/
theorem prime_dvd_exponentialMoment_scaled_cyclotomic
    {p N : ℕ} (d : ℤ) :
    (p : ℤ) ∣
      exponentialMoment N (C ((p : ℤ) * d) * cyclotomic p ℤ) := by
  rw [exponentialMoment_C_mul]
  refine ⟨d * exponentialMoment N (cyclotomic p ℤ), ?_⟩
  ring

/-- The factor theorem turns the hypotheses at `X = 1` into the common
two-summand decomposition used by both moment layers. -/
theorem exists_prime_cyclotomic_moment_decomposition
    {p : ℕ} (hp : p.Prime) {A B : ℤ[X]}
    (hfactor : A = cyclotomic p ℤ * B)
    (heval : ((p : ℤ) ^ 2) ∣ A.eval 1) :
    ∃ d : ℤ, ∃ Q : ℤ[X],
      A =
        C ((p : ℤ) * d) * cyclotomic p ℤ +
          (X ^ p - 1) * Q := by
  letI : Fact p.Prime := ⟨hp⟩
  have hEvalFactor :
      A.eval 1 = (p : ℤ) * B.eval 1 := by
    rw [hfactor, eval_mul, eval_one_cyclotomic_prime]
  rw [hEvalFactor] at heval
  have hpInt : (p : ℤ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hp_dvd_eval : (p : ℤ) ∣ B.eval 1 := by
    rcases heval with ⟨e, he⟩
    refine ⟨e, ?_⟩
    apply mul_left_cancel₀ hpInt
    calc
      (p : ℤ) * B.eval 1 = (p : ℤ) ^ 2 * e := he
      _ = (p : ℤ) * ((p : ℤ) * e) := by ring
  rcases hp_dvd_eval with ⟨d, hd⟩
  rcases X_sub_C_dvd_sub_C_eval
      (p := B) (a := (1 : ℤ)) with ⟨Q, hQ⟩
  refine ⟨d, Q, ?_⟩
  have hB :
      B = C ((p : ℤ) * d) + (X - 1) * Q := by
    calc
      B = (B - C (B.eval 1)) + C (B.eval 1) := by ring
      _ = (X - C (1 : ℤ)) * Q + C (B.eval 1) := by rw [hQ]
      _ = C ((p : ℤ) * d) + (X - 1) * Q := by
        rw [hd, C_1]
        ring
  calc
    A = cyclotomic p ℤ * B := hfactor
    _ = cyclotomic p ℤ *
        (C ((p : ℤ) * d) + (X - 1) * Q) := by rw [hB]
    _ = C ((p : ℤ) * d) * cyclotomic p ℤ +
        (X ^ p - 1) * Q := by
          rw [mul_add, ← mul_assoc,
            cyclotomic_prime_mul_X_sub_one]
          ring

/-- Generic prime-square moment lemma.

If an integral polynomial has a prime cyclotomic factor and its value at
one has an additional factor of `p`, then every positive moment whose
index is a multiple of `p`, but not of `p - 1`, has the same additional
factor of `p`. -/
theorem prime_sq_dvd_exponentialMoment_of_cyclotomic_mul
    {p N : ℕ} (hp : p.Prime)
    (hN : 0 < N) (hp_dvd_N : p ∣ N)
    (hnot : ¬(p - 1) ∣ N)
    {A B : ℤ[X]}
    (hfactor : A = cyclotomic p ℤ * B)
    (heval : ((p : ℤ) ^ 2) ∣ A.eval 1) :
    ((p : ℤ) ^ 2) ∣ exponentialMoment N A := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases exists_prime_cyclotomic_moment_decomposition
      hp hfactor heval with ⟨d, Q, hdecomp⟩
  rw [hdecomp, exponentialMoment_add]
  exact dvd_add
    (prime_sq_dvd_exponentialMoment_scaled_cyclotomic
      hN hnot d)
    (prime_sq_dvd_exponentialMoment_X_pow_sub_one_mul
      hp_dvd_N Q)

/-- Complementary first-layer moment lemma.

The cyclotomic factor and the extra factor of `p` at `X = 1` force every
positive exponential moment to vanish modulo `p`; no congruence condition
on the moment index is needed. -/
theorem prime_dvd_exponentialMoment_of_cyclotomic_mul
    {p N : ℕ} (hp : p.Prime) (_hN : 0 < N)
    {A B : ℤ[X]}
    (hfactor : A = cyclotomic p ℤ * B)
    (heval : ((p : ℤ) ^ 2) ∣ A.eval 1) :
    (p : ℤ) ∣ exponentialMoment N A := by
  rcases exists_prime_cyclotomic_moment_decomposition
      hp hfactor heval with ⟨d, Q, hdecomp⟩
  rw [hdecomp, exponentialMoment_add]
  exact dvd_add
    (prime_dvd_exponentialMoment_scaled_cyclotomic d)
    (prime_dvd_exponentialMoment_X_pow_sub_one_mul Q)

end Fermat.Conservation.Credit.Flow
