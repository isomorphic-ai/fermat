/-
Generic nonlinear jet flow for the generator-derived credit argument.

The input is the sequence of Euler jets of an integral numerator and
denominator. The quotient jets are characterized by Leibniz's rule. This
module proves that the prime and prime-square layers survive division by a
denominator whose constant jet is a unit, and then survive the logarithmic
derivative.
-/
import Fermat.Conservation.Credit.MomentFlow
import Mathlib.Data.Nat.Choose.Lucas

open scoped BigOperators

namespace Fermat.Conservation.Credit.Flow

open Polynomial

/-- Divisibility by the image of `p` inside `ZMod (p²)`. -/
def IsPrimeMultiple (p : ℕ) (x : ZMod (p ^ 2)) : Prop :=
  ∃ y, x = (p : ZMod (p ^ 2)) * y

theorem isPrimeMultiple_zero (p : ℕ) :
    IsPrimeMultiple p (0 : ZMod (p ^ 2)) :=
  ⟨0, by simp⟩

theorem IsPrimeMultiple.add {p : ℕ} {x y : ZMod (p ^ 2)}
    (hx : IsPrimeMultiple p x) (hy : IsPrimeMultiple p y) :
    IsPrimeMultiple p (x + y) := by
  rcases hx with ⟨x, rfl⟩
  rcases hy with ⟨y, rfl⟩
  exact ⟨x + y, by ring⟩

theorem IsPrimeMultiple.neg {p : ℕ} {x : ZMod (p ^ 2)}
    (hx : IsPrimeMultiple p x) :
    IsPrimeMultiple p (-x) := by
  rcases hx with ⟨x, rfl⟩
  exact ⟨-x, by ring⟩

theorem IsPrimeMultiple.sub {p : ℕ} {x y : ZMod (p ^ 2)}
    (hx : IsPrimeMultiple p x) (hy : IsPrimeMultiple p y) :
    IsPrimeMultiple p (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

theorem IsPrimeMultiple.mul_left {p : ℕ} {x y : ZMod (p ^ 2)}
    (hx : IsPrimeMultiple p x) :
    IsPrimeMultiple p (y * x) := by
  rcases hx with ⟨x, rfl⟩
  exact ⟨y * x, by ring⟩

theorem IsPrimeMultiple.mul_right {p : ℕ} {x y : ZMod (p ^ 2)}
    (hx : IsPrimeMultiple p x) :
    IsPrimeMultiple p (x * y) := by
  simpa [mul_comm] using hx.mul_left (y := y)

theorem IsPrimeMultiple.natCast_mul {p n : ℕ}
    {x : ZMod (p ^ 2)} (hx : IsPrimeMultiple p x) :
    IsPrimeMultiple p ((n : ZMod (p ^ 2)) * x) :=
  hx.mul_left

theorem IsPrimeMultiple.mul_eq_zero {p : ℕ}
    {x y : ZMod (p ^ 2)}
    (hx : IsPrimeMultiple p x) (hy : IsPrimeMultiple p y) :
    x * y = 0 := by
  rcases hx with ⟨x, rfl⟩
  rcases hy with ⟨y, rfl⟩
  rw [show (p : ZMod (p ^ 2)) * x *
      ((p : ZMod (p ^ 2)) * y) =
      ((p ^ 2 : ℕ) : ZMod (p ^ 2)) * (x * y) by
        push_cast
        ring]
  simp

theorem isPrimeMultiple_sum {p : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → ZMod (p ^ 2))
    (hf : ∀ i ∈ s, IsPrimeMultiple p (f i)) :
    IsPrimeMultiple p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [isPrimeMultiple_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply (hf a (by simp)).add
      exact ih fun i hi ↦ hf i (by simp [hi])

theorem IsPrimeMultiple.cancel_unit_left {p : ℕ}
    {u x : ZMod (p ^ 2)} (hu : IsUnit u)
    (hux : IsPrimeMultiple p (u * x)) :
    IsPrimeMultiple p x := by
  rcases hu with ⟨u, rfl⟩
  rcases hux with ⟨d, hd⟩
  refine ⟨(u⁻¹ : ZMod (p ^ 2)) * d, ?_⟩
  calc
    x = (u⁻¹ : ZMod (p ^ 2)) * ((u : ZMod (p ^ 2)) * x) := by
      simp
    _ = (u⁻¹ : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * d) := by
      rw [hd]
    _ = (p : ZMod (p ^ 2)) * ((u⁻¹ : ZMod (p ^ 2)) * d) := by
      ring

/-- One-digit Lucas consequence used by the quotient recurrence:
if the top index is a multiple of `p` and the bottom index is not,
then the binomial coefficient is a multiple of `p`. -/
theorem prime_dvd_choose_of_dvd_top_not_dvd_bottom
    {p n k : ℕ} (hp : p.Prime)
    (hpn : p ∣ n) (hpk : ¬p ∣ k) :
    p ∣ n.choose k := by
  letI : Fact p.Prime := ⟨hp⟩
  have hmod :
      n.choose k ≡
        (n % p).choose (k % p) * (n / p).choose (k / p) [MOD p] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := p) (n := n) (k := k)
  have hnmod : n % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hpn
  have hkmod : k % p ≠ 0 :=
    fun h ↦ hpk (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hzero :
      (n % p).choose (k % p) * (n / p).choose (k / p) = 0 := by
    rw [hnmod]
    rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hkmod)]
    simp
  rw [hzero] at hmod
  exact Nat.dvd_iff_mod_eq_zero.mpr hmod

/-- Abstract Leibniz recurrence for the Euler jets of a quotient.

`numerator n` is the `n`th Euler jet of `B * Y`, `denominator n`
is the jet of `B`, and `quotient n` is the jet of `Y`.
-/
def IsQuotientJetRecurrence {R : Type*} [CommSemiring R]
    (numerator denominator quotient : ℕ → R) : Prop :=
  ∀ n,
    numerator n =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : R) * denominator (n - k) * quotient k

/-- Prime and prime-square layers survive division by a series with
unit constant jet.

The square layer is required at every positive multiple of `p` up to
`N`; Lucas's theorem makes exactly those indices recur into one another.
-/
theorem quotientJet_prime_layers
    {p N : ℕ} (hp : p.Prime)
    {numerator denominator quotient : ℕ → ZMod (p ^ 2)}
    (hrec : IsQuotientJetRecurrence numerator denominator quotient)
    (hunit : IsUnit (denominator 0))
    (hzero : numerator 0 = 0)
    (hone :
      ∀ n, 0 < n → n ≤ N → IsPrimeMultiple p (numerator n))
    (htwo :
      ∀ n, 0 < n → n ≤ N → p ∣ n → numerator n = 0) :
    quotient 0 = 0 ∧
      (∀ n, 0 < n → n ≤ N → IsPrimeMultiple p (quotient n)) ∧
      (∀ n, 0 < n → n ≤ N → p ∣ n → quotient n = 0) := by
  have hqzero : quotient 0 = 0 := by
    have h := hrec 0
    simp only [Nat.zero_sub] at h
    apply hunit.mul_left_cancel
    simpa [hzero] using h.symm
  have hlayers :
      ∀ n, n ≤ N →
        (0 < n → IsPrimeMultiple p (quotient n)) ∧
        (0 < n → p ∣ n → quotient n = 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hnN
        constructor
        · intro hnpos
          have hrecn := hrec n
          rw [Finset.sum_range_succ] at hrecn
          simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self,
            one_mul] at hrecn
          have hrest :
              IsPrimeMultiple p
                (∑ k ∈ Finset.range n,
                  (n.choose k : ZMod (p ^ 2)) *
                    denominator (n - k) * quotient k) := by
            apply isPrimeMultiple_sum
            intro k hk
            have hkn : k < n := Finset.mem_range.mp hk
            by_cases hk0 : k = 0
            · subst k
              simp [hqzero, isPrimeMultiple_zero]
            · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
              have hqk :=
                (ih k hkn (le_trans hkn.le hnN)).1 hkpos
              exact hqk.mul_left
          have hdiff :
              IsPrimeMultiple p
                (numerator n -
                  ∑ k ∈ Finset.range n,
                    (n.choose k : ZMod (p ^ 2)) *
                      denominator (n - k) * quotient k) :=
            (hone n hnpos hnN).sub hrest
          have hsolve :
              denominator 0 * quotient n =
                numerator n -
                  ∑ k ∈ Finset.range n,
                    (n.choose k : ZMod (p ^ 2)) *
                      denominator (n - k) * quotient k := by
            linear_combination -hrecn
          apply IsPrimeMultiple.cancel_unit_left hunit
          rw [hsolve]
          exact hdiff
        · intro hnpos hpn
          have hrecn := hrec n
          rw [Finset.sum_range_succ] at hrecn
          simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self,
            one_mul] at hrecn
          have hrestzero :
              (∑ k ∈ Finset.range n,
                (n.choose k : ZMod (p ^ 2)) *
                  denominator (n - k) * quotient k) = 0 := by
            apply Finset.sum_eq_zero
            intro k hk
            have hkn : k < n := Finset.mem_range.mp hk
            by_cases hk0 : k = 0
            · subst k
              simp [hqzero]
            · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
              by_cases hpk : p ∣ k
              · have hqk :
                    quotient k = 0 :=
                  (ih k hkn (le_trans hkn.le hnN)).2 hkpos hpk
                simp [hqk]
              · have hchoose : p ∣ n.choose k :=
                  prime_dvd_choose_of_dvd_top_not_dvd_bottom
                    hp hpn hpk
                rcases hchoose with ⟨c, hc⟩
                have hqk :=
                  (ih k hkn (le_trans hkn.le hnN)).1 hkpos
                have hcoeff :
                    IsPrimeMultiple p
                      (n.choose k : ZMod (p ^ 2)) := by
                  refine ⟨(c : ZMod (p ^ 2)), ?_⟩
                  simp [hc]
                have hprod :
                    (n.choose k : ZMod (p ^ 2)) * quotient k = 0 :=
                  hcoeff.mul_eq_zero hqk
                calc
                  (n.choose k : ZMod (p ^ 2)) *
                        denominator (n - k) * quotient k =
                      denominator (n - k) *
                        ((n.choose k : ZMod (p ^ 2)) * quotient k) := by
                          ring
                  _ = 0 := by rw [hprod, mul_zero]
          have hnumzero := htwo n hnpos hnN hpn
          apply hunit.mul_left_cancel
          calc
            denominator 0 * quotient n =
                numerator n -
                  ∑ k ∈ Finset.range n,
                    (n.choose k : ZMod (p ^ 2)) *
                      denominator (n - k) * quotient k := by
                linear_combination -hrecn
            _ = 0 := by rw [hnumzero, hrestzero, sub_zero]
            _ = denominator 0 * 0 := by simp
  refine ⟨hqzero, ?_, ?_⟩
  · intro n hnpos hnN
    exact (hlayers n hnN).1 hnpos
  · intro n hnpos hnN hpn
    exact (hlayers n hnN).2 hnpos hpn

/-- Abstract Leibniz recurrence for Euler jets of a logarithmic
derivative.  If `G = D(log F)`, then `D F = F * G`. -/
def IsLogDerivativeJetRecurrence {R : Type*} [CommSemiring R]
    (source logDerivative : ℕ → R) : Prop :=
  ∀ n,
    source (n + 1) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : R) * source (n - k) * logDerivative k

/-- If every positive Euler jet of `F` is a prime multiple and its
`N`th jet is zero modulo `p²`, then the `(N-1)`st Euler jet of
`D(log F)` is zero modulo `p²`. -/
theorem logDerivativeJet_selected_prime_sq
    {p N : ℕ} (hN : 0 < N)
    {source logDerivative : ℕ → ZMod (p ^ 2)}
    (hrec : IsLogDerivativeJetRecurrence source logDerivative)
    (hunit : IsUnit (source 0))
    (hone :
      ∀ n, 0 < n → n ≤ N → IsPrimeMultiple p (source n))
    (htwo : source N = 0) :
    logDerivative (N - 1) = 0 := by
  have hlogOne :
      ∀ n, n < N → IsPrimeMultiple p (logDerivative n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hnN
        have hrecn := hrec n
        rw [Finset.sum_range_succ] at hrecn
        simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self,
          one_mul] at hrecn
        have hrest :
            IsPrimeMultiple p
              (∑ k ∈ Finset.range n,
                (n.choose k : ZMod (p ^ 2)) *
                  source (n - k) * logDerivative k) := by
          apply isPrimeMultiple_sum
          intro k hk
          have hkn : k < n := Finset.mem_range.mp hk
          have hdiffpos : 0 < n - k := Nat.sub_pos_of_lt hkn
          have hs := hone (n - k) hdiffpos (by omega)
          exact
            (hs.mul_left
              (y := (n.choose k : ZMod (p ^ 2)))).mul_right
        have hdiff :
            IsPrimeMultiple p
              (source (n + 1) -
                ∑ k ∈ Finset.range n,
                  (n.choose k : ZMod (p ^ 2)) *
                    source (n - k) * logDerivative k) :=
          (hone (n + 1) (by omega) (by omega)).sub hrest
        have hsolve :
            source 0 * logDerivative n =
              source (n + 1) -
                ∑ k ∈ Finset.range n,
                  (n.choose k : ZMod (p ^ 2)) *
                    source (n - k) * logDerivative k := by
          linear_combination -hrecn
        apply IsPrimeMultiple.cancel_unit_left hunit
        rw [hsolve]
        exact hdiff
  have hrecTop := hrec (N - 1)
  have hsucc : N - 1 + 1 = N := Nat.sub_add_cancel hN
  rw [Finset.sum_range_succ] at hrecTop
  rw [hsucc] at hrecTop
  simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self,
    one_mul] at hrecTop
  have hrestzero :
      (∑ k ∈ Finset.range (N - 1),
        ((N - 1).choose k : ZMod (p ^ 2)) *
          source (N - 1 - k) * logDerivative k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk : k < N - 1 := Finset.mem_range.mp hk
    have hsourcePos : 0 < N - 1 - k := Nat.sub_pos_of_lt hk
    have hs := hone (N - 1 - k) hsourcePos (by omega)
    have hg := hlogOne k (by omega)
    have hprod := hs.mul_eq_zero hg
    calc
      ((N - 1).choose k : ZMod (p ^ 2)) *
            source (N - 1 - k) * logDerivative k =
          ((N - 1).choose k : ZMod (p ^ 2)) *
            (source (N - 1 - k) * logDerivative k) := by ring
      _ = 0 := by rw [hprod, mul_zero]
  apply hunit.mul_left_cancel
  calc
    source 0 * logDerivative (N - 1) =
        source N -
          ∑ k ∈ Finset.range (N - 1),
            ((N - 1).choose k : ZMod (p ^ 2)) *
              source (N - 1 - k) * logDerivative k := by
      linear_combination -hrecTop
    _ = 0 := by rw [htwo, hrestzero, sub_zero]
    _ = source 0 * 0 := by simp

/-- Combined nonlinear bridge: a quotient with the two jet layers has a
prime-square-vanishing selected logarithmic derivative jet. -/
theorem quotient_logDerivative_selected_prime_sq
    {p N : ℕ} (hp : p.Prime) (hN : 0 < N) (hpN : p ∣ N)
    {numerator denominator quotient source logDerivative :
      ℕ → ZMod (p ^ 2)}
    (hquotient :
      IsQuotientJetRecurrence numerator denominator quotient)
    (hdenUnit : IsUnit (denominator 0))
    (hnumZero : numerator 0 = 0)
    (hnumOne :
      ∀ n, 0 < n → n ≤ N → IsPrimeMultiple p (numerator n))
    (hnumTwo :
      ∀ n, 0 < n → n ≤ N → p ∣ n → numerator n = 0)
    (hsourceZero : source 0 = 1)
    (hsourcePos : ∀ n, 0 < n → n ≤ N → source n = quotient n)
    (hlog :
      IsLogDerivativeJetRecurrence source logDerivative) :
    logDerivative (N - 1) = 0 := by
  obtain ⟨_hq0, hqOne, hqTwo⟩ :=
    quotientJet_prime_layers hp hquotient hdenUnit hnumZero
      hnumOne hnumTwo
  have hsourceUnit : IsUnit (source 0) := by
    rw [hsourceZero]
    exact isUnit_one
  apply logDerivativeJet_selected_prime_sq hN hlog hsourceUnit
  · intro n hn hnN
    rw [hsourcePos n hn hnN]
    exact hqOne n hn hnN
  · rw [hsourcePos N hN le_rfl]
    exact hqTwo N hN le_rfl hpN

/-! ## Polynomial wrapper -/

/-- Integral exponential moments reduced only after retaining their exact
integer value. -/
def momentModPrimeSq (p n : ℕ) (P : ℤ[X]) : ZMod (p ^ 2) :=
  (exponentialMoment n P : ZMod (p ^ 2))

/-- A polynomial numerator/denominator pair supplies the abstract
quotient-jet recurrence through its exponential moments. -/
def IsPolynomialQuotientJetRecurrence
    (p : ℕ) (P Q : ℤ[X])
    (quotient : ℕ → ZMod (p ^ 2)) : Prop :=
  IsQuotientJetRecurrence
    (fun n ↦ momentModPrimeSq p n P)
    (fun n ↦ momentModPrimeSq p n Q)
    quotient

theorem isPrimeMultiple_intCast_of_prime_dvd
    {p : ℕ} {z : ℤ} (hz : (p : ℤ) ∣ z) :
    IsPrimeMultiple p (z : ZMod (p ^ 2)) := by
  rcases hz with ⟨d, rfl⟩
  exact ⟨(d : ZMod (p ^ 2)), by push_cast; ring⟩

theorem intCast_eq_zero_of_prime_sq_dvd
    {p : ℕ} {z : ℤ} (hz : ((p : ℤ) ^ 2) ∣ z) :
    (z : ZMod (p ^ 2)) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact hz

theorem exponentialMoment_zero_eq_eval_one (P : ℤ[X]) :
    exponentialMoment 0 P = P.eval 1 := by
  simp [exponentialMoment, Polynomial.eval_eq_sum]

/-- In the high range `n ≤ p*M`, with `M < p-1`, a positive
`p`-multiple cannot also be a `(p-1)`-multiple. -/
theorem pred_not_dvd_of_prime_dvd_le_mul
    {p M n : ℕ} (hp : p.Prime)
    (hM : M < p - 1) (hn : 0 < n)
    (hnle : n ≤ p * M) (hpn : p ∣ n) :
    ¬(p - 1) ∣ n := by
  rintro hpred
  obtain ⟨j, rfl⟩ := hpn
  have hp0 : 0 < p := hp.pos
  have hj : 0 < j := by
    apply Nat.pos_of_ne_zero
    intro hj0
    subst j
    simp at hn
  have hjle : j ≤ M := by
    exact Nat.le_of_mul_le_mul_left hnle hp0
  have hcop : (p - 1).Coprime p := by
    conv_rhs => rw [show p = 1 + (p - 1) by omega]
    rw [Nat.coprime_add_self_right]
    simp
  have hpredj : p - 1 ∣ j :=
    hcop.dvd_of_dvd_mul_right (by simpa [mul_comm] using hpred)
  exact (Nat.not_dvd_of_pos_of_lt hj (lt_of_le_of_lt hjle hM)) hpredj

/-- Compiled polynomial form of the nonlinear bridge.

`P / (C*Q)` is written as `1 + (P-CQ)/(CQ)`.  A cyclotomic factor and
prime-square value at one supply the two moment layers for `P-CQ`.
The abstract quotient and logarithmic-derivative recurrences then force
the selected `p*M` logarithmic jet to vanish modulo `p²`.
-/
theorem polynomial_quotient_logDerivative_selected_prime_sq
    {p M : ℕ} (hp : p.Prime) (hMpos : 0 < M)
    (hMlt : M < p - 1)
    (P Q B : ℤ[X]) (c : ℤ)
    {quotient source logDerivative : ℕ → ZMod (p ^ 2)}
    (hfactor : P - Polynomial.C c * Q = cyclotomic p ℤ * B)
    (heval :
      ((p : ℤ) ^ 2) ∣ (P - Polynomial.C c * Q).eval 1)
    (hquotient :
      IsPolynomialQuotientJetRecurrence p
        (P - Polynomial.C c * Q) (Polynomial.C c * Q) quotient)
    (hdenUnit :
      IsUnit (momentModPrimeSq p 0 (Polynomial.C c * Q)))
    (hsourceZero : source 0 = 1)
    (hsourcePos :
      ∀ n, 0 < n → n ≤ p * M → source n = quotient n)
    (hlog :
      IsLogDerivativeJetRecurrence source logDerivative) :
    logDerivative (p * M - 1) = 0 := by
  apply quotient_logDerivative_selected_prime_sq hp
    (Nat.mul_pos hp.pos hMpos) (dvd_mul_right p M)
    hquotient hdenUnit
  · apply intCast_eq_zero_of_prime_sq_dvd
    rw [exponentialMoment_zero_eq_eval_one]
    exact heval
  · intro n hn hnle
    exact isPrimeMultiple_intCast_of_prime_dvd
      (prime_dvd_exponentialMoment_of_cyclotomic_mul
        hp hn hfactor heval)
  · intro n hn hnle hpn
    exact intCast_eq_zero_of_prime_sq_dvd
      (prime_sq_dvd_exponentialMoment_of_cyclotomic_mul
        hp hn hpn
        (pred_not_dvd_of_prime_dvd_le_mul
          hp hMlt hn hnle hpn)
        hfactor heval)
  · exact hsourceZero
  · exact hsourcePos
  · exact hlog

end Fermat.Conservation.Credit.Flow
