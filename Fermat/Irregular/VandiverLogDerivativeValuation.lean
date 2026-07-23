import Fermat.Irregular.VandiverPowerSeriesLog
import Fermat.Irregular.VandiverRemainderDerivative
import Fermat.Irregular.KummerTheorem

/-!
# Valuation propagation through Vandiver's logarithmic derivative

This file formalizes the source recursion used after Vandiver's additive
polynomial remainder calculation.  Let `Z` be a rational formal power
series whose constant coefficient is a nonzero `p`-adic unit.  If every
positive formal derivative of order at most `N` is divisible by `p`, then
the same is true of every positive derivative of `Z⁻¹` in that range.

The proof differentiates `Z⁻¹ * Z = 1`.  At order `s`, the last Leibniz
term is

`D^s(Z⁻¹)(0) * Z(0)`;

all preceding terms contain a positive derivative of `Z` and a lower
derivative of `Z⁻¹`.  Strong induction and cancellation of the unit
`Z(0)` therefore give the inverse bound.

If the derivative of `Z` at the top order `N` is moreover divisible by
`p²`, the Leibniz expansion of

`D^(N-1) (Z' * Z⁻¹)(0)`

has valuation at least two term by term.  This proves the desired bound
for the formal logarithmic derivative `Z'/Z`.

The file also records the uniform first-order bound for Vandiver's
additive remainder: every derivative of that remainder is divisible by
`p`; the stronger non-exceptional top-order bound remains in
`VandiverRemainderDerivative`.
-/

namespace Fermat.Irregular.VandiverLogDerivativeValuation

open Polynomial PowerSeries
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverRemainderDerivative
open Fermat.Irregular.Voronoi

/-! ## Formal Leibniz identities -/

/-- The formal derivatives at zero satisfy the binomial Leibniz rule. -/
theorem formalDerivativeAtZero_mul
    (n : ℕ) (f g : PowerSeries ℚ) :
    formalDerivativeAtZero n (f * g) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℚ) *
          formalDerivativeAtZero k f *
          formalDerivativeAtZero (n - k) g := by
  rw [formalDerivativeAtZero, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
  simp only [formalDerivativeAtZero]
  have hfac := Nat.choose_mul_factorial_mul_factorial hkn
  have hfacQ :
      (n.factorial : ℚ) =
        (n.choose k : ℚ) * (k.factorial : ℚ) *
          ((n - k).factorial : ℚ) := by
    exact_mod_cast hfac.symm
  rw [hfacQ]
  ring

@[simp]
theorem formalDerivativeAtZero_zero (f : PowerSeries ℚ) :
    formalDerivativeAtZero 0 f = PowerSeries.constantCoeff f := by
  rw [formalDerivativeAtZero]
  simp only [Nat.factorial_zero, Nat.cast_one, one_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- Differentiating the series increments the derivative order at zero. -/
theorem formalDerivativeAtZero_derivative
    (n : ℕ) (f : PowerSeries ℚ) :
    formalDerivativeAtZero n (d⁄dX ℚ f) =
      formalDerivativeAtZero (n + 1) f := by
  simp only [formalDerivativeAtZero, PowerSeries.coeff_derivative,
    Nat.factorial_succ]
  push_cast
  ring

/-! ## The uniform first-order bound for the additive remainder -/

/-- Translating an integer by `p` preserves every power modulo `p`. -/
theorem prime_dvd_shifted_pow_sub
    (p N : ℕ) (k : ℤ) :
    (p : ℤ) ∣ (k + p) ^ N - k ^ N := by
  have hbase :
      k + (p : ℤ) ≡ k [ZMOD (p : ℤ)] := by
    simpa only [mul_one] using
      (Int.modEq_add_fac_self
        (a := k) (n := (p : ℤ)) (t := 1))
  have hpow :
      (k + (p : ℤ)) ^ N ≡ k ^ N [ZMOD (p : ℤ)] :=
    hbase.pow N
  apply dvd_neg.mp
  simpa only [neg_sub] using hpow.dvd

theorem prime_dvd_shiftedPolynomialMoment
    (p N : ℕ) (P : ℤ[X]) :
    (p : ℤ) ∣ shiftedPolynomialMoment p P N := by
  rw [shiftedPolynomialMoment, Polynomial.sum_def]
  apply Finset.dvd_sum
  intro k hk
  apply dvd_mul_of_dvd_right
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    prime_dvd_shifted_pow_sub p N (k : ℤ)

theorem prime_dvd_additiveRemainderDerivativeInt
    (p N : ℕ) (P : ℤ[X]) (b₁ : ℤ) :
    (p : ℤ) ∣ additiveRemainderDerivativeInt p P b₁ N := by
  apply dvd_add
  · exact prime_dvd_shiftedPolynomialMoment p N P
  · refine ⟨b₁ * powerSumInt p N, ?_⟩
    ring

/-- Every derivative order of Vandiver's additive remainder has
`p`-adic valuation at least one.  This is the lower-order input to the
logarithmic-derivative recursion. -/
theorem additiveRemainder_derivative_hasPadicValAtLeast_one
    {p : ℕ} (hp : p.Prime) (N : ℕ) (P : ℤ[X]) (b₁ : ℤ) :
    HasPadicValAtLeast p 1
      (formalDerivativeAtZero N (additiveRemainder p P b₁)) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ :=
    prime_dvd_additiveRemainderDerivativeInt p N P b₁
  rw [formalDerivativeAtZero_additiveRemainder, hc]
  have hp1 := HasPadicValAtLeast.primePow (p := p) 1
  have hc0 := HasPadicValAtLeast.intCast (p := p) c
  norm_num [Int.cast_mul] at hp1 ⊢
  simpa only [Int.cast_natCast] using hp1.mul hc0

/-! ## Inverse-series recursion -/

/-- The constant derivative of the inverse of a valuation-zero constant
term again has valuation zero. -/
theorem formalDerivativeAtZero_inv_zero_hasVal_zero
    {p : ℕ} [Fact p.Prime] (Z : PowerSeries ℚ)
    (hZ0val : padicValRat p (PowerSeries.constantCoeff Z) = 0) :
    padicValRat p (formalDerivativeAtZero 0 Z⁻¹) = 0 := by
  rw [formalDerivativeAtZero_zero, PowerSeries.constantCoeff_inv,
    padicValRat.inv, hZ0val, neg_zero]

/-- If `Z(0)` is a nonzero `p`-adic unit and all positive derivatives of
`Z` through order `N` have valuation at least one, then the corresponding
positive derivatives of `Z⁻¹` do too. -/
theorem inverse_formalDerivative_hasPadicValAtLeast_one
    {p N : ℕ} (hp : p.Prime) (Z : PowerSeries ℚ)
    (hZ0 : PowerSeries.constantCoeff Z ≠ 0)
    (hZ0val : padicValRat p (PowerSeries.constantCoeff Z) = 0)
    (hZ : ∀ s : ℕ, 0 < s → s ≤ N →
      HasPadicValAtLeast p 1 (formalDerivativeAtZero s Z)) :
    ∀ s : ℕ, 0 < s → s ≤ N →
      HasPadicValAtLeast p 1 (formalDerivativeAtZero s Z⁻¹) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
      intro hs hsN
      let term : ℕ → ℚ := fun k ↦
        (s.choose k : ℚ) *
          formalDerivativeAtZero k Z⁻¹ *
          formalDerivativeAtZero (s - k) Z
      have hsum :
          HasPadicValAtLeast p 1
            (∑ k ∈ Finset.range s, term k) := by
        apply HasPadicValAtLeast.sum
        intro k hk
        have hks : k < s := Finset.mem_range.mp hk
        have hsubpos : 0 < s - k := Nat.sub_pos_of_lt hks
        have hsubN : s - k ≤ N := (Nat.sub_le s k).trans hsN
        have hZterm := hZ (s - k) hsubpos hsubN
        have hchoose :
            HasPadicValAtLeast p 0 (s.choose k : ℚ) := by
          simpa using
            (HasPadicValAtLeast.intCast
              (p := p) (s.choose k : ℤ))
        have hinv :
            HasPadicValAtLeast p 0
              (formalDerivativeAtZero k Z⁻¹) := by
          by_cases hk0 : k = 0
          · subst k
            right
            exact le_of_eq
              (formalDerivativeAtZero_inv_zero_hasVal_zero
                Z hZ0val).symm
          · exact (ih k hks (Nat.pos_of_ne_zero hk0)
              (Nat.le_of_lt hks |>.trans hsN)).mono (by omega)
        have hterm := hchoose.mul (hinv.mul hZterm)
        simpa only [term, zero_add, mul_assoc] using hterm
      have heq :
          (∑ k ∈ Finset.range (s + 1), term k) = 0 := by
        rw [← formalDerivativeAtZero_mul]
        rw [PowerSeries.inv_mul_cancel Z hZ0]
        simp [formalDerivativeAtZero, hs.ne']
      rw [Finset.sum_range_succ] at heq
      simp only [term, Nat.choose_self, Nat.cast_one, one_mul,
        Nat.sub_self, formalDerivativeAtZero_zero] at heq
      have hrec :
          PowerSeries.constantCoeff Z *
              formalDerivativeAtZero s Z⁻¹ =
            -(∑ k ∈ Finset.range s, term k) := by
        linarith
      have hmul :
          HasPadicValAtLeast p 1
            (PowerSeries.constantCoeff Z *
              formalDerivativeAtZero s Z⁻¹) := by
        rw [hrec]
        exact hsum.neg
      exact
        Fermat.Irregular.KummerTheorem.HasPadicValAtLeast.of_mul_left_of_val_eq_zero
          hZ0 hZ0val hmul

/-! ## The logarithmic-derivative consequence -/

/-- Source recursion for Vandiver's argument.

If `Z(0)` is a nonzero `p`-adic unit, every positive derivative through
order `N` has valuation at least one, and the order-`N` derivative has
valuation at least two, then the order-`N-1` derivative of `Z'/Z` has
valuation at least two. -/
theorem logarithmicDerivative_formalDerivative_hasPadicValAtLeast_two
    {p N : ℕ} (hp : p.Prime) (hN : 0 < N)
    (Z : PowerSeries ℚ)
    (hZ0 : PowerSeries.constantCoeff Z ≠ 0)
    (hZ0val : padicValRat p (PowerSeries.constantCoeff Z) = 0)
    (hZpos : ∀ s : ℕ, 0 < s → s ≤ N →
      HasPadicValAtLeast p 1 (formalDerivativeAtZero s Z))
    (hZN :
      HasPadicValAtLeast p 2 (formalDerivativeAtZero N Z)) :
    HasPadicValAtLeast p 2
      (formalDerivativeAtZero (N - 1) (logarithmicDerivative Z)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hInv :=
    inverse_formalDerivative_hasPadicValAtLeast_one
      hp Z hZ0 hZ0val hZpos
  rw [logarithmicDerivative, formalDerivativeAtZero_mul]
  apply HasPadicValAtLeast.sum
  intro k hk
  have hklt : k < N - 1 + 1 := Finset.mem_range.mp hk
  have hNm1 : N - 1 + 1 = N := by omega
  have hkN : k + 1 ≤ N := by omega
  have hchoose :
      HasPadicValAtLeast p 0 ((N - 1).choose k : ℚ) := by
    simpa using
      (HasPadicValAtLeast.intCast
        (p := p) ((N - 1).choose k : ℤ))
  rw [formalDerivativeAtZero_derivative]
  by_cases hktop : k = N - 1
  · subst k
    have hinv0 :
        HasPadicValAtLeast p 0
          (formalDerivativeAtZero (N - 1 - (N - 1)) Z⁻¹) := by
      simp only [Nat.sub_self]
      right
      exact le_of_eq
        (formalDerivativeAtZero_inv_zero_hasVal_zero
          Z hZ0val).symm
    have htop : formalDerivativeAtZero (N - 1 + 1) Z =
        formalDerivativeAtZero N Z := by rw [hNm1]
    rw [htop]
    have hterm := hchoose.mul (hZN.mul hinv0)
    simpa only [zero_add, add_zero, mul_assoc] using hterm
  · have hkstrict : k < N - 1 := Nat.lt_of_le_of_ne
        (by omega : k ≤ N - 1) hktop
    have hinv :
        HasPadicValAtLeast p 1
          (formalDerivativeAtZero (N - 1 - k) Z⁻¹) :=
      hInv (N - 1 - k) (Nat.sub_pos_of_lt hkstrict)
        (by omega)
    have hZterm :=
      hZpos (k + 1) (by omega) hkN
    have hterm := hchoose.mul (hZterm.mul hinv)
    norm_num [mul_assoc] at hterm ⊢
    exact hterm

/-- Additive-input form of the logarithmic-derivative propagation theorem.
This is convenient when the source series is split into a controlled base
and Vandiver's additive polynomial remainder. -/
theorem logarithmicDerivative_add_formalDerivative_hasPadicValAtLeast_two
    {p N : ℕ} (hp : p.Prime) (hN : 0 < N)
    (F G : PowerSeries ℚ)
    (h0 : PowerSeries.constantCoeff (F + G) ≠ 0)
    (h0val :
      padicValRat p (PowerSeries.constantCoeff (F + G)) = 0)
    (hFpos : ∀ s : ℕ, 0 < s → s ≤ N →
      HasPadicValAtLeast p 1 (formalDerivativeAtZero s F))
    (hGpos : ∀ s : ℕ, 0 < s → s ≤ N →
      HasPadicValAtLeast p 1 (formalDerivativeAtZero s G))
    (hFN : HasPadicValAtLeast p 2 (formalDerivativeAtZero N F))
    (hGN : HasPadicValAtLeast p 2 (formalDerivativeAtZero N G)) :
    HasPadicValAtLeast p 2
      (formalDerivativeAtZero (N - 1)
        (logarithmicDerivative (F + G))) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply logarithmicDerivative_formalDerivative_hasPadicValAtLeast_two
    hp hN (F + G) h0 h0val
  · intro s hs hsN
    rw [formalDerivativeAtZero_add]
    exact (hFpos s hs hsN).add (hGpos s hs hsN)
  · rw [formalDerivativeAtZero_add]
    exact hFN.add hGN

end Fermat.Irregular.VandiverLogDerivativeValuation
