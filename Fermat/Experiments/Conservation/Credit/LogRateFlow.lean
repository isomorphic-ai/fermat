/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Generator-derived logarithmic rate

Kummer's logarithmic derivative is constructed here from the same
geometric generator used by the real cyclotomic relation polynomials.
Its Bernoulli coefficients are therefore derived flow coefficients, not an
independent classical input.  Vandiver identified the resulting assembly;
this module records it without importing the classical chain.
-/
import Fermat.Experiments.Conservation.Credit.RelationDepthFlow
import Fermat.Experiments.Conservation.Credit.Bernoulli

open scoped BigOperators

namespace Fermat.Conservation.Credit.LogRate

open PowerSeries

namespace Formal

/-- The geometric cyclotomic node after the Euler substitution `X = exp T`. -/
noncomputable def geometricExp (r : ℕ) : PowerSeries ℚ :=
  ∑ j ∈ Finset.range r, PowerSeries.exp ℚ ^ j

/-- Its generator-derived logarithmic rate. -/
noncomputable def geometricRate (r : ℕ) : PowerSeries ℚ :=
  Flow.regularizedLogDerivative (r : ℚ)

theorem geometricExp_mul_exp_sub_one (r : ℕ) :
    geometricExp r * (PowerSeries.exp ℚ - 1) =
      PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ) - 1 := by
  rw [geometricExp, geom_sum_mul, PowerSeries.exp_pow_eq_rescale_exp]

theorem derivative_rescale_exp (r : ℚ) :
    d⁄dX ℚ (PowerSeries.rescale r (PowerSeries.exp ℚ)) =
      PowerSeries.C r * PowerSeries.rescale r (PowerSeries.exp ℚ) := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul]
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem rescale_generator_mul_rescale_exp_sub_one (r : ℚ) :
    PowerSeries.rescale r Flow.generator *
        (PowerSeries.rescale r (PowerSeries.exp ℚ) - 1) =
      PowerSeries.C r * PowerSeries.X *
        PowerSeries.rescale r (PowerSeries.exp ℚ) := by
  have h := congrArg
    (fun s : PowerSeries ℚ ↦ PowerSeries.rescale r s)
    Flow.generator_mul_exp_sub_one
  simpa [map_mul, map_sub, PowerSeries.rescale_X, mul_assoc] using h

theorem derivative_geometricExp (r : ℕ) :
    d⁄dX ℚ (geometricExp r) =
      geometricExp r * geometricRate r := by
  let E : PowerSeries ℚ := PowerSeries.exp ℚ
  let G : PowerSeries ℚ := geometricExp r
  let R : PowerSeries ℚ := geometricRate r
  have hgeom : G * (E - 1) =
      PowerSeries.rescale (r : ℚ) E - 1 := by
    simpa [E, G] using geometricExp_mul_exp_sub_one r
  have hderiv := congrArg (d⁄dX ℚ) hgeom
  have hderiv' :
      d⁄dX ℚ G * (E - 1) + G * E =
        PowerSeries.C (r : ℚ) *
          PowerSeries.rescale (r : ℚ) E := by
    simpa [E, map_sub, derivative_rescale_exp,
      PowerSeries.derivative_exp, mul_comm] using hderiv
  have hsolve :
      d⁄dX ℚ G * (E - 1) =
        PowerSeries.C (r : ℚ) *
            PowerSeries.rescale (r : ℚ) E -
          G * E := by
    linear_combination hderiv'
  have hscaled :
      PowerSeries.rescale (r : ℚ) Flow.generator *
          (PowerSeries.rescale (r : ℚ) E - 1) =
        PowerSeries.C (r : ℚ) * PowerSeries.X *
          PowerSeries.rescale (r : ℚ) E := by
    simpa [E] using
      rescale_generator_mul_rescale_exp_sub_one (r : ℚ)
  have hgen :
      Flow.generator * (E - 1) = PowerSeries.X * E := by
    simpa [E] using Flow.generator_mul_exp_sub_one
  have hXR :
      PowerSeries.X * R =
        PowerSeries.rescale (r : ℚ) Flow.generator -
          Flow.generator := by
    simpa [R, geometricRate] using
      Flow.X_mul_regularizedLogDerivative (r : ℚ)
  have hmul :
      d⁄dX ℚ G * (PowerSeries.X * (E - 1)) =
        (G * R) * (PowerSeries.X * (E - 1)) := by
    calc
      d⁄dX ℚ G * (PowerSeries.X * (E - 1)) =
          PowerSeries.X * (d⁄dX ℚ G * (E - 1)) := by ring
      _ = PowerSeries.X *
          (PowerSeries.C (r : ℚ) *
              PowerSeries.rescale (r : ℚ) E - G * E) := by
            rw [hsolve]
      _ = PowerSeries.C (r : ℚ) * PowerSeries.X *
            PowerSeries.rescale (r : ℚ) E -
          G * (PowerSeries.X * E) := by ring
      _ = PowerSeries.rescale (r : ℚ) Flow.generator *
            (PowerSeries.rescale (r : ℚ) E - 1) -
          G * (Flow.generator * (E - 1)) := by
            rw [hscaled, hgen]
      _ = G *
          (PowerSeries.rescale (r : ℚ) Flow.generator -
            Flow.generator) * (E - 1) := by
            rw [← hgeom]
            ring
      _ = (G * R) * (PowerSeries.X * (E - 1)) := by
            rw [← hXR]
            ring
  have hE : E - 1 ≠ 0 := by
    change PowerSeries.exp ℚ - 1 ≠ 0
    simp only [PowerSeries.exp, PowerSeries.ext_iff, ne_eq,
      not_forall]
    refine ⟨1, ?_⟩
    simp
  have hfactor : PowerSeries.X * (E - 1) ≠ 0 :=
    mul_ne_zero PowerSeries.X_ne_zero hE
  simpa [G, R] using mul_right_cancel₀ hfactor hmul

/-- The folded geometric node after the Euler substitution.  The first
factor is the conjugation monomial; the geometric unit occurs twice. -/
noncomputable def foldedExp (monomial r : ℕ) : PowerSeries ℚ :=
  PowerSeries.rescale (monomial : ℚ) (PowerSeries.exp ℚ) *
    geometricExp r ^ 2

/-- The logarithmic rate of a folded node is the constant monomial rate
plus twice the generated geometric rate. -/
noncomputable def foldedRate (monomial r : ℕ) : PowerSeries ℚ :=
  PowerSeries.C (monomial : ℚ) +
    PowerSeries.C 2 * geometricRate r

theorem derivative_foldedExp (monomial r : ℕ) :
    d⁄dX ℚ (foldedExp monomial r) =
      foldedExp monomial r * foldedRate monomial r := by
  rw [foldedExp, foldedRate]
  rw [Derivation.leibniz, derivative_rescale_exp,
    PowerSeries.derivative_pow, derivative_geometricExp]
  simp only [smul_eq_mul]
  push_cast
  simp only [map_natCast, map_ofNat]
  ring

/-- A source/rate pair satisfies the defining logarithmic-derivative
equation without choosing an inverse. -/
def IsLogRate (source rate : PowerSeries ℚ) : Prop :=
  d⁄dX ℚ source = source * rate

theorem isLogRate_foldedExp (monomial r : ℕ) :
    IsLogRate (foldedExp monomial r) (foldedRate monomial r) :=
  derivative_foldedExp monomial r

theorem IsLogRate.mul {f g rf rg : PowerSeries ℚ}
    (hf : IsLogRate f rf) (hg : IsLogRate g rg) :
    IsLogRate (f * g) (rf + rg) := by
  rw [IsLogRate, Derivation.leibniz, hf, hg]
  simp only [smul_eq_mul]
  ring

/-- A quotient represented without division: if `f = q * g`, then the
logarithmic rate of `q` is the difference of the rates of `f` and `g`. -/
theorem IsLogRate.quotient {f g q rf rg : PowerSeries ℚ}
    (hf : IsLogRate f rf) (hg : IsLogRate g rg)
    (hquot : f = q * g) (hg0 : g ≠ 0) :
    IsLogRate q (rf - rg) := by
  rw [IsLogRate] at hf hg ⊢
  have hderiv := congrArg (d⁄dX ℚ) hquot
  rw [hf, hquot, Derivation.leibniz, hg] at hderiv
  simp only [smul_eq_mul] at hderiv
  apply mul_right_cancel₀ hg0
  linear_combination -hderiv

theorem IsLogRate.pow {f rate : PowerSeries ℚ}
    (hf : IsLogRate f rate) (e : ℕ) :
    IsLogRate (f ^ e) (PowerSeries.C (e : ℚ) * rate) := by
  induction e with
  | zero =>
      simp [IsLogRate]
  | succ e ih =>
      rw [pow_succ]
      have hmul := ih.mul hf
      convert hmul using 1
      push_cast
      simp only [map_add, map_one, map_natCast]
      ring

theorem formalDerivativeAtZero_geometricRate (r n : ℕ) :
    Flow.formalDerivativeAtZero n (geometricRate r) =
      ((r : ℚ) ^ (n + 1) - 1) *
        (bernoulli' (n + 1) / (n + 1 : ℚ)) := by
  simpa [geometricRate] using
    Flow.formalDerivativeAtZero_regularizedLogDerivative
      (r : ℚ) n

theorem formalDerivativeAtZero_foldedRate_of_pos
    (monomial r n : ℕ) (hn : 0 < n) :
    Flow.formalDerivativeAtZero n (foldedRate monomial r) =
      2 * (((r : ℚ) ^ (n + 1) - 1) *
        (bernoulli' (n + 1) / (n + 1 : ℚ))) := by
  rw [Flow.formalDerivativeAtZero, foldedRate]
  simp only [map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C, if_neg hn.ne', zero_add]
  calc
    (Nat.factorial n : ℚ) *
          (2 * PowerSeries.coeff n (geometricRate r)) =
        2 * Flow.formalDerivativeAtZero n (geometricRate r) := by
          rw [Flow.formalDerivativeAtZero]
          ring
    _ = _ := by rw [formalDerivativeAtZero_geometricRate]

theorem formalDerivativeAtZero_foldedRate_high
    (monomial r N : ℕ) (hN : 1 < N) (heven : Even N) :
    Flow.formalDerivativeAtZero (N - 1) (foldedRate monomial r) =
      2 * (((r : ℚ) ^ N - 1) *
        (bernoulli N / (N : ℚ))) := by
  rw [formalDerivativeAtZero_foldedRate_of_pos monomial r
    (N - 1) (by omega)]
  have hindex : N - 1 + 1 = N := by omega
  rw [hindex, bernoulli'_eq_bernoulli, heven.neg_one_pow, one_mul]
  have hindexQ :
      ((N - 1 : ℕ) : ℚ) + 1 = (N : ℚ) := by
    exact_mod_cast hindex
  rw [hindexQ]

/-- Normalizing a folded node by an exponent multiplies its rate by that
same exponent. -/
theorem normalized_folded_logRate (monomial r e : ℕ) :
    IsLogRate ((foldedExp monomial r) ^ e)
      (PowerSeries.C (e : ℚ) * foldedRate monomial r) :=
  (isLogRate_foldedExp monomial r).pow e

theorem formalDerivativeAtZero_normalized_foldedRate_high
    (monomial r e N : ℕ) (hN : 1 < N) (heven : Even N) :
    Flow.formalDerivativeAtZero (N - 1)
        (PowerSeries.C (e : ℚ) * foldedRate monomial r) =
      (e : ℚ) * 2 * (((r : ℚ) ^ N - 1) *
        (bernoulli N / (N : ℚ))) := by
  rw [Flow.formalDerivativeAtZero, PowerSeries.coeff_C_mul]
  calc
    (Nat.factorial (N - 1) : ℚ) *
          ((e : ℚ) *
            PowerSeries.coeff (N - 1) (foldedRate monomial r)) =
        (e : ℚ) *
          Flow.formalDerivativeAtZero (N - 1)
            (foldedRate monomial r) := by
              rw [Flow.formalDerivativeAtZero]
              ring
    _ = _ := by
      rw [formalDerivativeAtZero_foldedRate_high monomial r N hN heven]
      ring

theorem formalDerivativeAtZero_add
    (n : ℕ) (f g : PowerSeries ℚ) :
    Flow.formalDerivativeAtZero n (f + g) =
      Flow.formalDerivativeAtZero n f +
        Flow.formalDerivativeAtZero n g := by
  simp [Flow.formalDerivativeAtZero, mul_add]

theorem formalDerivativeAtZero_sub
    (n : ℕ) (f g : PowerSeries ℚ) :
    Flow.formalDerivativeAtZero n (f - g) =
      Flow.formalDerivativeAtZero n f -
        Flow.formalDerivativeAtZero n g := by
  simp [Flow.formalDerivativeAtZero, mul_sub]

theorem formalDerivativeAtZero_C_mul
    (n : ℕ) (c : ℚ) (f : PowerSeries ℚ) :
    Flow.formalDerivativeAtZero n (PowerSeries.C c * f) =
      c * Flow.formalDerivativeAtZero n f := by
  rw [Flow.formalDerivativeAtZero, PowerSeries.coeff_C_mul,
    Flow.formalDerivativeAtZero]
  ring

theorem formalDerivativeAtZero_finset_sum
    {ι : Type*} (s : Finset ι) (n : ℕ)
    (f : ι → PowerSeries ℚ) :
    Flow.formalDerivativeAtZero n (∑ i ∈ s, f i) =
      ∑ i ∈ s, Flow.formalDerivativeAtZero n (f i) := by
  simp [Flow.formalDerivativeAtZero, Finset.mul_sum]

end Formal

namespace Relation

open RealFlow
open Formal

/-- The nonconstant logarithmic rate of the normalized generated
numerator divided by its denominator.  Constants from the folding
monomials disappear at every selected positive degree. -/
noncomputable def generatedRelationRate {p : ℕ}
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) : PowerSeries ℚ :=
  PowerSeries.C (2 * (p - 1 : ℚ)) *
    ∑ i,
      PowerSeries.C (raw i : ℚ) *
        (geometricRate
            (RealFlow.teichLift p (data.nodeLift (i.val + 1))) -
          geometricRate (RealFlow.teichLift p (data.nodeLift i.val)))

theorem formalDerivativeAtZero_generatedRelationRate
    {p N : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ)
    (hN : 1 < N) (heven : Even N) :
    Flow.formalDerivativeAtZero (N - 1)
        (generatedRelationRate data raw) =
      (2 * (p - 1 : ℚ)) *
        ((∑ i, (raw i : ℚ) *
          ((RealFlow.teichLift p
              (data.nodeLift (i.val + 1)) : ℚ) ^ N -
            (RealFlow.teichLift p (data.nodeLift i.val) : ℚ) ^ N)) *
          (bernoulli N / (N : ℚ))) := by
  rw [generatedRelationRate, formalDerivativeAtZero_C_mul,
    formalDerivativeAtZero_finset_sum]
  apply congrArg ((2 * (p - 1 : ℚ)) * ·)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [formalDerivativeAtZero_C_mul,
    formalDerivativeAtZero_sub,
    formalDerivativeAtZero_geometricRate,
    formalDerivativeAtZero_geometricRate]
  have hindex : N - 1 + 1 = N := by omega
  have hindexQ :
      ((N - 1 : ℕ) : ℚ) + 1 = (N : ℚ) := by
    exact_mod_cast hindex
  rw [hindex, bernoulli'_eq_bernoulli, heven.neg_one_pow,
    one_mul, hindexQ]
  ring

theorem formalDerivativeAtZero_generatedRelationRate_high
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (row : Fin data.rank) :
    Flow.formalDerivativeAtZero
        (RealFlow.highIndex (data := data) row - 1)
        (generatedRelationRate data raw) =
      (2 * (p - 1 : ℚ)) *
        ((RealFlow.exactHighEdgeCoefficient data raw row : ℚ) *
          (bernoulli (RealFlow.highIndex (data := data) row) /
            (RealFlow.highIndex (data := data) row : ℚ))) := by
  have hN :
      1 < RealFlow.highIndex (data := data) row := by
    unfold RealFlow.highIndex
    rw [mul_assoc]
    have hprod : 0 < (row.val + 1) * p :=
      Nat.mul_pos (Nat.succ_pos row.val) data.prime.pos
    omega
  have heven :
      Even (RealFlow.highIndex (data := data) row) := by
    simp [RealFlow.highIndex]
  rw [formalDerivativeAtZero_generatedRelationRate
    data raw hN heven]
  apply congrArg ((2 * (p - 1 : ℚ)) * ·)
  rw [RealFlow.exactHighEdgeCoefficient]
  push_cast
  apply congrArg (· *
    (bernoulli (RealFlow.highIndex (data := data) row) /
      (RealFlow.highIndex (data := data) row : ℚ)))
  apply Finset.sum_congr rfl
  intro i _
  have hnext :
      (RealFlow.teichLift p (data.nodeLift (i.val + 1)) : ℚ) =
        (RealFlow.teichNodeValue data (i.val + 1) : ℚ) := by
    rfl
  have hcurrent :
      (RealFlow.teichLift p (data.nodeLift i.val) : ℚ) =
        (RealFlow.teichNodeValue data i.val : ℚ) := by
    rfl
  rw [hnext, hcurrent]

end Relation

namespace Arithmetic

/-- A prime-square-zero rational log jet forces the prime-cube numerator
divisibility needed by `RealFlow.HighFlowVanishes`.

`hden` is the exact condition under which a rational jet reduces modulo
`p²`; `hsquare` says that reduction is zero.  The extra prime comes from
the selected index `N`, while `2(p-1)` and the jet denominator cancel as
prime-to-`p` factors. -/
theorem prime_cube_dvd_exact_of_rate_numerator_sq
    {p N : ℕ} (hp : p.Prime) (hpOdd : Odd p)
    (hN : 0 < N) (hpN : p ∣ N)
    {exact : ℤ} {rate : ℚ}
    (hrate :
      rate =
        (2 * (p - 1 : ℚ)) * (exact : ℚ) *
          (bernoulli N / (N : ℚ)))
    (hden : ¬p ∣ rate.den)
    (hsquare : (p : ℤ) ^ 2 ∣ rate.num) :
    (p : ℤ) ^ 3 ∣ exact * (bernoulli N).num := by
  let factor : ℕ := 2 * (p - 1)
  have hfactorQ :
      (factor : ℚ) = 2 * (p - 1 : ℚ) := by
    dsimp [factor]
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hp.one_le]
    norm_num
  have hcrossRat :
      (rate.num : ℚ) * (bernoulli N).den * N =
        (factor : ℚ) * (exact : ℚ) *
          (bernoulli N).num * rate.den := by
    rw [hfactorQ]
    rw [← rate.num_div_den, ← (bernoulli N).num_div_den] at hrate
    field_simp [hN.ne'] at hrate ⊢
    linear_combination hrate
  have hcross :
      rate.num * ((bernoulli N).den : ℤ) * (N : ℤ) =
        (factor : ℤ) * exact *
          (bernoulli N).num * (rate.den : ℤ) := by
    exact_mod_cast hcrossRat
  have hleft :
      (p : ℤ) ^ 3 ∣
        rate.num * ((bernoulli N).den : ℤ) * (N : ℤ) := by
    rcases hsquare with ⟨u, hu⟩
    rcases hpN with ⟨v, hv⟩
    refine ⟨u * ((bernoulli N).den : ℤ) * (v : ℤ), ?_⟩
    rw [hu, hv]
    push_cast
    ring
  have hwhole :
      (p : ℤ) ^ 3 ∣
        (factor : ℤ) *
          (exact * (bernoulli N).num * (rate.den : ℤ)) := by
    have hwhole' :
        (p : ℤ) ^ 3 ∣
          (factor : ℤ) * exact *
            (bernoulli N).num * (rate.den : ℤ) := by
      rw [← hcross]
      exact hleft
    simpa [mul_assoc] using hwhole'
  have hpcopTwo : p.Coprime 2 := hpOdd.coprime_two_right
  have hpcopPred : p.Coprime (p - 1) := by
    rw [Nat.coprime_self_sub_right hp.one_le]
    simp
  have hpcopFactor : p.Coprime factor := by
    change p.Coprime (2 * (p - 1))
    rw [Nat.coprime_mul_iff_right]
    exact ⟨hpcopTwo, hpcopPred⟩
  have hfactorInt :
      IsCoprime ((p : ℤ) ^ 3) (factor : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa [Int.natAbs_pow] using hpcopFactor.pow_left 3
  have hwithoutFactor :
      (p : ℤ) ^ 3 ∣
        exact * (bernoulli N).num * (rate.den : ℤ) :=
    hfactorInt.dvd_of_dvd_mul_left hwhole
  have hpcopDen : p.Coprime rate.den :=
    hp.coprime_iff_not_dvd.mpr hden
  have hdenInt :
      IsCoprime ((p : ℤ) ^ 3) (rate.den : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa [Int.natAbs_pow] using hpcopDen.pow_left 3
  exact hdenInt.dvd_of_dvd_mul_right hwithoutFactor

end Arithmetic

end Fermat.Conservation.Credit.LogRate
