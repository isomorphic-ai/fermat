import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Tactic

/-!
# Prime-parameterized diagonal arithmetic for Vandiver's Lemma II

Let `p = 2 * r + 1` be prime, and let `t` be a Teichmüller lift modulo
`p²` whose reduction is primitive modulo `p`. Vandiver's independent real
units are indexed by `Fin (r - 1)`, while each character sum has `r` terms.

This module proves the finite diagonal calculation uniformly in `p`.
Off the diagonal, the summand ratio is a nontrivial `(p - 1)`st root of
unity modulo `p²`; its difference from one is a unit, so the geometric sum
vanishes. On the diagonal, all `r` summands equal one.

The second half converts Vandiver's positive exponents to the same
character sum, reduces `rho = t ^ (p²)` to `t`, and records the outer
factor `p - 1`. Prime-specific modules need only supply the two finite
Teichmüller certificates.
-/

namespace Fermat.Irregular.VandiverDiagonalArithmeticPrime

open Finset

set_option maxHeartbeats 0
set_option maxRecDepth 100000

variable {p r t : ℕ} [Fact p.Prime]

/-- Vandiver's source indices `1, ..., r - 1`. -/
def sourceIndex (i : Fin (r - 1)) : ℕ := i.val + 1

/-- The exponent in the row-`k`, column-`n` character sum. -/
def characterExponent (p : ℕ) (k n : Fin (r - 1)) (j : ℕ) : ℕ :=
  2 * j * (p * sourceIndex k - sourceIndex n)

/-- The `r`-term character sum in Vandiver's formula (4). -/
def characterSum (p t : ℕ) (k n : Fin (r - 1)) : ZMod (p ^ 2) :=
  ∑ j ∈ range r,
    (t : ZMod (p ^ 2)) ^ characterExponent p k n j

/-- The complete prime-parameterized diagonal character-sum calculation. -/
theorem characterSum_eq
    (hp : p = 2 * r + 1)
    (hr : 2 ≤ r)
    (htpow : (t : ZMod (p ^ 2)) ^ (p - 1) = 1)
    (htprim : IsPrimitiveRoot (t : ZMod p) (p - 1))
    (k n : Fin (r - 1)) :
    characterSum p t k n = if k = n then r else 0 := by
  let d := p * sourceIndex k - sourceIndex n
  let w : ZMod (p ^ 2) := (t : ZMod (p ^ 2)) ^ (2 * d)
  have hsum :
      characterSum p t k n = ∑ j ∈ range r, w ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← pow_mul]
    congr 1
    simp only [characterExponent, d]
    ring
  by_cases hkn : k = n
  · subst n
    rw [if_pos rfl, hsum]
    have hw : w = 1 := by
      simp only [w, d]
      have heq :
          2 * (p * sourceIndex k - sourceIndex k) =
            (p - 1) * (2 * sourceIndex k) := by
        calc
          2 * (p * sourceIndex k - sourceIndex k) =
              2 * ((p - 1) * sourceIndex k) := by
                rw [Nat.sub_mul]
                simp
          _ = (p - 1) * (2 * sourceIndex k) := by ring
      rw [heq, pow_mul, htpow, one_pow]
    rw [hw]
    simp
  · rw [if_neg hkn, hsum]
    have hwcard : w ^ (p - 1) = 1 := by
      simp only [w]
      rw [← pow_mul]
      rw [show 2 * d * (p - 1) = (p - 1) * (2 * d) by ring]
      rw [pow_mul, htpow, one_pow]
    have hord : orderOf w ∣ p - 1 :=
      orderOf_dvd_iff_pow_eq_one.mpr hwcard
    have hcop : (orderOf w).Coprime (p ^ 2) :=
      Nat.Coprime.of_dvd_left hord (by
        apply Nat.Coprime.pow_right
        apply (Nat.coprime_self_sub_left (by omega : 1 ≤ p)).mpr
        exact Nat.coprime_one_left p)
    have hw_ne : w ≠ 1 := by
      intro hw
      have hmap := congrArg
        (ZMod.castHom (by exact dvd_pow_self p (by omega)) (ZMod p)) hw
      simp only [w, map_pow, map_natCast, map_one] at hmap
      have hdvd : p - 1 ∣ 2 * d :=
        (htprim.pow_eq_one_iff_dvd _).mp hmap
      have hpd : p - 1 = 2 * r := by omega
      have hrd : r ∣ d := by
        rw [hpd] at hdvd
        exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).mp hdvd
      have hkpos : 0 < sourceIndex k := by simp [sourceIndex]
      have hklt : sourceIndex k < r := by
        have hk := k.isLt
        simp [sourceIndex]
        omega
      have hnlt : sourceIndex n < r := by
        have hn := n.isLt
        simp [sourceIndex]
        omega
      have hpmod : p ≡ 1 [MOD r] := by
        rw [hp]
        simp [Nat.ModEq, Nat.add_mod,
          Nat.mod_eq_of_lt (by omega : 1 < r)]
      have hdeq : d + sourceIndex n = p * sourceIndex k := by
        simp only [d]
        have hnp : sourceIndex n ≤ p * sourceIndex k := by
          have hnp' : sourceIndex n < p := by omega
          exact hnp'.le.trans (Nat.le_mul_of_pos_right p hkpos)
        omega
      have hdmod : d ≡ 0 [MOD r] :=
        Nat.modEq_zero_iff_dvd.mpr hrd
      have hright :
          p * sourceIndex k ≡ sourceIndex n [MOD r] := by
        rw [← hdeq]
        simpa using hdmod.add_right (sourceIndex n)
      have hleft :
          p * sourceIndex k ≡ sourceIndex k [MOD r] := by
        simpa using hpmod.mul_right (sourceIndex k)
      have hindex :
          sourceIndex k ≡ sourceIndex n [MOD r] :=
        hleft.symm.trans hright
      have hindex' := hindex
      unfold Nat.ModEq at hindex'
      rw [Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt hnlt] at hindex'
      apply hkn
      apply Fin.ext
      simpa [sourceIndex] using hindex'
    obtain hwone | hunit :=
      ZMod.eq_one_or_isUnit_sub_one
        (p := p) (k := 2) rfl w hcop
    · exact (hw_ne hwone).elim
    · have hwroot : w ^ r = 1 := by
        simp only [w]
        rw [← pow_mul]
        have hpd : p - 1 = 2 * r := by omega
        have hexp : 2 * d * r = (p - 1) * d := by
          rw [hpd]
          ring
        rw [hexp, pow_mul, htpow, one_pow]
      have hgeom := mul_geom_sum w r
      rw [hwroot, sub_self] at hgeom
      exact hunit.mul_left_cancel (by simpa using hgeom)

/-- Off-diagonal character sums vanish modulo `p²`. -/
theorem characterSum_eq_zero
    (hp : p = 2 * r + 1)
    (hr : 2 ≤ r)
    (htpow : (t : ZMod (p ^ 2)) ^ (p - 1) = 1)
    (htprim : IsPrimitiveRoot (t : ZMod p) (p - 1))
    {k n : Fin (r - 1)} (hkn : k ≠ n) :
    characterSum p t k n = 0 := by
  rw [characterSum_eq hp hr htpow htprim, if_neg hkn]
  norm_num

/-- A diagonal character sum has exactly `r` terms. -/
theorem characterSum_self
    (hp : p = 2 * r + 1)
    (hr : 2 ≤ r)
    (htpow : (t : ZMod (p ^ 2)) ^ (p - 1) = 1)
    (htprim : IsPrimitiveRoot (t : ZMod p) (p - 1))
    (k : Fin (r - 1)) :
    characterSum p t k k = r := by
  rw [characterSum_eq hp hr htpow htprim, if_pos rfl]

/-- Vandiver's positive exponent after multiplying the formal exponent by
`rho = t ^ (p ^ 2)`. -/
def positiveCharacterExponent (p : ℕ) (k n : Fin (r - 1)) (j : ℕ) : ℕ :=
  p ^ 2 - 2 * sourceIndex n * j + 2 * p * sourceIndex k * j

/-- The diagonal character sum in its positive-exponent presentation. -/
def positiveCharacterSum (p t : ℕ) (k n : Fin (r - 1)) :
    ZMod (p ^ 2) :=
  ∑ j ∈ range r,
    (t : ZMod (p ^ 2)) ^ positiveCharacterExponent p k n j

/-- The positive-exponent sum is the original sum multiplied by
`rho = t ^ (p ^ 2)`. -/
theorem positiveCharacterSum_eq_rho_mul
    (hp : p = 2 * r + 1)
    (hr : 2 ≤ r)
    (k n : Fin (r - 1)) :
    positiveCharacterSum p t k n =
      (t : ZMod (p ^ 2)) ^ (p ^ 2) * characterSum p t k n := by
  rw [positiveCharacterSum, characterSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_add]
  congr 1
  simp only [positiveCharacterExponent, characterExponent]
  have hjlt : j < r := Finset.mem_range.mp hj
  have hkpos : 0 < sourceIndex k := by simp [sourceIndex]
  have hnlt : sourceIndex n < r := by
    have hn := n.isLt
    simp [sourceIndex]
    omega
  have hnPk : sourceIndex n ≤ p * sourceIndex k := by
    have hnp : sourceIndex n < p := by omega
    exact hnp.le.trans (Nat.le_mul_of_pos_right p hkpos)
  have hsmall :
      2 * sourceIndex n * j ≤ p ^ 2 := by
    calc
      2 * sourceIndex n * j ≤ 2 * r * r := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_left 2 hnlt.le)
          hjlt.le
      _ ≤ p ^ 2 := by
        subst p
        nlinarith
  have hsmall' :
      2 * j * sourceIndex n ≤ p ^ 2 := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hsmall
  rw [show 2 * p * sourceIndex k * j =
      2 * j * (p * sourceIndex k) by ring]
  rw [show 2 * sourceIndex n * j =
      2 * j * sourceIndex n by ring]
  rw [Nat.mul_sub_left_distrib]
  have hscaled :=
    Nat.mul_le_mul_left (2 * j) hnPk
  omega

/-- Prime-parameterized positive-exponent diagonal calculation. -/
theorem positiveCharacterSum_eq
    (hp : p = 2 * r + 1)
    (hr : 2 ≤ r)
    (htpow : (t : ZMod (p ^ 2)) ^ (p - 1) = 1)
    (htprim : IsPrimitiveRoot (t : ZMod p) (p - 1))
    (k n : Fin (r - 1)) :
    positiveCharacterSum p t k n =
      if k = n then r * (t : ZMod (p ^ 2)) ^ (p ^ 2) else 0 := by
  rw [positiveCharacterSum_eq_rho_mul hp hr,
    characterSum_eq hp hr htpow htprim]
  split_ifs <;> ring

omit [Fact p.Prime] in
/-- Since `p ^ 2 ≡ 1 (mod p - 1)`, `rho` reduces to the Teichmüller
root itself. -/
theorem rho_eq_root
    (hp : p = 2 * r + 1)
    (hr : 2 ≤ r)
    (htpow : (t : ZMod (p ^ 2)) ^ (p - 1) = 1) :
    (t : ZMod (p ^ 2)) ^ (p ^ 2) = t := by
  have hp1 : 1 ≤ p := by omega
  have hexp : p ^ 2 = (p - 1) * (p + 1) + 1 := by
    nlinarith [Nat.sub_add_cancel hp1]
  calc
    (t : ZMod (p ^ 2)) ^ (p ^ 2) =
        (t : ZMod (p ^ 2)) ^ ((p - 1) * (p + 1) + 1) := by rw [hexp]
    _ = ((t : ZMod (p ^ 2)) ^ (p - 1)) ^ (p + 1) * t := by
      rw [pow_add, pow_mul, pow_one]
    _ = t := by rw [htpow, one_pow, one_mul]

/-- The positive-exponent diagonal residue is `r * t`, and every
off-diagonal residue vanishes. -/
theorem positiveCharacterSum_eq_root_or_zero
    (hp : p = 2 * r + 1)
    (hr : 2 ≤ r)
    (htpow : (t : ZMod (p ^ 2)) ^ (p - 1) = 1)
    (htprim : IsPrimitiveRoot (t : ZMod p) (p - 1))
    (k n : Fin (r - 1)) :
    positiveCharacterSum p t k n =
      if k = n then r * (t : ZMod (p ^ 2)) else 0 := by
  rw [positiveCharacterSum_eq hp hr htpow htprim,
    rho_eq_root hp hr htpow]

/-- The positive diagonal entry is `r * t`. -/
theorem positiveCharacterSum_self
    (hp : p = 2 * r + 1)
    (hr : 2 ≤ r)
    (htpow : (t : ZMod (p ^ 2)) ^ (p - 1) = 1)
    (htprim : IsPrimitiveRoot (t : ZMod p) (p - 1))
    (k : Fin (r - 1)) :
    positiveCharacterSum p t k k = r * t := by
  rw [positiveCharacterSum_eq_root_or_zero hp hr htpow htprim, if_pos rfl]

/-- Positive off-diagonal entries vanish. -/
theorem positiveCharacterSum_eq_zero
    (hp : p = 2 * r + 1)
    (hr : 2 ≤ r)
    (htpow : (t : ZMod (p ^ 2)) ^ (p - 1) = 1)
    (htprim : IsPrimitiveRoot (t : ZMod p) (p - 1))
    {k n : Fin (r - 1)} (hkn : k ≠ n) :
    positiveCharacterSum p t k n = 0 := by
  rw [positiveCharacterSum_eq_root_or_zero hp hr htpow htprim, if_neg hkn]

/-- Multiplication by Vandiver's outer factor `p - 1` preserves the
diagonal form. -/
theorem relationCharacterFactor_eq
    (hp : p = 2 * r + 1)
    (hr : 2 ≤ r)
    (htpow : (t : ZMod (p ^ 2)) ^ (p - 1) = 1)
    (htprim : IsPrimitiveRoot (t : ZMod p) (p - 1))
    (k n : Fin (r - 1)) :
    (p - 1 : ZMod (p ^ 2)) * positiveCharacterSum p t k n =
      if k = n then
        (p - 1 : ZMod (p ^ 2)) * r * t
      else 0 := by
  rw [positiveCharacterSum_eq_root_or_zero hp hr htpow htprim]
  split_ifs <;> ring

end Fermat.Irregular.VandiverDiagonalArithmeticPrime
