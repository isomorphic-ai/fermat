import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.NumberField.DedekindZeta

open scoped NumberField Classical

namespace Fermat.Irregular.IdealCount

noncomputable section

variable {S : Type*} [CommRing S] [Nontrivial S] [IsDedekindDomain S]
  [Module.Free ℤ S] [Module.Finite ℤ S] [CharZero S]

omit [Module.Finite ℤ S] [CharZero S] in
/-- Ideals whose absolute norms are coprime are relatively prime as elements
of the ideal monoid. -/
theorem isRelPrime_of_absNorm_coprime {I J : Ideal S}
    (h : (Ideal.absNorm I).Coprime (Ideal.absNorm J)) :
    IsRelPrime I J := by
  intro D hDI hDJ
  have hnormDI : Ideal.absNorm D ∣ Ideal.absNorm I := map_dvd Ideal.absNorm hDI
  have hnormDJ : Ideal.absNorm D ∣ Ideal.absNorm J := map_dvd Ideal.absNorm hDJ
  have hnormD : Ideal.absNorm D = 1 :=
    Nat.eq_one_of_dvd_coprimes h hnormDI hnormDJ
  rw [Ideal.isUnit_iff]
  exact Ideal.absNorm_eq_one_iff.mp hnormD

omit [CharZero S] in
/-- Split an ideal of norm `m * n` into factors of norms `m` and `n` when
`m` and `n` are coprime. -/
theorem exists_mul_of_absNorm_eq_mul (I : Ideal S) :
    ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n →
      Ideal.absNorm I = m * n →
      ∃ A B : Ideal S,
        Ideal.absNorm A = m ∧ Ideal.absNorm B = n ∧ A * B = I := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
      intro m n hm hn _ hnorm
      exfalso
      exact (Nat.mul_ne_zero hm hn) (by simpa using hnorm.symm)
  | h₂ I hIunit =>
      intro m n _ _ _ hnorm
      have hItop : I = ⊤ := Ideal.isUnit_iff.mp hIunit
      subst I
      have hone : 1 = m * n := by simpa using hnorm
      obtain ⟨hm, hn⟩ := mul_eq_one.mp hone.symm
      subst m
      subst n
      exact ⟨⊤, ⊤, by simp⟩
  | h₃ J P hJ hP IH =>
      intro m n hm hn hcop hnorm
      have hPmax : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
      letI : P.IsMaximal := hPmax
      obtain ⟨q, f, hf, -, hq, hnormP⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
      have hnormProd : Ideal.absNorm P * Ideal.absNorm J = m * n := by
        simpa only [map_mul] using hnorm
      have hnormPdvd : Ideal.absNorm P ∣ m * n := ⟨Ideal.absNorm J, hnormProd.symm⟩
      have hqdvd : q ∣ m * n := by
        exact (dvd_pow_self q hf.ne').trans (hnormP ▸ hnormPdvd)
      rcases (hq.dvd_mul.mp hqdvd) with hqm | hqn
      · have hqcopn : q.Coprime n := hcop.coprime_dvd_left hqm
        have hPcopn : (Ideal.absNorm P).Coprime n := by
          rw [hnormP]
          exact hqcopn.pow_left f
        have hPdvdm : Ideal.absNorm P ∣ m :=
          hPcopn.dvd_of_dvd_mul_right hnormPdvd
        have hPpos : 0 < Ideal.absNorm P := by
          rw [hnormP]
          exact pow_pos hq.pos f
        have hmdivpos : 0 < m / Ideal.absNorm P :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hPdvdm) hPpos
        have hcop' : (m / Ideal.absNorm P).Coprime n :=
          hcop.coprime_dvd_left (Nat.div_dvd_of_dvd hPdvdm)
        have hnormJ : Ideal.absNorm J = (m / Ideal.absNorm P) * n := by
          have hmreconstruct : Ideal.absNorm P * (m / Ideal.absNorm P) = m :=
            Nat.mul_div_cancel' hPdvdm
          apply Nat.eq_of_mul_eq_mul_left hPpos
          calc
            Ideal.absNorm P * Ideal.absNorm J = m * n := hnormProd
            _ = (Ideal.absNorm P * (m / Ideal.absNorm P)) * n := by
              rw [hmreconstruct]
            _ = Ideal.absNorm P * ((m / Ideal.absNorm P) * n) := by
              rw [mul_assoc]
        obtain ⟨A, B, hnormA, hnormB, hAB⟩ :=
          IH hmdivpos.ne' hn hcop' hnormJ
        refine ⟨P * A, B, ?_, hnormB, ?_⟩
        · rw [map_mul, hnormA, Nat.mul_div_cancel' hPdvdm]
        · rw [mul_assoc, hAB]
      · have hqcopm : q.Coprime m := hcop.symm.coprime_dvd_left hqn
        have hPcopm : (Ideal.absNorm P).Coprime m := by
          rw [hnormP]
          exact hqcopm.pow_left f
        have hPdvdn : Ideal.absNorm P ∣ n :=
          hPcopm.dvd_of_dvd_mul_left hnormPdvd
        have hPpos : 0 < Ideal.absNorm P := by
          rw [hnormP]
          exact pow_pos hq.pos f
        have hndivpos : 0 < n / Ideal.absNorm P :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hPdvdn) hPpos
        have hcop' : m.Coprime (n / Ideal.absNorm P) :=
          hcop.coprime_dvd_right (Nat.div_dvd_of_dvd hPdvdn)
        have hnormJ : Ideal.absNorm J = m * (n / Ideal.absNorm P) := by
          have hnreconstruct : Ideal.absNorm P * (n / Ideal.absNorm P) = n :=
            Nat.mul_div_cancel' hPdvdn
          apply Nat.eq_of_mul_eq_mul_left hPpos
          calc
            Ideal.absNorm P * Ideal.absNorm J = m * n := hnormProd
            _ = m * (Ideal.absNorm P * (n / Ideal.absNorm P)) := by
              rw [hnreconstruct]
            _ = Ideal.absNorm P * (m * (n / Ideal.absNorm P)) := by
              ac_rfl
        obtain ⟨A, B, hnormA, hnormB, hAB⟩ :=
          IH hm hndivpos.ne' hcop' hnormJ
        refine ⟨A, P * B, hnormA, ?_, ?_⟩
        · rw [map_mul, hnormB, Nat.mul_div_cancel' hPdvdn]
        · rw [mul_left_comm, hAB]

/-- The finite fiber of the absolute norm over `n`. -/
abbrev NormFiber (S : Type*) [CommRing S] [Nontrivial S] [IsDedekindDomain S]
    [Module.Free ℤ S] (n : ℕ) :=
  {I : Ideal S // Ideal.absNorm I = n}

/-- Multiplication of ideals sends the product of the norm fibers over `m`
and `n` to the norm fiber over `m * n`. -/
def normFiberMul (m n : ℕ) :
    NormFiber S m × NormFiber S n → NormFiber S (m * n) :=
  fun I ↦ ⟨I.1.1 * I.2.1, by rw [map_mul, I.1.2, I.2.2]⟩

omit [Module.Finite ℤ S] [CharZero S] in
theorem normFiberMul_injective {m n : ℕ} (hm : m ≠ 0) (hcop : m.Coprime n) :
    Function.Injective (normFiberMul (S := S) m n) := by
  rintro ⟨A, B⟩ ⟨C, D⟩ h
  have hprod : A.1 * B.1 = C.1 * D.1 := congrArg Subtype.val h
  have hrelAD : IsRelPrime A.1 D.1 := by
    apply isRelPrime_of_absNorm_coprime
    simpa [A.2, D.2] using hcop
  have hrelCB : IsRelPrime C.1 B.1 := by
    apply isRelPrime_of_absNorm_coprime
    simpa [C.2, B.2] using hcop
  have hAC : A.1 ∣ C.1 :=
    hrelAD.dvd_of_dvd_mul_right (hprod ▸ dvd_mul_right A.1 B.1)
  have hCA : C.1 ∣ A.1 :=
    hrelCB.dvd_of_dvd_mul_right (hprod.symm ▸ dvd_mul_right C.1 D.1)
  have hAeqC : A.1 = C.1 :=
    associated_iff_eq.mp (associated_of_dvd_dvd hAC hCA)
  apply Prod.ext
  · exact Subtype.ext hAeqC
  · apply Subtype.ext
    have hAne : A.1 ≠ 0 := by
      intro hA
      have : m = 0 := by simpa [hA] using A.2.symm
      exact hm this
    exact mul_left_cancel₀ hAne (hAeqC ▸ hprod)

omit [CharZero S] in
theorem normFiberMul_surjective {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : m.Coprime n) :
    Function.Surjective (normFiberMul (S := S) m n) := by
  intro I
  obtain ⟨A, B, hA, hB, hAB⟩ :=
    exists_mul_of_absNorm_eq_mul I.1 hm hn hcop I.2
  refine ⟨⟨⟨A, hA⟩, ⟨B, hB⟩⟩, ?_⟩
  exact Subtype.ext hAB

/-- For coprime nonzero `m,n`, multiplication is an equivalence between
pairs of ideals of norms `m,n` and ideals of norm `m*n`. -/
def normFiberMulEquiv {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : m.Coprime n) :
    NormFiber S m × NormFiber S n ≃ NormFiber S (m * n) :=
  Equiv.ofBijective (normFiberMul (S := S) m n)
    ⟨normFiberMul_injective hm hcop, normFiberMul_surjective hm hn hcop⟩

/-- The number of ideals of a prescribed norm is multiplicative. -/
theorem natCard_normFiber_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : m.Coprime n) :
    Nat.card (NormFiber S (m * n)) =
      Nat.card (NormFiber S m) * Nat.card (NormFiber S n) := by
  letI : Fintype (NormFiber S m) := (Ideal.finite_setOf_absNorm_eq m).fintype
  letI : Fintype (NormFiber S n) := (Ideal.finite_setOf_absNorm_eq n).fintype
  letI : Fintype (NormFiber S (m * n)) :=
    (Ideal.finite_setOf_absNorm_eq (m * n)).fintype
  simpa using (Nat.card_congr (normFiberMulEquiv (S := S) hm hn hcop)).symm

/-- The arithmetic function counting ideals by absolute norm. -/
def idealCountArithmetic : ArithmeticFunction ℂ :=
  toArithmeticFunction (fun n ↦ (Nat.card (NormFiber S n) : ℂ))

/-- Ideal counting by absolute norm is a multiplicative arithmetic function. -/
theorem idealCountArithmetic_isMultiplicative :
    (idealCountArithmetic (S := S)).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · change (Nat.card (NormFiber S 1) : ℂ) = 1
    norm_cast
    refine Nat.card_eq_one_iff_unique.mpr ⟨?_, ⟨⟨⊤, Ideal.absNorm_top⟩⟩⟩
    constructor
    intro I J
    apply Subtype.ext
    rw [Ideal.absNorm_eq_one_iff.mp I.2, Ideal.absNorm_eq_one_iff.mp J.2]
  · intro m n hm hn hcop
    change (if m * n = 0 then 0 else (Nat.card (NormFiber S (m * n)) : ℂ)) =
      (if m = 0 then 0 else (Nat.card (NormFiber S m) : ℂ)) *
        (if n = 0 then 0 else (Nat.card (NormFiber S n) : ℂ))
    rw [if_neg (Nat.mul_ne_zero hm hn), if_neg hm, if_neg hn]
    exact_mod_cast natCard_normFiber_mul (S := S) hm hn hcop

/-- Multisets consisting entirely of prime ideals. -/
abbrev PrimeFactorMultiset (S : Type*) [CommRing S] :=
  {s : Multiset (Ideal S) // ∀ P ∈ s, Prime P}

/-- Unique ideal factorization as an actual equivalence: nonzero ideals are
equivalent to finite multisets of prime ideals. -/
def nonzeroIdealEquivPrimeFactorMultiset :
    {I : Ideal S // I ≠ 0} ≃ PrimeFactorMultiset S where
  toFun I := ⟨UniqueFactorizationMonoid.normalizedFactors I.1,
    fun P hP ↦ UniqueFactorizationMonoid.prime_of_normalized_factor P hP⟩
  invFun s := ⟨s.1.prod, s.1.prod_ne_zero_of_prime s.2⟩
  left_inv I := by
    apply Subtype.ext
    exact Ideal.prod_normalizedFactors_eq_self I.2
  right_inv s := by
    apply Subtype.ext
    exact UniqueFactorizationMonoid.normalizedFactors_prod_of_prime s.2

omit [Module.Finite ℤ S] [CharZero S] in
/-- If every factor in a multiset of ideals has norm `q^f`, the product has
norm `q^(f * card)`. -/
theorem absNorm_multiset_prod_of_forall_eq_pow
    (s : Multiset (Ideal S)) (q f : ℕ)
    (hs : ∀ P ∈ s, Ideal.absNorm P = q ^ f) :
    Ideal.absNorm s.prod = q ^ (f * s.card) := by
  rw [map_multiset_prod]
  calc
    (s.map Ideal.absNorm).prod = (s.map fun _ ↦ q ^ f).prod := by
      congr 1
      exact Multiset.map_congr rfl hs
    _ = (q ^ f) ^ s.card := by simp
    _ = q ^ (f * s.card) := by rw [pow_mul]

end

end Fermat.Irregular.IdealCount
