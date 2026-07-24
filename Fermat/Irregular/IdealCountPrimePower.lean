import Fermat.Irregular.IdealCount
import Mathlib.Data.Sym.Card

open scoped Classical

namespace Fermat.Irregular.IdealCount

noncomputable section

variable {S : Type*} [CommRing S] [Nontrivial S] [IsDedekindDomain S]
  [Module.Free ℤ S] [Module.Finite ℤ S] [CharZero S]

/-- Prime ideals having a specified absolute norm. -/
abbrev PrimeIdealOfNorm (S : Type*) [CommRing S] [Nontrivial S]
    [IsDedekindDomain S] [Module.Free ℤ S] (N : ℕ) :=
  {P : Ideal S // Prime P ∧ Ideal.absNorm P = N}

/-- Multiply an unordered `r`-tuple of prime ideals of norm `q^f`. -/
def symPrimeIdealOfNormProd (q f r k : ℕ) (hfr : f * r = k) :
    Sym (PrimeIdealOfNorm S (q ^ f)) r → NormFiber S (q ^ k) :=
  fun s ↦ ⟨(s.1.map (fun P ↦ P.1)).prod, by
    rw [absNorm_multiset_prod_of_forall_eq_pow]
    · rw [Multiset.card_map, s.2, hfr]
    · intro P hP
      obtain ⟨Q, -, rfl⟩ := Multiset.mem_map.mp hP
      exact Q.2.2⟩

omit [Module.Finite ℤ S] [CharZero S] in
theorem symPrimeIdealOfNormProd_injective
    (q f r k : ℕ) (hfr : f * r = k) :
    Function.Injective (symPrimeIdealOfNormProd (S := S) q f r k hfr) := by
  intro s t hst
  apply Subtype.ext
  have hprod : (s.1.map (fun P ↦ P.1)).prod =
      (t.1.map (fun P ↦ P.1)).prod := congrArg Subtype.val hst
  have hsprime : ∀ P ∈ s.1.map (fun P ↦ P.1), Prime P := by
    intro P hP
    obtain ⟨Q, -, rfl⟩ := Multiset.mem_map.mp hP
    exact Q.2.1
  have htprime : ∀ P ∈ t.1.map (fun P ↦ P.1), Prime P := by
    intro P hP
    obtain ⟨Q, -, rfl⟩ := Multiset.mem_map.mp hP
    exact Q.2.1
  have hmaps : s.1.map (fun P ↦ P.1) = t.1.map (fun P ↦ P.1) := by
    rw [← UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hsprime,
      ← UniqueFactorizationMonoid.normalizedFactors_prod_of_prime htprime, hprod]
  exact Multiset.map_injective Subtype.val_injective hmaps

omit [CharZero S] in
theorem symPrimeIdealOfNormProd_surjective
    {q f r k : ℕ} (hq : q.Prime) (hf : 0 < f) (hfr : f * r = k)
    (hall : ∀ P : Ideal S, Prime P → Ideal.absNorm P ∣ q ^ k →
      Ideal.absNorm P = q ^ f) :
    Function.Surjective (symPrimeIdealOfNormProd (S := S) q f r k hfr) := by
  intro I
  have hInorm_ne : Ideal.absNorm I.1 ≠ 0 := by
    rw [I.2]
    exact pow_ne_zero k hq.ne_zero
  have hIne : I.1 ≠ 0 := by
    intro hI
    exact hInorm_ne (Ideal.absNorm_eq_zero_iff.mpr hI)
  let factors := UniqueFactorizationMonoid.normalizedFactors I.1
  have hfactorAllowed : ∀ P ∈ factors,
      Prime P ∧ Ideal.absNorm P = q ^ f := by
    intro P hP
    have hPprime := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    refine ⟨hPprime, hall P hPprime ?_⟩
    rw [← I.2]
    exact map_dvd Ideal.absNorm
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
  let lifted : Multiset (PrimeIdealOfNorm S (q ^ f)) :=
    factors.pmap (fun P hP ↦ ⟨P, hP⟩) hfactorAllowed
  have hfactorsNorm : Ideal.absNorm factors.prod = q ^ (f * factors.card) :=
    absNorm_multiset_prod_of_forall_eq_pow factors q f
      (fun P hP ↦ (hfactorAllowed P hP).2)
  have hexp : f * factors.card = k := by
    apply Nat.pow_right_injective hq.two_le
    calc
      q ^ (f * factors.card) = Ideal.absNorm factors.prod := hfactorsNorm.symm
      _ = Ideal.absNorm I.1 := by rw [Ideal.prod_normalizedFactors_eq_self hIne]
      _ = q ^ k := I.2
  have hliftedCard : lifted.card = r := by
    calc
      lifted.card = factors.card := by simp only [lifted, Multiset.card_pmap]
      _ = r := Nat.eq_of_mul_eq_mul_left hf (hexp.trans hfr.symm)
  refine ⟨⟨lifted, hliftedCard⟩, ?_⟩
  apply Subtype.ext
  change (lifted.map (fun P ↦ P.1)).prod = I.1
  have hmap : lifted.map (fun P ↦ P.1) = factors := by
    simp only [lifted, Multiset.map_pmap]
    simpa using Multiset.pmap_eq_map
      (fun P : Ideal S ↦ Prime P ∧ Ideal.absNorm P = q ^ f) id factors hfactorAllowed
  rw [hmap, Ideal.prod_normalizedFactors_eq_self hIne]

/-- If all prime ideal factors of norm `q^k` have the common norm `q^f`,
then ideals of norm `q^k` are counted by a multichoose coefficient. -/
theorem natCard_normFiber_primePow_eq_multichoose
    {q f r k : ℕ} (hq : q.Prime) (hf : 0 < f) (hfr : f * r = k)
    (hall : ∀ P : Ideal S, Prime P → Ideal.absNorm P ∣ q ^ k →
      Ideal.absNorm P = q ^ f) :
    Nat.card (NormFiber S (q ^ k)) =
      Nat.multichoose (Nat.card (PrimeIdealOfNorm S (q ^ f))) r := by
  letI : Fintype (PrimeIdealOfNorm S (q ^ f)) :=
    ((Ideal.finite_setOf_absNorm_eq (q ^ f)).subset
      (fun P hP ↦ hP.2)).fintype
  letI : Fintype (NormFiber S (q ^ k)) :=
    (Ideal.finite_setOf_absNorm_eq (q ^ k)).fintype
  rw [show Nat.card (PrimeIdealOfNorm S (q ^ f)) =
    Fintype.card (PrimeIdealOfNorm S (q ^ f)) from Nat.card_eq_fintype_card]
  rw [← Sym.card_sym_eq_multichoose, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Equiv.ofBijective
    (symPrimeIdealOfNormProd (S := S) q f r k hfr)
    ⟨symPrimeIdealOfNormProd_injective q f r k hfr,
      symPrimeIdealOfNormProd_surjective hq hf hfr hall⟩)).symm

end

end Fermat.Irregular.IdealCount
