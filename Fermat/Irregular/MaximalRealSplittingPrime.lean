import Fermat.Irregular.CyclotomicZetaCoefficientsPrime
import Fermat.Irregular.CyclotomicDiscriminantPrime
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

/-!
# Splitting in maximal real prime cyclotomic fields

For an odd prime p and every rational prime q different from p, this file
proves the local splitting law in the maximal real subfield of a pth
cyclotomic field.  The residue degree is the order of q in
(ZMod p)ˣ / {±1}, ramification is trivial, and the number and norms of the
primes above q follow.
-/

open scoped NumberField Classical Pointwise

namespace Fermat.Irregular.MaximalRealSplittingPrime

open NumberField
open Fermat.Irregular.CyclotomicCharactersPrime
open Fermat.Irregular.CyclotomicZetaCoefficientsPrime
open Fermat.Irregular.CyclotomicDiscriminantPrime
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.CircularUnitFamily

noncomputable section

set_option maxHeartbeats 1200000

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K] [IsAbelianGalois ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

local instance : IsAbelianGalois ℚ K⁺ := IsAbelianGalois.tower_bot ℚ K⁺ K
local instance : IsAbelianGalois K⁺ K := IsAbelianGalois.tower_top ℚ K⁺ K

attribute [local instance] Ideal.Quotient.field

/-- The order of an element is the order of its image modulo a subgroup,
times the size of the intersection of its cyclic subgroup with that
subgroup. -/
theorem quotient_order_mul_card_inf
    {G : Type*} [CommGroup G] [Finite G]
    (N : Subgroup G) (a : G) :
    orderOf (QuotientGroup.mk a : G ⧸ N) *
      Nat.card ↑((Subgroup.zpowers a) ⊓ N) = orderOf a := by
  let Z : Subgroup G := Subgroup.zpowers a
  let f : Z →* G ⧸ N := (QuotientGroup.mk' N).restrict Z
  have hrange : f.range =
      Subgroup.zpowers (QuotientGroup.mk a : G ⧸ N) := by
    ext y
    simp [f, Z, Subgroup.mem_zpowers_iff]
  have hker : Nat.card f.ker = Nat.card ↑(Z ⊓ N) := by
    rw [MonoidHom.ker_restrict, QuotientGroup.ker_mk']
    calc
      Nat.card (N.subgroupOf Z) =
          Nat.card ((N.subgroupOf Z).map Z.subtype) :=
        Nat.card_congr
          ((N.subgroupOf Z).equivMapOfInjective Z.subtype
            Z.subtype_injective).toEquiv
      _ = Nat.card ↑(Z ⊓ N) := by
        rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  change orderOf (QuotientGroup.mk a : G ⧸ N) *
    Nat.card ↑(Z ⊓ N) = orderOf a
  rw [← Nat.card_zpowers (QuotientGroup.mk a : G ⧸ N), ← hrange,
    ← Subgroup.index_ker f, ← hker, Subgroup.index_mul_card,
    Nat.card_zpowers]

/-- Distinct rational primes are coprime. -/
theorem prime_coprime_exponent
    (q : ℕ) [Fact (Nat.Prime q)] (hq : q ≠ p) :
    q.Coprime p := by
  exact (Fact.out : Nat.Prime q).coprime_iff_not_dvd.mpr (by
    intro hdvd
    rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hdvd with hq1 | hqp
    · exact (Fact.out : Nat.Prime q).ne_one hq1
    · exact hq hqp)

noncomputable def fullComplexConj : Gal(K/ℚ) :=
  (NumberField.IsCMField.complexConj K).restrictScalars ℚ

theorem galEquivZMod_fullComplexConj :
    IsCyclotomicExtension.Rat.galEquivZMod p K
      (fullComplexConj (K := K)) = -1 := by
  let zeta := IsCyclotomicExtension.zeta p ℚ K
  have hzeta : IsPrimitiveRoot zeta p :=
    IsCyclotomicExtension.zeta_spec p ℚ K
  apply Units.ext
  rw [← ZMod.natCast_zmod_val
      (IsCyclotomicExtension.Rat.galEquivZMod p K
        (fullComplexConj (K := K)) : ZMod p),
    ← ZMod.natCast_zmod_val ((-1 : (ZMod p)ˣ) : ZMod p),
    ZMod.natCast_eq_natCast_iff']
  have hpow :
      zeta ^ (IsCyclotomicExtension.Rat.galEquivZMod p K
          (fullComplexConj (K := K))).val.val =
        zeta ^ ((-1 : (ZMod p)ˣ) : ZMod p).val := by
    rw [← IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq p K]
    · change NumberField.IsCMField.complexConj K zeta = _
      rw [complexConj_zeta_inv hzeta]
      have hpSucc : p - 1 + 1 = p := Nat.sub_add_cancel (by
        have hpgt : 2 < p := Fact.out
        omega)
      have hval : ((-1 : (ZMod p)ˣ) : ZMod p).val = p - 1 := by
        obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := by
          exact ⟨p - 1, hpSucc.symm⟩
        exact ZMod.val_neg_one n
      rw [hval]
      apply (eq_inv_of_mul_eq_one_right ?_).symm
      rw [mul_comm, ← pow_succ, hpSucc]
      exact hzeta.pow_eq_one
    · exact hzeta.pow_eq_one
  simpa only [← hzeta.eq_orderOf] using
    (hzeta.isOfFinOrder (Nat.Prime.ne_zero
      (Fact.out : Nat.Prime p))).pow_inj_mod.mp hpow

noncomputable def maximalRealIntermediate : IntermediateField ℚ K :=
  (NumberField.maximalRealSubfield K).toIntermediateField (by
    intro x phi
    simp)

theorem galEquivZMod_map_fixingSubgroup_maximalReal :
    (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
        (maximalRealIntermediate (K := K)).fixingSubgroup =
      signSubgroup p := by
  let E : IntermediateField ℚ K :=
    maximalRealIntermediate (K := K)
  have hconj : fullComplexConj (K := K) ∈
      E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change NumberField.IsCMField.complexConj K x = x
    exact (NumberField.IsCMField.complexConj_eq_self_iff K x).mpr hx
  have hle : signSubgroup p ≤
      (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
        E.fixingSubgroup := by
    rw [signSubgroup, Subgroup.zpowers_le]
    exact ⟨fullComplexConj (K := K), hconj,
      galEquivZMod_fullComplexConj⟩
  have hcard_sign : Nat.card (signSubgroup p) = 2 := by
    rw [Nat.card_eq_fintype_card, card_signSubgroup (p := p)]
  have hcard_fix : Nat.card E.fixingSubgroup = 2 := by
    rw [Nat.card_congr E.fixingSubgroupEquiv.toEquiv,
      IsGalois.card_aut_eq_finrank]
    change Module.finrank K⁺ K = 2
    exact Algebra.IsQuadraticExtension.finrank_eq_two K⁺ K
  have heq := Subgroup.eq_of_le_of_card_ge hle (by
    rw [Subgroup.card_mapSubgroup, hcard_fix, hcard_sign])
  simpa [E] using heq.symm

noncomputable def restrictScalarsHom : Gal(K/K⁺) →* Gal(K/ℚ) where
  toFun τ := τ.restrictScalars ℚ
  map_one' := rfl
  map_mul' _ _ := rfl

omit [IsCyclotomicExtension {p} ℚ K] in
theorem range_restrictScalarsHom :
    (restrictScalarsHom (K := K)).range =
      (maximalRealIntermediate (K := K)).fixingSubgroup := by
  let E : IntermediateField ℚ K :=
    maximalRealIntermediate (K := K)
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact τ.commutes ⟨x, hx⟩
  · intro hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    let τ : Gal(K/K⁺) :=
      { σ.toRingEquiv with
        commutes' := fun x ↦ hσ x x.prop }
    exact ⟨τ, rfl⟩

omit [IsCyclotomicExtension {p} ℚ K] in
theorem restrictScalars_smul_ideal_eq
    (τ : Gal(K/K⁺)) (P : Ideal (NumberField.RingOfIntegers K)) :
    (τ.restrictScalars ℚ) • P = τ • P := by
  rfl

omit [IsCyclotomicExtension {p} ℚ K] in
theorem map_stabilizer_restrictScalarsHom
    (P : Ideal (NumberField.RingOfIntegers K)) :
    (MulAction.stabilizer Gal(K/K⁺) P).map
        (restrictScalarsHom (K := K)) =
      MulAction.stabilizer Gal(K/ℚ) P ⊓
        (maximalRealIntermediate (K := K)).fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    constructor
    · change τ • P = P at hτ
      change (τ.restrictScalars ℚ) • P = P
      simpa only [restrictScalars_smul_ideal_eq] using hτ
    · rw [← range_restrictScalarsHom]
      exact ⟨τ, rfl⟩
  · rintro ⟨hσ, hσFix⟩
    rw [← range_restrictScalarsHom] at hσFix
    obtain ⟨τ, hτ⟩ := hσFix
    refine ⟨τ, ?_, hτ⟩
    change τ.restrictScalars ℚ = σ at hτ
    change σ • P = P at hσ
    change τ • P = P
    rw [← restrictScalars_smul_ideal_eq, hτ]
    exact hσ

theorem galEquivZMod_map_relative_stabilizer
    (q : ℕ) [Fact (Nat.Prime q)] (hq : q ≠ p)
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))] :
    (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
        ((MulAction.stabilizer Gal(K/K⁺) P).map
          (restrictScalarsHom (K := K))) =
      Subgroup.zpowers
        (ZMod.unitOfCoprime q (prime_coprime_exponent q hq)) ⊓
          signSubgroup p := by
  let hcop : q.Coprime p := prime_coprime_exponent q hq
  rw [map_stabilizer_restrictScalarsHom]
  change ((MulAction.stabilizer Gal(K/ℚ) P ⊓
      (maximalRealIntermediate (K := K)).fixingSubgroup).map
        (IsCyclotomicExtension.Rat.galEquivZMod p K).toMonoidHom) = _
  rw [Subgroup.map_inf]
  have hfull :=
    IsCyclotomicExtension.Rat.galEquivZMod_stabilizer p K q P hcop
  have hfix :=
    galEquivZMod_map_fixingSubgroup_maximalReal (p := p) (K := K)
  rw [MulEquiv.coe_mapSubgroup] at hfull hfix
  simpa only [hcop] using
    congrArg₂ (fun A B : Subgroup (ZMod p)ˣ ↦ A ⊓ B) hfull hfix
  exact (IsCyclotomicExtension.Rat.galEquivZMod p K).injective

theorem card_relative_stabilizer
    (q : ℕ) [Fact (Nat.Prime q)] (hq : q ≠ p)
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))] :
    Nat.card (MulAction.stabilizer Gal(K/K⁺) P) =
      Nat.card ↑(Subgroup.zpowers
        (ZMod.unitOfCoprime q (prime_coprime_exponent q hq)) ⊓
          signSubgroup p) := by
  let S : Subgroup Gal(K/K⁺) :=
    MulAction.stabilizer Gal(K/K⁺) P
  have hi : Function.Injective
      (restrictScalarsHom (K := K)) := by
    intro σ τ h
    exact AlgEquiv.restrictScalars_injective ℚ h
  calc
    Nat.card S =
        Nat.card (S.map (restrictScalarsHom (K := K))) :=
      (Subgroup.card_map_of_injective hi).symm
    _ = Nat.card
        ((IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
          (S.map (restrictScalarsHom (K := K)))) :=
      (Subgroup.card_mapSubgroup _ _).symm
    _ = _ := congrArg
      (fun H : Subgroup (ZMod p)ˣ ↦ Nat.card H)
      (galEquivZMod_map_relative_stabilizer
        (p := p) (K := K) q hq P)

theorem inertiaDegIn_maximalReal_eq_orderOf_realResidue
    (q : ℕ) [Fact (Nat.Prime q)] (hq : q ≠ p) :
    (Ideal.span ({(q : ℤ)} : Set ℤ)).inertiaDegIn
        (NumberField.RingOfIntegers K⁺) =
      orderOf (QuotientGroup.mk
        (ZMod.unitOfCoprime q (prime_coprime_exponent q hq)) :
          RealResidueGroup p) := by
  let qIdeal : Ideal ℤ := Ideal.span ({(q : ℤ)} : Set ℤ)
  have hqIdeal_ne : qIdeal ≠ ⊥ := by
    simpa [qIdeal] using (Fact.out : Nat.Prime q).ne_zero
  have hnot : ¬ q ∣ p := by
    intro hdvd
    rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hdvd with hq1 | hqp
    · exact (Fact.out : Nat.Prime q).ne_one hq1
    · exact hq hqp
  let hcop : q.Coprime p := prime_coprime_exponent q hq
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime q hcop
  obtain ⟨Pplus⟩ := qIdeal.nonempty_primesOver
    (S := NumberField.RingOfIntegers K⁺)
  letI : Pplus.1.IsPrime := Pplus.property.1
  letI : Pplus.1.LiesOver qIdeal := Pplus.property.2
  have hPplus_ne : Pplus.1 ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hqIdeal_ne Pplus.1
  letI : Pplus.1.IsMaximal :=
    (show Pplus.1.IsPrime from inferInstance).isMaximal hPplus_ne
  obtain ⟨P⟩ := Pplus.1.nonempty_primesOver
    (S := NumberField.RingOfIntegers K)
  letI : P.1.IsPrime := P.property.1
  letI : P.1.LiesOver Pplus.1 := P.property.2
  letI : P.1.LiesOver qIdeal :=
    Ideal.LiesOver.trans P.1 Pplus.1 qIdeal
  have hP_ne : P.1 ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hPplus_ne P.1
  letI : P.1.IsMaximal :=
    (show P.1.IsPrime from inferInstance).isMaximal hP_ne
  have hfullRam :
      qIdeal.ramificationIdxIn (NumberField.RingOfIntegers K) = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd
      q (m := p) K hnot
  have hramTower := Ideal.ramificationIdxIn_mul_ramificationIdxIn'
    (p := qIdeal) Pplus.1 Gal(K⁺/ℚ)
      (NumberField.RingOfIntegers K) Gal(K/ℚ) Gal(K/K⁺)
  rw [hfullRam] at hramTower
  have hrelRam :
      Pplus.1.ramificationIdxIn (NumberField.RingOfIntegers K) = 1 :=
    Nat.eq_one_of_mul_eq_one_left hramTower
  have hstab := Ideal.card_stabilizer_eq (G := Gal(K/K⁺))
    Pplus.1 hPplus_ne P.1
  rw [hrelRam, one_mul] at hstab
  have hcard :=
    card_relative_stabilizer (p := p) (K := K) q hq P.1
  have hrelInertiaCard :
      Pplus.1.inertiaDegIn (NumberField.RingOfIntegers K) =
        Nat.card ↑(Subgroup.zpowers u ⊓ signSubgroup p) := by
    exact hstab.symm.trans hcard
  have hfullInertia :
      qIdeal.inertiaDegIn (NumberField.RingOfIntegers K) =
        orderOf (q : ZMod p) :=
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd
      q (m := p) K hnot
  have hinertiaTower := Ideal.inertiaDegIn_mul_inertiaDegIn
    qIdeal Pplus.1 Gal(K⁺/ℚ) (NumberField.RingOfIntegers K)
      Gal(K/ℚ) Gal(K/K⁺)
  rw [hfullInertia] at hinertiaTower
  have hunitOrder : orderOf u = orderOf (q : ZMod p) := by
    simpa [u, Units.coeHom_apply, ZMod.coe_unitOfCoprime] using
      (orderOf_injective (Units.coeHom (ZMod p))
        Units.coeHom_injective u).symm
  have hquot := quotient_order_mul_card_inf (signSubgroup p) u
  have hquot' :
      orderOf (QuotientGroup.mk u : RealResidueGroup p) *
          Pplus.1.inertiaDegIn (NumberField.RingOfIntegers K) =
        orderOf (q : ZMod p) := by
    rw [hrelInertiaCard]
    exact hquot.trans hunitOrder
  have hrelPos :
      0 < Pplus.1.inertiaDegIn (NumberField.RingOfIntegers K) := by
    rw [hrelInertiaCard]
    exact Nat.card_pos
  apply Nat.mul_right_cancel hrelPos
  exact hinertiaTower.trans hquot'.symm

theorem ramificationIdxIn_maximalReal_eq_one
    (q : ℕ) [Fact (Nat.Prime q)] (hq : q ≠ p) :
    (Ideal.span ({(q : ℤ)} : Set ℤ)).ramificationIdxIn
      (NumberField.RingOfIntegers K⁺) = 1 := by
  let qIdeal : Ideal ℤ := Ideal.span ({(q : ℤ)} : Set ℤ)
  have hqIdeal_ne : qIdeal ≠ ⊥ := by
    simpa [qIdeal] using (Fact.out : Nat.Prime q).ne_zero
  obtain ⟨P⟩ := qIdeal.nonempty_primesOver
    (S := NumberField.RingOfIntegers K⁺)
  have hfull :
      qIdeal.ramificationIdxIn (NumberField.RingOfIntegers K) = 1 := by
    apply IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd
      q (m := p) K
    intro hdvd
    rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hdvd with hq1 | hqp
    · exact (Fact.out : Nat.Prime q).ne_one hq1
    · exact hq hqp
  have htower := Ideal.ramificationIdxIn_mul_ramificationIdxIn'
    (p := qIdeal) P.1 Gal(K⁺/ℚ)
      (NumberField.RingOfIntegers K) Gal(K/ℚ) Gal(K/K⁺)
  rw [hfull] at htower
  have hplus := Nat.eq_one_of_mul_eq_one_right htower
  simpa [qIdeal] using hplus

theorem inertiaDegIn_maximalReal_eq_orderOf_realResidueOfCoprime
    (q : ℕ) [Fact (Nat.Prime q)] (hcop : q.Coprime p) :
    (Ideal.span ({(q : ℤ)} : Set ℤ)).inertiaDegIn
        (NumberField.RingOfIntegers K⁺) =
      orderOf (realResidueOfCoprime q hcop) := by
  have hq : q ≠ p := by
    intro h
    subst q
    exact (Fact.out : Nat.Prime p).ne_one
      (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl p) (dvd_refl p))
  simpa [realResidueOfCoprime] using
    inertiaDegIn_maximalReal_eq_orderOf_realResidue
      (p := p) (K := K) q hq

theorem ramificationIdxIn_maximalReal_eq_one_of_coprime
    (q : ℕ) [Fact (Nat.Prime q)] (hcop : q.Coprime p) :
    (Ideal.span ({(q : ℤ)} : Set ℤ)).ramificationIdxIn
      (NumberField.RingOfIntegers K⁺) = 1 := by
  apply ramificationIdxIn_maximalReal_eq_one (p := p) (K := K) q
  intro h
  subst q
  exact (Fact.out : Nat.Prime p).ne_one
    (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl p) (dvd_refl p))

theorem finrank_maximalReal :
    Module.finrank ℚ K⁺ = (p - 1) / 2 := by
  have htower := Module.finrank_mul_finrank ℚ K⁺ K
  rw [Algebra.IsQuadraticExtension.finrank_eq_two K⁺ K,
    IsCyclotomicExtension.Rat.finrank p K,
    Nat.totient_prime (Fact.out : Nat.Prime p)] at htower
  exact Nat.eq_div_of_mul_eq_right (by norm_num) (by
    simpa [mul_comm] using htower)

theorem ncard_primesOver_maximalReal
    (q : ℕ) [Fact (Nat.Prime q)] (hcop : q.Coprime p) :
    ((Ideal.span ({(q : ℤ)} : Set ℤ)).primesOver
        (NumberField.RingOfIntegers K⁺)).ncard =
      ((p - 1) / 2) / orderOf (realResidueOfCoprime q hcop) := by
  let qIdeal : Ideal ℤ := Ideal.span ({(q : ℤ)} : Set ℤ)
  have hqIdeal_ne : qIdeal ≠ ⊥ := by
    simpa [qIdeal] using (Fact.out : Nat.Prime q).ne_zero
  letI : qIdeal.IsMaximal := by
    apply Ideal.IsPrime.isMaximal
    · exact (Ideal.span_singleton_prime (by
        exact_mod_cast (Fact.out : Nat.Prime q).ne_zero)).2
          (Nat.prime_iff_prime_int.mp Fact.out)
    · exact hqIdeal_ne
  have hfund :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      hqIdeal_ne (NumberField.RingOfIntegers K⁺) Gal(K⁺/ℚ)
  rw [ramificationIdxIn_maximalReal_eq_one_of_coprime
      (p := p) (K := K) q hcop,
    inertiaDegIn_maximalReal_eq_orderOf_realResidueOfCoprime
      (p := p) (K := K) q hcop,
    one_mul, IsGalois.card_aut_eq_finrank,
    finrank_maximalReal (p := p) (K := K)] at hfund
  exact Nat.eq_div_of_mul_eq_right (orderOf_pos _).ne' (by
    simpa [qIdeal, mul_comm] using hfund)

theorem absNorm_primeOver_maximalReal
    (q : ℕ) [Fact (Nat.Prime q)] (hcop : q.Coprime p)
    (P : Ideal (NumberField.RingOfIntegers K⁺)) [P.IsPrime]
    [P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))] :
    Ideal.absNorm P =
      q ^ orderOf (realResidueOfCoprime q hcop) := by
  rw [Ideal.absNorm_eq_pow_inertiaDeg' P (Fact.out : Nat.Prime q),
    ← Ideal.inertiaDegIn_eq_inertiaDeg
      (Ideal.span ({(q : ℤ)} : Set ℤ)) P Gal(K⁺/ℚ),
    inertiaDegIn_maximalReal_eq_orderOf_realResidueOfCoprime
      (p := p) (K := K) q hcop]

end

end Fermat.Irregular.MaximalRealSplittingPrime
