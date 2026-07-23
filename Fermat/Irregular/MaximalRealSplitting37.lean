import Fermat.Irregular.CyclotomicZetaCoefficients37
import Fermat.Irregular.CyclotomicDiscriminantPrime
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

/-!
# Splitting in the maximal real 37th cyclotomic field

For every rational prime `q` coprime to `37`, this file proves the local splitting law in the
maximal real subfield `K⁺` of a 37th cyclotomic field.  Its residue degree is the order of the
Frobenius class in `(ZMod 37)ˣ / {±1}`, its ramification index is one, and consequently the
number of primes above `q` is `18 / f`.  A final corollary gives the common absolute norm of
all primes above `q`.

The key group-theoretic step identifies the relative decomposition group with the intersection
of the full decomposition group and complex conjugation.  Passing through the cyclotomic
Galois equivalence turns that intersection into `<q> ∩ {±1}`.  The order formula for a cyclic
subgroup under a quotient then gives exactly the order of `q` modulo sign.
-/

open scoped NumberField Classical Pointwise

namespace Fermat.Irregular.MaximalRealSplitting37

open NumberField
open Fermat.Irregular.CyclotomicLogDet
open Fermat.Irregular.CyclotomicZetaCoefficients37
open Fermat.Irregular.CyclotomicDiscriminantPrime
open Fermat.Irregular.CircularUnitIndex

noncomputable section

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

local instance : NumberField.IsCMField K := cyclotomic37_isCMField (K := K)
local instance : IsAbelianGalois ℚ K :=
  IsCyclotomicExtension.isAbelianGalois {37} ℚ K
local instance : IsAbelianGalois ℚ K⁺ := IsAbelianGalois.tower_bot ℚ K⁺ K
local instance : IsAbelianGalois K⁺ K := IsAbelianGalois.tower_top ℚ K⁺ K

attribute [local instance] Ideal.Quotient.field

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
          ((N.subgroupOf Z).equivMapOfInjective Z.subtype Z.subtype_injective).toEquiv
      _ = Nat.card ↑(Z ⊓ N) := by rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  change orderOf (QuotientGroup.mk a : G ⧸ N) * Nat.card ↑(Z ⊓ N) = orderOf a
  rw [← Nat.card_zpowers (QuotientGroup.mk a : G ⧸ N), ← hrange,
    ← Subgroup.index_ker f, ← hker, Subgroup.index_mul_card, Nat.card_zpowers]

noncomputable def fullComplexConj37 : Gal(K/ℚ) :=
  (NumberField.IsCMField.complexConj K).restrictScalars ℚ

theorem galEquivZMod_fullComplexConj37 :
    IsCyclotomicExtension.Rat.galEquivZMod 37 K (fullComplexConj37 (K := K)) = -1 := by
  let zeta := IsCyclotomicExtension.zeta 37 ℚ K
  have hzeta : IsPrimitiveRoot zeta 37 := IsCyclotomicExtension.zeta_spec 37 ℚ K
  apply Units.ext
  rw [← ZMod.natCast_zmod_val
      (IsCyclotomicExtension.Rat.galEquivZMod 37 K (fullComplexConj37 (K := K)) : ZMod 37),
    ← ZMod.natCast_zmod_val ((-1 : (ZMod 37)ˣ) : ZMod 37),
    ZMod.natCast_eq_natCast_iff']
  have hpow :
      zeta ^ (IsCyclotomicExtension.Rat.galEquivZMod 37 K
          (fullComplexConj37 (K := K))).val.val =
        zeta ^ ((-1 : (ZMod 37)ˣ) : ZMod 37).val := by
    rw [← IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq 37 K]
    · change NumberField.IsCMField.complexConj K zeta = _
      rw [complexConj_zeta_inv hzeta]
      rw [show ((-1 : (ZMod 37)ˣ) : ZMod 37).val = 36 by decide]
      apply (eq_inv_of_mul_eq_one_right ?_).symm
      rw [mul_comm, ← pow_succ]
      norm_num
      exact hzeta.pow_eq_one
    · exact hzeta.pow_eq_one
  simpa only [← hzeta.eq_orderOf] using
    (hzeta.isOfFinOrder (by norm_num)).pow_inj_mod.mp hpow

noncomputable def maximalRealIntermediate37 : IntermediateField ℚ K :=
  (NumberField.maximalRealSubfield K).toIntermediateField (by
    intro x phi
    simp)

theorem galEquivZMod_map_fixingSubgroup_maximalReal37 :
    (IsCyclotomicExtension.Rat.galEquivZMod 37 K).mapSubgroup
        (maximalRealIntermediate37 (K := K)).fixingSubgroup =
      signSubgroup37 := by
  let E : IntermediateField ℚ K := maximalRealIntermediate37 (K := K)
  have hconj : fullComplexConj37 (K := K) ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change NumberField.IsCMField.complexConj K x = x
    exact (NumberField.IsCMField.complexConj_eq_self_iff K x).mpr hx
  have hle : signSubgroup37 ≤
      (IsCyclotomicExtension.Rat.galEquivZMod 37 K).mapSubgroup E.fixingSubgroup := by
    rw [signSubgroup37, Subgroup.zpowers_le]
    exact ⟨fullComplexConj37 (K := K), hconj, galEquivZMod_fullComplexConj37⟩
  have hcard_sign : Nat.card signSubgroup37 = 2 := by
    rw [signSubgroup37, Nat.card_zpowers]
    apply orderOf_eq_prime
    · norm_num
    · intro h
      have hval := congrArg Units.val h
      exact (by decide : (-1 : ZMod 37) ≠ 1) hval
  have hcard_fix : Nat.card E.fixingSubgroup = 2 := by
    rw [Nat.card_congr E.fixingSubgroupEquiv.toEquiv,
      IsGalois.card_aut_eq_finrank]
    change Module.finrank K⁺ K = 2
    exact Algebra.IsQuadraticExtension.finrank_eq_two K⁺ K
  have heq := Subgroup.eq_of_le_of_card_ge hle (by
    rw [Subgroup.card_mapSubgroup, hcard_fix, hcard_sign])
  simpa [E] using heq.symm

noncomputable def restrictScalarsHom37 : Gal(K/K⁺) →* Gal(K/ℚ) where
  toFun tau := tau.restrictScalars ℚ
  map_one' := rfl
  map_mul' _ _ := rfl

omit [IsCyclotomicExtension {37} ℚ K] in
theorem range_restrictScalarsHom37 :
    (restrictScalarsHom37 (K := K)).range =
      (maximalRealIntermediate37 (K := K)).fixingSubgroup := by
  let E : IntermediateField ℚ K := maximalRealIntermediate37 (K := K)
  ext sigma
  constructor
  · rintro ⟨tau, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact tau.commutes ⟨x, hx⟩
  · intro hsigma
    rw [IntermediateField.mem_fixingSubgroup_iff] at hsigma
    let tau : Gal(K/K⁺) :=
      { sigma.toRingEquiv with
        commutes' := fun x ↦ hsigma x x.prop }
    exact ⟨tau, rfl⟩

omit [IsCyclotomicExtension {37} ℚ K] in
theorem restrictScalars_smul_ideal_eq
    (tau : Gal(K/K⁺)) (P : Ideal (NumberField.RingOfIntegers K)) :
    (tau.restrictScalars ℚ) • P = tau • P := by
  rfl

omit [IsCyclotomicExtension {37} ℚ K] in
theorem map_stabilizer_restrictScalarsHom37
    (P : Ideal (NumberField.RingOfIntegers K)) :
    (MulAction.stabilizer Gal(K/K⁺) P).map (restrictScalarsHom37 (K := K)) =
      MulAction.stabilizer Gal(K/ℚ) P ⊓
        (maximalRealIntermediate37 (K := K)).fixingSubgroup := by
  ext sigma
  constructor
  · rintro ⟨tau, htau, rfl⟩
    constructor
    · change tau • P = P at htau
      change (tau.restrictScalars ℚ) • P = P
      simpa only [restrictScalars_smul_ideal_eq] using htau
    · rw [← range_restrictScalarsHom37]
      exact ⟨tau, rfl⟩
  · rintro ⟨hsigma, hsigmaFix⟩
    rw [← range_restrictScalarsHom37] at hsigmaFix
    obtain ⟨tau, htau⟩ := hsigmaFix
    refine ⟨tau, ?_, htau⟩
    change tau.restrictScalars ℚ = sigma at htau
    change sigma • P = P at hsigma
    change tau • P = P
    rw [← restrictScalars_smul_ideal_eq, htau]
    exact hsigma

theorem galEquivZMod_map_relative_stabilizer37
    (q : ℕ) [Fact (Nat.Prime q)] (hq : q ≠ 37)
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))] :
    (IsCyclotomicExtension.Rat.galEquivZMod 37 K).mapSubgroup
        ((MulAction.stabilizer Gal(K/K⁺) P).map (restrictScalarsHom37 (K := K))) =
      Subgroup.zpowers (ZMod.unitOfCoprime q
          ((Fact.out : Nat.Prime q).coprime_iff_not_dvd.mpr (by
            intro hdvd
            rcases (Nat.dvd_prime (by decide : Nat.Prime 37)).mp hdvd with hq1 | hq37
            · exact (Fact.out : Nat.Prime q).ne_one hq1
            · exact hq hq37))) ⊓ signSubgroup37 := by
  let hcop : q.Coprime 37 :=
    (Fact.out : Nat.Prime q).coprime_iff_not_dvd.mpr (by
      intro hdvd
      rcases (Nat.dvd_prime (by decide : Nat.Prime 37)).mp hdvd with hq1 | hq37
      · exact (Fact.out : Nat.Prime q).ne_one hq1
      · exact hq hq37)
  rw [map_stabilizer_restrictScalarsHom37]
  change ((MulAction.stabilizer Gal(K/ℚ) P ⊓
      (maximalRealIntermediate37 (K := K)).fixingSubgroup).map
        (IsCyclotomicExtension.Rat.galEquivZMod 37 K).toMonoidHom) = _
  rw [Subgroup.map_inf]
  have hfull := IsCyclotomicExtension.Rat.galEquivZMod_stabilizer 37 K q P hcop
  have hfix := galEquivZMod_map_fixingSubgroup_maximalReal37 (K := K)
  rw [MulEquiv.coe_mapSubgroup] at hfull hfix
  simpa only [] using
    congrArg₂ (fun A B : Subgroup (ZMod 37)ˣ ↦ A ⊓ B) hfull hfix
  exact (IsCyclotomicExtension.Rat.galEquivZMod 37 K).injective

theorem card_relative_stabilizer37
    (q : ℕ) [Fact (Nat.Prime q)] (hq : q ≠ 37)
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))] :
    Nat.card (MulAction.stabilizer Gal(K/K⁺) P) =
      Nat.card ↑(Subgroup.zpowers (ZMod.unitOfCoprime q
          ((Fact.out : Nat.Prime q).coprime_iff_not_dvd.mpr (by
            intro hdvd
            rcases (Nat.dvd_prime (by decide : Nat.Prime 37)).mp hdvd with hq1 | hq37
            · exact (Fact.out : Nat.Prime q).ne_one hq1
            · exact hq hq37))) ⊓ signSubgroup37) := by
  let S : Subgroup Gal(K/K⁺) := MulAction.stabilizer Gal(K/K⁺) P
  have hi : Function.Injective (restrictScalarsHom37 (K := K)) := by
    intro sigma tau h
    exact AlgEquiv.restrictScalars_injective ℚ h
  calc
    Nat.card S = Nat.card (S.map (restrictScalarsHom37 (K := K))) :=
      (Subgroup.card_map_of_injective hi).symm
    _ = Nat.card ((IsCyclotomicExtension.Rat.galEquivZMod 37 K).mapSubgroup
        (S.map (restrictScalarsHom37 (K := K)))) :=
      (Subgroup.card_mapSubgroup _ _).symm
    _ = _ := congrArg (fun H : Subgroup (ZMod 37)ˣ ↦ Nat.card H)
      (galEquivZMod_map_relative_stabilizer37 (K := K) q hq P)

theorem inertiaDegIn_maximalReal_eq_orderOf_realResidue37
    (q : ℕ) [Fact (Nat.Prime q)] (hq : q ≠ 37) :
    (Ideal.span ({(q : ℤ)} : Set ℤ)).inertiaDegIn
        (NumberField.RingOfIntegers K⁺) =
      orderOf (QuotientGroup.mk (ZMod.unitOfCoprime q
        ((Fact.out : Nat.Prime q).coprime_iff_not_dvd.mpr (by
          intro hdvd
          rcases (Nat.dvd_prime (by decide : Nat.Prime 37)).mp hdvd with hq1 | hq37
          · exact (Fact.out : Nat.Prime q).ne_one hq1
          · exact hq hq37))) : RealResidueGroup37) := by
  let p : Ideal ℤ := Ideal.span ({(q : ℤ)} : Set ℤ)
  have hp_ne : p ≠ ⊥ := by simpa [p] using (Fact.out : Nat.Prime q).ne_zero
  have hnot : ¬ q ∣ 37 := by
    intro hdvd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 37)).mp hdvd with hq1 | hq37
    · exact (Fact.out : Nat.Prime q).ne_one hq1
    · exact hq hq37
  let hcop : q.Coprime 37 :=
    (Fact.out : Nat.Prime q).coprime_iff_not_dvd.mpr hnot
  let u : (ZMod 37)ˣ := ZMod.unitOfCoprime q hcop
  obtain ⟨Pplus⟩ := p.nonempty_primesOver
    (S := NumberField.RingOfIntegers K⁺)
  letI : Pplus.1.IsPrime := Pplus.property.1
  letI : Pplus.1.LiesOver p := Pplus.property.2
  have hPplus_ne : Pplus.1 ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp_ne Pplus.1
  letI : Pplus.1.IsMaximal :=
    (show Pplus.1.IsPrime from inferInstance).isMaximal hPplus_ne
  obtain ⟨P⟩ := Pplus.1.nonempty_primesOver
    (S := NumberField.RingOfIntegers K)
  letI : P.1.IsPrime := P.property.1
  letI : P.1.LiesOver Pplus.1 := P.property.2
  letI : P.1.LiesOver p := Ideal.LiesOver.trans P.1 Pplus.1 p
  have hP_ne : P.1 ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hPplus_ne P.1
  letI : P.1.IsMaximal :=
    (show P.1.IsPrime from inferInstance).isMaximal hP_ne
  have hfullRam : p.ramificationIdxIn (NumberField.RingOfIntegers K) = 1 := by
    exact IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd
      q (m := 37) K hnot
  have hramTower := Ideal.ramificationIdxIn_mul_ramificationIdxIn'
    (p := p) Pplus.1 Gal(K⁺/ℚ) (NumberField.RingOfIntegers K)
      Gal(K/ℚ) Gal(K/K⁺)
  rw [hfullRam] at hramTower
  have hrelRam : Pplus.1.ramificationIdxIn
      (NumberField.RingOfIntegers K) = 1 :=
    Nat.eq_one_of_mul_eq_one_left hramTower
  have hstab := Ideal.card_stabilizer_eq (G := Gal(K/K⁺))
    Pplus.1 hPplus_ne P.1
  rw [hrelRam, one_mul] at hstab
  have hcard := card_relative_stabilizer37 (K := K) q hq P.1
  have hrelInertiaCard :
      Pplus.1.inertiaDegIn (NumberField.RingOfIntegers K) =
        Nat.card ↑(Subgroup.zpowers u ⊓ signSubgroup37) := by
    exact hstab.symm.trans hcard
  have hfullInertia : p.inertiaDegIn (NumberField.RingOfIntegers K) =
      orderOf (q : ZMod 37) := by
    exact IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd
      q (m := 37) K hnot
  have hinertiaTower := Ideal.inertiaDegIn_mul_inertiaDegIn
    p Pplus.1 Gal(K⁺/ℚ) (NumberField.RingOfIntegers K)
      Gal(K/ℚ) Gal(K/K⁺)
  rw [hfullInertia] at hinertiaTower
  have hunitOrder : orderOf u = orderOf (q : ZMod 37) := by
    simpa [u, Units.coeHom_apply, ZMod.coe_unitOfCoprime] using
      (orderOf_injective (Units.coeHom (ZMod 37)) Units.coeHom_injective u).symm
  have hquot := quotient_order_mul_card_inf signSubgroup37 u
  have hquot' :
      orderOf (QuotientGroup.mk u : RealResidueGroup37) *
          Pplus.1.inertiaDegIn (NumberField.RingOfIntegers K) =
        orderOf (q : ZMod 37) := by
    rw [hrelInertiaCard]
    exact hquot.trans hunitOrder
  have hrelPos : 0 < Pplus.1.inertiaDegIn (NumberField.RingOfIntegers K) := by
    rw [hrelInertiaCard]
    exact Nat.card_pos
  apply Nat.mul_right_cancel hrelPos
  exact hinertiaTower.trans hquot'.symm

theorem ramificationIdxIn_maximalReal_eq_one
    (q : ℕ) [Fact (Nat.Prime q)] (hq : q ≠ 37) :
    (Ideal.span ({(q : ℤ)} : Set ℤ)).ramificationIdxIn
      (NumberField.RingOfIntegers K⁺) = 1 := by
  let p : Ideal ℤ := Ideal.span ({(q : ℤ)} : Set ℤ)
  have hp_ne : p ≠ ⊥ := by
    simpa [p] using (Fact.out : Nat.Prime q).ne_zero
  obtain ⟨P⟩ := p.nonempty_primesOver (S := NumberField.RingOfIntegers K⁺)
  have hfull : p.ramificationIdxIn (NumberField.RingOfIntegers K) = 1 := by
    apply IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd q (m := 37) K
    intro hdvd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 37)).mp hdvd with hq1 | hq37
    · exact (Fact.out : Nat.Prime q).ne_one hq1
    · exact hq hq37
  have htower := Ideal.ramificationIdxIn_mul_ramificationIdxIn'
    (p := p) P.1 Gal(K⁺/ℚ) (NumberField.RingOfIntegers K) Gal(K/ℚ) Gal(K/K⁺)
  rw [hfull] at htower
  have hplus := Nat.eq_one_of_mul_eq_one_right htower
  simpa [p] using hplus

theorem inertiaDegIn_maximalReal_eq_orderOf_realResidueOfCoprime37
    (q : ℕ) [Fact (Nat.Prime q)] (hcop : q.Coprime 37) :
    (Ideal.span ({(q : ℤ)} : Set ℤ)).inertiaDegIn
        (NumberField.RingOfIntegers K⁺) =
      orderOf (realResidueOfCoprime37 q hcop) := by
  have hq : q ≠ 37 := by
    intro h
    subst q
    norm_num at hcop
  simpa [realResidueOfCoprime37] using
    inertiaDegIn_maximalReal_eq_orderOf_realResidue37 (K := K) q hq

theorem ramificationIdxIn_maximalReal_eq_one_of_coprime
    (q : ℕ) [Fact (Nat.Prime q)] (hcop : q.Coprime 37) :
    (Ideal.span ({(q : ℤ)} : Set ℤ)).ramificationIdxIn
      (NumberField.RingOfIntegers K⁺) = 1 := by
  apply ramificationIdxIn_maximalReal_eq_one (K := K) q
  intro h
  subst q
  norm_num at hcop

theorem finrank_maximalReal37 : Module.finrank ℚ K⁺ = 18 := by
  have htower := Module.finrank_mul_finrank ℚ K⁺ K
  rw [Algebra.IsQuadraticExtension.finrank_eq_two K⁺ K,
    IsCyclotomicExtension.Rat.finrank 37 K] at htower
  rw [show Nat.totient 37 = 36 by decide] at htower
  omega

theorem ncard_primesOver_maximalReal37
    (q : ℕ) [Fact (Nat.Prime q)] (hcop : q.Coprime 37) :
    ((Ideal.span ({(q : ℤ)} : Set ℤ)).primesOver
        (NumberField.RingOfIntegers K⁺)).ncard =
      18 / orderOf (realResidueOfCoprime37 q hcop) := by
  let p : Ideal ℤ := Ideal.span ({(q : ℤ)} : Set ℤ)
  have hp_ne : p ≠ ⊥ := by simpa [p] using (Fact.out : Nat.Prime q).ne_zero
  letI : p.IsMaximal := by
    apply Ideal.IsPrime.isMaximal
    · exact (Ideal.span_singleton_prime (by
        exact_mod_cast (Fact.out : Nat.Prime q).ne_zero)).2
          (Nat.prime_iff_prime_int.mp Fact.out)
    · exact hp_ne
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    hp_ne (NumberField.RingOfIntegers K⁺) Gal(K⁺/ℚ)
  rw [ramificationIdxIn_maximalReal_eq_one_of_coprime (K := K) q hcop,
    inertiaDegIn_maximalReal_eq_orderOf_realResidueOfCoprime37 (K := K) q hcop,
    one_mul, IsGalois.card_aut_eq_finrank, finrank_maximalReal37 (K := K)] at hfund
  exact Nat.eq_div_of_mul_eq_right (orderOf_pos _).ne' (by
    simpa [p, mul_comm] using hfund)

theorem absNorm_primeOver_maximalReal37
    (q : ℕ) [Fact (Nat.Prime q)] (hcop : q.Coprime 37)
    (P : Ideal (NumberField.RingOfIntegers K⁺)) [P.IsPrime]
    [P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))] :
    Ideal.absNorm P = q ^ orderOf (realResidueOfCoprime37 q hcop) := by
  rw [Ideal.absNorm_eq_pow_inertiaDeg' P (Fact.out : Nat.Prime q),
    ← Ideal.inertiaDegIn_eq_inertiaDeg
      (Ideal.span ({(q : ℤ)} : Set ℤ)) P Gal(K⁺/ℚ),
    inertiaDegIn_maximalReal_eq_orderOf_realResidueOfCoprime37 (K := K) q hcop]

end

end Fermat.Irregular.MaximalRealSplitting37
