/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Transverse polynomial annihilators

The reflection cycle owns the periodic relation `(T ^ r - 1) • d = 0`.
A genuinely transverse source supplies a second relation `P • d = 0`.
Their normalized polynomial gcd is itself an annihilator; if it is one,
Bézout kills the difference mode.  If it is nontrivial, it is retained as a
`LivelockChannel` rather than discarded.

Stickelberger and supporter-prime lamps enter only through named interfaces.
In particular, no finite sweep is rerun here.  The `k_first` table and the
observed sixfold law used by intended instances are recorded in
`GENERATION-CHAINS.md`.
-/
import Fermat.SophieGermain

namespace Fermat.Conservation.TransverseAnnihilator

open Polynomial

/-! ## Periodic and Wendt polynomials -/

/-- The polynomial belonging to a cycle of length `r`. -/
noncomputable def cyclePolynomial (F : Type*) [CommRing F] (r : ℕ) : Polynomial F :=
  X ^ r - 1

/-- The quadratic Wendt factor forced by the sixfold obstruction. -/
noncomputable def wendtPolynomial (F : Type*) [CommRing F] : Polynomial F :=
  X ^ 2 - X + 1

/-- A polynomial annihilates a mode when its scalar action sends the mode to
zero. -/
def Annihilates {R M : Type*} [Zero M] [SMul R M] (P : R) (d : M) : Prop :=
  P • d = 0

/-! ## The abstract corner service

An idempotent corner is a unital ring in its own right, whose unit is the
ambient idempotent.  The service below is therefore stated for an arbitrary
ring `A`; taking `A = h_e.Corner` makes the displayed `1` literally `e` in
the ambient algebra.  No commutativity is needed: the relation carrier is
the quotient by the sum of the two left-principal submodules.
-/

namespace CornerService

variable {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]

/-- A left Bézout identity in a unital corner.  In an idempotent corner the
right side `1` is the corner idempotent itself. -/
structure BezoutCertificate (cycle transverse : A) where
  cycleCoefficient : A
  transverseCoefficient : A
  combine :
    cycleCoefficient * cycle + transverseCoefficient * transverse = 1

/-- A transverse relation breaks the cycle precisely when the two relations
generate the unit of the corner as a left ideal. -/
def BreaksCycle (cycle transverse : A) : Prop :=
  Nonempty (BezoutCertificate cycle transverse)

/-- The corner service theorem: two annihilators whose left Bézout
combination is the corner identity kill the carried mode. -/
theorem eq_zero_of_annihilates_of_bezout
    {cycle transverse : A} {m : M}
    (hcycle : Annihilates cycle m)
    (htransverse : Annihilates transverse m)
    (bezout : BezoutCertificate cycle transverse) :
    m = 0 := by
  change cycle • m = 0 at hcycle
  change transverse • m = 0 at htransverse
  calc
    m = (1 : A) • m := (one_smul A m).symm
    _ = (bezout.cycleCoefficient * cycle +
          bezout.transverseCoefficient * transverse) • m := by
      rw [bezout.combine]
    _ = 0 := by simp [add_smul, mul_smul, hcycle, htransverse]

/-- The sum `A cycle + A transverse` of the two left-principal relation
submodules. -/
def relationSubmodule (cycle transverse : A) : Submodule A A :=
  Submodule.span A {cycle} ⊔ Submodule.span A {transverse}

/-- The surviving corner carrier
`A / (A cycle + A transverse)`. -/
abbrev LivelockCarrier (cycle transverse : A) :=
  A ⧸ relationSubmodule cycle transverse

/-- Membership of the corner unit in the relation submodule is exactly a
left Bézout certificate. -/
theorem one_mem_relationSubmodule_iff
    {cycle transverse : A} :
    (1 : A) ∈ relationSubmodule cycle transverse ↔
      BreaksCycle cycle transverse := by
  constructor
  · intro h
    rw [relationSubmodule, Submodule.mem_sup] at h
    obtain ⟨x, hx, y, hy, hxy⟩ := h
    rw [Submodule.mem_span_singleton] at hx hy
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact ⟨⟨u, v, by simpa [smul_eq_mul] using hxy⟩⟩
  · rintro ⟨bezout⟩
    rw [← bezout.combine]
    exact Submodule.add_mem_sup
      ((Submodule.span A {cycle}).smul_mem bezout.cycleCoefficient
        (Submodule.mem_span_singleton_self cycle))
      ((Submodule.span A {transverse}).smul_mem bezout.transverseCoefficient
        (Submodule.mem_span_singleton_self transverse))

/-- The relation submodule fills the corner exactly when the transverse
relation breaks the cycle. -/
theorem relationSubmodule_eq_top_iff
    {cycle transverse : A} :
    relationSubmodule cycle transverse = ⊤ ↔
      BreaksCycle cycle transverse := by
  rw [← one_mem_relationSubmodule_iff]
  constructor
  · intro htop
    rw [htop]
    exact Submodule.mem_top
  · intro hone
    apply le_antisymm le_top
    intro x _
    simpa [smul_eq_mul] using
      (relationSubmodule cycle transverse).smul_mem x hone

/-- `L = 0` in the module sense (`L` is subsingleton) if and only if the
transverse relation breaks the cycle. -/
theorem livelockCarrier_subsingleton_iff
    {cycle transverse : A} :
    Subsingleton (LivelockCarrier cycle transverse) ↔
      BreaksCycle cycle transverse := by
  rw [Submodule.Quotient.subsingleton_iff, relationSubmodule_eq_top_iff]

/-- The quotient carrier is nontrivial exactly when the cycle survives the
transverse relation. -/
theorem livelockCarrier_nontrivial_iff
    {cycle transverse : A} :
    Nontrivial (LivelockCarrier cycle transverse) ↔
      ¬ BreaksCycle cycle transverse := by
  rw [Submodule.Quotient.nontrivial_iff, ne_eq,
    relationSubmodule_eq_top_iff]

/-- A surviving livelock channel retains an actual nonzero class in the
two-relation quotient, rather than only a Boolean failure flag. -/
structure CornerLivelockChannel (cycle transverse : A) where
  carrierClass : LivelockCarrier cycle transverse
  carrierClass_ne_zero : carrierClass ≠ 0

/-- A nonzero quotient class exists exactly when the transverse relation
does not break the cycle. -/
theorem nonempty_cornerLivelockChannel_iff
    {cycle transverse : A} :
    Nonempty (CornerLivelockChannel cycle transverse) ↔
      ¬ BreaksCycle cycle transverse := by
  constructor
  · rintro ⟨channel⟩ hbreak
    have hsubsingle : Subsingleton (LivelockCarrier cycle transverse) :=
      livelockCarrier_subsingleton_iff.mpr hbreak
    exact channel.carrierClass_ne_zero
      (@Subsingleton.elim _ hsubsingle channel.carrierClass 0)
  · intro hsurvives
    have hnontrivial : Nontrivial (LivelockCarrier cycle transverse) :=
      livelockCarrier_nontrivial_iff.mpr hsurvives
    letI := hnontrivial
    obtain ⟨channel, hchannel⟩ :=
      exists_ne (0 : LivelockCarrier cycle transverse)
    exact ⟨⟨channel, hchannel⟩⟩

end CornerService

section PolynomialGCD

variable {F M : Type*} [Field F] [DecidableEq F]
  [AddCommGroup M] [Module (Polynomial F) M]

/-- The canonical common annihilator is the normalized Euclidean gcd.  The
normalization matters: a unit gcd is then literally `1`, not an arbitrary
nonzero constant. -/
noncomputable def polynomialGCD (P Q : Polynomial F) : Polynomial F :=
  normalize (EuclideanDomain.gcd P Q)

/-- In the commutative polynomial image, the abstract corner Bézout
condition is exactly the normalized-gcd-one condition. -/
theorem breaksCycle_iff_polynomialGCD_eq_one
    {P Q : Polynomial F} :
    CornerService.BreaksCycle P Q ↔ polynomialGCD P Q = 1 := by
  constructor
  · rintro ⟨bezout⟩
    have hcoprime : IsCoprime P Q :=
      ⟨bezout.cycleCoefficient, bezout.transverseCoefficient,
        bezout.combine⟩
    have hunit : IsUnit (EuclideanDomain.gcd P Q) :=
      EuclideanDomain.gcd_isUnit_iff.mpr hcoprime
    exact normalize_eq_one.mpr hunit
  · intro hgcd
    have hunit : IsUnit (EuclideanDomain.gcd P Q) :=
      normalize_eq_one.mp hgcd
    obtain ⟨u, v, huv⟩ := EuclideanDomain.gcd_isUnit_iff.mp hunit
    exact ⟨⟨u, v, huv⟩⟩

/-- The old polynomial gcd law is the one-loop commutative image of the
corner quotient law: its two-relation carrier is zero exactly when the
normalized gcd is one. -/
theorem polynomial_livelockCarrier_subsingleton_iff
    {P Q : Polynomial F} :
    Subsingleton (CornerService.LivelockCarrier P Q) ↔
      polynomialGCD P Q = 1 :=
  CornerService.livelockCarrier_subsingleton_iff.trans
    breaksCycle_iff_polynomialGCD_eq_one

/-- A genuine polynomial quotient channel survives exactly when the
normalized gcd is not one. -/
theorem nonempty_polynomial_cornerLivelockChannel_iff
    {P Q : Polynomial F} :
    Nonempty (CornerService.CornerLivelockChannel P Q) ↔
      polynomialGCD P Q ≠ 1 :=
  CornerService.nonempty_cornerLivelockChannel_iff.trans
    (not_congr breaksCycle_iff_polynomialGCD_eq_one)

@[simp] theorem normalize_polynomialGCD (P Q : Polynomial F) :
    normalize (polynomialGCD P Q) = polynomialGCD P Q := by
  simp [polynomialGCD, normalize_idem]

/-- The canonical gcd divides its left input. -/
theorem polynomialGCD_dvd_left (P Q : Polynomial F) :
    polynomialGCD P Q ∣ P :=
  (normalize_associated (EuclideanDomain.gcd P Q)).dvd.trans
    (EuclideanDomain.gcd_dvd_left P Q)

/-- The canonical gcd divides its right input. -/
theorem polynomialGCD_dvd_right (P Q : Polynomial F) :
    polynomialGCD P Q ∣ Q :=
  (normalize_associated (EuclideanDomain.gcd P Q)).dvd.trans
    (EuclideanDomain.gcd_dvd_right P Q)

/-- Every common polynomial factor divides the canonical gcd. -/
theorem dvd_polynomialGCD {W P Q : Polynomial F}
    (hWP : W ∣ P) (hWQ : W ∣ Q) :
    W ∣ polynomialGCD P Q :=
  (EuclideanDomain.dvd_gcd hWP hWQ).trans
    (associated_normalize (EuclideanDomain.gcd P Q)).dvd

/-- Bézout's identity acts on the module: two annihilators make their raw
Euclidean gcd an annihilator. -/
theorem annihilates_euclideanGCD {P Q : Polynomial F} {d : M}
    (hP : Annihilates P d) (hQ : Annihilates Q d) :
    Annihilates (EuclideanDomain.gcd P Q) d := by
  change P • d = 0 at hP
  change Q • d = 0 at hQ
  have hbezout : EuclideanDomain.gcd P Q =
      EuclideanDomain.gcdA P Q * P +
        EuclideanDomain.gcdB P Q * Q := by
    rw [EuclideanDomain.gcd_eq_gcd_ab]
    ac_rfl
  simp [Annihilates, hbezout, add_smul, mul_smul, hP, hQ]

/-- Normalization only multiplies by a unit, so the canonical gcd remains an
annihilator. -/
theorem annihilates_polynomialGCD {P Q : Polynomial F} {d : M}
    (hP : Annihilates P d) (hQ : Annihilates Q d) :
    Annihilates (polynomialGCD P Q) d := by
  have hgcd := annihilates_euclideanGCD hP hQ
  change EuclideanDomain.gcd P Q • d = 0 at hgcd
  change normalize (EuclideanDomain.gcd P Q) • d = 0
  rw [normalize_apply, mul_comm, mul_smul, hgcd, smul_zero]

/-- The two-annihilator Bézout law.  Coprimality with the cycle polynomial
kills the difference mode. -/
theorem eq_zero_of_cycle_and_transverse_gcd_eq_one
    {r : ℕ} {P : Polynomial F} {d : M}
    (hcycle : Annihilates (cyclePolynomial F r) d)
    (htransverse : Annihilates P d)
    (hcoprime : polynomialGCD P (cyclePolynomial F r) = 1) :
    d = 0 := by
  obtain ⟨bezout⟩ :=
    (breaksCycle_iff_polynomialGCD_eq_one (P := P)
      (Q := cyclePolynomial F r)).mpr hcoprime
  exact CornerService.eq_zero_of_annihilates_of_bezout
    htransverse hcycle bezout

/-- A normalized polynomial is nonunit exactly when it is not one.  This
form is used to ensure that a retained channel is genuinely nontrivial. -/
theorem polynomialGCD_not_isUnit_of_ne_one {P Q : Polynomial F}
    (hne : polynomialGCD P Q ≠ 1) :
    ¬ IsUnit (polynomialGCD P Q) := by
  intro hunit
  apply hne
  calc
    polynomialGCD P Q = normalize (polynomialGCD P Q) :=
      (normalize_polynomialGCD P Q).symm
    _ = 1 := normalize_eq_one.mpr hunit

/-! ## The constructive surviving channel -/

/-- A mode carrying the reflection-cycle relation and one transverse
annihilator. -/
structure TwoAnnihilatorMode (F M : Type*) [Field F] [DecidableEq F]
    [AddCommGroup M] [Module (Polynomial F) M] (r : ℕ) where
  mode : M
  transverse : Polynomial F
  cycle_annihilates : Annihilates (cyclePolynomial F r) mode
  transverse_annihilates : Annihilates transverse mode

/-- A non-lossy record of the surviving periodic channel.  Its factor is
definitionally tied to the normalized gcd, is a genuine nonunit common
factor, and still annihilates the mode. -/
structure LivelockChannel {r : ℕ}
    (data : TwoAnnihilatorMode F M r) where
  factor : Polynomial F
  factor_eq_gcd :
    factor = polynomialGCD data.transverse (cyclePolynomial F r)
  factor_not_isUnit : ¬ IsUnit factor
  factor_dvd_transverse : factor ∣ data.transverse
  factor_dvd_cycle : factor ∣ cyclePolynomial F r
  factor_annihilates : Annihilates factor data.mode

namespace TwoAnnihilatorMode

variable {r : ℕ} (data : TwoAnnihilatorMode F M r)

/-- The normalized gcd of the two recorded relations annihilates the mode. -/
theorem gcd_annihilates :
    Annihilates
      (polynomialGCD data.transverse (cyclePolynomial F r)) data.mode :=
  annihilates_polynomialGCD data.transverse_annihilates
    data.cycle_annihilates

/-- The record form of the two-annihilator Bézout law. -/
theorem mode_eq_zero
    (hcoprime :
      polynomialGCD data.transverse (cyclePolynomial F r) = 1) :
    data.mode = 0 :=
  eq_zero_of_cycle_and_transverse_gcd_eq_one data.cycle_annihilates
    data.transverse_annihilates hcoprime

/-- If the gcd is not one, retain that exact nonunit gcd as the livelock
channel. -/
noncomputable def livelockChannel
    (hne : polynomialGCD data.transverse (cyclePolynomial F r) ≠ 1) :
    LivelockChannel data where
  factor := polynomialGCD data.transverse (cyclePolynomial F r)
  factor_eq_gcd := rfl
  factor_not_isUnit := polynomialGCD_not_isUnit_of_ne_one hne
  factor_dvd_transverse := polynomialGCD_dvd_left _ _
  factor_dvd_cycle := polynomialGCD_dvd_right _ _
  factor_annihilates := data.gcd_annihilates

end TwoAnnihilatorMode

/-! ## Named transverse sources -/

/-- A transverse annihilator credited to the Stickelberger source.  Existing
specialized Stickelberger developments do not expose this module action, so
an instance must provide the polynomial and its action theorem explicitly. -/
structure StickelbergerTransverse (F M : Type*) [Field F] [DecidableEq F]
    [AddCommGroup M] [Module (Polynomial F) M] (d : M) where
  polynomial : Polynomial F
  annihilates : Annihilates polynomial d

namespace StickelbergerTransverse

variable {d : M} (source : StickelbergerTransverse F M d)

/-- Pair a Stickelberger source with the owned reflection-cycle relation. -/
def withCycle (r : ℕ)
    (hcycle : Annihilates (cyclePolynomial F r) d) :
    TwoAnnihilatorMode F M r where
  mode := d
  transverse := source.polynomial
  cycle_annihilates := hcycle
  transverse_annihilates := source.annihilates

/-- A Stickelberger annihilator transverse to the cycle kills the mode when
the two polynomials are coprime. -/
theorem mode_eq_zero_of_gcd_eq_one {r : ℕ}
    (hcycle : Annihilates (cyclePolynomial F r) d)
    (hcoprime :
      polynomialGCD source.polynomial (cyclePolynomial F r) = 1) :
    d = 0 :=
  (source.withCycle r hcycle).mode_eq_zero hcoprime

end StickelbergerTransverse

/-- A supporter-prime lamp as a named transverse source.  The arithmetic
fields identify `q = 2*k*p+1`; the polynomial action remains explicit and
cannot be smuggled in from a residue sweep. -/
structure LampTransverse (F M : Type*) [Field F] [DecidableEq F]
    [AddCommGroup M] [Module (Polynomial F) M]
    (p q k : ℕ) (d : M) where
  exponent_prime : p.Prime
  supporter_prime : q.Prime
  supporter_relation : q = 2 * k * p + 1
  polynomial : Polynomial F
  annihilates : Annihilates polynomial d

/-- The two Sophie--Germain residue conditions.  Only condition (a), the
`NoConsecutivePowers` component, controls the polynomial gcd below;
condition (b) remains part of a full lamp certificate. -/
def SophieGermainConditions (p q : ℕ) : Prop :=
  Fermat.SophieGermain.NoConsecutivePowers p q ∧
    Fermat.SophieGermain.ExponentNotPower p q

namespace LampTransverse

variable {p q k : ℕ} {d : M}
  (lamp : LampTransverse F M p q k d)

/-- Pair the lamp annihilator with the owned reflection-cycle relation. -/
def withCycle (r : ℕ)
    (hcycle : Annihilates (cyclePolynomial F r) d) :
    TwoAnnihilatorMode F M r where
  mode := d
  transverse := lamp.polynomial
  cycle_annihilates := hcycle
  transverse_annihilates := lamp.annihilates

end LampTransverse

/-- The exact adapter between Sophie--Germain condition (a) and the
two-annihilator gcd.  Failure of condition (a) is therefore not discarded:
it returns the nonunit gcd channel below. -/
structure SophieGermainGCDLaw {p q k : ℕ} {d : M} {r : ℕ}
    (lamp : LampTransverse F M p q k d) : Prop where
  conditionA_iff_gcd_eq_one :
    Fermat.SophieGermain.NoConsecutivePowers p q ↔
      polynomialGCD lamp.polynomial (cyclePolynomial F r) = 1

namespace SophieGermainGCDLaw

variable {p q k : ℕ} {d : M} {r : ℕ}
  {lamp : LampTransverse F M p q k d}
  (law : SophieGermainGCDLaw (r := r) lamp)

include law

/-- A complete SG lamp certificate supplies the coprime transverse relation;
condition (b) is retained even though this projection uses condition (a). -/
theorem gcd_eq_one_of_certificate
    (hcertificate : SophieGermainConditions p q) :
    polynomialGCD lamp.polynomial (cyclePolynomial F r) = 1 :=
  (law.conditionA_iff_gcd_eq_one).mp hcertificate.1

/-- The certified lamp kills a mode already carrying its cycle relation. -/
theorem mode_eq_zero_of_certificate
    (hcycle : Annihilates (cyclePolynomial F r) d)
    (hcertificate : SophieGermainConditions p q) :
    d = 0 :=
  (LampTransverse.withCycle lamp r hcycle).mode_eq_zero
    (SophieGermainGCDLaw.gcd_eq_one_of_certificate law hcertificate)

/-- A condition-(a) failure constructively returns the exact gcd livelock
channel instead of a Boolean failure flag. -/
noncomputable def channel_of_conditionA_failure
    (hcycle : Annihilates (cyclePolynomial F r) d)
    (hfailure :
      ¬ Fermat.SophieGermain.NoConsecutivePowers p q) :
    LivelockChannel (LampTransverse.withCycle lamp r hcycle) := by
  apply (LampTransverse.withCycle lamp r hcycle).livelockChannel
  intro hgcd
  exact hfailure ((law.conditionA_iff_gcd_eq_one).mpr hgcd)

end SophieGermainGCDLaw

/-! ## The sixfold/Wendt interface -/

/-- A constructive common-factor witness, retaining the actual factor and
proof that it is nonunit. -/
structure SharedFactor (P Q : Polynomial F) where
  factor : Polynomial F
  factor_not_isUnit : ¬ IsUnit factor
  factor_dvd_left : factor ∣ P
  factor_dvd_right : factor ∣ Q

omit [DecidableEq F] in
/-- `X²-X+1` is never a unit, over any field. -/
theorem wendtPolynomial_not_isUnit :
    ¬ IsUnit (wendtPolynomial F) := by
  intro hunit
  rw [Polynomial.isUnit_iff] at hunit
  obtain ⟨c, _, hc⟩ := hunit
  have hcoeff := congrArg (fun P : Polynomial F ↦ P.coeff 2) hc
  simp [wendtPolynomial, Polynomial.coeff_X, Polynomial.coeff_X_pow,
    Polynomial.coeff_one] at hcoeff

/-- Any nonunit common factor forces the canonical gcd to be nontrivial. -/
theorem polynomialGCD_ne_one_of_sharedFactor {P Q : Polynomial F}
    (shared : SharedFactor P Q) :
    polynomialGCD P Q ≠ 1 := by
  intro hgcd
  have hdiv : shared.factor ∣ polynomialGCD P Q :=
    dvd_polynomialGCD shared.factor_dvd_left shared.factor_dvd_right
  rw [hgcd] at hdiv
  exact shared.factor_not_isUnit (isUnit_iff_dvd_one.mpr hdiv)

/-- The sixfold law as an explicit interface: whenever `3 ∣ k`, the Wendt
quadratic divides both the lamp polynomial and the cycle polynomial.  The
empirical absence of such `k_first` values is data in `GENERATION-CHAINS.md`,
not a theorem recomputed in this generic module. -/
structure SixfoldWendtLaw {p q k : ℕ} {d : M} {r : ℕ}
    (lamp : LampTransverse F M p q k d) : Prop where
  wendt_shared_of_three_dvd :
    3 ∣ k →
      wendtPolynomial F ∣ lamp.polynomial ∧
        wendtPolynomial F ∣ cyclePolynomial F r

namespace SixfoldWendtLaw

variable {p q k : ℕ} {d : M} {r : ℕ}
  {lamp : LampTransverse F M p q k d}
  (law : SixfoldWendtLaw (r := r) lamp)

include law

/-- For `3 ∣ k`, retain the Wendt quadratic itself as a shared-factor
witness. -/
noncomputable def sharedFactor (hthree : 3 ∣ k) :
    SharedFactor lamp.polynomial (cyclePolynomial F r) where
  factor := wendtPolynomial F
  factor_not_isUnit := wendtPolynomial_not_isUnit
  factor_dvd_left := (law.wendt_shared_of_three_dvd hthree).1
  factor_dvd_right := (law.wendt_shared_of_three_dvd hthree).2

/-- The sixfold obstruction produces the normalized gcd livelock channel. -/
noncomputable def livelockChannel (hthree : 3 ∣ k)
    (hcycle : Annihilates (cyclePolynomial F r) d) :
    LivelockChannel (LampTransverse.withCycle lamp r hcycle) :=
  (LampTransverse.withCycle lamp r hcycle).livelockChannel
    (polynomialGCD_ne_one_of_sharedFactor
      (SixfoldWendtLaw.sharedFactor law hthree))

/-- Combining the Wendt law with the SG/gcd adapter states the traditional
sixfold consequence: `3 ∣ k` forces condition (a) to fail. -/
theorem conditionA_fails_of_three_dvd
    (sgLaw : SophieGermainGCDLaw (r := r) lamp)
    (hthree : 3 ∣ k) :
    ¬ Fermat.SophieGermain.NoConsecutivePowers p q := by
  intro hconditionA
  have hgcd := (sgLaw.conditionA_iff_gcd_eq_one).mp hconditionA
  exact polynomialGCD_ne_one_of_sharedFactor
    (SixfoldWendtLaw.sharedFactor law hthree) hgcd

end SixfoldWendtLaw

end PolynomialGCD

end Fermat.Conservation.TransverseAnnihilator
