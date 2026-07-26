import Fermat.KummerIso.Correction

/-!
# The ideal-class automorphism boundary

The first regularity use in Kummer's Case-II induction starts from an ideal
class `c` whose `p`-th power is principal.  In additive class-group notation
this says only

`p • c = 0`.

Transport through an additive or linear equivalence preserves both zero and
`p`-torsion.  Consequently an equivalence cannot, by itself, turn this source
equation into `c = 0`: a separate arithmetic theorem must first prove that
the *corrected* class is zero.

The final theorem gives the universal countermodel.  For every prime `p`,
`1 : ZMod p` is nonzero `p`-torsion, and every additive automorphism carries
it to another nonzero `p`-torsion element.

This is different from the unit-side Bernoulli correction.  There the source
is an integral divisibility statement such as `p ^ 3 ∣ a * B`; powers of `p`
can be cancelled in `ℤ` before reducing modulo `p`, producing the additional
corrected-zero equation required by the automorphism.
-/

namespace Fermat.KummerIso.IdealAutomorphismBoundary

/-- An additive equivalence reflects zero.  Thus a transported class is zero
exactly when the original class was already zero. -/
theorem addEquiv_map_eq_zero_iff
    {M N : Type*} [AddMonoid M] [AddMonoid N]
    (e : M ≃+ N) (x : M) :
    e x = 0 ↔ x = 0 :=
  e.map_eq_zero_iff

/-- Additive equivalences preserve and reflect the `n`-torsion equation. -/
theorem addEquiv_nsmul_eq_zero_iff
    {M N : Type*} [AddMonoid M] [AddMonoid N]
    (e : M ≃+ N) (n : ℕ) (x : M) :
    n • e x = 0 ↔ n • x = 0 := by
  have hmap : e (n • x) = n • e x :=
    e.toAddMonoidHom.map_nsmul n x
  constructor
  · intro h
    apply e.injective
    rw [e.map_zero, hmap]
    exact h
  · intro h
    rw [← hmap, h, e.map_zero]

/-- A linear equivalence likewise reflects zero. -/
theorem linearEquiv_map_eq_zero_iff
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) (x : M) :
    e x = 0 ↔ x = 0 :=
  e.map_eq_zero_iff

/-- Linear equivalences preserve and reflect scalar-annihilation equations. -/
theorem linearEquiv_smul_eq_zero_iff
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) (r : R) (x : M) :
    r • e x = 0 ↔ r • x = 0 := by
  rw [← e.map_smul, e.map_eq_zero_iff]

/-- The basic obstruction: `1 : ZMod p` is a nonzero element killed by `p`. -/
theorem zmod_one_nonzero_and_p_torsion
    {p : ℕ} (hp : p.Prime) :
    (1 : ZMod p) ≠ 0 ∧ p • (1 : ZMod p) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · exact one_ne_zero
  · simp [nsmul_eq_mul]

/-- No additive automorphism can remove the nonzero `p`-torsion
counterexample.  It preserves both its nonzeroness and its torsion equation. -/
theorem zmod_automorphism_preserves_nonzero_p_torsion
    {p : ℕ} (hp : p.Prime)
    (e : ZMod p ≃+ ZMod p) :
    e 1 ≠ 0 ∧ p • e 1 = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hsource := zmod_one_nonzero_and_p_torsion hp
  constructor
  · intro hzero
    exact hsource.1 (e.map_eq_zero_iff.mp hzero)
  · exact
      (addEquiv_nsmul_eq_zero_iff e p (1 : ZMod p)).2
        hsource.2

/-- A single model satisfying the ideal-class source equation while
remaining nonzero under every automorphism.

Therefore the implication

`p • c = 0 → c = 0`

cannot follow from primality of `p` and the existence of an automorphism.
For the actual Fermat ideals, one still needs a provenance theorem producing
a corrected-zero equation (or, equivalently, a special principalization
theorem such as the primary Takagi--Furtwängler step). -/
theorem exists_nonzero_p_torsion_preserved_by_every_automorphism
    {p : ℕ} (hp : p.Prime) :
    ∃ c : ZMod p,
      c ≠ 0 ∧
      p • c = 0 ∧
      ∀ e : ZMod p ≃+ ZMod p,
        e c ≠ 0 ∧ p • e c = 0 := by
  refine ⟨1, (zmod_one_nonzero_and_p_torsion hp).1,
    (zmod_one_nonzero_and_p_torsion hp).2, ?_⟩
  intro e
  exact zmod_automorphism_preserves_nonzero_p_torsion hp e

end Fermat.KummerIso.IdealAutomorphismBoundary
