import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

/-!
# The degree-two Heisenberg carrier

This file is a minimal, dependency-light port of the Heisenberg carrier and
the scheduler-independent payload laws developed in `iso-conserve-lean`.

Provenance:

* Carrier source: `~/scheduler/iso-conserve-lean/IsoConserve/Heis.lean` at
  commit `e5b23b59a09c4406e09f50ded9e24ec0e08d300f`, SHA-256
  `f7301f8cef1c9b84756528821218be45139b9d3ca883f0a8fe26e85accf9bed4`.
* Payload-law source:
  `~/scheduler/iso-conserve-lean/IsoConserve/HeisenbergPayload.lean` at
  commit `f7b8e6fddd8e2429864a923abc5baf89a40f4b37`, SHA-256
  `061cffa58e76b0e7ead41e6e4458862e184218dcd0a9e022fb6a27ef5650591d`.
* Audit record: commit `ea920d97f1d8f31b1bc9bbbe8235d8587046473e`
  records a clean build, sorry/admit scan, and public-theorem axiom audit for
  the source at `f7b8e6f`; the two source blobs above are unchanged through
  that audit commit.

The source tree used Lean `v4.30.0` and `Std`'s `Lean.Grind` commutative-ring
interface.  This port targets Fermat's Lean `v4.31.0-rc1`/Mathlib environment
and replaces the small `grind` calculations with structure extensionality and
ring normalization.  The multiplication order and all mathematical statements
are unchanged.

Multiplication retains the signed area swept out by the visible coordinates:

`(a,b,c) * (a',b',c') = (a+a', b+b', c+c'+a*b')`.
-/

namespace Fermat.Conservation

universe u v

/-- The degree-two Heisenberg carrier over a commutative ring. -/
structure Heis (R : Type u) where
  a : R
  b : R
  c : R
deriving DecidableEq, Repr

namespace Heis

variable {R : Type u} [CommRing R]

/-- Twisted Heisenberg multiplication. -/
def mul (g h : Heis R) : Heis R :=
  { a := g.a + h.a
    b := g.b + h.b
    c := g.c + h.c + g.a * h.b }

instance instMul : Mul (Heis R) := ⟨mul⟩

/-- The identity element. -/
def identity : Heis R := ⟨0, 0, 0⟩

instance instOne : One (Heis R) := ⟨identity⟩

/-- The inverse for twisted multiplication. -/
def inverse (g : Heis R) : Heis R :=
  ⟨-g.a, -g.b, -g.c + g.a * g.b⟩

instance instInv : Inv (Heis R) := ⟨inverse⟩

omit [CommRing R] in
private theorem eq_of_coordinates {g h : Heis R}
    (ha : g.a = h.a) (hb : g.b = h.b) (hc : g.c = h.c) : g = h := by
  cases g
  cases h
  simp_all

/-- Twisted multiplication is associative. -/
theorem mul_assoc (g h k : Heis R) : (g * h) * k = g * (h * k) := by
  change mul (mul g h) k = mul g (mul h k)
  apply eq_of_coordinates <;> simp only [mul] <;> ring

/-- The Heisenberg identity is a left identity. -/
theorem one_mul (g : Heis R) : 1 * g = g := by
  change mul identity g = g
  apply eq_of_coordinates <;> simp [identity, mul]

/-- The Heisenberg identity is a right identity. -/
theorem mul_one (g : Heis R) : g * 1 = g := by
  change mul g identity = g
  apply eq_of_coordinates <;> simp [identity, mul]

/-- The explicit inverse is a left inverse. -/
theorem inv_mul (g : Heis R) : g⁻¹ * g = 1 := by
  change mul (inverse g) g = identity
  apply eq_of_coordinates <;> simp only [inverse, mul, identity] <;> ring

/-- The explicit inverse is a right inverse. -/
theorem mul_inv (g : Heis R) : g * g⁻¹ = 1 := by
  change mul g (inverse g) = identity
  apply eq_of_coordinates <;> simp only [inverse, mul, identity] <;> ring

/-- A compact certificate that the operations above obey all group laws. -/
structure GroupLaws : Prop where
  associative : ∀ g h k : Heis R, (g * h) * k = g * (h * k)
  left_identity : ∀ g : Heis R, 1 * g = g
  right_identity : ∀ g : Heis R, g * 1 = g
  left_inverse : ∀ g : Heis R, g⁻¹ * g = 1
  right_inverse : ∀ g : Heis R, g * g⁻¹ = 1

/-- `Heis R` obeys the group laws under twisted multiplication. -/
theorem groupLaws : GroupLaws (R := R) :=
  ⟨mul_assoc, one_mul, mul_one, inv_mul, mul_inv⟩

/-- Embed a scalar as a purely central Heisenberg element. -/
def center (c : R) : Heis R := ⟨0, 0, c⟩

/-- An element is central when it commutes with every Heisenberg element. -/
def Central (z : Heis R) : Prop := ∀ g : Heis R, z * g = g * z

/-- Every element `(0,0,c)` lies in the center. -/
theorem center_is_central (c : R) : Central (center c) := by
  intro g
  change mul (center c) g = mul g (center c)
  apply eq_of_coordinates <;> simp only [center, mul] <;> ring

/-- Central elements are exactly those with zero visible coordinates. -/
theorem central_iff (z : Heis R) : Central z ↔ z.a = 0 ∧ z.b = 0 := by
  constructor
  · intro hz
    have ha := congrArg Heis.c (hz ⟨0, 1, 0⟩)
    have hb := congrArg Heis.c (hz ⟨1, 0, 0⟩)
    change (mul z ⟨0, 1, 0⟩).c = (mul ⟨0, 1, 0⟩ z).c at ha
    change (mul z ⟨1, 0, 0⟩).c = (mul ⟨1, 0, 0⟩ z).c at hb
    constructor
    · simpa [mul] using ha
    · simpa [mul] using hb
  · rintro ⟨ha, hb⟩ g
    change mul z g = mul g z
    apply eq_of_coordinates <;> simp [mul, ha, hb, add_comm]

/-- The central embedding is injective. -/
theorem center_injective {c d : R} (h : center c = center d) : c = d := by
  exact congrArg Heis.c h

/-- The central embedding converts addition into Heisenberg multiplication. -/
theorem center_add (c d : R) : center (c + d) = center c * center d := by
  change center (c + d) = mul (center c) (center d)
  apply eq_of_coordinates <;> simp [center, mul]

/-- Exact carrier-level description of the center. -/
theorem eq_center_iff (z : Heis R) : (∃ c : R, z = center c) ↔ Central z := by
  constructor
  · rintro ⟨c, rfl⟩
    exact center_is_central c
  · intro hz
    refine ⟨z.c, ?_⟩
    apply eq_of_coordinates
    · exact (central_iff z).1 hz |>.1
    · exact (central_iff z).1 hz |>.2
    · rfl

/-! ## Abelianization -/

/-- The visible two-coordinate abelian carrier. Its multiplication is addition. -/
structure Abelian (R : Type u) where
  a : R
  b : R
deriving DecidableEq, Repr

namespace Abelian

variable {R : Type u} [CommRing R]

def mul (x y : Abelian R) : Abelian R := ⟨x.a + y.a, x.b + y.b⟩

instance instMul : Mul (Abelian R) := ⟨mul⟩

def identity : Abelian R := ⟨0, 0⟩

instance instOne : One (Abelian R) := ⟨identity⟩

def inverse (x : Abelian R) : Abelian R := ⟨-x.a, -x.b⟩

instance instInv : Inv (Abelian R) := ⟨inverse⟩

end Abelian

/-- A dependency-light bundled unital multiplicative homomorphism. -/
structure Hom (G : Type u) (H : Type v) [Mul G] [One G] [Mul H] [One H] where
  toFun : G → H
  map_one : toFun 1 = 1
  map_mul : ∀ g h, toFun (g * h) = toFun g * toFun h

instance {G : Type u} {H : Type v} [Mul G] [One G] [Mul H] [One H] :
    CoeFun (Hom G H) (fun _ => G → H) :=
  ⟨Hom.toFun⟩

/-- Forget the central coordinate. -/
def abelianization (g : Heis R) : Abelian R := ⟨g.a, g.b⟩

omit [CommRing R] in
/-- Abelianization of an explicit carrier value. -/
@[simp] theorem abelianization_mk (a b c : R) :
    abelianization (⟨a, b, c⟩ : Heis R) = (⟨a, b⟩ : Abelian R) := by
  rfl

/-- Projection to `(a,b)` preserves the identity. -/
theorem abelianization_one : abelianization (1 : Heis R) = 1 := by
  rfl

/-- Projection to `(a,b)` respects the group operation. -/
theorem abelianization_mul (g h : Heis R) :
    abelianization (g * h) = abelianization g * abelianization h := by
  rfl

/-- The abelianization as a bundled homomorphism. -/
def abelianizationHom : Hom (Heis R) (Abelian R) :=
  ⟨abelianization, abelianization_one, abelianization_mul⟩

/-- The abelianization kernel has exactly zero visible coordinates. -/
theorem abelianization_eq_one_iff (g : Heis R) :
    abelianization g = 1 ↔ g.a = 0 ∧ g.b = 0 := by
  change (Abelian.mk g.a g.b = Abelian.identity) ↔ g.a = 0 ∧ g.b = 0
  constructor
  · intro h
    exact ⟨congrArg Abelian.a h, congrArg Abelian.b h⟩
  · rintro ⟨ha, hb⟩
    cases g
    simp_all [Abelian.identity]

/-- The kernel of abelianization is exactly the center. -/
theorem abelianization_kernel_eq_center (g : Heis R) :
    abelianizationHom g = 1 ↔ ∃ c : R, g = center c := by
  rw [show abelianizationHom g = abelianization g from rfl]
  rw [abelianization_eq_one_iff]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨g.c, ?_⟩
    apply eq_of_coordinates <;> simp [center, ha, hb]
  · rintro ⟨c, rfl⟩
    simp [center]

/-! ## The enclosed area -/

/-- Signed area of the visible parallelogram spanned by `g` and `h`. -/
def area (g h : Heis R) : R := g.a * h.b - h.a * g.b

/-- Multiplicative commutator, with the route order `g h g⁻¹ h⁻¹`. -/
def commutator (g h : Heis R) : Heis R := g * h * g⁻¹ * h⁻¹

/-- A commutator returns visibly to zero and retains its signed area centrally. -/
theorem commutator_formula (g h : Heis R) :
    commutator g h = ⟨0, 0, g.a * h.b - h.a * g.b⟩ := by
  change mul (mul (mul g h) (inverse g)) (inverse h) =
    ⟨0, 0, g.a * h.b - h.a * g.b⟩
  apply eq_of_coordinates <;> simp only [inverse, mul] <;> ring

/-- Coordinate-free form of `commutator_formula`: commutator equals enclosed area. -/
theorem commutator_eq_area_center (g h : Heis R) :
    commutator g h = center (area g h) := by
  simpa [center, area] using commutator_formula g h

/-- Every commutator is central. -/
theorem commutator_is_central (g h : Heis R) : Central (commutator g h) := by
  rw [commutator_eq_area_center]
  exact center_is_central _

/-! ## Scheduler-independent payload laws -/

/-- A closed word translates a purely central input by its enclosed-area
coordinate. -/
theorem closed_route_acts_on_center_by_enclosed_area
    (word : Heis R) (c : R) (ha : word.a = 0) (hb : word.b = 0) :
    center c * word = center (c + word.c) := by
  change mul (center c) word = center (c + word.c)
  apply eq_of_coordinates <;> simp [mul, center, ha, hb]

/-- A fixed route word preserves every difference between private central
coordinates. It is a translation, never a projection. -/
theorem central_difference_preserved (word : Heis R) (c d : R) :
    (center c * word).c - (center d * word).c = c - d := by
  change (mul (center c) word).c - (mul (center d) word).c = c - d
  simp only [center, mul]
  ring

/-- Right-composition by any route word is injective on private central state. -/
theorem no_private_drain (word : Heis R) :
    Function.Injective (fun c : R ↦ center c * word) := by
  intro c d h
  have hc := congrArg Heis.c h
  change (mul (center c) word).c = (mul (center d) word).c at hc
  simp only [center, mul, zero_mul, add_zero, zero_add] at hc
  exact add_right_cancel hc

/-- Vanishing at one chosen input is possible exactly by additive cancellation;
the input is retained with coefficient one and is not erased. -/
theorem central_coordinate_eq_zero_iff_exact_cancellation
    (word : Heis R) (c : R) :
    (center c * word).c = 0 ↔ word.c = -c := by
  change (mul (center c) word).c = 0 ↔ word.c = -c
  simp only [mul, center, zero_mul, add_zero, zero_add]
  constructor
  · intro h
    calc
      word.c = 0 + word.c := (zero_add word.c).symm
      _ = (-c + c) + word.c := by rw [neg_add_cancel]
      _ = -c + (c + word.c) := by rw [add_assoc]
      _ = -c + 0 := by rw [h]
      _ = -c := add_zero (-c)
  · intro h
    rw [h]
    exact add_neg_cancel c

end Heis
end Fermat.Conservation
