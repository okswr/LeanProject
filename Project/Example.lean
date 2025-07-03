import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Data.One.Defs
import Mathlib.Algebra.Group.Operations
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.OfNat
import Batteries.Logic

namespace ogasawara

/-
  以下確認用オプション（型等のダイアログ表示）
-/
set_option diagnostics true

/-
  Mathlib/Algebra/Group/Defs.lean
-/

--44

universe u v w

open Function

variable {G : Type*}

section Mul

variable [Mul G]

--62
/-- A mixin for left cancellative multiplication. -/
class IsLeftCancelMul (G : Type u) [Mul G] : Prop where
  /-- Multiplication is left cancellative. -/
  protected mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c
/-- A mixin for right cancellative multiplication. -/
class IsRightCancelMul (G : Type u) [Mul G] : Prop where
  /-- Multiplication is right cancellative. -/
  protected mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c
/-- A mixin for cancellative multiplication. -/
class IsCancelMul (G : Type u) [Mul G] extends IsLeftCancelMul G, IsRightCancelMul G : Prop

/-- A mixin for left cancellative addition. -/
class IsLeftCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is left cancellative. -/
  protected add_left_cancel : ∀ a b c : G, a + b = a + c → b = c

attribute [to_additive IsLeftCancelAdd] IsLeftCancelMul

/-- A mixin for right cancellative addition. -/
class IsRightCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is right cancellative. -/
  protected add_right_cancel : ∀ a b c : G, a + b = c + b → a = c

attribute [to_additive IsRightCancelAdd] IsRightCancelMul

/-- A mixin for cancellative addition. -/
class IsCancelAdd (G : Type u) [Add G] extends IsLeftCancelAdd G, IsRightCancelAdd G : Prop

attribute [to_additive IsCancelAdd] IsCancelMul

--92

section IsLeftCancelMul

variable [IsLeftCancelMul G] {a b c : G}

@[to_additive]
theorem mul_left_cancel : a * b = a * c → b = c :=
  IsLeftCancelMul.mul_left_cancel a b c

@[to_additive]
theorem mul_left_cancel_iff : a * b = a * c ↔ b = c :=
  ⟨mul_left_cancel, congrArg _⟩

@[to_additive]
theorem mul_right_injective (a : G) : Injective (a * ·) := fun _ _ ↦ mul_left_cancel

@[to_additive (attr := simp)]
theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
  (mul_right_injective a).eq_iff

@[to_additive]
theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
  (mul_right_injective a).ne_iff

end IsLeftCancelMul
--144
/-- A semigroup is a type with an associative `(*)`. -/
@[ext]
class Semigroup (G : Type u) extends Mul G where
  /-- Multiplication is associative -/
  protected mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

--150
/-- An additive semigroup is a type with an associative `(+)`. -/
@[ext]
class AddSemigroup (G : Type u) extends Add G where
  /-- Addition is associative -/
  protected add_assoc : ∀ a b c : G, a + b + c = a + (b + c)


--168
/-- A commutative additive magma is a type with an addition which commutes. -/
@[ext]
class AddCommMagma (G : Type u) extends Add G where
  /-- Addition is commutative in an commutative additive magma. -/
  protected add_comm : ∀ a b : G, a + b = b + a

/-- A commutative multiplicative magma is a type with a multiplication which commutes. -/
@[ext]
class CommMagma (G : Type u) extends Mul G where
  /-- Multiplication is commutative in a commutative multiplicative magma. -/
  protected mul_comm : ∀ a b : G, a * b = b * a

attribute [to_additive] CommMagma


/-- A commutative semigroup is a type with an associative commutative `(*)`. -/
@[ext]
class CommSemigroup (G : Type u) extends Semigroup G, CommMagma G where

/-- A commutative additive semigroup is a type with an associative commutative `(+)`. -/
@[ext]
class AddCommSemigroup (G : Type u) extends AddSemigroup G, AddCommMagma G where

attribute [to_additive] CommSemigroup

section CommMagma

variable [CommMagma G]

@[to_additive]
theorem mul_comm : ∀ a b : G, a * b = b * a := CommMagma.mul_comm


--199

/-- Any `CommMagma G` that satisfies `IsRightCancelMul G` also satisfies `IsLeftCancelMul G`. -/
@[to_additive AddCommMagma.IsRightCancelAdd.toIsLeftCancelAdd "Any `AddCommMagma G` that satisfies
`IsRightCancelAdd G` also satisfies `IsLeftCancelAdd G`."]
lemma CommMagma.IsRightCancelMul.toIsLeftCancelMul (G : Type u) [CommMagma G] [IsRightCancelMul G] :
    IsLeftCancelMul G :=
  ⟨fun _ _ _ h => mul_right_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

/-- Any `CommMagma G` that satisfies `IsLeftCancelMul G` also satisfies `IsRightCancelMul G`. -/
@[to_additive AddCommMagma.IsLeftCancelAdd.toIsRightCancelAdd "Any `AddCommMagma G` that satisfies
`IsLeftCancelAdd G` also satisfies `IsRightCancelAdd G`."]
lemma CommMagma.IsLeftCancelMul.toIsRightCancelMul (G : Type u) [CommMagma G] [IsLeftCancelMul G] :
    IsRightCancelMul G :=
  ⟨fun _ _ _ h => mul_left_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

/-- Any `CommMagma G` that satisfies `IsLeftCancelMul G` also satisfies `IsCancelMul G`. -/
@[to_additive AddCommMagma.IsLeftCancelAdd.toIsCancelAdd "Any `AddCommMagma G` that satisfies
`IsLeftCancelAdd G` also satisfies `IsCancelAdd G`."]
lemma CommMagma.IsLeftCancelMul.toIsCancelMul (G : Type u) [CommMagma G] [IsLeftCancelMul G] :
    IsCancelMul G := { CommMagma.IsLeftCancelMul.toIsRightCancelMul G with }

/-- Any `CommMagma G` that satisfies `IsRightCancelMul G` also satisfies `IsCancelMul G`. -/
@[to_additive AddCommMagma.IsRightCancelAdd.toIsCancelAdd "Any `AddCommMagma G` that satisfies
`IsRightCancelAdd G` also satisfies `IsCancelAdd G`."]
lemma CommMagma.IsRightCancelMul.toIsCancelMul (G : Type u) [CommMagma G] [IsRightCancelMul G] :
    IsCancelMul G := { CommMagma.IsRightCancelMul.toIsLeftCancelMul G with }

end CommMagma

--281
/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
class MulOneClass (M : Type u) extends One M, Mul M where
  /-- One is a left neutral element for multiplication -/
  protected one_mul : ∀ a : M, 1 * a = a
  /-- One is a right neutral element for multiplication -/
  protected mul_one : ∀ a : M, a * 1 = a

--323
variable {M : Type u}

/-- The fundamental power operation in a monoid. `npowRec n a = a*a*...*a` n times.
Use instead `a ^ n`, which has better definitional behavior. -/
def npowRec [One M] [Mul M] : ℕ → M → M
  | 0, _ => 1
  | n + 1, a => npowRec n a * a

/-- The fundamental scalar multiplication in an additive monoid. `nsmulRec n a = a+a+...+a` n
times. Use instead `n • a`, which has better definitional behavior. -/
def nsmulRec [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => nsmulRec n a + a

attribute [to_additive existing] npowRec



--512
/--
An abbreviation for `npowRec` with an additional typeclass assumption on associativity
so that we can use `@[csimp]` to replace it with an implementation by repeated squaring
in compiled code.
-/
@[to_additive
"An abbreviation for `nsmulRec` with an additional typeclass assumptions on associativity
so that we can use `@[csimp]` to replace it with an implementation by repeated doubling in compiled
code as an automatic parameter."]
abbrev npowRecAuto {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) : M :=
  npowRec k m


--558
/-- A `Monoid` is a `Semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[to_additive]
class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  /-- Raising to the power of a natural number. -/
  protected npow : ℕ → M → M := npowRecAuto
  /-- Raising to the power `(0 : ℕ)` gives `1`. -/
  protected npow_zero : ∀ x, npow 0 x = 1 := by intros; rfl
  /-- Raising to the power `(n + 1 : ℕ)` behaves as expected. -/
  protected npow_succ : ∀ (n : ℕ) (x), npow (n + 1) x = npow n x * x := by intros; rfl



--758
/-!
### Design note on `DivInvMonoid`/`SubNegMonoid` and `DivisionMonoid`/`SubtractionMonoid`

Those two pairs of made-up classes fulfill slightly different roles.

`DivInvMonoid`/`SubNegMonoid` provides the minimum amount of information to define the
`ℤ` action (`zpow` or `zsmul`). Further, it provides a `div` field, matching the forgetful
inheritance pattern. This is useful to shorten extension clauses of stronger structures (`Group`,
`GroupWithZero`, `DivisionRing`, `Field`) and for a few structures with a rather weak
pseudo-inverse (`Matrix`).

`DivisionMonoid`/`SubtractionMonoid` is targeted at structures with stronger pseudo-inverses. It
is an ad hoc collection of axioms that are mainly respected by three things:
* Groups
* Groups with zero
* The pointwise monoids `Set α`, `Finset α`, `Filter α`

It acts as a middle ground for structures with an inversion operator that plays well with
multiplication, except for the fact that it might not be a true inverse (`a / a ≠ 1` in general).
The axioms are pretty arbitrary (many other combinations are equivalent to it), but they are
independent:
* Without `DivisionMonoid.div_eq_mul_inv`, you can define `/` arbitrarily.
* Without `DivisionMonoid.inv_inv`, you can consider `WithTop Unit` with `a⁻¹ = ⊤` for all `a`.
* Without `DivisionMonoid.mul_inv_rev`, you can consider `WithTop α` with `a⁻¹ = a` for all `a`
  where `α` non commutative.
* Without `DivisionMonoid.inv_eq_of_mul`, you can consider any `CommMonoid` with `a⁻¹ = a` for all
  `a`.

As a consequence, a few natural structures do not fit in this framework. For example, `ENNReal`
respects everything except for the fact that `(0 * ∞)⁻¹ = 0⁻¹ = ∞` while `∞⁻¹ * 0⁻¹ = 0 * ∞ = 0`.
-/

/-- In a class equipped with instances of both `Monoid` and `Inv`, this definition records what the
default definition for `Div` would be: `a * b⁻¹`.  This is later provided as the default value for
the `Div` instance in `DivInvMonoid`.

We keep it as a separate definition rather than inlining it in `DivInvMonoid` so that the `Div`
field of individual `DivInvMonoid`s constructed using that default value will not be unfolded at
`.instance` transparency. -/
def DivInvMonoid.div' {G : Type u} [Monoid G] [Inv G] (a b : G) : G := a * b⁻¹

/-- A `DivInvMonoid` is a `Monoid` with operations `/` and `⁻¹` satisfying
`div_eq_mul_inv : ∀ a b, a / b = a * b⁻¹`.

This deduplicates the name `div_eq_mul_inv`.
The default for `div` is such that `a / b = a * b⁻¹` holds by definition.

Adding `div` as a field rather than defining `a / b := a * b⁻¹` allows us to
avoid certain classes of unification failures, for example:
Let `Foo X` be a type with a `∀ X, Div (Foo X)` instance but no
`∀ X, Inv (Foo X)`, e.g. when `Foo X` is a `EuclideanDomain`. Suppose we
also have an instance `∀ X [Cromulent X], GroupWithZero (Foo X)`. Then the
`(/)` coming from `GroupWithZero.div` cannot be definitionally equal to
the `(/)` coming from `Foo.Div`.

In the same way, adding a `zpow` field makes it possible to avoid definitional failures
in diamonds. See the definition of `Monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  protected div := DivInvMonoid.div'
  /-- `a / b := a * b⁻¹` -/
  protected div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ := by intros; rfl
  /-- The power operation: `a ^ n = a * ··· * a`; `a ^ (-n) = a⁻¹ * ··· a⁻¹` (`n` times) -/
  protected zpow : ℤ → G → G := zpowRec npowRec
  /-- `a ^ 0 = 1` -/
  protected zpow_zero' : ∀ a : G, zpow 0 a = 1 := by intros; rfl
  /-- `a ^ (n + 1) = a ^ n * a` -/
  protected zpow_succ' (n : ℕ) (a : G) : zpow n.succ a = zpow n a * a := by
    intros; rfl
  /-- `a ^ -(n + 1) = (a ^ (n + 1))⁻¹` -/
  protected zpow_neg' (n : ℕ) (a : G) : zpow (Int.negSucc n) a = (zpow n.succ a)⁻¹ := by intros; rfl


#eval(H : MonoidHom)




variable {G : Type u} [Group G] (N : Subgroup G) [nN : N.Normal] {H : Type v} [Group H]
  {M : Type x} [Monoid M]

variable (φ : G →* H)

open MonoidHom

/-- The induced map from the quotient by the kernel to the codomain. -/
@[to_additive "The induced map from the quotient by the kernel to the codomain."]
def kerLift : G ⧸ ker φ →* H :=
  lift _ φ fun _g => mem_ker.mp

@[to_additive (attr := simp)]
theorem kerLift_mk (g : G) : (kerLift φ) g = φ g :=
  lift_mk _ _ _

@[to_additive (attr := simp)]
theorem kerLift_mk' (g : G) : (kerLift φ) (mk g) = φ g :=
  lift_mk' _ _ _

@[to_additive]
theorem kerLift_injective : Injective (kerLift φ) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ a = φ b) =>
    Quotient.sound' <| by rw [leftRel_apply, mem_ker, φ.map_mul, ← h, φ.map_inv, inv_mul_cancel]

-- Note that `ker φ` isn't definitionally `ker (φ.rangeRestrict)`
-- so there is a bit of annoying code duplication here
/-- The induced map from the quotient by the kernel to the range. -/
@[to_additive "The induced map from the quotient by the kernel to the range."]
def rangeKerLift : G ⧸ ker φ →* φ.range :=
  lift _ φ.rangeRestrict fun g hg => mem_ker.mp <| by rwa [ker_rangeRestrict]

@[to_additive]
theorem rangeKerLift_injective : Injective (rangeKerLift φ) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ.rangeRestrict a = φ.rangeRestrict b) =>
    Quotient.sound' <| by
      rw [leftRel_apply, ← ker_rangeRestrict, mem_ker, φ.rangeRestrict.map_mul, ← h,
        φ.rangeRestrict.map_inv, inv_mul_cancel]

@[to_additive]
theorem rangeKerLift_surjective : Surjective (rangeKerLift φ) := by
  rintro ⟨_, g, rfl⟩
  use mk g
  rfl



/-- **Noether's first isomorphism theorem** (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`. -/
@[to_additive "The first isomorphism theorem (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`."]
noncomputable def quotientKerEquivRange : G ⧸ ker φ ≃* range φ :=
  MulEquiv.ofBijective (rangeKerLift φ) ⟨rangeKerLift_injective φ, rangeKerLift_surjective φ⟩

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a homomorphism `φ : G →* H`
with a right inverse `ψ : H → G`. -/
@[to_additive (attr := simps) "The canonical isomorphism `G/(ker φ) ≃+ H` induced by a homomorphism
`φ : G →+ H` with a right inverse `ψ : H → G`."]
def quotientKerEquivOfRightInverse (ψ : H → G) (hφ : RightInverse ψ φ) : G ⧸ ker φ ≃* H :=
  { kerLift φ with
    toFun := kerLift φ
    invFun := mk ∘ ψ
    left_inv := fun x => kerLift_injective φ (by rw [Function.comp_apply, kerLift_mk', hφ])
    right_inv := hφ }
