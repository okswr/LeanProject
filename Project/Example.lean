/-
Copyright (c) 2018 Kevin Buzzard, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot
-/
-- This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.


import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Subgroup.MulOppositeLemmas
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs


/-!
# Quotients of groups by normal subgroups

This files develops the basic theory of quotients of groups by normal subgroups. In particular it
proves Noether's first and second isomorphism theorems.

## Main statements

* `QuotientGroup.quotientKerEquivRange`: Noether's first isomorphism theorem, an explicit
  isomorphism `G/ker φ → range φ` for every group homomorphism `φ : G →* H`.
* `QuotientGroup.quotientInfEquivProdNormalizerQuotient`: Noether's second isomorphism
  theorem, an explicit isomorphism between `H/(H ∩ N)` and `(HN)/N` given a subgroup `H`
  that lies in the normalizer `N_G(N)` of a subgroup `N` of a group `G`.
* `QuotientGroup.quotientQuotientEquivQuotient`: Noether's third isomorphism theorem,
  the canonical isomorphism between `(G / N) / (M / N)` and `G / M`, where `N ≤ M`.
* `QuotientGroup.comapMk'OrderIso`: The correspondence theorem, a lattice
  isomorphism between the lattice of subgroups of `G ⧸ N` and the sublattice
  of subgroups of `G` containing `N`.

## Tags

isomorphism theorems, quotient groups
-/

open Function
open scoped Pointwise

universe u v w x
namespace QuotientGroup

variable {G : Type u} [Group G] (N : Subgroup G) [nN : N.Normal] {H : Type v} [Group H]
  {M : Type x} [Monoid M]

open scoped Pointwise in
@[to_additive]
theorem sound (U : Set (G ⧸ N)) (g : N.op) :
    g • (mk' N) ⁻¹' U = (mk' N) ⁻¹' U := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  congr! 1
  exact Quotient.sound ⟨g⁻¹, rfl⟩

-- for commutative groups we don't need normality assumption

local notation " Q " => G ⧸ N

@[to_additive (attr := simp)]
theorem mk_prod {G ι : Type*} [CommGroup G] (N : Subgroup G) (s : Finset ι) {f : ι → G} :
    ((Finset.prod s f : G) : G ⧸ N) = Finset.prod s (fun i => (f i : G ⧸ N)) :=
  map_prod (QuotientGroup.mk' N) _ _

@[to_additive QuotientAddGroup.strictMono_comap_prod_map]
theorem strictMono_comap_prod_map :
    StrictMono fun H : Subgroup G ↦ (H.comap N.subtype, H.map (mk' N)) :=
  strictMono_comap_prod_image N
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

#min_imports
