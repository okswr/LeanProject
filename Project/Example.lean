/-
Copyright (c) 2018 Kevin Buzzard, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot
-/
-- This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.

import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Quotients of groups by normal subgroups

This files develops the basic theory of quotients of groups by normal subgroups. In particular it
proves Noether's first and second isomorphism theorems.

## Main statements

* `QuotientGroup.quotientKerEquivRange`: Noether's first isomorphism theorem, an explicit
  isomorphism `G/ker φ → range φ` for every group homomorphism `φ : G →* H`.


## Tags

isomorphism theorems, quotient groups
-/

open Function

open MonoidHom

namespace QuotientGroup

variable {G : Type u} [Group G] {H : Type v} [Group H]

variable (φ : G →* H)




-- Note that `ker φ` isn't definitionally `ker (φ.rangeRestrict)`
-- so there is a bit of annoying code duplication here
/-- The induced map from the quotient by the kernel to the range. -/
@[to_additive "The induced map from the quotient by the kernel to the range."]
def rangeKerLift : G ⧸ ker φ →* φ.range :=
  lift _ φ.rangeRestrict fun g hg => mem_ker.mp <| by rwa [ker_rangeRestrict]


-- 説明のために，上記をタクティクスモードで証明
-- def : G ⧸ ker φ →* φ.range

example : G ⧸ ker φ →* φ.range := by
-- G ⧸ kerφ →* Imφ (G ⧸ kerφ) と Imφ が準同型であることを示す．
-- つまり，準同型写像 f : G ⧸ kerφ → Imφを与えられることを示す
  refine {
    -- 具体的に準同型写像を以下のように与える．
    -- 準同型写像 φ : G →* H に対して，終域を Imφ に制限した準同型写像 φ.rangeRestrict : G →* Imφ を与える．
    -- φ.rangeRestrict : G →* Imφ の商写像 G ⧸ kerφ →* Imφ を与える（あるいは，G →* Imφ にリフトするような写像 G ⧸ kerφ →* Imφを与える）
    -- kerφ が kerφ.rangeRestrict の部分群であることを与える．
    --  つまり g ∈ kerφ → g ∈ kerφ.rangeRestrict を示すために
    --  ∀ g ∈ kerφ, φ.rangeRestrict g = 1 を示す．
    --  これらは商写像として定義できることを示している．
    toFun := QuotientGroup.lift (ker φ) φ.rangeRestrict fun g hg => mem_ker.mp <| by
        rw [ker_rangeRestrict]
        exact hg
    -- この写像が準同型写像であることを示す．
    -- この写像が1を1に移すことを示す．
    map_one' := by
    -- モノイド準同型の写像は 1 を 1 に移す．
      rw [@MonoidHom.map_one]
    -- この写像が演算を保つことを示す．
    map_mul' := by
      dsimp
    -- モノイド準同型は演算について準同型である(マグマ準同型?)．
    -- 演算について準同型の写像は演算を保つ
      simp only [@MonoidHom.map_mul]
      simp only [implies_true]
  }




@[to_additive]
theorem rangeKerLift_injective : Injective (rangeKerLift φ) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ.rangeRestrict a = φ.rangeRestrict b) =>
    Quotient.sound' <| by
      rw [leftRel_apply, ← ker_rangeRestrict, mem_ker, φ.rangeRestrict.map_mul, ← h,
        φ.rangeRestrict.map_inv, inv_mul_cancel]


-- 説明のために，上記をタクティクスモードで証明

example : Injective (rangeKerLift φ) := by
  -- rangeKerLift φ が単射であることを示す．
  -- これはつまり，
  -- (rangeKerLift φ) q = (rangeKerLift φ) q' → q = q'
  -- であることを意味する．
  intro q q'
  intro eqf
  -- q,q' ∈ G⧸ker φをg,g'∈G,g kerφ = q,g' kerφ = q'で置き換える．
  obtain ⟨g,eqg⟩ := QuotientGroup.mk_surjective q
  obtain ⟨g',eqg'⟩ := QuotientGroup.mk_surjective q'
  -- q = q' にq = g kerφ , q' = g' kerφを代入する．
  rw [← eqg,← eqg']
  -- g kerφ = g' kerφ から商群G/kerφの等号の定義より g⁻¹ g' ∈ kerφ
  rw [@QuotientGroup.eq]
  simp only [mem_ker, map_mul, map_inv]
  -- simpを用いて(φ g)⁻¹を右へ移項した．
  refine inv_mul_eq_one.mpr ?_
  -- φ g = φ g'を示す
  calc
    φ g
      = rangeKerLift φ ↑g := by exact rfl     -- φ g = (rangeKerLift φ)g kerφ
      _= rangeKerLift φ q := by rw [eqg.symm] -- g kerφ = q
      _= rangeKerLift φ q' := by rw [eqf]     -- (rangeKerLift)q = (rangeKerLift)q'
      _= rangeKerLift φ (↑g') := by rw [eqg'] -- q' = g' kerφ
      _= φ g' := by exact rfl                 -- (rangeKerLift φ)g kerφ = φ g'


@[to_additive]
theorem rangeKerLift_surjective : Surjective (rangeKerLift φ) := by
  rintro ⟨_, g, rfl⟩
  use mk g
  rfl


-- 説明のために，上記をタクティクスモードで証明

example : Surjective (rangeKerLift φ) := by
  -- Surjective (rangeKerLift φ)
  -- (rangeKerLift φ)が全射であることを示す．
  -- これはつまり，
  -- ∀ b ∈ Imφ, ∃ a ∈ G ⧸ kerφ, (rangeKerLift φ) a = b
  -- であることを意味する．
  -- mem_rangeより y ∈ f.range ↔ ∃ x, f x = y なので
  -- ∃ x ∈ G, φ x = b, ∃ a ∈ G ⧸ kerφ, (rangeKerLift φ) a = b

  -- b = φ g と置く．つまり，∃ x, φ x = φ g
  rintro ⟨_, g, rfl⟩
  -- b = φ g に対して a = g kerφ を与える．
  use mk g
  -- (rangeKerLift φ) (g kerφ) = φ g より全射
  exact rfl




-- 群の準同型定理について示す．
-- def : G ⧸ ker φ ≃* range φ
-- G ⧸ ker φ →* range φ ,

/-- **Noether's first isomorphism theorem** (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`. -/
@[to_additive "The first isomorphism theorem (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`."]
noncomputable def quotientKerEquivRange : G ⧸ ker φ ≃* range φ :=
  MulEquiv.ofBijective (rangeKerLift φ) ⟨rangeKerLift_injective φ, rangeKerLift_surjective φ⟩


-- 説明のために，上記をタクティクスモードで証明

noncomputable example : G ⧸ ker φ ≃* range φ := by
  -- φ : G →* H，つまり φ は G から H へのモノイド準同型（つまり群準同型）写像である．
  -- φ : G →* H のリフト (rangeKerLift φ) : G ⧸ kerφ →* Imφは単射である
  have f := rangeKerLift_injective φ
  -- φ : G →* H のリフト (rangeKerLift φ) : G ⧸ kerφ →* Imφは全射である
  have g := rangeKerLift_surjective φ
  -- φ : G →* H のリフト (rangeKerLift φ) : G ⧸ kerφ →* Imφが全単射であることを示す
  have bj : Bijective (rangeKerLift φ) := by
    constructor
    --単射性を示す
    · exact f     --rangeKerLift_injectiveにて示した
    --全射性を示す
    · exact g     --rangeKerLift_surkectiveにて示した
  -- G ⧸ Kerφ から Imφ へ写す群同型写像の具体例として，(rangeKerLift φ)を与えたい
  -- この時，MulEquiv.ofBijective (rangeKerLift φ) bjは乗法について準同型かつ全単射ならば同型に型を置きなおすものである．
  -- すなわち，下記の二つの組を持つMulEquiv.ofBijective (rangeKerLift φ) bjは同型
  -- rangeKerLift φ : 乗法について準同型（実際にはモノイド準同型）
  -- bj : rangekerLift φは全単射
  use MulEquiv.ofBijective (rangeKerLift φ) bj
  dsimp
  -- 演算を保つことはrangeKerLift φがモノイド準同型であることから成り立つ
  simp only [@MonoidHom.map_mul]
  simp only [implies_true]




#min_imports
