/-
Copyright (c) 2024 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
import Mathlib.CategoryTheory.Preradical.Basic
import Mathlib.CategoryTheory.Preradical.Hom

/-!
# A preorder on preradicals

In this file we put a preorder on `Preradical C` for an abelian category `C`.

We declare `r ≤ s` if there exists a morphism of preradicals `r ⟶ s`.  With
this relation, `Preradical C` forms a preorder.  We also prove a weak form of
antisymmetry: if `r ≤ s` and `s ≤ r`, then the underlying functors `r.F` and
`s.F` are isomorphic.

This file is part of the `Preradical` hierarchy; see
`CategoryTheory/Preradical/Basic.lean` for an overview of the package.
-/

open CategoryTheory
open CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Preradical

/-- For `r s : Preradical C`, we declare `r ≤ s` if there exists a morphism of
preradicals `r ⟶ s`. -/
instance : LE (Preradical C) where
  le := fun r s => Nonempty (r ⟶ s)
  --le := fun r s => ∃ μ : r.F ⟶ s.F, μ ≫ s.η = r.η

/-- The class `Preradical C` forms a preorder under `≤`. -/
instance : Preorder (Preradical C) where
  le := (· ≤ ·)
  le_refl := fun r => ⟨𝟙 r⟩
  le_trans := fun r s t ⟨μ⟩ ⟨ν⟩ => ⟨μ ≫ ν⟩
  lt_iff_le_not_ge := by simp

/-- The relation `≤` is weakly antisymmetric. -/
theorem iso_of_antisymm (r s : Preradical C) (r_le_s : r ≤ s) (s_le_r : s ≤ r) :
    Nonempty (r ≅ s) := by
  obtain ⟨μ⟩ := r_le_s
  obtain ⟨ν⟩ := s_le_r

  have h₁ : μ ≫ ν = 𝟙 r  := by
    ext X
    exact (cancel_mono_id (r.ι X)).mp (by simp)
  have h₂ : ν ≫ μ = 𝟙 s := by
    ext X
    exact (cancel_mono_id (s.ι X)).mp (by simp)

  exact ⟨Iso.mk μ ν h₁ h₂⟩
end Preradical
