/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.Preradical.Basic
public import Mathlib.CategoryTheory.Preradical.Hom

/-!
# A preorder on preradicals

In this file we put a preorder on `Preradical C` for an abelian category `C`.

We declare `r ≤ s` if there exists a morphism of preradicals `r ⟶ s`.  With
this relation, `Preradical C` forms a preorder.  We also prove a weak form of
antisymmetry: if `r ≤ s` and `s ≤ r`, then the underlying functors `r.toFunctor` and
`s.toFunctor` are isomorphic.

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]
-/

@[expose] public section

open CategoryTheory

variable {C : Type*} [Category C] [Abelian C]

namespace Preradical

/-- For `r s : Preradical C`, we declare `r ≤ s` if there exists a morphism of
preradicals `r ⟶ s`. -/
instance : LE (Preradical C) where
  le := fun r s => Nonempty (r ⟶ s)

/-- The class `Preradical C` forms a preorder under `≤`. -/
instance : Preorder (Preradical C) where
  le := (· ≤ ·)
  le_refl := fun r => ⟨𝟙 r⟩
  le_trans := fun r s t ⟨μ⟩ ⟨ν⟩ => ⟨μ ≫ ν⟩
  lt_iff_le_not_ge := by simp

/-- The relation `≤` is weakly antisymmetric. -/
def iso_of_le_antisymm (r s : Preradical C) (hrs : r ≤ s) (hsr : s ≤ r) :
   Nonempty (r ≅ s) := by
  obtain ⟨μ⟩ := hrs
  obtain ⟨ν⟩ := hsr
  have h₁ : μ ≫ ν = 𝟙 r  := by
    ext X
    exact (cancel_mono_id (r.ι X)).mp (by simp)
  have h₂ : ν ≫ μ = 𝟙 s := by
    ext X
    exact (cancel_mono_id (s.ι X)).mp (by simp)
  exact ⟨Iso.mk μ ν h₁ h₂⟩

@[simp]
lemma le_iff {r s : Preradical C} : r ≤ s ↔ Nonempty (r ⟶ s) := Iff.rfl

end Preradical
