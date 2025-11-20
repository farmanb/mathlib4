/-
Copyright (c) 2025 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
import Mathlib.CategoryTheory.Preradical.Basic

/-!
# Morphisms of preradicals

This file develops the morphisms between preradicals on an abelian category `C` and equips
`Preradical C` with a category structure.

A morphism of preradicals `μ : r ⟶ s` consists of a natural transformation
`μ.toNatTrans : r.F ⟶ s.F` whose components commute with the structure
morphisms `r.ι` and `s.ι`, in the sense that each square

r X — μ.app X –> s X
|                |
r.ι X            s.ι X
|                |
v                v
X  ––  𝟙 X  —–>  X

commutes.

This file is part of the `Preradical` hierarchy; see
`CategoryTheory/Preradical/Basic.lean` for an overview of the entire package.
-/

open CategoryTheory
open CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Preradical

/-- A morphism of preradicals `μ : r ⟶ s` is a natural transformation `r.F ⟶ s.F`
whose components are compatible with the structure maps in the sense that the square
r X — μ.app X –> s X
|                |
r.ι X            s.ι X
|                |
v                v
X  ––  𝟙 X  —–>  X
commutes. -/
structure Hom (r s : Preradical C) extends (r.F ⟶ s.F) where
  w : toNatTrans ≫ s.η = r.η

@[simp, reassoc]
lemma Hom.app_naturality {r s : Preradical C} (μ : Preradical.Hom r s) {X Y : C} (f : X ⟶ Y) :
    r.map f ≫ μ.app Y = μ.app X ≫ s.map f :=
  μ.naturality f

lemma Hom.ext {r s : Preradical C} {f g : Hom r s} (h : f.toNatTrans = g.toNatTrans) :
    f = g := by
  cases f; cases g; cases h; rfl

instance : Category (Preradical C) where
  Hom := Hom
  id := fun r => Hom.mk (𝟙 r.F) (Category.id_comp r.η)
  comp {r s t} μ ν :=
    Hom.mk (μ.toNatTrans ≫ ν.toNatTrans : r.F ⟶ t.F) (by simp [ν.w, μ.w])
  id_comp := by simp
  comp_id := by simp
  assoc := by simp

@[simp]
lemma Hom.w_app {r s : Preradical C} (μ : r ⟶ s) (X : C) :
    μ.app X ≫ s.ι X = r.ι X :=
  congrArg (fun (ν : r.F ⟶ 𝟭 C) => ν.app X) μ.w

@[ext]
lemma ext_hom {r s : Preradical C} {μ ν : r ⟶ s} (h : μ.toNatTrans = ν.toNatTrans) :
    μ = ν :=
  Preradical.Hom.ext h

@[simp, reassoc]
lemma Hom.comp_app {r s t : Preradical C} (μ : r ⟶ s) (ν : Hom s t) (X : C) :
    (μ ≫ ν).app X = μ.app X ≫ ν.app X := by
  rfl

theorem epi_of_epi_app {r s : Preradical C} (μ : r ⟶ s) [h_μ : ∀ X : C, Epi (μ.app X)] :
    Epi μ where
  left_cancellation := by
    intro t _ _ h_comp
    ext X
    exact (cancel_epi (μ.app X)).mp (by simp [← Hom.comp_app, h_comp])

theorem mono_of_mono_app {r s : Preradical C} (μ : r ⟶ s) [h_μ : ∀ X : C, Mono (μ.app X)] :
    Mono μ where
  right_cancellation := by
    intro t _ _ h_comp
    ext X
    exact (cancel_mono (μ.app X)).mp (by simp [← Hom.comp_app, h_comp])

theorem iso_of_iso_app {r s : Preradical C} (μ : r ⟶ s) (h_μ : ∀ X : C, IsIso (μ.app X)) :
    IsIso μ where
  out := by
    let ν : s ⟶ r := {
      app := fun X => inv (μ.app X)
      naturality := by
        intro X Y f
        exact (cancel_epi (μ.app X)).mp (by simp [← Category.assoc, ← Hom.app_naturality])
      w := by
        ext X
        simp
    }
    use ν
    constructor <;> (ext; simp [ν]; rfl)
end Preradical
