/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module
public import Mathlib.CategoryTheory.Preradical.Basic

/-!
# Morphisms of preradicals

This file develops the morphisms between preradicals on an abelian category `C` and equips
`Preradical C` with a category structure.

A morphism of preradicals `μ : r ⟶ s` consists of a natural transformation
`μ.toNatTrans : r.toFunctor ⟶ s.toFunctor` whose components commute with the structure
morphisms for `r` and `s` in the sense that `μ.toNatTrans ≫ s.η = r.η`.

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

-/

@[expose] public section

open CategoryTheory

variable {C : Type*} [Category C] [Abelian C]

namespace Preradical

/-- A morphism of preradicals `μ : r ⟶ s` is a natural transformation `r.toFunctor ⟶ s.toFunctor`
whose components are compatible with the structure maps in the sense that
`μ.toNatTrans ≫ s.η = r.η`. -/
structure Hom (r s : Preradical C) extends (r.toFunctor ⟶ s.toFunctor) where
  w : toNatTrans ≫ s.η = r.η

instance : Category (Preradical C) where
  Hom := Hom
  id := fun r => Hom.mk (𝟙 r.toFunctor) (Category.id_comp r.η)
  comp {r s t} μ ν :=
    Hom.mk (μ.toNatTrans ≫ ν.toNatTrans : r.toFunctor ⟶ t.toFunctor) (by simp [ν.w, μ.w])
  id_comp := by simp
  comp_id := by simp
  assoc := by simp

namespace Hom

variable {r s t : Preradical C}
@[simp]
lemma w_app (μ : r ⟶ s) (X : C) : μ.app X ≫ s.η.app X = r.η.app X :=
   congrArg (fun (ν : r.toFunctor ⟶ 𝟭 C) => ν.app X) μ.w

@[ext]
lemma ext {μ ν : r ⟶ s} (h : μ.toNatTrans = ν.toNatTrans) : μ = ν := by
  cases μ; cases ν; cases h; rfl

@[simp, reassoc]
lemma comp_app (μ : r ⟶ s) (ν : s ⟶ t) (X : C) : (μ ≫ ν).app X = μ.app X ≫ ν.app X := by
  rfl

/-- A morphism of preradicals is epi whenever its components are. -/
theorem epi_of_epi_app (μ : r ⟶ s) [hμ : ∀ X : C, Epi (μ.app X)] :
    Epi μ where
  left_cancellation := by
    intro t _ _ hcomp
    ext X
    exact (cancel_epi (μ.app X)).mp (by simp [← Hom.comp_app, hcomp])

/-- A morphism of preradicals is mono whenever its components are. -/
theorem mono_of_mono_app (μ : r ⟶ s) [hμ : ∀ X : C, Mono (μ.app X)] :
    Mono μ where
  right_cancellation := by
    intro t _ _ hcomp
    ext X
    exact (cancel_mono (μ.app X)).mp (by simp [← Hom.comp_app, hcomp])

/-- A morphism of preradicals is an isomorphism whenever its components are. -/
theorem isIso_of_isIso_app (μ : r ⟶ s) [∀ X : C, IsIso (μ.app X)] :
    IsIso μ := by
  letI : IsIso (C := C ⥤ C) (μ.toNatTrans : r.toFunctor ⟶ s.toFunctor) :=
    NatIso.isIso_of_isIso_app μ.toNatTrans
  refine ⟨?_, ?_⟩
  · exact {
    app := (inv (C := C ⥤ C) (μ.toNatTrans : r.toFunctor ⟶ s.toFunctor)).app
    naturality := by
      intro X Y f
      exact (cancel_epi (μ.app X)).mp (by simp)
    w := by
      ext X
      simp only [Functor.id_obj, NatTrans.comp_app, NatIso.isIso_inv_app, IsIso.inv_comp_eq,
        Hom.w_app]}
  · constructor <;>
      ext X <;>
      simp only [Hom.comp_app, NatIso.isIso_inv_app, IsIso.hom_inv_id, IsIso.inv_hom_id] <;>
      rfl

end Hom

end Preradical
