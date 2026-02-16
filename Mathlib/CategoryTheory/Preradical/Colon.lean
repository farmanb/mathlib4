/-
Copyright (c) 2025 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.Preradical.Basic
public import Mathlib.CategoryTheory.Preradical.Hom
public import Mathlib.CategoryTheory.Preradical.CokernelConstruction

/-!
# The colon construction on preradicals

Given preradicals `r` and `s` on an abelian category `C`, this file defines
their **colon** `r : s` in the sense of Stenström.  Categorically, `r : s` is
constructed objectwise as a pullback of the cokernel projection of `r` along
the inclusion of `s`.

This file is part of the `Preradical` hierarchy; see
`CategoryTheory/Preradical/Basic.lean` for an overview of the package.

## Main definitions

* `Preradical.colon_obj r s X` : The object `X` equipped with the pullback over `r.π X` and
  `s.ι (r.quotient.obj X)`.
* `Preradical.colon_fst r s X` : The first projection `colon_obj r s X ⟶ X`.
* `Preradical.colon_snd r s X` : The second projection `colon_obj r s X ⟶ s (r.quotient.obj X)`.
* `Preradical.colon_map r s f` : The induced map `colon_obj r s X ⟶ colon_obj r s Y`
  for a morphism `f : X ⟶ Y`.
* `Preradical.colon r s : Preradical C` : The colon preradical, given objectwise by
  `colon_obj r s` and inclusion `colon_fst r s`.

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

category_theory, preradical, colon, pullback, torsion theory
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C]

namespace Preradical

/-- The colon preradical `r : s` from Stenström, defined objectwise as
the pullback of `r.π X` along `s.ι (r.quotient.obj X)`. -/
noncomputable
def colon (r s : Preradical C) : Preradical C where
  obj (X : C):= pullback (r.π X) (s.ι (r.quotient.obj X))
  map {X Y : C} (f : X ⟶ Y) := pullback.map
    (r.π X) (s.ι (r.quotient.obj X))
    (r.π Y) (s.ι (r.quotient.obj Y))
    (f)
    (s.map (r.quotient.map f))
    (r.quotient.map f)
    (Eq.symm (π_naturality r f))
    (by simp)
  map_id := by simp
  map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) := by
    apply pullback.hom_ext <;> simp
  η := {
    app (X : C) := pullback.fst (r.π X) (s.ι (r.quotient.obj X))
    naturality {X Y : C} (f : X ⟶ Y) := by simp
  }
  mono_app := by infer_instance

/-- There is a morphism `r ⟶ (r.colon s)` whose components are the morphisms induced by the
universal property for the pullback along `r.ι X : r X ⟶ X` and the zero morphism
`r X ⟶ s.obj (r.quotient.obj X)`. -/
noncomputable
def toColon (r s : Preradical C) : r ⟶ r.colon s where
  app {X : C} := pullback.lift (r.ι X) 0 (by simp)
  naturality {X Y : C} (f : X ⟶ Y) := by
    apply pullback.hom_ext <;> simp [Preradical.colon, Category.assoc]
  w := by
    ext X
    simp [Preradical.colon]


/-- If for all `X : C`, `s (r.quotient.obj X) = 0`, then `r.toColon s` is an isomorphism. -/
theorem isIso_toColon_of_kills_quotients (r s : Preradical C)
    (h : ∀ X : C, IsZero (s (r.quotient.obj X))) : IsIso (r.toColon s) := by
  refine Preradical.Hom.isIso_of_isIso_app (r.toColon s) ?_
  intro X

  have hsnd := IsZero.eq_zero_of_tgt (h X) (pullback.snd (r.π X) (s.ι (r.quotient.obj X)))

  have hfst : pullback.fst (r.π X) (s.ι (r.quotient.obj X)) ≫ r.π X = 0 := by
    rw [pullback.condition, hsnd, zero_comp]

  let inv : (r.colon s) X ⟶ kernel (r.π X) :=
    kernel.lift (r.π X) (pullback.fst (r.π X) (s.ι (r.quotient.obj X))) (by simpa using hfst)

  let hom : kernel (r.π X) ⟶ (r.colon s) X :=
    pullback.lift (kernel.ι (r.π X)) 0 (by rw [kernel.condition, zero_comp])

  have hom_inv : hom ≫ inv = 𝟙 _ := by
    apply equalizer.hom_ext
    simp [hom, inv, Category.assoc]

  have inv_hom : inv ≫ hom = 𝟙 _ := by
    apply pullback.hom_ext
    · simp [hom, inv, Category.assoc]
    · simp only [hsnd, comp_zero]
  let e₁ : kernel (r.π X) ≅ (r.colon s) X :=
  { hom := hom
    inv := inv
    hom_inv_id := hom_inv
    inv_hom_id := inv_hom }

  let e₂ : r X ≅ kernel (r.π X) := r.isoKernel_π X

  have hx : (r.toColon s).app X = (e₂ ≪≫ e₁).hom := by
    apply pullback.hom_ext
    · simp [Preradical.toColon, Preradical.colon, e₁, e₂, hom, Category.assoc]
    · simp [Preradical.toColon, Preradical.colon, e₁, e₂, hom, Category.assoc]

  simpa [hx] using (show IsIso ((e₂ ≪≫ e₁).hom) from by infer_instance)

end Preradical
