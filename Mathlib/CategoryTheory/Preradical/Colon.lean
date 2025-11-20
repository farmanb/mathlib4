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
  `s.ι (r.coker X)`.
* `Preradical.colon_fst r s X` : The first projection `colon_obj r s X ⟶ X`.
* `Preradical.colon_snd r s X` : The second projection `colon_obj r s X ⟶ s (r.coker X)`.
* `Preradical.colon_map r s f` : The induced map `colon_obj r s X ⟶ colon_obj r s Y`
  for a morphism `f : X ⟶ Y`.
* `Preradical.colon r s : Preradical C` : The colon preradical, given objectwise by
  `colon_obj r s` and inclusion `colon_fst r s`.

## Tags

category_theory, preradical, colon, pullback
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Preradical

/-- The object used to define the colon preradical `r : s` at an object `X`,
given by the pullback of `r.π X` along `s.ι (r.coker X)`. -/
noncomputable
def colon_obj (r s : Preradical C) (X : C) : C :=
  pullback (r.π X) (s.ι (r.coker X))

/-- The first projection from the colon object `colon_obj r s X` to `X`. -/
noncomputable
def colon_fst (r s : Preradical C) (X : C) : colon_obj r s X ⟶ X :=
  pullback.fst (r.π X) (s.ι (r.coker X))

/-- The second projection from the colon object `colon_obj r s X` to `s (r.coker X)`. -/
noncomputable
def colon_snd (r s : Preradical C) (X : C) : colon_obj r s X ⟶ s (r.coker X) :=
  pullback.snd (r.π X) (s.ι (r.coker X))

noncomputable
instance (r s : Preradical C) (X : C) : Mono (r.colon_fst s X) :=
  pullback.fst_of_mono

instance colon_snd_epi (r s : Preradical C) (X : C) : Epi (r.colon_snd s X) :=
  Abelian.epi_pullback_of_epi_f (r.π X) (s.ι (r.coker X))

@[simp, reassoc]
lemma colon.condition {r s : Preradical C} {X : C} :
    r.colon_fst s X ≫ r.π X = r.colon_snd s X ≫ s.ι (r.coker X) :=
  pullback.condition

@[simp]
lemma ι_comp_f_comp_π (r : Preradical C) {X Y : C} (f : X ⟶ Y) :
    r.ι X ≫ (f ≫ r.π Y) = 0 := by
  rw [π_naturality, ← Category.assoc, ι_comp_π, zero_comp]

@[simp]
lemma colon_map_condition (r s : Preradical C) {X Y : C} (f : X ⟶ Y) :
    (r.colon_fst s X ≫ f) ≫ (r.π Y) =
    (r.colon_snd s X ≫ s.map (r.coker_map f)) ≫ s.ι (r.coker Y) := calc
  _ = r.colon_fst s X ≫ r.π X ≫ (r.coker_map f) := by
      rw [Category.assoc, π_naturality]
  _ = r.colon_snd s X ≫ s.ι (r.coker X) ≫ (r.coker_map f) := by
      rw [← Category.assoc, colon.condition, Category.assoc]
  _ = (r.colon_snd s X ≫ s.map (r.coker_map f)) ≫ s.ι (r.coker Y) := by
      rw [← ι_naturality, Category.assoc]

@[simp, reassoc]
lemma colon_map_id (r s : Preradical C) (X : C) :
    pullback.map (r.π X) (s.ι (r.coker X))
      (r.π X) (s.ι (r.coker X))
      (𝟙 X) (𝟙 (s (r.coker X))) (𝟙 (r.coker X))
      (by simp) (by simp) = 𝟙 (colon_obj r s X) :=
  pullback.map_id

/-- The morphism on colon objects induced by a morphism `f : X ⟶ Y`. -/
noncomputable
def colon_map (r s : Preradical C) {X Y : C} (f : X ⟶ Y) :
colon_obj r s X ⟶ colon_obj r s Y :=
  pullback.map
        (f₁ := r.π X) (f₂ := s.ι (r.coker X))
        (g₁ := r.π Y) (g₂ := s.ι (r.coker Y))
        (i₁ := f)
        (i₂ := s.map (r.coker_map f))
        (i₃ := r.coker_map f)
        (eq₁ := Eq.symm (π_naturality r f))
        (eq₂ := Eq.symm (ι_naturality s (r.coker_map f)))

@[simp]
lemma colon_map_comp (r s : Preradical C) {L X Y : C} (f : L ⟶ X) (g : X ⟶ Y) :
    colon_map r s f ≫ colon_map r s g = colon_map r s (f ≫ g) := by
  apply pullback.hom_ext <;> simp [colon_map,Category.assoc]

@[simp, reassoc]
lemma colon_map_fst (r s : Preradical C) {X Y : C} (f : X ⟶ Y) :
    colon_map r s f ≫ r.colon_fst s Y = r.colon_fst s X ≫ f := by
  simp [colon_map, colon_fst]

@[simp, reassoc]
lemma colon_map_snd (r s : Preradical C) {X Y : C} (f : X ⟶ Y) :
    r.colon_snd s X ≫ s.map (r.coker_map f) = colon_map r s f ≫ r.colon_snd s Y := by
  simp [colon_map, colon_snd]

/-- The colon preradical `r : s` from Stenström, defined objectwise as
the pullback of `r.π X` along `s.ι (r.coker X)`. -/
noncomputable
def colon (r s : Preradical C) : Preradical C where
  F := {
    obj := fun X => colon_obj r s X
    map := fun f => colon_map r s f
    map_id := by
      intro X
      simp [colon_map, ← colon_map_id]
    map_comp := by
      intro L X Y f g
      apply pullback.hom_ext <;> simp [colon_map]
  }
  η := {
    app := fun X => r.colon_fst s X
    naturality := by
      intro X Y f
      simp
  }
  mono_app := by infer_instance

@[simp, reassoc]
lemma colon_map_eq (r s : Preradical C) {X Y : C} (f : X ⟶ Y) :
    (r.colon s).map f = colon_map r s f :=
  rfl

@[simp]
lemma colon_fst_eq_η_app (r s : Preradical C) :
    ∀ X : C, (r.colon_fst s X) = (colon r s).η.app X :=
  fun _ => rfl

@[simp]
lemma colon_fst_eq_ι (r s : Preradical C) :
    ∀ X : C, (r.colon_fst s X) = (colon r s).ι X := by
  intro X
  rw [colon_fst_eq_η_app, ι_eq_app]

@[simp, reassoc]
lemma colon_fst_naturality (r s : Preradical C) {X Y : C} (f : X ⟶ Y) :
    (r.colon s).ι X ≫ f = (r.colon s).map f ≫ (r.colon s).ι Y := by
  simp [← ι_naturality]

@[simp]
lemma colon_snd_naturality (r s : Preradical C) {X Y : C} (f : X ⟶ Y) :
    r.colon_snd s X ≫ s.map (r.coker_map f) = (r.colon s).map f ≫ r.colon_snd s Y :=
  colon_map_snd r s f

end Preradical
