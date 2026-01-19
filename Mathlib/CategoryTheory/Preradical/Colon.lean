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

variable {C : Type*} [Category C] [Abelian C]

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

lemma colon.condition {r s : Preradical C} {X : C} :
    r.colon_fst s X ≫ r.π X = r.colon_snd s X ≫ s.ι (r.coker X) :=
  pullback.condition

@[simp]
lemma ι_comp_f_comp_π (r : Preradical C) {X Y : C} (f : X ⟶ Y) :
    r.η.app X ≫ (f ≫ r.π Y) = 0 := by
  rw [r.π_naturality f, ← Category.assoc, ι_comp_π, zero_comp]

lemma colon_map_condition (r s : Preradical C) {X Y : C} (f : X ⟶ Y) :
    r.colon_fst s X ≫ f ≫ (r.π Y) =
    (r.colon_snd s X ≫ s.map (r.coker_map f)) ≫ s.ι (r.coker Y) := calc
  _ = r.colon_fst s X ≫ r.π X ≫ (r.coker_map f) := by
      rw [π_naturality]
  _ = r.colon_snd s X ≫ s.ι (r.coker X) ≫ (r.coker_map f) := by
      rw [← Category.assoc, colon.condition, Category.assoc]
  _ = (r.colon_snd s X ≫ s.map (r.coker_map f)) ≫ s.ι (r.coker Y) := by
      rw [s.ι_naturality (r.coker_map f), Category.assoc]

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
        (eq₂ := ι_naturality s (r.coker_map f))

@[simp]
lemma colon_map_id (r s : Preradical C) (X : C) :
    r.colon_map s (𝟙 X) = 𝟙 (colon_obj r s X) := by
  simp [colon_map]
  rfl

@[simp]
lemma colon_map_comp (r s : Preradical C) {L X Y : C} (f : L ⟶ X) (g : X ⟶ Y) :
    colon_map r s f ≫ colon_map r s g = colon_map r s (f ≫ g) := by
  apply pullback.hom_ext <;> simp [colon_map,Category.assoc]

@[reassoc]
lemma colon_map_fst (r s : Preradical C) {X Y : C} (f : X ⟶ Y) :
    colon_map r s f ≫ r.colon_fst s Y = r.colon_fst s X ≫ f := by
  simp [colon_map, colon_fst]

@[simp, reassoc]
lemma colon_map_snd (r s : Preradical C) {X Y : C} (f : X ⟶ Y) :
     r.colon_snd s X ≫ s.map (r.cokernel_of.map f) = colon_map r s f ≫ r.colon_snd s Y := by
  simp [colon_map, colon_snd]

/-- The colon preradical `r : s` from Stenström, defined objectwise as
the pullback of `r.π X` along `s.ι (r.coker X)`. -/
noncomputable
def colon (r s : Preradical C) : Preradical C where
  obj := fun X => colon_obj r s X
  map := fun f => colon_map r s f
  map_id := by simp only [colon_map_id, implies_true]
  map_comp := by
    intro L X Y f g
    apply pullback.hom_ext <;> simp [colon_map]
  η := {
    app := fun X => r.colon_fst s X
    naturality := fun X Y f => colon_map_fst r s f
  }
  mono_app := by infer_instance

@[simp]
lemma colon_fst_eq_η_app (r s : Preradical C) :
    ∀ X : C, (r.colon_fst s X) = (colon r s).η.app X :=
  fun _ => rfl

@[simp, reassoc]
lemma colon_fst_naturality (r s : Preradical C) {X Y : C} (f : X ⟶ Y) :
    (r.colon s).ι X ≫ f = (r.colon s).map f ≫ (r.colon s).ι Y := by
  exact ι_naturality (r.colon s) f

@[simp]
lemma colon_snd_naturality (r s : Preradical C) {X Y : C} (f : X ⟶ Y) :
  r.colon_map s f ≫ r.colon_snd s Y = (r.colon s).map f ≫ r.colon_snd s Y := rfl

/-- For all `r s : Preradical C`, there is always a morphism `r X ⟶ r.colon s X`. -/
noncomputable
def toColon_app (r s : Preradical C) (X : C) : r X ⟶ (r.colon s) X := by
  refine pullback.lift (r.ι X) 0 ?_
  simp only [coker_eq, ι_eq_app, ι_comp_π, zero_comp]

/-- The canonical morphisms `r ι X : r X ⟶ X` factor through
`r.toColon_app s X : r X ⟶ (r.colon s) X` via `(r.colon s).ι X = r.colon_fst s X`. -/
@[simp, reassoc]
lemma toColon_app_comp_colon_fst (r s : Preradical C) (X : C) :
    r.toColon_app s X ≫ (r.colon s).η.app X = r.ι X := by
  apply pullback.lift_fst

/-- By construction, `r.toColon_app s X ≫ r.colon_snd s X = 0`. -/
@[simp, reassoc]
lemma toColon_app_comp_colon_snd (r s : Preradical C) (X : C) :
    r.toColon_app s X ≫ r.colon_snd s X = 0 := by
  apply pullback.lift_snd

/-- The morphism `r.toColon_app X` is natural in `X`. -/
@[simp, reassoc]
lemma toColon_app_naturality (r s : Preradical C) {X Y : C} (f : X ⟶ Y) :
    r.map f ≫ r.toColon_app s Y = r.toColon_app s X ≫ (r.colon s).map f := by
  apply pullback.hom_ext
  · calc
    _ = (r.map f ≫ r.toColon_app s Y) ≫ (r.colon s).ι Y := rfl
    _ = r.map f ≫ r.toColon_app s Y ≫ (r.colon s).ι Y := by rw [Category.assoc]
    _ = r.map f ≫ r.ι Y := by
      simp only [ι_eq_app, toColon_app_comp_colon_fst, NatTrans.naturality, Functor.id_obj,
        Functor.id_map]
    _ = r.ι X ≫ f := by simp only [ι_eq_app, NatTrans.naturality, Functor.id_obj, Functor.id_map]
    _ = (r.toColon_app s X ≫ (r.colon s).ι X )≫ f := by
      simp only [ι_eq_app, toColon_app_comp_colon_fst]
    _ = r.toColon_app s X ≫ (r.colon s).ι X ≫ f := by rw [Category.assoc]
    _ = r.toColon_app s X ≫ (r.colon s).map f ≫ (r.colon s).ι Y := by
        rw [←(r.colon s).ι_naturality f]
    _ = (r.toColon_app s X ≫ (r.colon s).map f )≫ (r.colon s).ι Y := by rw [Category.assoc]
    _ = (r.toColon_app s X ≫ (r.colon s).map f) ≫ pullback.fst (r.π Y) (s.ι (r.coker Y)) :=
      rfl
  · calc
    _ = (r.map f ≫ r.toColon_app s Y) ≫ r.colon_snd s Y := rfl
    _ = r.map f ≫ r.toColon_app s Y ≫ r.colon_snd s Y := by simp
    _ = 0 := by simp
    _ = r.toColon_app s X ≫ r.colon_snd s X ≫ s.map (r.coker_map f) := by
      rw [← Category.assoc, toColon_app_comp_colon_snd, zero_comp]
    _ = r.toColon_app s X ≫ (r.colon s).map f ≫ r.colon_snd s Y := by
      simp only [coker_eq, coker_map_eq, colon_map_snd, colon_snd_naturality]
    _ = (r.toColon_app s X ≫ (r.colon s).map f) ≫ r.colon_snd s Y := by
      rw [Category.assoc]
    _ = (r.toColon_app s X ≫ (r.colon s).map f) ≫ pullback.snd (r.π Y) (s.ι (r.coker Y)) :=
      rfl

/-- The canonical morphism `r ⟶ r.colon s`.

Objectwise, this is the morphism `r.toColon_app s X : r X ⟶ (r.colon s) X`
induced by the universal property of the pullback defining the colon
preradical, factoring `r.ι X` through the first projection
`(r.colon s).ι X`. -/
noncomputable
def toColon (r s : Preradical C) : r ⟶ r.colon s where
  app := toColon_app r s
  naturality := fun {X Y} f => toColon_app_naturality r s f
  w := by
    ext X
    exact toColon_app_comp_colon_fst r s X

@[simp]
lemma zero_snd_of_zero_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (zero_right : IsZero Y) :
    pullback.snd f g = 0 :=
  IsZero.eq_zero_of_tgt zero_right _

@[simp]
lemma zero_condition_of_zero_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (zero_right : IsZero Y) :
    pullback.fst f g ≫ f = 0 :=
  by simp [pullback.condition,zero_right]

/-- In the pullback square
    P - - f' - - > Y
    |              |
    g'             g
    |              |
    v              V
    X - - f - - - >Z
  if `g = 0`, then `P ≅ kernel f`.
-/
noncomputable
def kernel_of_pullback_along_zero {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (zero_right : IsZero Y) :
    kernel f ≅ pullback f g := by
  exact {
    hom := pullback.lift (kernel.ι f) 0 (by simp),
    inv := kernel.lift f (pullback.fst f g) (zero_condition_of_zero_right _ _ zero_right),
    hom_inv_id := by
      apply equalizer.hom_ext; simp
    inv_hom_id := by
      apply pullback.hom_ext <;> simp [zero_right]
  }

@[simp, reassoc]
lemma kernel_of_pullback_along_zero_hom_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    (zero_right : IsZero Y) :
(kernel_of_pullback_along_zero f g zero_right).hom ≫ pullback.fst f g = kernel.ι f := by
  simp [kernel_of_pullback_along_zero]

@[simp, reassoc]
lemma kernel_of_pullback_along_zero_inv_hom_kernel_ι {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    (zero_right : IsZero Y) :
    (kernel_of_pullback_along_zero f g zero_right).inv ≫ kernel.ι f = pullback.fst f g := by
  simp [kernel_of_pullback_along_zero]

/-- If for all `X : C`, `s (r.coker X) = 0`, then `r.toColon s` is an isomorphism. -/
lemma isIso_toColon_of_kills_quotients (r s : Preradical C)
    (h : ∀ X : C, IsZero (s (r.coker X))) : IsIso (r.toColon s) := by
  refine Preradical.isIso_of_isIso_app (r.toColon s) ?_
  intro X

  let e₁ : kernel (r.π X) ≅ pullback (r.π X) (s.ι (r.coker X)) :=
    kernel_of_pullback_along_zero (r.π X) (s.ι (r.coker X)) (h X)
  let e₂ : r X ≅ kernel (r.π X) := r.kernelIso_π X

  let e : r X ≅ pullback (r.π X) (s.ι (r.coker X)) := e₂ ≪≫ e₁

  have : (r.toColon s).app X = e.hom := by
    apply pullback.hom_ext
    · calc
      _ = (r.toColon s).app X ≫ (r.colon s).ι X := rfl
      _ = r.ι X := by simp
      _ = e₂.hom ≫ kernel.ι (r.π X) := by rw [kernelIso_π_hom_ι]
      _ = e₂.hom ≫ (e₁.hom ≫ r.colon_fst s X) := by
          rw [←kernel_of_pullback_along_zero_hom_fst (r.π X) (s.ι (r.coker X)) (h X)]
          rfl
      _ = e₂.hom ≫ e₁.hom ≫ r.colon_fst s X := by rw [← Category.assoc]
      _ = (e₂.hom ≫ e₁.hom) ≫ r.colon_fst s X := by rw [←Category.assoc]
      _ = (e₂.hom ≫ e₁.hom) ≫ (r.colon s).ι X := by rfl
      _ = e.hom ≫ (r.colon s).ι X := by
        have : e₂.hom ≫ e₁.hom = e.hom := rfl
        rw [this]
    · simp [IsZero.eq_zero_of_tgt (h X)]
  rw [this]
  infer_instance

end Preradical
