/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.Preradical.Basic
public import Mathlib.CategoryTheory.Preradical.CokernelConstruction

/-!
# The colon construction on preradicals

Given preradicals `Φ` and `Ψ` on an abelian category `C`, this file defines their **colon** `Φ : Ψ`
in the sense of Stenström.  Categorically, `Φ : Ψ` is constructed objectwise as a pullback of the
canonical projection `Φ.π X : X ⟶ Φ.quotient.obj X` along the inclusion
`Ψ.ι.app (Φ.quotient.obj X) : Ψ.r.obj (Φ.quotient.obj X) ⟶ Φ.quotient.obj X`.

## Main definitions

* `Preradical.colon Φ Ψ : Preradical C` : The colon preradical `Φ : Ψ` of Stenström.
* `toColon Φ Ψ : Φ ⟶ Φ.colon Ψ` : The canonical inclusion of the left preradical into the colon.

## Main results

* `isIso_toColon_of_kills_quotients` : If `Ψ` kills all quotients in the sense that for all `X : C`
`Ψ.r.obj (Φ.quotient.obj X)` is the zero object, then the canonical inclusion `toColon Φ Ψ` is an
isomorphism.

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

category_theory, preradical, colon, pullback, torsion theory
-/

@[expose] public section

namespace CategoryTheory.Abelian

open CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C]

namespace Preradical

variable (Φ Ψ : Preradical C)

/-- The underlying endofunctor of the colon preradical `Φ : Ψ`. -/
noncomputable
def colonLeft : C ⥤ C where
  obj (X : C) := pullback (Φ.π X) (Ψ.ι.app (Φ.quotient.obj X))
  map {X Y : C} (f : X ⟶ Y) :=
    pullback.map
      (Φ.π X) (Ψ.ι.app (Φ.quotient.obj X))
      (Φ.π Y) (Ψ.ι.app (Φ.quotient.obj Y))
      (f)
      (Ψ.r.map (Φ.quotient.map f))
      (Φ.quotient.map f)
      (Eq.symm (π_naturality Φ f))
      (by simp)
  map_id := by simp
  map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) := by apply pullback.hom_ext <;> simp

@[simp]
lemma colonLeft_obj (X : C) :
    (colonLeft Φ Ψ).obj X = pullback (Φ.π X) (Ψ.ι.app (Φ.quotient.obj X)) :=
  rfl

@[simp]
lemma colonLeft_map {X Y : C} (f : X ⟶ Y) : (colonLeft Φ Ψ).map f =
    pullback.map (Φ.π X) (Ψ.ι.app (Φ.quotient.obj X)) (Φ.π Y) (Ψ.ι.app (Φ.quotient.obj Y)) (f)
        (Ψ.r.map (Φ.quotient.map f)) (Φ.quotient.map f) (Eq.symm (π_naturality Φ f)) (by simp) :=
  rfl

/-- The structure morphism `colonLeft Φ Ψ ⟶ 𝟭 C`. -/
noncomputable
def colonHom : colonLeft Φ Ψ ⟶ 𝟭 C where
  app (X : C) := pullback.fst (Φ.π X) (Ψ.ι.app (Φ.quotient.obj X))
  naturality := by simp

@[simp]
lemma colonHom_app (X : C) :
    (colonHom Φ Ψ).app X = pullback.fst (Φ.π X) (Ψ.ι.app (Φ.quotient.obj X)) :=
  rfl

/-- The colon preradical from Stenström, defined objectwise as the pullback of `Φ.π X` along
`Ψ.ι.app (Φ.quotient.obj X)`. -/
noncomputable
def colon : Preradical C where
  obj := {
    left := colonLeft Φ Ψ
    right := {as := ()}
    hom := colonHom Φ Ψ
  }
  property := by
    change Mono (colonHom Φ Ψ)
    letI : ∀ X : C, Mono ((colonHom Φ Ψ).app X) := fun X ↦ pullback.fst_of_mono
    exact NatTrans.mono_of_mono_app (colonHom Φ Ψ)

lemma colon_condition {Φ Ψ : Preradical C} {X : C} : (Φ.colon Ψ).ι.app X ≫ (cokernel.π Φ.ι).app X =
      (pullback.snd (Φ.π X) (Ψ.ι.app (Φ.quotient.obj X))) ≫ Ψ.ι.app (Φ.quotient.obj X) :=
  pullback.condition

/-- There is a morphism `Φ ⟶ (Φ.colon Ψ)` whose components are the morphisms induced by the
universal property for the pullback along `Φ.ι.app X : Φ.r.obj X ⟶ X` and the zero morphism
`Φ.r.obj X  ⟶ Ψ.r.obj (Φ.quotient.obj X)`. -/
noncomputable
def toColon : Φ ⟶ Φ.colon Ψ where
  hom := {
    left := {
      app {X : C} := pullback.lift (Φ.ι.app X) 0 (by simp)
      naturality {X Y : C} (f : X ⟶ Y) := by
        apply pullback.hom_ext <;> simp [colon]
    }
    right := {
      down := {
        down := by
          exact Discrete.ext_iff.mp rfl
      }
    }
    w := by
      ext X
      dsimp [colon, colonLeft, colonHom]
      simp
  }

/-- If for all `X : C`, `Ψ.r.obj (Φ.quotient.obj X)` is the zero object, then `Φ.toColon Ψ` is an
isomorphism. -/
theorem isIso_toColon_of_kills_quotients (h : ∀ X : C, IsZero (Ψ.r.obj (Φ.quotient.obj X))) :
    IsIso (Φ.toColon Ψ) := by
  letI : ∀ X : C, IsIso ((Φ.toColon Ψ).hom.left.app X) := by
    intro X
    have hsnd := IsZero.eq_zero_of_tgt (h X) (pullback.snd (Φ.π X) (Ψ.ι.app (Φ.quotient.obj X)))
    have hfst : pullback.fst (Φ.π X) (Ψ.ι.app (Φ.quotient.obj X)) ≫ Φ.π X = 0 := by
      rw [pullback.condition, hsnd, zero_comp]
    let inv : (Φ.colon Ψ).r.obj X ⟶ kernel (Φ.π X) :=
      kernel.lift (Φ.π X) (pullback.fst (Φ.π X) (Ψ.ι.app (Φ.quotient.obj X))) (by simpa using hfst)
    let hom : kernel (Φ.π X) ⟶ (Φ.colon Ψ).r.obj X :=
      pullback.lift (kernel.ι (Φ.π X)) 0 (by rw [kernel.condition, zero_comp])
    have hom_inv : hom ≫ inv = 𝟙 _ := by
      apply equalizer.hom_ext
      simp [hom, inv, Category.assoc]
    have inv_hom : inv ≫ hom = 𝟙 _ := by
      apply pullback.hom_ext
      · simp [hom, inv, Category.assoc]
      · simp only [hsnd, comp_zero]
    let e₁ : kernel (Φ.π X) ≅ (Φ.colon Ψ).r.obj X :=
    { hom := hom
      inv := inv
      hom_inv_id := hom_inv
      inv_hom_id := inv_hom }
    let e₂ : Φ.r.obj X  ≅ kernel (Φ.π X) := Φ.isoKernel_π X
    have hx : (Φ.toColon Ψ).hom.left.app X = (e₂ ≪≫ e₁).hom := by
      apply pullback.hom_ext
      · simp [Preradical.toColon, Preradical.colon, e₁, e₂, hom, Category.assoc]
      · simp [Preradical.toColon, Preradical.colon, e₁, e₂, hom, Category.assoc]
    simpa [hx] using (show IsIso ((e₂ ≪≫ e₁).hom) from by infer_instance)
  refine (MonoOver.isIso_iff_isIso_hom_left (Φ.toColon Ψ)).mpr ?_
  exact NatIso.isIso_of_isIso_app (Φ.toColon Ψ).hom.left

end Preradical
end CategoryTheory.Abelian
