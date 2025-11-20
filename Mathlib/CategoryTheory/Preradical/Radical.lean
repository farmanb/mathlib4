/-
Copyright (c) 2024 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/

import Mathlib.CategoryTheory.Preradical.Basic
import Mathlib.CategoryTheory.Preradical.Hom
import Mathlib.CategoryTheory.Preradical.Colon
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Radicals of preradicals

In this file we define what it means for a preradical `r : Preradical C` on an
abelian category `C` to be *radical*, and we introduce a bundled `Radical C`
structure.

Following Stenström, a preradical `r` is called radical if `r : r = r`, where
`r : r` is the colon preradical defined via a pullback.  We encode this as the
existence of an isomorphism `(r : r) ≅ r`.  We then prove a basic
characterization of radical preradicals in terms of the vanishing of `r` on the
quotients `r.coker X`.

This file is part of the `Preradical` hierarchy; see
`CategoryTheory/Preradical/Basic.lean` for an overview of the package.

## Main definitions

* `Preradical.IsRadical r` :
  The proposition that a preradical `r` is radical, i.e. that `(r : r) ≅ r`.

* `Preradical.Radical C` :
  The type of radicals on `C`, given by a preradical together with a proof
  that it is radical.

## Main results

* `Preradical.isRadical_iff_kills_quotients` :
  A preradical `r` is radical if and only if `r (r.coker X)` is zero for all
  objects `X : C`.

Along the way we construct an auxiliary isomorphism identifying a pullback
along a zero map with a kernel, which is used in the proof of the
characterization theorem.

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]

## Tags

category_theory, preradical, radical, torsion, abelian
-/

open CategoryTheory
open CategoryTheory.Limits

namespace Preradical

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A preradical `r` is *radical* if `r : r = r`. -/
def IsRadical (r : Preradical C) : Prop := Nonempty ((Preradical.colon r r) ≅ r)

structure Radical extends Preradical C where
    colon_stable : IsRadical toPreradical

@[simp]
lemma zero_snd_of_zero_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (zero_right : IsZero Y) :
pullback.snd f g = 0 := IsZero.eq_zero_of_tgt zero_right _

@[simp]
lemma zero_condition_of_zero_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (zero_right : IsZero Y) :
pullback.fst f g ≫ f = 0 := by simp[pullback.condition,zero_right]

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
  have w₁ : kernel.ι f ≫ f = 0 ≫ g := by rw[zero_comp, kernel.condition]
  exact {
    hom := pullback.lift (kernel.ι f) 0 (by simp),
    inv := kernel.lift f (pullback.fst f g) (zero_condition_of_zero_right _ _ zero_right),
    hom_inv_id := by
      apply equalizer.hom_ext; simp
    inv_hom_id := by
      apply pullback.hom_ext <;> simp[zero_right]
  }

@[simp, reassoc]
lemma kernel_of_pullback_along_zero_hom_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
(zero_right : IsZero Y) :
(kernel_of_pullback_along_zero f g zero_right).hom ≫ pullback.fst f g = kernel.ι f := by
  simp [kernel_of_pullback_along_zero]

@[simp, reassoc]
lemma kernel_of_pullback_along_zero_inv_hom_kernel.ι {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
(zero_right : IsZero Y) :
(kernel_of_pullback_along_zero f g zero_right).inv ≫ kernel.ι f = pullback.fst f g := by
  simp[kernel_of_pullback_along_zero]

/-- For all `r s : Preradical C`, there is always a morphism `r ⟶ r.colon s`. -/
noncomputable
def toColon (r s : Preradical C) (X : C) : r X ⟶ (r.colon s) X :=
  pullback.lift (r.ι X) 0 (by rw[zero_comp,ι_comp_π])

/-- The canonical morphisms `r ι X : r X ⟶ X` factor through `r.toColon s X : r X ⟶ (r.colon s) X`
via `(r.colon s).ι X = r.colon_fst s X`. -/
@[simp, reassoc]
lemma toColon_comp_colon_fst (r s : Preradical C) (X : C) :
r.toColon s X ≫ (r.colon s).ι X = r.ι X := by apply pullback.lift_fst

/-- By construction, `r.toColon s X ≫ r.colon_snd s X = 0`. -/
@[simp, reassoc]
lemma toColon_comp_colon_snd (r s : Preradical C) (X : C) :
r.toColon s X ≫ r.colon_snd s X = 0 := by apply pullback.lift_snd

/-- The morphism `r.toColon X` is natural in `X`. -/
@[simp, reassoc]
lemma toColon_naturality (r s : Preradical C) {X Y : C} (f : X ⟶ Y) :
  r.map f ≫ r.toColon s Y = r.toColon s X ≫ (r.colon s).map f := by
  apply pullback.hom_ext
  · calc
    _= (r.map f ≫ r.toColon s Y) ≫ (r.colon s).ι Y := rfl
    _= r.map f ≫ r.toColon s Y ≫ (r.colon s).ι Y := by rw[Category.assoc]
    _= r.map f ≫ r.ι Y := by rw[toColon_comp_colon_fst r s Y]
    _= r.ι X ≫ f := ι_naturality r f
    _= (r.toColon s X ≫ (r.colon s).ι X )≫ f := by rw[toColon_comp_colon_fst]
    _= r.toColon s X ≫ (r.colon s).ι X ≫ f := by rw[Category.assoc]
    _= r.toColon s X ≫ (r.colon s).map f ≫ (r.colon s).ι Y := by rw[←(r.colon s).ι_naturality f]
    _= (r.toColon s X ≫ (r.colon s).map f )≫ (r.colon s).ι Y := by rw[Category.assoc]
    _= (r.toColon s X ≫ (r.colon s).map f) ≫ pullback.fst (r.π Y) (s.ι (r.coker Y)) := rfl
  · calc
    _= (r.map f ≫ r.toColon s Y) ≫ r.colon_snd s Y := rfl
    _= r.map f ≫ r.toColon s Y ≫ r.colon_snd s Y := by simp
    _= 0 := by simp
    _= r.toColon s X ≫ r.colon_snd s X ≫ s.map (r.coker_map f) := by simp[← Category.assoc]
    _= r.toColon s X ≫ (r.colon s).map f ≫ r.colon_snd s Y := by rw[colon_snd_naturality]
    _= (r.toColon s X ≫ (r.colon s).map f) ≫ r.colon_snd s Y := by rw[Category.assoc]
    _= (r.toColon s X ≫ (r.colon s).map f) ≫ pullback.snd (r.π Y) (s.ι (r.coker Y)) := rfl



theorem isRadical_iff_kills_quotients (r : Preradical C) :
  IsRadical r ↔ ∀ X, IsZero (r (r.coker X)) := by
    constructor
    · intro h X
      apply IsZero.of_mono_eq_zero (r.ι (r.coker X))
      apply zero_of_epi_comp (colon_snd r r X)

      obtain ⟨μ,_,h_μ,_⟩ := h
      calc
      _= r.colon_fst r X ≫ r.π X := Eq.symm colon.condition
      _= (μ.toNatTrans ≫ r.η).app X ≫ r.π X := by
        rw[μ.w,colon_fst_eq_η_app]
      _= (μ.app X ≫ r.ι X) ≫ r.π X := by
        rw[NatTrans.comp_app,ι_eq_app]
      _= μ.app X ≫ r.ι X ≫ r.π X := by rw[Category.assoc]
      _= 0 := by rw[ι_comp_π, comp_zero]
    · intro h
      apply Nonempty.intro
      let μ : r ⟶ r.colon r := {
        app := fun X => r.toColon r X
        naturality := fun X Y f => r.toColon_naturality r f
        w := by
          ext; simp
      }
      symm

      haveI iso_μ : IsIso μ := by
        apply (Preradical.iso_of_iso_app μ)
        intro X
        let e₁ : kernel (r.π X) ≅ pullback (r.π X) (r.ι (r.coker X)) :=
          kernel_of_pullback_along_zero (r.π X) (r.ι (r.coker X)) (h X)
        let e₂ : r X ≅ kernel (r.π X) := r.kernelIso_π X

        let e : r X ≅ pullback (r.π X) (r.ι (r.coker X)) := e₂ ≪≫ e₁

        have : μ.app X = e.hom := by
          apply pullback.hom_ext
          · calc
            _= μ.app X ≫ (r.colon r).ι X := rfl
            _= r.ι X := by simp
            _= e₂.hom ≫ kernel.ι (r.π X) := by rw[kernelIso_π_hom_ι]
            _= e₂.hom ≫ (e₁.hom ≫ r.colon_fst r X) := by
              rw[←kernel_of_pullback_along_zero_hom_fst (r.π X) (r.ι (r.coker X)) (h X)]
              rfl
            _= e₂.hom ≫ e₁.hom ≫ r.colon_fst r X := by rw[← Category.assoc]
            _= (e₂.hom ≫ e₁.hom) ≫ r.colon_fst r X := by rw[←Category.assoc]
            _= (e₂.hom ≫ e₁.hom) ≫ (r.colon r).ι X := by rfl
            _= e.hom ≫ (r.colon r).ι X := by
              have : e₂.hom ≫ e₁.hom = e.hom := rfl
              rw[this]
          · simp[IsZero.eq_zero_of_tgt (h X)]
        rw[this]
        infer_instance
      exact asIso μ
end Preradical

 /- let e₁ := kernel_of_pullback_along_zero (r.π X) (r.ι (r.coker X)) (h X)
      let e₂ := kernelIso_π r X
      let e : r X ≅ r.colon r X := e₂ ≪≫ e₁.symm -/
      /- have : ∀ X : C, r.colon_snd r X = 0 := by
        intro X
        exact zero_snd_of_zero_right (r.π X) (r.ι (r.coker X)) (h X) -/

      /- have w_pullback : ∀ X : C, r.ι X ≫ r.π X = 0 ≫ r.ι (r.coker X) := by
        intro X
        rw[zero_comp,ι_comp_π]

      let u : ∀ X : C, r X ⟶ r.colon r X := fun X => pullback.lift (r.ι X) 0 (w_pullback X)
      have h_u : ∀ X : C, u X ≫ (r.colon r).ι X = r.ι X:= by
        intro X
        apply r.toColon_comp_colon_fst r X -/
        --apply pullback.lift_fst

       /- have : ∀ X : C, IsIso (μ.app X) := by
          intro X

          --change IsIso (u X)

          have w_kernel : (r.colon r).ι X ≫ r.π X = 0 := by
            change r.colon_fst r X ≫ r.π X = 0
            calc r.colon_fst r X ≫ r.π X
              _= (r.colon_snd r X) ≫ r.ι (r.coker X) := pullback.condition
              _= (r.colon_snd r X) ≫ 0 := by rw[IsZero.eq_zero_of_src (h X) (r.ι (r.coker X))]
              _= 0 := by rw[comp_zero]

          let v' : (r.colon r X) ⟶ kernel (r.π X) :=
             kernel.lift (r.π X) ((r.colon r).ι X) w_kernel
          have h_v' : v' ≫ kernel.ι (r.π X) = (r.colon r).ι X :=
            kernel.lift_ι (r.π X) ((r.colon r).ι X) w_kernel

          let e := kernelIso_π r X

          let v : (r.colon r X) ⟶ r X := v' ≫ e.inv
          have : e.inv ≫ e.hom = 𝟙 _ := by exact e.inv_hom_id
          have uv_id : u X ≫ v = 𝟙 (r X) := by
            apply (cancel_mono_id (r.ι X)).mp
            calc (u X ≫ v) ≫ r.ι X
              _= u X ≫ v ≫ e.hom ≫ kernel.ι (r.π X) := by
                rw[Category.assoc,←(kernelIso_π_hom_ι r X)]
              _= u X ≫ v' ≫ e.inv ≫ e.hom ≫ kernel.ι (r.π X) := by
                simp[v]
              _= u X ≫ v' ≫ kernel.ι (r.π X) := by simp
              _= u X ≫ (r.colon r).ι X := by rw[h_v']
              _= r.ι X := by rw[h_u X]
          have vu_id : v ≫ u X = 𝟙 _ := by
            apply pullback.hom_ext
            · rw[Category.id_comp]
              change (v ≫ u X) ≫ (r.colon r).ι X = (r.colon r).ι X
              calc (v ≫ u X) ≫ (r.colon r).ι X
              _= v ≫ u X ≫ (r.colon r).ι X := by rw[Category.assoc]
              _= v ≫ r.ι X := by rw[h_u X]
              _= (v' ≫ e.inv) ≫ (r.ι X) := by rfl
              _= (v' ≫ e.inv) ≫ (e.hom ≫ kernel.ι (r.π X)) := by rw[kernelIso_π_hom_ι]
              _= v' ≫ kernel.ι (r.π X) := by simp
              _= (r.colon r).ι X := by rw[h_v']
            · exact
              IsZero.eq_of_tgt (h X) ((v ≫ u X) ≫ pullback.snd (r.π X) (r.ι (r.coker X)))
                (𝟙 ((fun X ↦ (r.colon r).F.obj X) X) ≫ pullback.snd (r.π X) (r.ι (r.coker X)))
          use v
          sorry
        exact this
      exact asIso μ -/

/- · calc (r.map f ≫ r.toColon s Y) ≫ pullback.fst (r.π Y) (s.ι (r.coker Y))
    _= (r.map f ≫ r.toColon s Y) ≫ (r.colon s).ι Y := rfl
    _= r.map f ≫ r.toColon s Y ≫ (r.colon s).ι Y := by rw[Category.assoc]
    _= r.map f ≫ r.ι Y := by rw[toColon_comp_colon_fst r s Y]
    _= r.ι X ≫ f := ι_naturality r f
    _= (r.toColon s X ≫ (r.colon s).ι X )≫ f := by rw[toColon_comp_colon_fst]
    _= r.toColon s X ≫ (r.colon s).ι X ≫ f := by rw[Category.assoc]
    _= r.toColon s X ≫ (r.colon s).map f ≫ (r.colon s).ι Y := by rw[←(r.colon s).ι_naturality f]
    _= (r.toColon s X ≫ (r.colon s).map f )≫ (r.colon s).ι Y := by rw[Category.assoc]
    _= (r.toColon s X ≫ (r.colon s).map f) ≫ pullback.fst (r.π Y) (s.ι (r.coker Y)) := rfl
  · calc (r.map f ≫ r.toColon s Y) ≫ pullback.snd (r.π Y) (s.ι (r.coker Y))
      _= r.map f ≫ r.toColon s Y ≫ pullback.snd (r.π Y) (s.ι (r.coker Y)) := by rw[Category.assoc]
      _= r.map f ≫ r.toColon s Y ≫ r.colon_snd s Y := rfl
      _= 0 := by simp
      _= 0 ≫ s.map (r.coker_map f) := by rw[zero_comp]
      _= (r.toColon s X ≫ r.colon_snd s X) ≫ s.map (r.coker_map f) := by simp
      _= r.toColon s X ≫ r.colon_snd s X ≫ s.map (r.coker_map f) := by rw[Category.assoc]
      _= r.toColon s X ≫ (r.colon s).map f ≫ r.colon_snd s Y := by rw[colon_map_snd']
      _= (r.toColon s X ≫ (r.colon s).map f) ≫ r.colon_snd s Y := by rw[Category.assoc]
      _= (r.toColon s X ≫ (r.colon s).map f) ≫ pullback.snd (r.π Y) (s.ι (r.coker Y)) := rfl -/


/-       let μ : r ⟶ r.colon r := {
        app := fun X => u X
        naturality := by
          intro X Y f
          apply pullback.hom_ext
          · calc (r.map f ≫ u Y) ≫ (r.colon r).ι Y
              _= r.map f ≫ (u Y ≫ (r.colon r).ι Y) := by rw[Category.assoc]
              _= r.map f ≫ r.ι Y := by rw[h_u Y]
              _= r.ι X ≫ f := ι_naturality r f
              _= (u X ≫ (r.colon r).ι X) ≫ f := by rw[← h_u X]
              _= u X ≫ (r.colon r).ι X ≫ f := by rw[Category.assoc]
              _= u X ≫ (r.colon r).map f ≫ (r.colon r).ι Y := by rw[ι_naturality]
              _= (u X ≫ (r.colon r).map f) ≫ (r.colon r).ι Y := by rw[Category.assoc]
          · exact
              IsZero.eq_of_tgt (h Y) ((r.F.map f ≫ u Y) ≫ pullback.snd (r.π Y) (r.ι (r.coker Y)))
                ((u X ≫ (r.colon r).F.map f) ≫ pullback.snd (r.π Y) (r.ι (r.coker Y)))
        w := by
          ext X
          exact h_u X
      } -/
