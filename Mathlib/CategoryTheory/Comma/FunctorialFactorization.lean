/-
Copyright (c) 2024 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Opposite

import Mathlib.CategoryTheory.Category.Basic

import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Comma.Basic

/-!
# Functorial Factorization Systems

For a category, `C`, a functorial factorization consists of two endofunctors
`L,R : Arrow C ⥤ Arrow C` that satisfy the condition for every arrow `f : X ⟶ Y` there exists
an intermediate object `I` of `C` such that the arrows `L f : X ⟶ I` and `R f : I → Y` compose to
`f`.

In order to make this construction more natural, we regard a `FunctorialFactorization` as a
functor `Arrow C → Comma Arrow.rightFunc Arrow.leftFunc` defined by mapping `f : Arrow C` to the
triple `(L f, R f, h)`, where `h` is an isomorphism between the intermediate objects.

## Main definitions

* `FunctorialFactorization C`: a functorial factorization system on a category `C`.

## References

* [Mark Hovey, Model Categories][hovey-1999]
* https://ncatlab.org/nlab/show/functorial+factorization

## Tags

functorial factorization, factorization system, arrow category, comma category, category theory,
model categories
-/
namespace CategoryTheory
open Category

universe v u

-- morphism levels before object levels. See note [CategoryTheory universes].
variable {C : Type u} [Category.{v} C]

section

variable (C)

/-- A functorial factorization, regarded as a functor
`Arrow T ⥤ Comma Arrow.rightFunc Arrow.leftFunc`.
-/
structure FunctorialFactorization where
  factor : Arrow C ⥤ Comma (Arrow.rightFunc : Arrow C ⥤ C) (Arrow.leftFunc : Arrow C ⥤ C)

  factor_left_obj : ∀ X : Arrow C, (factor.obj X).left.left = X.left
  factor_right_obj : ∀ X : Arrow C, (factor.obj X).right.right = X.right

  factor_middle_iso : ∀ X : Arrow C, IsIso (factor.obj X).hom

  factorization_spec : ∀ X : Arrow C,
    --inv (eqToHom (factor_left_obj X)) ≫
    eqToHom ((factor_left_obj X).symm) ≫
    (factor.obj X).left.hom ≫
    (factor.obj X).hom ≫
    (factor.obj X).right.hom ≫
    eqToHom (factor_right_obj X) = X.hom
end

namespace FunctorialFactorization
open Abelian
open Limits

def factor_left (F : FunctorialFactorization C) : Arrow C ⥤ Arrow C :=
  F.factor ⋙ Comma.fst (Arrow.rightFunc) (Arrow.leftFunc)

def factor_right (F : FunctorialFactorization C) : Arrow C ⥤ Arrow C :=
  F.factor ⋙ Comma.snd (Arrow.rightFunc) (Arrow.leftFunc)

@[simp]
lemma intermediate_obj_iso (F : FunctorialFactorization C) (f : Arrow C) :
  IsIso (F.factor.obj f).hom := F.factor_middle_iso f

section images
/-- The image inclusion, followed by the right leg of a morphism in `Arrow C`,
  and then the cokernel projection, is zero. -/
@[simp]
private lemma image_to_cokernel_comp_eq_zero [Abelian C] {X Y : Arrow C} (f : X ⟶ Y) :
  (Abelian.image.ι X.hom ≫ f.right) ≫ cokernel.π Y.hom = 0 := by
    rw[← cancel_epi (coimage.π X.hom ≫ coimageImageComparison X.hom)]
    calc
      (coimage.π X.hom ≫ coimageImageComparison X.hom) ≫
      (Abelian.image.ι X.hom ≫ f.right) ≫
      cokernel.π Y.hom
    _= coimage.π X.hom ≫ coimageImageComparison X.hom ≫
      Abelian.image.ι X.hom ≫ f.right ≫
      cokernel.π Y.hom := by rw[assoc,assoc]
    _= X.hom ≫ f.right ≫ cokernel.π Y.hom := by
      simp only[← assoc,coimage_image_factorisation X.hom]
    _= f.left ≫ Y.hom ≫ cokernel.π Y.hom := by
      rw[←assoc,← Arrow.w f,assoc]
    _= f.left ≫ 0 := by rw[cokernel.condition Y.hom]
    _= 0 := HasZeroMorphisms.comp_zero f.left (cokernel Y.hom)
    _= (coimage.π X.hom ≫ coimageImageComparison X.hom) ≫ 0 := by
      exact Eq.symm (HasZeroMorphisms.comp_zero
          (coimage.π X.hom ≫ coimageImageComparison X.hom)
          (cokernel Y.hom))

/-- Assume `f : X ⟶ Y` is a morphism in an abelian category. If `z : Z ⟶ X` satisfies the
  condition that `z ≫ f = 0`, then `z = kernel.lift f z h_z`.
-/
@[simp]
private lemma kernel.lift_unique [Abelian C] {X Y Z : C} {f : X ⟶ Y}
  (z : Z ⟶ X)
  (h_z : z ≫ f = 0)
  (w : Z ⟶ kernel f)
  (h_w : w ≫ kernel.ι f = z) : w = kernel.lift f z h_z :=
    (kernelIsKernel f).uniq (KernelFork.ofι z h_z) w (by rintro (_ | _) <;> simp[h_z,h_w])


noncomputable def image.map [Abelian C] {X Y : Arrow C} (f : X ⟶ Y) :
  Abelian.image X.hom ⟶ Abelian.image Y.hom :=
    kernel.map
    (cokernel.π X.hom)
    (cokernel.π Y.hom) f.right
    (cokernel.map X.hom Y.hom f.left f.right (Arrow.w f).symm)
    (cokernel.π_desc X.hom (f.right ≫ cokernel.π Y.hom)
      (cokernel.map._proof_1 X.hom Y.hom f.left f.right (Eq.symm (Arrow.w f))))


@[simp]
private lemma image.naturality [Abelian C] {X Y : Arrow C} (f : X ⟶ Y) :
  image.map f ≫ Abelian.image.ι Y.hom = Abelian.image.ι X.hom ≫ f.right :=
    kernel.lift_ι _ _ _

private lemma image.map_unique [Abelian C] {X Y : Arrow C} (f : X ⟶ Y)
  (g : Abelian.image X.hom ⟶ Abelian.image Y.hom)
  (h_f : g ≫ Abelian.image.ι Y.hom = Abelian.image.ι X.hom ≫ f.right) : g = image.map f :=
    kernel.lift_unique _ _ _ h_f

@[simp]
private lemma image_id_eq_id_image [Abelian C] (X : Arrow C) :
  𝟙 (Abelian.image X.hom) = image.map (𝟙 X) := by
    ext; simp

@[simp]
private lemma image.map_comp [Abelian C] {X Y Z : Arrow C} (f : X ⟶ Y) (g : Y ⟶ Z) :
 image.map f ≫ image.map g = image.map (f ≫ g) := by
  apply image.map_unique (f ≫ g)
  simp [Eq.symm (assoc (image.map f) (Abelian.image.ι Y.hom) g.right)]

noncomputable def imFunc [Abelian C] : Arrow C ⥤ Arrow C where
  obj := fun X : Arrow C => Arrow.mk (Abelian.image.ι X.hom)
  map := fun {_ _} f => Arrow.homMk' (image.map f) f.right
  map_id := by intro; ext <;> simp
  map_comp := by
    intro X Y Z f g
    ext <;> simp

@[simp]
private lemma imFunc_obj_hom_eq [Abelian C] (X : Arrow C) :
   (imFunc.obj X).hom = Abelian.image.ι X.hom := rfl

@[simp]
private lemma imFunc_map_right_eq [Abelian C] {X Y : Arrow C} (f : X ⟶ Y) :
  (imFunc.map f).right = f.right := rfl

@[simp]
private lemma imFunc_map_left_eq [Abelian C] {X Y : Arrow C} (f : X ⟶ Y) :
  (Arrow.leftFunc : Arrow C ⥤ C).map (imFunc.map f) = image.map f := rfl

noncomputable def id_to_imFunc [Abelian C] : 𝟭 (Arrow C) ⟶ imFunc :=
{
  /-
    Construct the morphism on objects using the commutative diagram

    X.left - coimage.π X.hom ≫ coimageImageComparison X.hom - -> Abelian.image X.hom
      |                                                             |
      | X.hom                                                       | Abelian.image.ι X.hom
      v                                                             v
      X.right - - - - - - - - - - 𝟙 X.right - - - - - - - - -  > X.right
  -/
  app := fun X => Arrow.homMk' (coimage.π X.hom ≫ coimageImageComparison X.hom) (𝟙 X.right)
  naturality := by
    intro X Y f
    ext
    · simp[← cancel_mono (Abelian.image.ι Y.hom)]
    · simp
}

end images

section coimages
open Abelian
open Limits
@[simp]
private lemma kernel_to_coimage_comp_eq_zero [Abelian C] {X Y : Arrow C} (f : X ⟶ Y) :
  kernel.ι X.hom ≫ (f.left ≫ coimage.π Y.hom) = 0 := by
    rw[← cancel_mono (coimageImageComparison Y.hom ≫ Abelian.image.ι Y.hom)]
    simp


@[simp]
private lemma cokernel.lift_unique [Abelian C] {X Y Z : C} {f : X ⟶ Y}
  (z : Y ⟶ Z)
  (h_z : f ≫ z = 0)
  (w : cokernel f ⟶ Z)
  (h_w : cokernel.π f ≫ w = z) : w = cokernel.desc f z h_z :=
   (cokernelIsCokernel f).uniq (CokernelCofork.ofπ z h_z) w (by rintro (_ | _) <;> simp[h_z,h_w])

noncomputable def coimage.map [Abelian C] {X Y : Arrow C} (f : X ⟶ Y) :
  Abelian.coimage X.hom ⟶ Abelian.coimage Y.hom :=
    cokernel.map
      (kernel.ι X.hom)
      (kernel.ι Y.hom)
      (kernel.map X.hom Y.hom f.left f.right (by simp))
      f.left
      (by simp)

@[simp]
private lemma coimage.naturality [Abelian C] {X Y : Arrow C} (f : X ⟶ Y) :
   Abelian.coimage.π X.hom ≫ coimage.map f  = f.left ≫ Abelian.coimage.π Y.hom :=
    cokernel.π_desc _ _ _

private lemma coimage.map_unique [Abelian C] {X Y : Arrow C} (f : X ⟶ Y)
  (g : Abelian.coimage X.hom ⟶ Abelian.coimage Y.hom)
  (h_f : Abelian.coimage.π X.hom ≫ g = f.left ≫ Abelian.coimage.π Y.hom) : g = coimage.map f :=
    cokernel.lift_unique _ _ _ h_f

@[simp]
private lemma coimage.id_eq_id_image [Abelian C] (X : Arrow C) :
  𝟙 (Abelian.coimage X.hom) = coimage.map (𝟙 X) :=
    coimage.map_unique (𝟙 X) _ (by simp)

@[simp]
private lemma coimage.map_comp [Abelian C] {X Y Z : Arrow C} (f : X ⟶ Y) (g : Y ⟶ Z) :
 coimage.map f ≫ coimage.map g = coimage.map (f ≫ g) := by
  apply coimage.map_unique (f ≫ g)
  simp[Eq.symm (assoc (coimage.π X.hom) (coimage.map f) (coimage.map g))]

noncomputable def coimFunc [Abelian C] : Arrow C ⥤ Arrow C where
  obj := fun X : Arrow C => Arrow.mk (Abelian.coimage.π X.hom)
  map := fun {_ _} f => Arrow.homMk' f.left (coimage.map f)
  map_id := by intro; ext <;> simp
  map_comp := by
    intro X Y Z f g
    ext <;> simp

@[simp]
private lemma coimFunc_obj_hom_eq [Abelian C] (X : Arrow C) :
   (coimFunc.obj X).hom = Abelian.coimage.π X.hom := rfl

@[simp]
private lemma coimFunc_map_left_eq [Abelian C] {X Y : Arrow C} (f : X ⟶ Y) :
  (coimFunc.map f).left = f.left := rfl

@[simp]
private lemma coimFunc_map_right_eq [Abelian C] {X Y : Arrow C} (f : X ⟶ Y) :
  (Arrow.rightFunc : Arrow C ⥤ C).map (coimFunc.map f) = coimage.map f := rfl


noncomputable def coimFunc_to_id [Abelian C] : coimFunc ⟶ 𝟭 (Arrow C) :=
{
  /-
    Construct the morphism on objects using the commutative diagram
    X.left - - - - - - - - - - 𝟙 X.left - - - - - - - - - - - > X.left
      |                                                           |
      | X.coimage.π X.hom                                         | X.hom
      v                                                           v
    Abelian.coimage X.hom - coimageImageComparison X.hom ≫ - -> X.right
                            Abelian.image.ι X.hom
  -/
  app := fun X => Arrow.homMk' (𝟙 X.left) (coimageImageComparison X.hom ≫ Abelian.image.ι X.hom)
  naturality := by
    intro X Y f
    ext
    · simp[comp_id f.left,id_comp f.left]
    · simp[← cancel_epi (Abelian.coimage.π X.hom)]
      calc cokernel.π (kernel.ι X.hom) ≫
        (coimFunc.map f).right ≫
        coimageImageComparison Y.hom ≫
        kernel.ι (cokernel.π Y.hom)
        _= Abelian.coimage.π X.hom ≫
          coimage.map f ≫
          coimageImageComparison Y.hom ≫
          kernel.ι (cokernel.π Y.hom) := rfl
        _= (Abelian.coimage.π X.hom ≫ coimage.map f)
          ≫ coimageImageComparison Y.hom
          ≫ kernel.ι (cokernel.π Y.hom) := by
          exact Eq.symm
            (assoc (coimage.π X.hom)
            (coimage.map f)
            (coimageImageComparison Y.hom ≫ kernel.ι (cokernel.π Y.hom)))
        _= f.left ≫ Abelian.coimage.π Y.hom ≫ coimageImageComparison Y.hom ≫
          kernel.ι (cokernel.π Y.hom) := by simp
        _= f.left ≫
          (Abelian.coimage.π Y.hom ≫ coimageImageComparison Y.hom ≫ Abelian.image.ι Y.hom) := rfl
        _= f.left ≫ Y.hom := by rw[coimage_image_factorisation Y.hom]
        _= X.hom ≫f.right := Arrow.w f
}

end coimages

@[simp]
lemma coim_to_im [Abelian C] {X Y : Arrow C} (f : X ⟶ Y) :
  Arrow.rightFunc.map (coimFunc.map f) ≫
  coimageImageComparison Y.hom = coimageImageComparison X.hom ≫
  Arrow.leftFunc.map (imFunc.map f) := by
    simp only [coimFunc_map_right_eq,imFunc_map_left_eq,
      ← cancel_mono (Abelian.image.ι Y.hom),
      ← cancel_epi (Abelian.coimage.π X.hom)]
    calc
      coimage.π X.hom ≫
      (coimage.map f ≫
      coimageImageComparison Y.hom) ≫
      Abelian.image.ι Y.hom
      _= (coimage.π X.hom ≫
      coimage.map f) ≫
      (coimageImageComparison Y.hom ≫
      Abelian.image.ι Y.hom)  := by simp only [assoc]
      _= (f.left ≫ coimage.π Y.hom) ≫
      (coimageImageComparison Y.hom ≫
      Abelian.image.ι Y.hom)  := by
        simp
      _= f.left ≫ (coimage.π Y.hom ≫
      (coimageImageComparison Y.hom ≫
      Abelian.image.ι Y.hom)) := by simp only[assoc]
      _= f.left ≫ Y.hom := by simp
      _= X.hom ≫ f.right := by simp
      _= (coimage.π X.hom ≫
        coimageImageComparison X.hom ≫
        image.ι X.hom)
        ≫ f.right := by simp
      _= coimage.π X.hom ≫
          (coimageImageComparison X.hom ≫
          image.map f) ≫
          Abelian.image.ι Y.hom := by simp

noncomputable def coimage_image_factor [Abelian C] :
  Arrow C ⥤ Comma (Arrow.rightFunc : Arrow C ⥤ C) (Arrow.leftFunc : Arrow C ⥤ C) where
    obj := fun (X : Arrow C) =>
      Comma.mk (coimFunc.obj X) (imFunc.obj X) (coimageImageComparison X.hom)
    map := fun {X Y : Arrow C} (f : X ⟶ Y) =>
      CommaMorphism.mk (coimFunc.map f) (imFunc.map f) (coim_to_im f)
    map_id := fun X => by ext <;> simp
    map_comp := fun {X Y Z} f g => by ext <;> simp

@[simp]
lemma coimage_image_factor_obj_left_eq [Abelian C] (X : Arrow C) :
  (coimage_image_factor.obj X).left = coimFunc.obj X := rfl

@[simp]
lemma coimage_image_factor_obj_right_eq [Abelian C] (X : Arrow C) :
  (coimage_image_factor.obj X).right = imFunc.obj X := rfl

@[simp]
lemma coimage_image_factor_hom_eq [Abelian C] (X : Arrow C) :
  (coimage_image_factor.obj X).hom = coimageImageComparison X.hom := rfl

@[simp]
lemma left_obj_eq_left [Abelian C] (X : Arrow C) :
  (coimage_image_factor.obj X).left.left = X.left := rfl
@[simp]
lemma right_obj_eq_right [Abelian C] (X : Arrow C) :
  (coimage_image_factor.obj X).right.right = X.right := rfl

noncomputable def functorial_coim_im_factorisation [Abelian C] : FunctorialFactorization C where
  factor := coimage_image_factor
  factor_left_obj := left_obj_eq_left
  factor_right_obj := right_obj_eq_right
  factorization_spec := by simp
  factor_middle_iso := fun X => by
    simp only[coimage_image_factor_hom_eq, instIsIsoCoimageImageComparison]
end FunctorialFactorization

end CategoryTheory
