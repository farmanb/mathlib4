/-
Copyright (c) 2025 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
import Mathlib.CategoryTheory.Abelian.Basic
/-!
# Preradicals

A **preradical** on an abelian category `C` is a subfunctor of the identity functor,
given by a functor `F : C ⥤ C` together with a natural transformation `η : F ⟶ 𝟭 C`
whose components are monomorphisms.  This notion originates in the study of radicals
and torsion theories (Stenström).

## Main definitions

* `Preradical C`: the type of preradicals on `C`.
* `Preradical.ι r X`: the structure morphism `r X ⟶ X`.
* `Preradical.map r f`: the functorial action of a preradical on a morphism.
* `Preradical.Hom`: A morphism of preradicals `r ⟶ s` (developed in `Hom.lean`).
* `cokernel_of r` : The functor that assigns to `X : C` the cokernel object associated to `r X ⟶ X`
    (developed in `CokernelConstruction.lean`).
* `r.colon s` : Stenström's `r : s`, constructed as a pullback (developed in `Colon.lean`).
* `r.π X`: The projection `X ⟶ cokernel (r.ι X)` associated to `r.ι X : r X ⟶ X`.
* `Radical C` : the type of a radical on `C` (developed in `Radical.lean`).

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]

## Tags

category theory, preradical, subfunctor
-/

open CategoryTheory
open CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A preradical on an abelian category `C` is a subfunctor of the identity functor,
given by a functor `F : C ⥤ C` together with a natural transformation `η : F ⟶ 𝟭 C`
whose components are monomorphisms. -/
structure Preradical (C : Type u) [Category.{v} C] [Abelian C] where
  F : C ⥤ C
  η : F ⟶ (𝟭 C)
  [mono_app : ∀ X : C, Mono (η.app X)]
attribute [instance] Preradical.mono_app

namespace Preradical

/-- A preradical `r` is idempotent if `r ∘ r = r` as endofunctors. -/
def IsIdempotent (r : Preradical C) : Prop := r.F ⋙ r.F = r.F

/-- The natural transformation `η : r.F ⟶ 𝟭 (C)` is always `Mono` since each component
`η.app X : r X ⟶ X` is mono. -/
instance (r : Preradical C) : Mono r.η := NatTrans.mono_of_mono_app (α := r.η)

instance : CoeFun (Preradical C) (fun _ => C → C) :=
  ⟨fun r X => r.F.obj X⟩

/-- The structure map of a preradical `r`, viewed as a subobject of the identity,
at an object `X`. -/
def ι (r : Preradical C) (X : C) : r X ⟶ X := r.η.app X

instance (r : Preradical C) (X : C) : Mono (r.ι X) := r.mono_app X

def map (r : Preradical C) {X Y : C} (f : X ⟶ Y) : r X ⟶ r Y := r.F.map f

@[simp]
lemma map_id (r : Preradical C) (X : C) : r.map (𝟙 X) = 𝟙 (r X) := r.F.map_id X

@[simp]
lemma map_comp (r : Preradical C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    r.map (f ≫ g) = r.map f ≫ r.map g :=
  r.F.map_comp f g

@[simp]
lemma ι_eq_app (r : Preradical C) (X : C) :
    r.η.app X = r.ι X :=
  rfl

@[simp, reassoc]
lemma ι_naturality (r : Preradical C) {X Y : C} (f : X ⟶ Y) :
    r.map f ≫ r.ι Y = r.ι X ≫ f :=
  r.η.naturality f

@[simp]
lemma map_eq_map (r : Preradical C) {X Y : C} (f : X ⟶ Y) : r.F.map f = r.map f := rfl

end Preradical
