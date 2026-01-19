/-
Copyright (c) 2025 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module
public import Mathlib.CategoryTheory.Abelian.Basic
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

@[expose] public section

open CategoryTheory

/-- A preradical on an abelian category `C` is a subfunctor of the identity functor,
given by a functor `F : C ⥤ C` together with a natural transformation `η : F ⟶ 𝟭 C`
whose components are monomorphisms. -/
structure Preradical (C : Type*) [Category C] [Abelian C] extends (C ⥤ C) where
  /-- The structure morphism of a preradical. -/
  η : toFunctor ⟶ (𝟭 C)
  [mono_app : ∀ X : C, Mono (η.app X)]
attribute [instance] Preradical.mono_app

namespace Preradical

variable {C : Type*} [Category C] [Abelian C]

instance : Coe (Preradical C) (C ⥤ C) := ⟨fun r => r.toFunctor⟩

/-- A preradical `r` is idempotent if `r ⋙ r = r` as endofunctors. -/
def IsIdempotent (r : Preradical C) : Prop := r.toFunctor ⋙ r.toFunctor = r.toFunctor

/-- The natural transformation `η : r.F ⟶ 𝟭 (C)` is always `Mono` since each component
`η.app X : r X ⟶ X` is mono. -/
instance (r : Preradical C) : Mono r.η := NatTrans.mono_of_mono_app (α := r.η)

instance : CoeFun (Preradical C) (fun _ => C → C) := ⟨fun r X => r.obj X⟩

/-- The structure morphism of the subobject `r X` of `X`. -/
def ι (r : Preradical C) (X : C) : r X ⟶ X := r.η.app X

instance (r : Preradical C) (X : C) : Mono (r.ι X) := r.mono_app X

@[simp]
lemma ι_eq_app (r : Preradical C) (X : C) : r.ι X = r.η.app X := rfl

@[simp, reassoc]
lemma ι_naturality (r : Preradical C) {X Y : C} (f : X ⟶ Y) :
    r.ι X ≫ f = (r : C ⥤ C).map f ≫ r.ι Y := by
  simp only [ι_eq_app, NatTrans.naturality, Functor.id_obj, Functor.id_map]

end Preradical
