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
whose components are monomorphisms.

## Main definitions

* `Preradical C`: the type of preradicals on `C`.
* `Preradical.ι r X`: the structure morphism `r X ⟶ X`.

## References

* [Bo Stenström, *Rings and Modules of Quotients*][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

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
instance (r : Preradical C) : Mono r.η := NatTrans.mono_of_mono_app r.η

instance : CoeFun (Preradical C) (fun _ => C → C) := ⟨fun r X => r.obj X⟩

/-- The structure morphism of the subobject `r X` of `X`. -/
def ι (r : Preradical C) (X : C) : r X ⟶ X := r.η.app X

instance (r : Preradical C) (X : C) : Mono (r.ι X) := r.mono_app X

@[simp]
lemma ι_def (r : Preradical C) (X : C) : r.ι X = r.η.app X := rfl

end Preradical
