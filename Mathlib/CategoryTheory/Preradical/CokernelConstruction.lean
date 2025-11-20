/-
Copyright (c) 2025 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.Preradical.Basic
public import Mathlib.CategoryTheory.Preradical.Hom

/-!
# The cokernel construction associated to a preradical

Given a preradical `r : Preradical C` on an abelian category `C`, this file
develops the functor `cokernel_of r : C ⥤ C` sending `X` to the cokernel of the
structure morphism `r.ι X : r X ⟶ X`.  We also construct the associated natural
projection `π r X : X ⟶ r.coker X` and prove the canonical isomorphism `r X ≅ kernel (r.π X)`.

This comparison isomorphism expresses categorically that a preradical embeds each
object as the kernel of the corresponding cokernel projection.

This file is part of the `Preradical` hierarchy; see
`CategoryTheory/Preradical/Basic.lean` for an overview of the entire package.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Preradical

/-- The functor sending `X` to the cokernel of the structure map `r.ι X`. -/
noncomputable
def cokernel_of (r : Preradical C) : C ⥤ C where
  obj := fun X => cokernel (r.ι X)
  map := fun {X Y} f => cokernel.map (r.ι X) (r.ι Y) (r.map f) f (Eq.symm (ι_naturality r f))
  map_id := fun X => coequalizer.hom_ext (by simp)
  map_comp := fun {X Y Z} f g => coequalizer.hom_ext (by simp)

noncomputable
def coker (r : Preradical C) (X : C) := (cokernel_of r).obj X

noncomputable
def coker_map (r : Preradical C) {X Y : C} (f : X ⟶ Y) : r.coker X ⟶ r.coker Y :=
  (cokernel_of r).map f

@[simp]
lemma coker_eq (r : Preradical C) (X : C) : r.coker X = (cokernel_of r).obj X := rfl

@[simp]
lemma coker_map_eq (r : Preradical C) {X Y : C} (f : X ⟶ Y) :
    r.coker_map f = (cokernel_of r).map f :=
  rfl

@[simp]
lemma coker_map_id (r : Preradical C) (X : C) :
    r.coker_map (𝟙 X) = 𝟙 (r.coker X) :=
  (cokernel_of r).map_id X

@[simp]
lemma coker_map_comp (r : Preradical C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    r.coker_map (f ≫ g) = (r.coker_map f) ≫ (r.coker_map g) :=
  (cokernel_of r).map_comp f g

noncomputable
def π (r : Preradical C) (X : C) : X ⟶ r.coker X := cokernel.π (r.ι X)

instance (r : Preradical C) (X : C) : Epi (r.π X) := by
  change Epi (cokernel.π (r.ι X))
  infer_instance

noncomputable
def coker_η (r : Preradical C) : 𝟭 C ⟶ cokernel_of r where
  app := fun X => r.π X
  naturality := fun X Y f =>
    Eq.symm
    (cokernel.π_desc (r.ι X) (f ≫ cokernel.π (r.ι Y))
    (cokernel.map._proof_1 (r.ι X) (r.ι Y) (r.map f) f (Eq.symm (ι_naturality r f))))

instance (r : Preradical C) (X : C) : Epi (r.coker_η.app X) := by
  change Epi (r.π X)
  infer_instance

instance (r : Preradical C) : Epi r.coker_η := NatTrans.epi_of_epi_app r.coker_η

/-- The morphism `r.π : X ⟶ r.coker X` is natural in `X`. -/
@[simp, reassoc]
lemma π_naturality (r : Preradical C) {X Y : C} (f : X ⟶ Y) :
f ≫ r.π Y = r.π X ≫ r.coker_map f := (r.coker_η).naturality f

/-- For all `X : C`, `r.ι X ≫ r.π X = 0`. -/
@[simp]
lemma ι_comp_π (r : Preradical C) (X : C) : r.ι X ≫ r.π X = 0 := by
  change r.ι X ≫ cokernel.π (r.ι X) = 0
  exact cokernel.condition (r.ι X)

/-- For every `X : C`, there is a canonical morphism `r X ⟶ kernel (r.π X)` induced by the
universal property of the kernel via `r.ι X ≫ r.π X = 0`. -/
noncomputable
def toKernel_π (r : Preradical C) (X : C) : r X ⟶ kernel (r.π X) :=
kernel.lift (r.π X) (r.ι X) (ι_comp_π r X)

/-- The property of the induced morphism `toKernel_π : r X ⟶ kernel (r.π X)`. -/
@[simp, reassoc]
lemma toKernel_π_comp_kernel_ι (r : Preradical C) (X : C) :
r.toKernel_π X ≫ kernel.ι (r.π X) = r.ι X := kernel.lift_ι (r.π X) (r.ι X) (ι_comp_π r X)

/-- For every `X : C`, there is a canonical morphism `kernel (r.π X) ⟶ r X`. -/
noncomputable
def fromKernel_π (r : Preradical C) (X : C) : kernel (r.π X) ⟶ r X :=
  (KernelFork.IsLimit.lift'
    (Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ (r.π X) (ι_comp_π r X))
      ((cokernelIsCokernel (r.ι X))))
    (kernel.ι (r.π X)) (kernel.condition (r.π X))).1

@[simp, reassoc]
lemma fromKernel_π_comp (r : Preradical C) (X : C) :
r.fromKernel_π X ≫ (r.ι X) = kernel.ι (r.π X) :=
(KernelFork.IsLimit.lift' (Abelian.monoIsKernelOfCokernel
  (CokernelCofork.ofπ (r.π X) (ι_comp_π r X)) ((cokernelIsCokernel (r.ι X))))
  (kernel.ι (r.π X)) (kernel.condition (r.π X))).2

@[simp, reassoc]
lemma toKernel_π_comp_fromKernel_π_id (r : Preradical C) (X : C) :
r.toKernel_π X ≫ r.fromKernel_π X = 𝟙 (r X) := by
  apply (cancel_mono_id (r.ι X)).mp
  simp

@[simp, reassoc]
lemma fromKernel_π_comp_toKernel_π_id (r : Preradical C) (X : C) :
r.fromKernel_π X ≫ r.toKernel_π X = 𝟙 (kernel (r.π X)) := by
  apply (cancel_mono_id (kernel.ι (r.π X))).mp
  simp

/-- For all `X : C`, `r.toKernel_π X : r X ⟶ kernel (r.π X)` is an isomorphism. -/
instance (r : Preradical C) (X : C) : IsIso (r.toKernel_π X) :=
  ⟨r.fromKernel_π X, ⟨toKernel_π_comp_fromKernel_π_id _ _, fromKernel_π_comp_toKernel_π_id _ _⟩⟩

/-- The expected isomorphism between `r X ≅ kernel (r.π X)`. -/
noncomputable
def kernelIso_π (r : Preradical C) (X : C) : r X ≅ kernel (r.π X) :=
  {
    hom := r.toKernel_π X
    inv := r.fromKernel_π X
    hom_inv_id := toKernel_π_comp_fromKernel_π_id _ _
    inv_hom_id := fromKernel_π_comp_toKernel_π_id _ _
  }

@[simp, reassoc]
lemma kernelIso_π_hom_ι (r : Preradical C) (X : C) :
  (kernelIso_π r X).hom ≫ kernel.ι (r.π X) = r.ι X := by simp [kernelIso_π]

end Preradical
