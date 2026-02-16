/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.Preradical.Basic
public import Mathlib.CategoryTheory.Preradical.Hom

/-!
# The cokernel construction associated to a preradical

Given a preradical `r : Preradical C` on an abelian category `C`, this file
develops the functor `quotient r : C ⥤ C` sending `X` to `X / r X`, the cokernel of the
structure morphism `r.ι X : r X ⟶ X`.  We also construct the associated natural
projection `π r X : X ⟶ r.quotient.obj X` and prove the canonical isomorphism
`r X ≅ kernel (r.π X)`.

## References

* [Bo Stenström, *Rings and Modules of Quotients*][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

category theory, preradical, torsion theory
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C]

namespace Preradical

variable (r : Preradical C)

/-- The cokernel of `r.η : r.toFunctor ⟶ 𝟭 C`. -/
noncomputable abbrev quotient : C ⥤ C := cokernel r.η

/-- The canonical projection onto the cokernel of `r.ι X : r X ⟶ X`. -/
noncomputable def π (X : C) : X ⟶ r.quotient.obj X := (cokernel.π r.η).app X

@[simp]
lemma π_def (X : C) : r.π X = (cokernel.π r.η).app X := rfl

@[simp, reassoc]
lemma π_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (cokernel.π r.η).app Y = (cokernel.π r.η).app X ≫ r.quotient.map f := by
  exact (cokernel.π r.η).naturality f

/-- This lemma allows simp to automatically prove `r.ι X ≫ r.π X = 0`. -/
@[simp, reassoc]
lemma π_app_comp_map_η (X : C) : (cokernel.π r.η).app (r X) ≫ r.quotient.map (r.η.app X) = 0 := by
  rw [← (cokernel.π r.η).naturality (r.η.app X)]
  exact Eq.trans (NatTrans.comp_app r.η (cokernel.π r.η) X)
    (congrArg (fun α => α.app X) (cokernel.condition r.η))

/-- The canonical isomorphism between the functorial cokernel `r.quotient.obj X` and the cokernel of
`r.ι X`. -/
noncomputable
def quotientObjIso (X : C) : r.quotient.obj X ≅ cokernel (r.ι X) := by
  simpa using (CategoryTheory.Limits.PreservesCokernel.iso
    ((CategoryTheory.evaluation C C).obj X) r.η)

lemma π_comp_quotientObjIso (X : C) : r.π X ≫ (r.quotientObjIso X).hom = cokernel.π (r.ι X) := by
  simpa [Preradical.π, quotientObjIso, Preradical.ι]
    using (CategoryTheory.Limits.PreservesCokernel.π_iso_hom
      (G := (CategoryTheory.evaluation C C).obj X) (f := r.η))

/-- The morphism `r.π X` exhibits `r.quotient.obj X` as the cokernel of `r.ι X`. -/
noncomputable
def isCokernel_π (X : C) :
    IsColimit (CokernelCofork.ofπ (r.π X) (show r.ι X ≫ r.π X = 0 by simp)) := by
  let t  : CokernelCofork (r.ι X) :=
    CokernelCofork.ofπ (r.π X) (show r.ι X ≫ r.π X = 0 by simp)
  let t₀ : CokernelCofork (r.ι X) :=
    CokernelCofork.ofπ (cokernel.π (r.ι X)) (cokernel.condition (r.ι X))
  have e : t ≅ t₀ :=
    { hom :=
        { hom := (r.quotientObjIso X).hom
          w := by
              intro j
              cases j
              · simp
              · simpa [t,t₀] using π_comp_quotientObjIso r X}
      inv :=
        { hom := (r.quotientObjIso X).inv
          w := by
            have h : t.π ≫ (r.quotientObjIso X).hom = t₀.π := by
              simpa [t, t₀] using (π_comp_quotientObjIso (r := r) (X := X))
            have h' : (t.π ≫ (r.quotientObjIso X).hom) ≫ (r.quotientObjIso X).inv =
              t₀.π ≫ (r.quotientObjIso X).inv := by
                simpa [Category.assoc] using congrArg (fun k => k ≫ (r.quotientObjIso X).inv) h
            intro j
            cases j <;> simp [h'.symm]}
      hom_inv_id := by ext; simp
      inv_hom_id := by ext; simp}
  exact IsColimit.ofIsoColimit (cokernelIsCokernel (r.ι X)) e.symm

instance (X : C) : Epi (r.π X) := epi_of_isColimit_cofork (r.isCokernel_π X)

/-- The morphism `r.ι X` exhibits `r X` as the kernel of `r.π X`. -/
noncomputable
def isKernel_ι (X : C) : IsLimit (KernelFork.ofι (r.ι X) (show r.ι X ≫ r.π X = 0 by simp)) :=
  Abelian.monoIsKernelOfCokernel _ (isCokernel_π r X)

/-- The canonical isomorphism r X ≅ kernel (r.π X). -/
noncomputable
def isoKernel_π (X : C) : r X ≅ kernel (r.π X) := by
  simpa using
    ( (isKernel_ι (r := r) (X := X)).conePointUniqueUpToIso
        (kernelIsKernel (r.π X)) )

@[simp, reassoc]
lemma isoKernel_π_hom_ι (X : C) :
    (isoKernel_π r X).hom ≫ kernel.ι ((cokernel.π r.η).app X) = r.ι X := by
  simpa [isoKernel_π] using
    (IsLimit.conePointUniqueUpToIso_hom_comp
      (isKernel_ι (r := r) (X := X))
      (kernelIsKernel (r.π X))
      WalkingParallelPair.zero)

end Preradical
