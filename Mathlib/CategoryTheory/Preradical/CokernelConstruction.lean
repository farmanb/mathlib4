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
develops the functor `coker r : C ⥤ C` sending `X` to the cokernel of the
structure morphism `r.ι X : r X ⟶ X`.  We also construct the associated natural
projection `π r X : X ⟶ r.coker.obj X` and prove the canonical isomorphism `r X ≅ kernel (r.π X)`.

This comparison isomorphism expresses categorically that a preradical embeds each
object as the kernel of the corresponding cokernel projection.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C]

namespace Preradical

/-- The cokernel of `r.η : r.toFunctor ⟶ 𝟭 C`. -/
noncomputable abbrev coker (r : Preradical C) : C ⥤ C := cokernel r.η

/-- The canonical isomorphism between the functorial cokernel
`r.coker.obj X` and the cokernel of `r.ι X`. -/
noncomputable
def cokerObjIso (r : Preradical C) (X : C) : r.coker.obj X ≅ cokernel (r.ι X) := by
  simpa [Preradical.coker, Preradical.ι] using (CategoryTheory.Limits.PreservesCokernel.iso
    ((CategoryTheory.evaluation C C).obj X) r.η)

/-- The projection `𝟭 C ⟶ r.coker`. -/
noncomputable abbrev coker_π (r : Preradical C) : 𝟭 C ⟶ r.coker := cokernel.π r.η

/-- The canonical projection onto the cokernel of `r.ι X : r X ⟶ X`. -/
noncomputable def π (r : Preradical C) (X : C) : X ⟶ r.coker.obj X := r.coker_π.app X

@[simp]
lemma π_def (r : Preradical C) (X : C) : r.π X = (cokernel.π r.η).app X := rfl

@[simp, reassoc]
lemma π_naturality (r : Preradical C) {X Y : C} (f : X ⟶ Y) :
    f ≫ (cokernel.π r.η).app Y = (cokernel.π r.η).app X ≫ r.coker.map f := by
  exact (cokernel.π r.η).naturality f

/-- The simpNF for `r.η.app X ≫ (cokernel.π r.η).app X = 0`.
     (cokernel.π r.η).app (r X)
    r X - - - - - - - - - - - - -> r.coker.obj (r X)
     |                                 |
     | r.η.app X                       | r.coker.map (r.η X)
     v                                 v
     X - - - - - - - - - - - - - > r.coker.obj X
       (cokernel.π r.η).app X
-/
@[simp, reassoc]
lemma η_app_comp_coker_π_app (r : Preradical C) (X : C) :
    (cokernel.π r.η).app (r X) ≫ r.coker.map (r.η.app X) = 0 := by
  rw[←(cokernel.π r.η).naturality (r.η.app X)]
  exact Eq.trans (NatTrans.comp_app r.η (cokernel.π r.η) X)
    (congrArg (fun α => α.app X) (cokernel.condition r.η))

lemma π_comp_cokerObjIso_hom (r : Preradical C) (X : C) :
    r.π X ≫ (r.cokerObjIso X).hom = cokernel.π (r.ι X) := by
  simpa [Preradical.π, Preradical.coker_π, cokerObjIso, Preradical.ι]
    using (CategoryTheory.Limits.PreservesCokernel.π_iso_hom
      (G := (CategoryTheory.evaluation C C).obj X) (f := r.η))

/-- The morphism `r.π X` exhibits `r.coker.obj X` as the cokernel of `r.ι X`. -/
noncomputable
def isCokernel_π (r : Preradical C) (X : C) :
    IsColimit (CokernelCofork.ofπ (r.π X) (show r.ι X ≫ r.π X = 0 by simp)) := by
  let t  : CokernelCofork (r.ι X) :=
    CokernelCofork.ofπ (r.π X) (show r.ι X ≫ r.π X = 0 by simp)
  let t₀ : CokernelCofork (r.ι X) :=
    CokernelCofork.ofπ (cokernel.π (r.ι X)) (cokernel.condition (r.ι X))
  have e : t ≅ t₀ := by
    refine
      { hom :=
          { hom := (r.cokerObjIso X).hom
            w := ?_ }
        inv :=
          { hom := (r.cokerObjIso X).inv
            w := ?_ }
        hom_inv_id := by ext; simp
        inv_hom_id := by ext; simp }
    · intro j
      cases j
      · simp
      · simpa [t, t₀] using π_comp_cokerObjIso_hom r X
    · have h : t.π ≫ (r.cokerObjIso X).hom = t₀.π := by
        simpa [t, t₀] using (π_comp_cokerObjIso_hom (r := r) (X := X))
      have h' : (t.π ≫ (r.cokerObjIso X).hom) ≫ (r.cokerObjIso X).inv =
          t₀.π ≫ (r.cokerObjIso X).inv := by
        simpa [Category.assoc] using congrArg (fun k => k ≫ (r.cokerObjIso X).inv) h
      intro j
      cases j <;> simp [h'.symm]
  exact IsColimit.ofIsoColimit (cokernelIsCokernel (r.ι X)) e.symm

instance (r : Preradical C) (X : C) : Epi (r.π X) := epi_of_isColimit_cofork (r.isCokernel_π X)

/-- The morphism `r.ι X` exhibits `r X` as the kernel of `r.π X`. -/
noncomputable
def isKernel_ι_of_π (r : Preradical C) (X : C) :
    IsLimit (KernelFork.ofι (r.ι X) (show r.ι X ≫ r.π X = 0 by simp)) :=
  Abelian.monoIsKernelOfCokernel _ (isCokernel_π r X)

/-- The canonical isomorphism r X ≅ kernel (r.π X). -/
noncomputable
def kernelIso_π (r : Preradical C) (X : C) : r X ≅ kernel (r.π X) := by
  simpa using
    ( (isKernel_ι_of_π (r := r) (X := X)).conePointUniqueUpToIso
        (kernelIsKernel (r.π X)) )

@[simp, reassoc]
lemma kernelIso_π_hom_ι (r : Preradical C) (X : C) :
    (kernelIso_π r X).hom ≫ kernel.ι ((cokernel.π r.η).app X) = r.ι X := by
  simpa [kernelIso_π] using
    (IsLimit.conePointUniqueUpToIso_hom_comp
      (isKernel_ι_of_π (r := r) (X := X))
      (kernelIsKernel (r.π X))
      WalkingParallelPair.zero)

end Preradical
