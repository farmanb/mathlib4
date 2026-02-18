/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.Preradical.Basic

/-!
# The cokernel construction associated to a preradical

Given a preradical `Φ : Preradical C` on an abelian category `C`, this file develops the functor
`quotient Φ : C ⥤ C` sending `X` to the cokernel of `Φ.ι.app X : Φ.r.obj X ⟶ X`.  We also construct
the associated natural projection `π Φ X : X ⟶ Φ.quotient.obj X` and prove the canonical
isomorphism `Φ.r.obj X ≅ kernel (Φ.π X)`.

## References

* [Bo Stenström, *Rings and Modules of Quotients*][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

category theory, preradical, torsion theory
-/

@[expose] public section

namespace CategoryTheory.Abelian
open CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C]

namespace Preradical

variable (Φ : Preradical C)

/-- The cokernel of `Φ.ι : Φ.r ⟶ 𝟭 C`. -/
noncomputable abbrev quotient : C ⥤ C := cokernel Φ.ι

/-- The canonical projection onto the cokernel of `Φ.ι.app X : Φ.r.obj X ⟶ X`. -/
noncomputable def π (X : C) : X ⟶ Φ.quotient.obj X := (cokernel.π Φ.ι).app X

@[simp]
lemma π_def (X : C) : Φ.π X = (cokernel.π Φ.ι).app X := rfl

@[simp, reassoc]
lemma π_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (cokernel.π Φ.ι).app Y = (cokernel.π Φ.ι).app X ≫ Φ.quotient.map f := by
  exact (cokernel.π Φ.ι).naturality f

@[simp, reassoc]
lemma π_app_comp_map_ι (X : C) :
    (cokernel.π Φ.ι).app (Φ.r.obj X) ≫ Φ.quotient.map (Φ.ι.app X) = 0 := by
  rw [← (cokernel.π Φ.ι).naturality (Φ.ι.app X)]
  exact Eq.trans (NatTrans.comp_app Φ.ι (cokernel.π Φ.ι) X)
    (congrArg (fun α => α.app X) (cokernel.condition Φ.ι))

/-- The canonical isomorphism between the functorial cokernel `Φ.quotient.obj X` and the cokernel
of `Φ.ι.app X`. -/
noncomputable
def quotientObjIso (X : C) : Φ.quotient.obj X ≅ cokernel (Φ.ι.app X) := by
  simpa using (CategoryTheory.Limits.PreservesCokernel.iso
    ((CategoryTheory.evaluation C C).obj X) Φ.ι)

lemma π_comp_quotientObjIso (X : C) :
    Φ.π X ≫ (Φ.quotientObjIso X).hom = cokernel.π (Φ.ι.app X) := by
  simpa [Preradical.π, quotientObjIso, Preradical.ι]
    using (CategoryTheory.Limits.PreservesCokernel.π_iso_hom
      (G := (CategoryTheory.evaluation C C).obj X) (f := Φ.ι))

/-- The morphism `Φ.π X` exhibits `Φ.quotient.obj X` as the cokernel of `Φ.ι.app X`. -/
noncomputable
def isCokernel_π (X : C) :
    IsColimit (CokernelCofork.ofπ (Φ.π X) (show Φ.ι.app X ≫ Φ.π X = 0 by simp)) := by
  let t  : CokernelCofork (Φ.ι.app X) :=
    CokernelCofork.ofπ (Φ.π X) (show Φ.ι.app X ≫ Φ.π X = 0 by simp)
  let t₀ : CokernelCofork (Φ.ι.app X) :=
    CokernelCofork.ofπ (cokernel.π (Φ.ι.app X)) (cokernel.condition (Φ.ι.app X))
  have e : t ≅ t₀ :=
    { hom :=
        { hom := (Φ.quotientObjIso X).hom
          w := by
              intro j
              cases j
              · simp
              · simpa [t,t₀] using π_comp_quotientObjIso Φ X}
      inv :=
        { hom := (Φ.quotientObjIso X).inv
          w := by
            have h : t.π ≫ (Φ.quotientObjIso X).hom = t₀.π := by
              simpa [t, t₀] using (π_comp_quotientObjIso (Φ := Φ) (X := X))
            have h' : (t.π ≫ (Φ.quotientObjIso X).hom) ≫ (Φ.quotientObjIso X).inv =
              t₀.π ≫ (Φ.quotientObjIso X).inv := by
                simpa [Category.assoc] using congrArg (fun k => k ≫ (Φ.quotientObjIso X).inv) h
            intro j
            cases j <;> simp [h'.symm]}
      hom_inv_id := by ext; simp
      inv_hom_id := by ext; simp}
  exact IsColimit.ofIsoColimit (cokernelIsCokernel (Φ.ι.app X)) e.symm

instance (X : C) : Epi (Φ.π X) := epi_of_isColimit_cofork (Φ.isCokernel_π X)

/-- The morphism `Φ.ι.app X` exhibits `Φ.r.obj X` as the kernel of `Φ.π X`. -/
noncomputable
def isKernel_ι (X : C) :
    IsLimit (KernelFork.ofι (Φ.ι.app X) (show Φ.ι.app X ≫ Φ.π X = 0 by simp)) :=
  Abelian.monoIsKernelOfCokernel _ (Φ.isCokernel_π X)

/-- The canonical isomorphism `Φ.r.obj X ≅ kernel (Φ.π X)`. -/
noncomputable
def isoKernel_π (X : C) : Φ.r.obj X ≅ kernel (Φ.π X) := by
  simpa using
    ( (isKernel_ι (Φ := Φ) (X := X)).conePointUniqueUpToIso
        (kernelIsKernel (Φ.π X)) )

@[simp, reassoc]
lemma isoKernel_π_hom_ι (X : C) :
    (Φ.isoKernel_π X).hom ≫ kernel.ι ((cokernel.π Φ.ι).app X) = Φ.ι.app X := by
  simpa [isoKernel_π] using
    (IsLimit.conePointUniqueUpToIso_hom_comp
      (isKernel_ι (Φ := Φ) (X := X))
      (kernelIsKernel (Φ.π X))
      WalkingParallelPair.zero)

end Preradical

end CategoryTheory.Abelian
