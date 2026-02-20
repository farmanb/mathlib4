/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.Abelian.Preradical.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# The colon construction on preradicals

Given preradicals `Φ` and `Ψ` on an abelian category `C`, this file defines their **colon** `Φ : Ψ`
in the sense of Stenström.  Categorically, `Φ : Ψ` is constructed objectwise as a pullback of the
canonical projection `Φ.π X : X ⟶ Φ.quotient.obj X` along the inclusion
`Functor.whiskerLeft Φ.quotient Ψ.ι`.

## Main definitions

* `Preradical.colon Φ Ψ : Preradical C` : The colon preradical `Φ : Ψ` of Stenström.
* `toColon Φ Ψ : Φ ⟶ Φ.colon Ψ` : The canonical inclusion of the left preradical into the colon.

## Main results

* `isIso_toColon_of_isZero_whisker` : If `Ψ` kills quotients in the sense that `Φ.quotient ⋙ Ψ.r`
is the zero object, then the canonical inclusion `toColon Φ Ψ` is an isomorphism.

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

section KernelCokernel

variable (Φ : Preradical C)

/-- The cokernel of `Φ.ι : Φ.r ⟶ 𝟭 C`. -/
noncomputable abbrev quotient : C ⥤ C := cokernel Φ.ι

/-- The canonical projection onto the cokernel of `Φ.ι : Φ.r ⟶ 𝟭 C`. -/
noncomputable abbrev π : 𝟭 C ⟶ Φ.quotient := cokernel.π Φ.ι

/-- The cokernel cofork of the structure morphism `Φ.ι : Φ.r ⟶ 𝟭 C`. -/
noncomputable
def cokernelCofork_π : CokernelCofork Φ.ι := by
  refine CokernelCofork.ofπ Φ.π ?_
  simp

/-- The cofork `Φ.cokernelCofork_π` is a cokernel of `Φ.ι`. -/
noncomputable
def isCokernel_π : IsColimit Φ.cokernelCofork_π := cokernelIsCokernel Φ.ι

/-- The kernel fork of the projection `Φ.π : 𝟭 C ⟶ Φ.quotient`. -/
noncomputable
def kernelFork_ι : KernelFork Φ.π := by
  refine KernelFork.ofι Φ.ι ?_
  simp

/-- The fork `Φ.kernelFork_ι` is a kernel of `Φ.π`. -/
noncomputable
def isKernel_ι_of_π : IsLimit (Φ.kernelFork_ι) :=
  Abelian.monoIsKernelOfCokernel Φ.cokernelCofork_π Φ.isCokernel_π

/-- The canonical isomorphism `Φ.r ≅ kernel Φ.π`. -/
noncomputable
def isoKernel : Φ.r ≅ kernel (Φ.π) := by
  simpa using Φ.isKernel_ι_of_π.conePointUniqueUpToIso (kernelIsKernel Φ.π)

/-- The isomorphism `Φ.r ≅ kernel (Φ.π)` provides a factorization of `Φ.ι` through the kernel. -/
lemma isoKernel_π_hom_comp_kernel_ι : Φ.isoKernel.hom ≫ kernel.ι Φ.π = Φ.ι := by
  simpa [isoKernel, Preradical.kernelFork_ι] using
    (IsLimit.conePointUniqueUpToIso_hom_comp
      Φ.isKernel_ι_of_π (kernelIsKernel Φ.π) WalkingParallelPair.zero)

/-- The isomorphism `Φ.r ≅ kernel (Φ.π)` provides a factorization of the kernel through `Φ.ι`. -/
lemma isoKernel_π_inv_comp_ι : Φ.isoKernel.inv ≫ Φ.ι = kernel.ι Φ.π := by
  simpa [isoKernel, Preradical.kernelFork_ι] using
    (IsLimit.conePointUniqueUpToIso_inv_comp
      Φ.isKernel_ι_of_π (kernelIsKernel Φ.π) WalkingParallelPair.zero)

end KernelCokernel

variable (Φ Ψ : Preradical C)

instance : Mono (Functor.whiskerLeft Φ.quotient Ψ.ι) := by
  letI := (NatTrans.mono_iff_mono_app (Ψ.ι)).mp (MonoOver.mono Ψ)
  letI :  ∀ (X : C), Mono ((Φ.quotient.whiskerLeft Ψ.ι).app X) := by
    intro X
    have : (Functor.whiskerLeft Φ.quotient Ψ.ι).app X = Ψ.ι.app (Φ.quotient.obj X) :=
      Eq.symm (congr_app rfl (Φ.quotient.obj X))
    rw [this]
    exact instMonoAppOfFunctor Ψ.ι (Φ.quotient.obj X)
  exact NatTrans.mono_of_mono_app (α := Functor.whiskerLeft Φ.quotient Ψ.ι)

/-- The colon preradical from Stenström, defined objectwise as the pullback of `Φ.π X` along
`Ψ.ι.app (Φ.quotient.obj X)`. -/
noncomputable
def colon : Preradical C where
  obj := {
    left := pullback Φ.π (Functor.whiskerLeft Φ.quotient Ψ.ι)
    right := {as := ()}
    hom := pullback.fst Φ.π (Functor.whiskerLeft Φ.quotient Ψ.ι)
  }
  property := pullback.fst_of_mono

/-- There is a morphism `Φ ⟶ (Φ.colon Ψ)` induced by the universal property for the pullback
via `Φ.ι : Φ.r X ⟶ 𝟭 C` and the zero morphism `Φ.r ⟶  Φ.quotient ⋙ Ψ.r`. -/
noncomputable
def toColon : Φ ⟶ Φ.colon Ψ where
  hom := {
    left := {
      app := (pullback.lift (f := Φ.π) (g := Φ.quotient.whiskerLeft Ψ.ι) Φ.ι 0 (by simp)).app
      naturality := (pullback.lift (f := Φ.π) (g := Φ.quotient.whiskerLeft Ψ.ι)
        Φ.ι 0 (by simp)).naturality
    }
    right := {
      down := {
        down := by exact Discrete.ext_iff.mp rfl
      }
    }
    w := by
      ext
      simp [Preradical.colon]
  }

/-- If for all `Φ.quotient ⋙ Ψ.r` is the zero object, then `Φ.toColon Ψ` is an isomorphism. -/
theorem isIso_toColon_of_isZero_whisker (h : IsZero (Φ.quotient ⋙ Ψ.r)) :
    IsIso (Φ.toColon Ψ) := by
  refine (MonoOver.isIso_iff_isIso_hom_left (Φ.toColon Ψ)).mpr ?_
  have hsnd := IsZero.eq_zero_of_tgt h (pullback.snd (Φ.π) (Functor.whiskerLeft Φ.quotient Ψ.ι))
  have hfst : (pullback.fst Φ.π (Functor.whiskerLeft Φ.quotient Ψ.ι)) ≫ Φ.π = 0 := by
    rw [pullback.condition, hsnd ,zero_comp]
  let inv₀ : (Φ.colon Ψ).r ⟶ kernel Φ.π := by
      refine kernel.lift (f := Φ.π) (Φ.colon Ψ).ι ?_
      change (pullback.fst (Φ.π) (Functor.whiskerLeft Φ.quotient Ψ.ι)) ≫ Φ.π = 0
      rw [pullback.condition, hsnd, zero_comp]
  have hfactor : inv₀ ≫ kernel.ι Φ.π = (Φ.colon Ψ).ι:= by
      exact
        kernel.lift_ι Φ.π (Φ.colon Ψ).ι
          (id
            (Eq.mpr (id (congrArg (fun _a ↦ _a = 0) pullback.condition))
              (Eq.mpr (id (congrArg (fun _a ↦ _a ≫ Φ.quotient.whiskerLeft Ψ.ι = 0) hsnd))
                (Eq.mpr (id (congrArg (fun _a ↦ _a = 0) zero_comp)) (Eq.refl 0)))))
  let inv : (Φ.colon Ψ).r ⟶ Φ.r := inv₀ ≫ Φ.isoKernel.inv
  refine ⟨inv, ?_, ?_⟩
  · apply (cancel_mono Φ.ι).mp
    rw [Category.id_comp]
    calc
      _ = ((Φ.toColon Ψ).hom.left ≫ inv₀ ≫ Φ.isoKernel.inv) ≫ Φ.ι := rfl
      _ = (Φ.toColon Ψ).hom.left ≫ inv₀ ≫ kernel.ι Φ.π := by simp [Φ.isoKernel_π_inv_comp_ι]
      _ = (Φ.toColon Ψ).hom.left ≫ (Φ.colon Ψ).ι := by rw [hfactor]
      _= Φ.ι := MonoOver.w (Φ.toColon Ψ)
  · apply (cancel_mono (Φ.colon Ψ).ι).mp
    rw [Category.id_comp]
    calc
     _ = inv ≫ Φ.ι := by
      simp
    _ = (inv₀ ≫ Φ.isoKernel.inv) ≫ Φ.ι :=
      rfl
    _ = (inv₀ ≫ Φ.isoKernel.inv) ≫ (Φ.isoKernel.hom ≫ kernel.ι Φ.π) := by
      rw [← Φ.isoKernel_π_hom_comp_kernel_ι]
    _ = inv₀ ≫ kernel.ι Φ.π := by
      simp
    _ = (Φ.colon Ψ).ι := hfactor

end Preradical

end CategoryTheory.Abelian
