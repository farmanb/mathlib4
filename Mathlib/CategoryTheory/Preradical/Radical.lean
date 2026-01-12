/-
Copyright (c) 2024 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.Preradical.Basic
public import Mathlib.CategoryTheory.Preradical.Hom
public import Mathlib.CategoryTheory.Preradical.Colon
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

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
@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

namespace Preradical

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A preradical `r` is *radical* if `r : r = r`. -/
def IsRadical (r : Preradical C) : Prop := Nonempty ((Preradical.colon r r) ≅ r)

/-- A *radical* on `C` is a preradical together with a proof that it is radical
in the sense of `IsRadical`. -/
structure Radical extends Preradical C where
  colon_stable : IsRadical toPreradical

/-- A preradical `r` is radical if and only if it vanishes on the quotients `r.coker X`
for all objects `X`. -/
theorem isRadical_iff_kills_quotients (r : Preradical C) :
    IsRadical r ↔ ∀ X, IsZero (r (r.coker X)) := by
  constructor
  · intro h X
    apply IsZero.of_mono_eq_zero (r.ι (r.coker X))
    apply zero_of_epi_comp (colon_snd r r X)

    obtain ⟨μ,_,h_μ,_⟩ := h
    calc
    _ = r.colon_fst r X ≫ r.π X := Eq.symm colon.condition
    _ = (μ.toNatTrans ≫ r.η).app X ≫ r.π X := by
      rw [μ.w,colon_fst_eq_η_app]
    _ = (μ.app X ≫ r.ι X) ≫ r.π X := by
      rw [NatTrans.comp_app,ι_eq_app]
    _ = μ.app X ≫ r.ι X ≫ r.π X := by rw [Category.assoc]
    _ = 0 := by simp only [coker_eq, ι_eq_app, ι_comp_π, comp_zero]
  · intro h
    apply Nonempty.intro
    symm
    haveI := (isIso_toColon_of_kills_quotients r r h : IsIso (r.toColon r))
    exact asIso (r.toColon r)
end Preradical
