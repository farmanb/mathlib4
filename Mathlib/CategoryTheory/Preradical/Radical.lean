/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.Preradical.Basic
public import Mathlib.CategoryTheory.Preradical.Hom
public import Mathlib.CategoryTheory.Preradical.Colon

/-!
# Radicals of preradicals

In this file we define what it means for a preradical `r : Preradical C` on an
abelian category `C` to be *radical*, and we introduce a bundled `Radical C`
structure.

Following Stenström, a preradical `r` is called radical if `r : r = r`, where
`r : r` is the colon preradical defined via a pullback.  We encode this as the
existence of an isomorphism `r.colon r ≅ r`.  We then prove a basic
characterization of radical preradicals in terms of the vanishing of `r` on the
quotients `r.quotient.obj X`.

## Main definitions

* `Preradical.IsRadical r` :
  The proposition that a preradical `r` is radical, i.e. that `(r.colon r) ≅ r`.

* `Preradical.Radical C` :
  The type of radicals on `C`, given by a preradical together with a proof
  that it is radical.

## Main results

* `Preradical.isRadical_iff_kills_quotients` :
  A preradical `r` is radical if and only if `r (r.quotient.obj X)` is zero for all
  objects `X : C`.

Along the way we construct an auxiliary isomorphism identifying a pullback
along a zero map with a kernel, which is used in the proof of the
characterization theorem.

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

category_theory, preradical, radical, torsion theory, abelian
-/
@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

namespace Preradical

variable {C : Type*} [Category C] [Abelian C]

/-- A preradical `r` is *radical* if `r.colon r = r`. -/
def IsRadical (r : Preradical C) : Prop := Nonempty ((Preradical.colon r r) ≅ r)

/-- A *radical* on `C` is a preradical together with a proof that it is radical
in the sense of `IsRadical`. -/
structure Radical extends Preradical C where
  colon_stable : IsRadical toPreradical

/-- A preradical `r` is radical if and only if it vanishes on the quotients `r.quotient.obj X`
for all objects `X`. -/
theorem isRadical_iff_kills_quotients {r : Preradical C} :
    IsRadical r ↔ ∀ X, IsZero (r (r.quotient.obj X)) := by
  constructor
  · intro h X
    apply IsZero.of_mono_eq_zero (r.ι (r.quotient.obj X))
    apply zero_of_epi_comp (pullback.snd (r.π X) (r.ι (r.quotient.obj X)))
    obtain ⟨μ,_,hμ,_⟩ := h
    calc
      _ = (r.colon r).η.app X ≫ (cokernel.π r.η).app X := colon_condition.symm
      _ = μ.app X ≫ r.η.app X ≫ (cokernel.π r.η).app X := by
        rw [← Category.assoc, μ.w_app X]
      _= 0 := by simp
  · intro h
    apply Nonempty.intro
    symm
    haveI := (isIso_toColon_of_kills_quotients r r h : IsIso (r.toColon r))
    exact asIso (r.toColon r)
end Preradical
