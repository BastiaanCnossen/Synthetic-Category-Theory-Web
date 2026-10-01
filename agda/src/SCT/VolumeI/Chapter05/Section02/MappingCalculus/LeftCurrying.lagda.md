# Currying in the left variable

For a functor on `R × B`, curry in `R` to obtain a functor from `B`
to `Fun R D`. Symmetry relates this convention to the existing currying
operation. Its computation, uniqueness, and parameter-change rules below
are derived, with no additional assumption.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as Products
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter01.Section07.Currying as Currying
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.ProductSymmetry as Symmetry

module SCT.VolumeI.Chapter05.Section02.MappingCalculus.LeftCurrying
  {l : Level} (T : Theory l l l) (M : Mapping.MappingAnimae T)
  (F : Functors.FunctorCategories T M) where

open View T
open Calculus T using (_then_)
open Products vocabulary terminal products productLaws composition using (productMap; swap)
open Functors.FunctorCategories F using (Fun)
module Native = Currying T M F using
  (funUncurry; funCurry; funCurry-β; funUncurry-cong; funReflect; funCurry-cong; funUncurry-restrict)
open Symmetry T using (twice; swap-natural)

uncurry : {R B D : CAT} → MAP B (Fun R D) → MAP (R × B) D
uncurry h = Native.funUncurry h ∘ swap

curry : {R B D : CAT} → MAP (R × B) D → MAP B (Fun R D)
curry f = Native.funCurry (f ∘ swap)

curry-β : {R B D : CAT} (f : MAP (R × B) D) → uncurry (curry f) =₁ f
curry-β f = (Native.funCurry-β (f ∘ swap) ▷ swap) then twice f

reflect : {R B D : CAT} {f g : MAP B (Fun R D)} → uncurry f =₁ uncurry g → f =₁ g
reflect {f = f} {g} α = Native.funReflect f g
  ((twice (Native.funUncurry f)) ⁻¹ then (α ▷ swap) then twice (Native.funUncurry g))

curry-η : {R B D : CAT} (h : MAP B (Fun R D)) → curry (uncurry h) =₁ h
curry-η h = reflect (curry-β (uncurry h))

curry-cong : {R B D : CAT} {f g : MAP (R × B) D} → f =₁ g → curry f =₁ curry g
curry-cong α = Native.funCurry-cong (α ▷ swap)

uncurry-cong : {R B D : CAT} {f g : MAP B (Fun R D)} → f =₁ g → uncurry f =₁ uncurry g
uncurry-cong α = Native.funUncurry-cong α ▷ swap

uncurry-pre : {R B C D : CAT} (h : MAP B (Fun R D)) (r : MAP C B)
  → uncurry (h ∘ r) =₁ (uncurry h ∘ productMap (id R) r)
uncurry-pre {R} h r = (Native.funUncurry-restrict h r ▷ swap) then
  comp-assoc swap (productMap r (id R)) (Native.funUncurry h) then
  (Native.funUncurry h ◁ swap-natural r (id R)) then
  (comp-assoc (productMap (id R) r) swap (Native.funUncurry h)) ⁻¹
```
