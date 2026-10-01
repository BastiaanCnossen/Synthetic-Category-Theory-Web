# Product symmetry and changes of parameter

These calculations retain the actual pairing maps used for symmetry and
products of functors.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as Products

module SCT.VolumeI.Chapter05.Section02.MappingCalculus.ProductSymmetry
  {l : Level} (T : Theory l l l) where

open View T
open Calculus T using (_then_; pair-pre; pair-cong)
open Products vocabulary terminal products productLaws composition using (productMap; productMap-comp; swap; swap-swap)

twice : {A B D : CAT} (f : MAP (A × B) D) → ((f ∘ swap) ∘ swap) =₁ f
twice {A} {B} f = comp-assoc swap swap f then (f ◁ swap-swap A B) then comp-unitʳ f

swap-natural : {A B C D : CAT} (f : MAP A C) (g : MAP B D)
  → (productMap f g ∘ swap) =₁ (swap ∘ productMap g f)
swap-natural f g = pair-pre (f ∘ pr₁) (g ∘ pr₂) swap then
  pair-cong (comp-assoc swap pr₁ f then (f ◁ pair-β₁ pr₂ pr₁))
    (comp-assoc swap pr₂ g then (g ◁ pair-β₂ pr₂ pr₁)) then
  (pair-pre pr₂ pr₁ (productMap g f) then
    pair-cong (pair-β₂ (g ∘ pr₁) (f ∘ pr₂)) (pair-β₁ (g ∘ pr₁) (f ∘ pr₂))) ⁻¹

independent : {A B C D : CAT} (f : MAP A C) (g : MAP B D)
  → (productMap f (id D) ∘ productMap (id A) g) =₁
    (productMap (id C) g ∘ productMap f (id B))
independent {A} {B} {C} {D} f g = productMap-comp (id A) f g (id D) then
  pair-cong (comp-unitʳ f ▷ pr₁) (comp-unitˡ g ▷ pr₂) then
  (pair-cong (comp-unitˡ f ▷ pr₁) (comp-unitʳ g ▷ pr₂)) ⁻¹ then
  (productMap-comp f (id C) (id B) g) ⁻¹
```
