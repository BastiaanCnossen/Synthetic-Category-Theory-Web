# Evaluation at the terminal object

This proves `lem:Functors_Out_Of_Point`. The inverse curries the first
projection, and both composites are compared with the identity.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.Currying as Currying

import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.TerminalDomain
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (F : Categories.FunctorCategories 𝒯 M) where

open Setup 𝒯

open Currying 𝒯 M F

private
  insert-terminal-natural : {A B : CAT} (f : MAP A B)
    → (productMap f (id One) ∘ product-unitʳ-inverse A) =₁
        (product-unitʳ-inverse B ∘ f)
  insert-terminal-natural {A} {B} f = pair-iso
    ((comp-unitˡ f ∙ project-pair₁ (id B) (terminate B) f) ⁻¹ ∙
      (comp-unitʳ f ∙ ((f ◁ pair-β₁ (id A) (terminate A)) ∙
        (comp-assoc (product-unitʳ-inverse A) pr₁ f ∙
          project-pair₁ (f ∘ pr₁) (id One ∘ pr₂) (product-unitʳ-inverse A)))))
    (terminal-iso _ _)

module TerminalContext (A : CAT) where
  forward : MAP A (Fun One A)
  forward = funCurry pr₁

  backward : MAP (Fun One A) A
  backward = funEval ∘ product-unitʳ-inverse (Fun One A)

  forward-β : (funUncurry forward) =₁ pr₁
  forward-β = funCurry-β pr₁
```

The first inverse comparison is beta evaluated on `A × One`. The other
uses beta over `Fun One A` and the product unitor before reflecting through
uncurrying. Both are comparisons of functors on the entire source category.

```agda
  backward-forward : (backward ∘ forward) =₁ (id A)
  backward-forward = pair-β₁ (id A) (terminate A) ∙
    ((forward-β ▷ product-unitʳ-inverse A) ∙
    ((comp-assoc (product-unitʳ-inverse A) (productMap forward (id One)) funEval) ⁻¹ ∙
    ((funEval ◁ (insert-terminal-natural forward) ⁻¹) ∙
      comp-assoc forward (product-unitʳ-inverse (Fun One A)) funEval)))

  forward-backward-uncurried : (funUncurry (forward ∘ backward)) =₁ funEval
  forward-backward-uncurried = comp-unitʳ funEval ∙
    ((funEval ◁ product-unitʳ-section (Fun One A)) ∙
    (comp-assoc pr₁ (product-unitʳ-inverse (Fun One A)) funEval ∙
    (pair-β₁ (backward ∘ pr₁) (id One ∘ pr₂) ∙
    ((forward-β ▷ productMap backward (id One)) ∙ funUncurry-restrict forward backward))))

  forward-backward : (forward ∘ backward) =₁ (id (Fun One A))
  forward-backward = funReflect _ _
    ((funUncurry-id One A) ⁻¹ ∙ forward-backward-uncurried)

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward
    ; sectionIso = backward-forward ⁻¹
    ; retractionIso = forward-backward ⁻¹
    }
```

```agda
  backward-isEquiv : IsEquiv backward
  backward-isEquiv = equiv-inverse forward-isEquiv

evalAt : {C D : CAT} → Obj-abs C → MAP (Fun C D) D
evalAt {C} {D} x = funEval ∘ (productMap (id (Fun C D)) x ∘ product-unitʳ-inverse (Fun C D))

evalAt-point : (D : CAT) → (evalAt {D = D} (id One)) =₁ (TerminalContext.backward D)
evalAt-point D = (funEval ◁ (comp-unitˡ (product-unitʳ-inverse (Fun One D)) ∙
  (productMap-id (Fun One D) One ▷ product-unitʳ-inverse (Fun One D))))

evalAt-point-isEquiv : (D : CAT) → IsEquiv (evalAt {D = D} (id One))
evalAt-point-isEquiv D = equiv-transport ((evalAt-point D) ⁻¹) (TerminalContext.backward-isEquiv D)
```
