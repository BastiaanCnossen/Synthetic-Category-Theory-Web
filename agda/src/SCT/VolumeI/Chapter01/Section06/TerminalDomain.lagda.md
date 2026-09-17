# Evaluation at the terminal object

This proves `lem:Functors_Out_Of_Point`. The inverse curries the first
projection, and both composites are compared with the identity.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.Currying as Currying

import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section06.TerminalDomain
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (F : Categories.FunctorCategories 𝒯 M) where

open Setup 𝒯

open Currying 𝒯 M F

private
  insert-terminal-natural : {A B : CAT} (f : MAP A B)
    → =₁ (productMap f (id One) ∘ product-unit-inverse A)
        (product-unit-inverse B ∘ f)
  insert-terminal-natural {A} {B} f = pair-iso
    (invIso (comp-unitˡ f ∙ project-pair₁ (id B) (terminate B) f) ∙
      (comp-unitʳ f ∙ ((f ◁ pair-β₁ (id A) (terminate A)) ∙
        (comp-assoc (product-unit-inverse A) pr₁ f ∙
          project-pair₁ (f ∘ pr₁) (id One ∘ pr₂) (product-unit-inverse A)))))
    (terminal-iso _ _)

module TerminalContext (A : CAT) where
  forward : MAP A (Fun One A)
  forward = funCurry pr₁

  backward : MAP (Fun One A) A
  backward = funEval ∘ product-unit-inverse (Fun One A)

  forward-β : =₁ (funUncurry forward) pr₁
  forward-β = funCurry-β pr₁
```

The first inverse comparison is beta evaluated on `A × One`. The other
uses beta over `Fun One A` and the product unitor before reflecting through
uncurrying. Both are comparisons of functors on the entire source category.

```agda
  backward-forward : =₁ (backward ∘ forward) (id A)
  backward-forward = pair-β₁ (id A) (terminate A) ∙
    ((forward-β ▷ product-unit-inverse A) ∙
    (invIso (comp-assoc (product-unit-inverse A) (productMap forward (id One)) funEval) ∙
    ((funEval ◁ invIso (insert-terminal-natural forward)) ∙
      comp-assoc forward (product-unit-inverse (Fun One A)) funEval)))

  forward-backward-uncurried : =₁ (funUncurry (forward ∘ backward)) funEval
  forward-backward-uncurried = comp-unitʳ funEval ∙
    ((funEval ◁ product-unit-section (Fun One A)) ∙
    (comp-assoc pr₁ (product-unit-inverse (Fun One A)) funEval ∙
    (pair-β₁ (backward ∘ pr₁) (id One ∘ pr₂) ∙
    ((forward-β ▷ productMap backward (id One)) ∙ funUncurry-pre forward backward))))

  forward-backward : =₁ (forward ∘ backward) (id (Fun One A))
  forward-backward = funReflect _ _
    (invIso (funUncurry-id One A) ∙ forward-backward-uncurried)

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward
    ; sectionIso = invIso backward-forward
    ; retractionIso = invIso forward-backward
    }
```

```agda
  backward-isEquiv : IsEquiv backward
  backward-isEquiv = equiv-inverse forward-isEquiv

evalAt : {C D : CAT} → Obj-abs C → MAP (Fun C D) D
evalAt {C} {D} x = funEval ∘ (productMap (id (Fun C D)) x ∘ product-unit-inverse (Fun C D))

evalAt-point : (D : CAT) → =₁ (evalAt {D = D} (id One)) (TerminalContext.backward D)
evalAt-point D = (funEval ◁ (comp-unitˡ (product-unit-inverse (Fun One D)) ∙
  (productMap-id (Fun One D) One ▷ product-unit-inverse (Fun One D))))

evalAt-point-isEquiv : (D : CAT) → IsEquiv (evalAt {D = D} (id One))
evalAt-point-isEquiv D = equiv-transport (invIso (evalAt-point D)) (TerminalContext.backward-isEquiv D)
```
