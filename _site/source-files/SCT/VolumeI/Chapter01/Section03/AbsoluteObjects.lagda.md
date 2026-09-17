# Absolute objects and the terminal context

For an anima `A`, currying the first projection gives an equivalence
`A → Map One A`. Its inverse evaluates at the terminal variable. This
formalizes the last proposition of Section 1.3. It does not introduce a
generalized-object type or change the agreed meaning of `Obj-abs`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Currying as Currying

module SCT.VolumeI.Chapter01.Section03.AbsoluteObjects
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M

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

module TerminalContext (A : CAT) (aAn : isAn A) where
  forward : MAP A (Map One A)
  forward = mapCurry aAn pr₁

  backward : MAP (Map One A) A
  backward = mapEval ∘ product-unit-inverse (Map One A)

  forward-β : =₁ (mapUncurry forward) pr₁
  forward-β = mapCurry-β aAn pr₁
```

The first inverse comparison is beta evaluated on `A × One`. The other
uses beta over `Map One A` and the product unitor before reflecting through
uncurrying. Both are comparisons of functors on the entire source anima.

```agda
  backward-forward : =₁ (backward ∘ forward) (id A)
  backward-forward = pair-β₁ (id A) (terminate A) ∙
    ((forward-β ▷ product-unit-inverse A) ∙
    (invIso (comp-assoc (product-unit-inverse A) (productMap forward (id One)) mapEval) ∙
    ((mapEval ◁ invIso (insert-terminal-natural forward)) ∙
      comp-assoc forward (product-unit-inverse (Map One A)) mapEval)))

  forward-backward-uncurried : =₁ (mapUncurry (forward ∘ backward)) mapEval
  forward-backward-uncurried = comp-unitʳ mapEval ∙
    ((mapEval ◁ product-unit-section (Map One A)) ∙
    (comp-assoc pr₁ (product-unit-inverse (Map One A)) mapEval ∙
    (pair-β₁ (backward ∘ pr₁) (id One ∘ pr₂) ∙
    ((forward-β ▷ productMap backward (id One)) ∙ mapUncurry-pre forward backward))))

  forward-backward : =₁ (forward ∘ backward) (id (Map One A))
  forward-backward = mapReflect (map-isAn One A) _ _
    (invIso (mapUncurry-id One A) ∙ forward-backward-uncurried)

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward
    ; sectionIso = invIso backward-forward
    ; retractionIso = invIso forward-backward
    }
```
