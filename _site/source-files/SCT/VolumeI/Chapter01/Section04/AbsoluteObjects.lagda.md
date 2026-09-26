# Absolute objects and the terminal context

For an anima `A`, currying the first projection gives an equivalence
`A → Map One A`. Its inverse evaluates at the terminal variable. This
formalizes the last proposition of Section 1.4. It does not introduce a
generalized-object type or change the agreed meaning of `Obj-abs`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Currying as Currying

module SCT.VolumeI.Chapter01.Section04.AbsoluteObjects
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M

open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.TerminalInsertion 𝒯 public
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (core-of-anima)

open TerminalInsertion

module TerminalContext (A : CAT) (aAn : isAn A) where
  forward : MAP A (Map One A)
  forward = mapCurry aAn pr₁

  backward : MAP (Map One A) A
  backward = mapEval ∘ product-unitʳ-inverse (Map One A)

  forward-β : (mapUncurry forward) =₁ pr₁
  forward-β = mapCurry-β aAn pr₁
```

The core universal property first proves that the inclusion is an equivalence.
Beta identifies its composite with the displayed inverse. Cancellation through
that equivalence then gives the other inverse comparison, as in the manuscript.

```agda
  backward-forward : (backward ∘ forward) =₁ (id A)
  backward-forward = pair-β₁ (id A) (terminate A) ∙
    ((forward-β ▷ product-unitʳ-inverse A) ∙
    ((comp-assoc (product-unitʳ-inverse A) (productMap forward (id One)) mapEval) ⁻¹ ∙
    ((mapEval ◁ (insert-terminal-natural forward) ⁻¹) ∙
      comp-assoc forward (product-unitʳ-inverse (Map One A)) mapEval)))

  backward-isEquiv : IsEquiv backward
  backward-isEquiv = core-of-anima A aAn

  forward-backward : (forward ∘ backward) =₁ (id (Map One A))
  forward-backward = equiv-reflect backward-isEquiv _ _
    ((comp-unitʳ backward) ⁻¹ ∙
      (comp-unitˡ backward ∙
        ((backward-forward ▷ backward) ∙ (comp-assoc backward forward backward) ⁻¹)))

  forward-backward-uncurried : (mapUncurry (forward ∘ backward)) =₁ mapEval
  forward-backward-uncurried = mapUncurry-id One A ∙ mapUncurryIso forward-backward

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward
    ; sectionIso = backward-forward ⁻¹
    ; retractionIso = forward-backward ⁻¹
    }

```
