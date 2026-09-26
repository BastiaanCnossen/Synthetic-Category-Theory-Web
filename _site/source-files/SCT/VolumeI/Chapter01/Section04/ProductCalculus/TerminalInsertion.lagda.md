# Inserting the terminal factor

Naturality of the inverse right product unitor, used by both the core
universal property and its specialization to animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section04.ProductCalculus.TerminalInsertion
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯

module TerminalInsertion where
  insert-terminal-natural : {A B : CAT} (f : MAP A B)
    → (productMap f (id One) ∘ product-unitʳ-inverse A) =₁
        (product-unitʳ-inverse B ∘ f)
  insert-terminal-natural {A} {B} f = pair-iso
    ((comp-unitˡ f ∙ project-pair₁ (id B) (terminate B) f) ⁻¹ ∙
      (comp-unitʳ f ∙ ((f ◁ pair-β₁ (id A) (terminate A)) ∙
        (comp-assoc (product-unitʳ-inverse A) pr₁ f ∙
          project-pair₁ (f ∘ pr₁) (id One ∘ pr₂) (product-unitʳ-inverse A)))))
    (terminal-iso _ _)

```
