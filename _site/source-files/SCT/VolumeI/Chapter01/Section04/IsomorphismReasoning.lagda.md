# Reading identifications from left to right

These combinators display a proof between specified identifications in
its reading order. Each step still supplies an `Iso₂`; no identifications
are discarded, and no normalization or proof irrelevance is assumed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section04.IsomorphismReasoning
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯

infix 1 begin₂_
infixr 2 _=₂⟨_⟩_
infix 3 _∎₂

begin₂_ : {X Y : CAT} {f g : MAP X Y} {α β : f =₁ g} →
  α =₂ β → α =₂ β
begin₂ proof = proof

_=₂⟨_⟩_ : {X Y : CAT} {f g : MAP X Y} (α : f =₁ g) {β γ : f =₁ g} →
  α =₂ β → β =₂ γ → α =₂ γ
α =₂⟨ first ⟩ second = second ∙ first

_∎₂ : {X Y : CAT} {f g : MAP X Y} (α : f =₁ g) → α =₂ α
α ∎₂ = idIso α
```
