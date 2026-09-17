# Opaque uncurrying coherence proofs

The cone calculations use these checked statements without unfolding the
underlying evaluation and product proofs. All comparison maps retain their
definitions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section03.ParameterChange as ParameterChange

import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section06.MappingProofs
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M) where

module Original = Setup 𝒯 M ℱ
open Original hiding (funUncurryIso-comp; funUncurryIso-inverse; funUncurry-pre-inputs)
module Change = Setup 𝒯 M ℱ
module Compatible = Setup 𝒯 M ℱ

abstract
  funUncurryIso-comp : {X C D : CAT} {f g h : MAP X (Fun C D)}
    (β : NatIso g h) (α : NatIso f g) →
    Iso₂ (funUncurryIso (β ∙ α)) (funUncurryIso β ∙ funUncurryIso α)
  funUncurryIso-comp = Original.funUncurryIso-comp

  funUncurryIso-inverse : {X C D : CAT} {f g : MAP X (Fun C D)} (α : NatIso f g) →
    Iso₂ (funUncurryIso (invIso α)) (invIso (funUncurryIso α))
  funUncurryIso-inverse = Change.funUncurryIso-inverse

  funUncurry-pre-inputs : {Y X C D : CAT} {f g : MAP X (Fun C D)}
    (α : NatIso f g) (σ : MAP Y X) →
    Iso₂ (funUncurry-pre g σ ∙ funUncurryIso (α ▷ σ))
      ((funUncurryIso α ▷ productMap σ (id C)) ∙ funUncurry-pre f σ)
  funUncurry-pre-inputs = Compatible.funUncurry-pre-inputs
```


