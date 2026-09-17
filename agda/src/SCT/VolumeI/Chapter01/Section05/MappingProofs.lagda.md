# Opaque uncurrying coherence proofs

The cone calculations use these checked statements without unfolding the
underlying evaluation and product proofs. All comparison maps retain their
definitions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section03.ParameterChange as ParameterChange

module SCT.VolumeI.Chapter01.Section05.MappingProofs
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

module Original = Setup 𝒯 M
open Original hiding (mapUncurryIso-comp)
module Change = ParameterChange 𝒯 M
module Compatible = Compatibility 𝒯 M

abstract
  mapUncurryIso-comp : {X C D : CAT} {f g h : MAP X (Map C D)}
    (β : NatIso g h) (α : NatIso f g) →
    Iso₂ (mapUncurryIso (β ∙ α)) (mapUncurryIso β ∙ mapUncurryIso α)
  mapUncurryIso-comp = Original.mapUncurryIso-comp

  mapUncurryIso-inverse : {X C D : CAT} {f g : MAP X (Map C D)} (α : NatIso f g) →
    Iso₂ (mapUncurryIso (invIso α)) (invIso (mapUncurryIso α))
  mapUncurryIso-inverse = Change.mapUncurryIso-inverse

  mapUncurry-pre-inputs : {Y X C D : CAT} {f g : MAP X (Map C D)}
    (α : NatIso f g) (σ : MAP Y X) →
    Iso₂ (mapUncurry-pre g σ ∙ mapUncurryIso (α ▷ σ))
      ((mapUncurryIso α ▷ productMap σ (id C)) ∙ mapUncurry-pre f σ)
  mapUncurry-pre-inputs = Compatible.mapUncurry-pre-inputs
```
