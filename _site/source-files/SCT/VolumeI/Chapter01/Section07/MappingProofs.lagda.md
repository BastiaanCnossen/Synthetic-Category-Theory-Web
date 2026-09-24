# Uncurrying, vertical composition, and restriction

These aliases collect the comparisons for uncurrying a vertical composite,
an inverse, or a restriction of the inputs. The cone calculations use
their statements without unfolding the underlying evaluation and product
proofs. All comparison maps retain their definitions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section04.ParameterChange as ParameterChange

import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.MappingProofs
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M) where

module Original = Setup 𝒯 M ℱ
open Original hiding (funUncurryIso-comp; funUncurryIso-inverse; funUncurry-restrict-inputs)
module Change = Setup 𝒯 M ℱ
module Compatible = Setup 𝒯 M ℱ

abstract
  funUncurryIso-comp : {X C D : CAT} {f g h : MAP X (Fun C D)}
    (β : g =₁ h) (α : f =₁ g) →
    (funUncurryIso (β ∙ α)) =₂ (funUncurryIso β ∙ funUncurryIso α)
  funUncurryIso-comp = Original.funUncurryIso-comp

  funUncurryIso-inverse : {X C D : CAT} {f g : MAP X (Fun C D)} (α : f =₁ g) →
    (funUncurryIso (α ⁻¹)) =₂ ((funUncurryIso α) ⁻¹)
  funUncurryIso-inverse = Change.funUncurryIso-inverse

  funUncurry-restrict-inputs : {Y X C D : CAT} {f g : MAP X (Fun C D)}
    (α : f =₁ g) (σ : MAP Y X) →
    (funUncurry-restrict g σ ∙ funUncurryIso (α ▷ σ)) =₂
      ((funUncurryIso α ▷ productMap σ (id C)) ∙ funUncurry-restrict f σ)
  funUncurry-restrict-inputs = Compatible.funUncurry-restrict-inputs
```


