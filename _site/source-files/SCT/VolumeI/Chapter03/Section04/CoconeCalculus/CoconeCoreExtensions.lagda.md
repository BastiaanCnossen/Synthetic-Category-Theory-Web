# Extending anima cocones into arbitrary targets

A cocone whose two outer vertices are animae lifts into the core of its
target. Extend that lifted cocone, then compose with the core inclusion.
The two comparisons retain the full matching. Reflection of extensions
is supplied separately, since the cone point need not be an anima.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeCoreExtensions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core; coreInclusion; core-isAn)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (IsEmbedding)
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost; coconeIso-post)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeUniversality 𝒯 using (CoconeExtensionProperty)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeCoreLifting 𝒯 M P using (module Lift)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconePostAssociativity 𝒯 M using (coconePost-assoc)

record Factorization {A B C D E : CAT} {u : MAP A B} {v : MAP A C}
  (s : Cocone u v D) (q : Cocone u v E) : Set m where
  field
    functor : MAP D E
    comparison : CoconeIso (coconePost functor s) q

module Extend {A B C D : CAT} {u : MAP A B} {v : MAP A C} (s : Cocone u v D)
  (bAn : isAn B) (cAn : isAn C)
  (embedding : (E : CAT) → IsEmbedding (coreInclusion E))
  (into-anima : (E : CAT) → isAn E → (q : Cocone u v E) → Factorization s q) where

  module At (E : CAT) (q : Cocone u v E) where
    module Lifted = Lift bAn cAn (embedding E) q using (value; comparison)
    chosen : Factorization s Lifted.value
    chosen = into-anima (Core E) (core-isAn E) Lifted.value
    h : MAP D (Core E)
    h = Factorization.functor chosen
    functor : MAP D E
    functor = coreInclusion E ∘ h

    abstract
      comparison : CoconeIso (coconePost functor s) q
      comparison = coconeIso-compose Lifted.comparison
        (coconeIso-compose (coconeIso-post (coreInclusion E) (Factorization.comparison chosen))
          (coconePost-assoc s h (coreInclusion E)))

  abstract
    extensions : ((E : CAT) (F G : MAP D E) →
      CoconeIso (coconePost F s) (coconePost G s) → F =₁ G) → CoconeExtensionProperty s
    extensions reflection = record { factor = At.functor ; factor-β = At.comparison ; reflect = reflection }
```
