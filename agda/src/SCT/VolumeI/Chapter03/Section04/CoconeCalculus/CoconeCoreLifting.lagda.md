# Lifting cocones from animae to a core

Lift the two legs using the universal property of the core. The core
embedding lifts their matching with its specified image. This produces
a cocone in the core and a comparison of the entire resulting cocone
with the original one.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeCoreLifting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core; coreInclusion; module CoreLift)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (IsEmbedding)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (untransport)
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter03.Section01.Lifting.EmbeddingLifting 𝒯 P using (embedding-lift)

module Lift {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (bAn : isAn B) (cAn : isAn C) (embedding : IsEmbedding (coreInclusion E)) (s : Cocone u v E) where
  i = coreInclusion E
  module F = CoreLift bAn (Cocone.left s) using (lift; comparison)
  module G = CoreLift cAn (Cocone.right s) using (lift; comparison)
  retargeted = coconeRetarget s (i ∘ F.lift) (i ∘ G.lift) (F.comparison ⁻¹) (G.comparison ⁻¹)
  L = comp-assoc u F.lift i
  R = comp-assoc v G.lift i
  raw = R ∙ (Cocone.match retargeted ∙ L ⁻¹)
  abstract
    chosen : FunctorLift (postWhisker i) raw
    chosen = embedding-lift i embedding (F.lift ∘ u) (G.lift ∘ v) raw

  raw-value : Cocone u v (Core E)
  raw-value = record { left = F.lift ; right = G.lift ; match = FunctorLift.lift chosen }

  abstract
    matching : Cocone.match (coconePost i raw-value) =₂ Cocone.match retargeted
    matching = untransport L R (Cocone.match retargeted) ∙
      isoComp-cong (idIso (R ⁻¹)) (isoComp-cong (FunctorLift.comparison chosen) (idIso L))

    raw-comparison : CoconeIso (coconePost i raw-value) s
    raw-comparison = coconeIso-compose
      (coconeIso-inverse (coconeRetarget-β s (i ∘ F.lift) (i ∘ G.lift) (F.comparison ⁻¹) (G.comparison ⁻¹)))
      (cocone-match-change _ _ _ _ matching)

  abstract
    value : Cocone u v (Core E)
    value = raw-value

    comparison : CoconeIso (coconePost i value) s
    comparison = raw-comparison
```
