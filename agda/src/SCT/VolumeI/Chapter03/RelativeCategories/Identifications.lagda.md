# Identifications of functors over a base

A comparison of relative functors includes compatibility with their
specified triangles. Composition, inversion, and whiskering retain this
compatibility. The associator is the original associator of functors;
its compatibility over the base is the projection-square pentagon
calculation already established in Chapter 1.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as ProjectionSquares
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter03.RelativeCategories.Identifications
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
  using (FunctorOver; identity-over; compose-over)
module Squares = ProjectionSquares 𝒯
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (triangle-whiskered; unit-square-projection)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (IsEmbedding)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.PrescribedLifting 𝒯 P using (embedding-lift)

record FunctorOverIso {C D S : CAT} {f : MAP C S} {g : MAP D S}
  (u v : FunctorOver f g) : Set m where
  field
    underlying : FunctorLift.lift u =₁ FunctorLift.lift v
    compatible : (FunctorLift.comparison v ∙ (g ◁ underlying)) =₂ FunctorLift.comparison u

identity-iso-over : {C D S : CAT} {f : MAP C S} {g : MAP D S}
  (u : FunctorOver f g) → FunctorOverIso u u
identity-iso-over {g = g} u = record
  { underlying = idIso (FunctorLift.lift u)
  ; compatible = isoComp-unitʳ-at (FunctorLift.comparison u) ∙
      isoComp-cong (idIso (FunctorLift.comparison u)) (postWhisker-idIso g (FunctorLift.lift u)) }

compose-iso-over : {C D S : CAT} {f : MAP C S} {g : MAP D S}
  {u v w : FunctorOver f g} → FunctorOverIso v w → FunctorOverIso u v → FunctorOverIso u w
compose-iso-over {g = g} {u} {v} {w} β α = record
  { underlying = FunctorOverIso.underlying β ∙ FunctorOverIso.underlying α
  ; compatible = Squares.compose-square g (FunctorLift.comparison u) (FunctorLift.comparison v)
      (FunctorLift.comparison w) (FunctorOverIso.underlying β) (FunctorOverIso.underlying α)
      (FunctorOverIso.compatible β) (FunctorOverIso.compatible α) }

inverse-iso-over : {C D S : CAT} {f : MAP C S} {g : MAP D S}
  {u v : FunctorOver f g} → FunctorOverIso u v → FunctorOverIso v u
inverse-iso-over {g = g} {u} {v} α = record
  { underlying = (FunctorOverIso.underlying α) ⁻¹
  ; compatible = Squares.inverse-square g (FunctorLift.comparison u) (FunctorLift.comparison v)
      (FunctorOverIso.underlying α) (FunctorOverIso.compatible α) }

prewhisker-over : {B C D S : CAT} {f : MAP B S} {g : MAP C S} {h : MAP D S}
  {v w : FunctorOver g h} (u : FunctorOver f g) → FunctorOverIso v w →
  FunctorOverIso (compose-over v u) (compose-over w u)
prewhisker-over {h = h} {v} {w} u α = record
  { underlying = FunctorOverIso.underlying α ▷ FunctorLift.lift u
  ; compatible = Squares.pre-square h (FunctorLift.lift u) (FunctorLift.comparison v)
      (FunctorLift.comparison w) (FunctorLift.comparison u) (FunctorOverIso.underlying α) (FunctorOverIso.compatible α) }

postwhisker-over : {B C D S : CAT} {f : MAP B S} {g : MAP C S} {h : MAP D S}
  (w : FunctorOver g h) {u v : FunctorOver f g} → FunctorOverIso u v →
  FunctorOverIso (compose-over w u) (compose-over w v)
postwhisker-over {h = h} w {u} {v} α = record
  { underlying = FunctorLift.lift w ◁ FunctorOverIso.underlying α
  ; compatible = Squares.post-square h (FunctorLift.lift w) (FunctorLift.comparison w)
      (FunctorLift.comparison u) (FunctorLift.comparison v) (FunctorOverIso.underlying α) (FunctorOverIso.compatible α) }

associator-over : {A B C D S : CAT} {f : MAP A S} {g : MAP B S} {h : MAP C S} {k : MAP D S}
  (u : FunctorOver f g) (v : FunctorOver g h) (w : FunctorOver h k) →
  FunctorOverIso (compose-over (compose-over w v) u) (compose-over w (compose-over v u))
associator-over {k = k} u v w = record
  { underlying = comp-assoc (FunctorLift.lift u) (FunctorLift.lift v) (FunctorLift.lift w)
  ; compatible = Squares.associator-square k (FunctorLift.lift w) (FunctorLift.lift v) (FunctorLift.lift u)
      (FunctorLift.comparison w) (FunctorLift.comparison v) (FunctorLift.comparison u) }

left-unit-over : {C D S : CAT} {f : MAP C S} {g : MAP D S}
  (u : FunctorOver f g) → FunctorOverIso (compose-over (identity-over g) u) u
left-unit-over {g = g} u = record
  { underlying = comp-unitˡ (FunctorLift.lift u)
  ; compatible = isoComp-cong (idIso (FunctorLift.comparison u))
      ((cancel-right (comp-assoc (FunctorLift.lift u) (id _) g) (g ◁ comp-unitˡ (FunctorLift.lift u)) ∙
        isoComp-cong (triangle-whiskered (FunctorLift.lift u) g)
          (idIso ((comp-assoc (FunctorLift.lift u) (id _) g) ⁻¹))) ⁻¹) }

right-unit-over : {C D S : CAT} {f : MAP C S} {g : MAP D S}
  (u : FunctorOver f g) → FunctorOverIso (compose-over u (identity-over f)) u
right-unit-over {f = f} {g} u = record
  { underlying = comp-unitʳ (FunctorLift.lift u)
  ; compatible = (unit-square-projection g (FunctorLift.lift u) f (FunctorLift.comparison u)) ⁻¹ }
```

## Functors over an embedding

Two functors over an embedding are identified over the base. Lift the
identification of their images through the embedding; the specified
image of the lift gives the compatibility with the two triangles. The
underlying identification is the specified lift. It is not asserted to
agree with `lift-unique` applied to `embedding-reflect`, which supplies
only an identification of the underlying functors.

```agda
embedding-iso-over : {C S : CAT} (f : MAP C S) → IsEmbedding f →
  {X : CAT} {t : MAP X S} (u v : FunctorOver t f) → FunctorOverIso u v
embedding-iso-over f ef u v = record { underlying = FunctorLift.lift chosen
  ; compatible = cancel-inverse θv θu ∙ isoComp-cong (idIso θv) (FunctorLift.comparison chosen) }
  where
  θu = FunctorLift.comparison u
  θv = FunctorLift.comparison v
  chosen = embedding-lift f ef (FunctorLift.lift u) (FunctorLift.lift v) (θv ⁻¹ ∙ θu)
```

## Identifications between relative identifications

```agda
record FunctorOverIso₂ {C D S : CAT} {f : MAP C S} {g : MAP D S}
  {u v : FunctorOver f g} (Φ Ψ : FunctorOverIso u v) : Set m where
  field
    underlying : FunctorOverIso.underlying Φ =₂ FunctorOverIso.underlying Ψ
  boundary = isoComp-cong (idIso (FunctorLift.comparison v)) (postWhisker g ◁ underlying)
  field
    compatible : (FunctorOverIso.compatible Ψ ∙ boundary) =₃ FunctorOverIso.compatible Φ
```
