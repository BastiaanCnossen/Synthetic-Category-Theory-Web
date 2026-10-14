# Frames for a precomposition triangle

A chosen evaluated composite determines a common middle frame for the
triangle. This calculation retains the two product projections and does
not identify composition with a projection strictly.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionTriangleFrames
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module At {C D : CAT} (K : CAT) (l : MAP C D) (r : MAP D C)
  (u : funUncurry (funPre {D = K} l ∘ funPre {D = K} r) =₁
    (funEval ∘ pair (pr₁ {Fun C K} {C}) (r ∘ (l ∘ pr₂)))) where
  X = Fun C K
  Y = Fun D K
  L : MAP X Y
  L = funPre {D = K} r
  R : MAP Y X
  R = funPre {D = K} l
  e : MAP (X × C) K
  e = funEval
  W : MAP (X × D) (X × C)
  W = productMap (id X) r
  H : MAP (X × C) (X × C)
  H = pair pr₁ (r ∘ (l ∘ pr₂))
  outside-object : MAP (X × D) K
  outside-object = e ∘ pair pr₁ (r ∘ pr₂)
  middle-object : MAP (X × D) K
  middle-object = e ∘ pair pr₁ (r ∘ (l ∘ (r ∘ pr₂)))
  outside : funUncurry L =₁ outside-object
  outside = (e ◁ pair-cong (comp-unitˡ pr₁) (idIso (r ∘ pr₂))) ∙ funPre-β {D = K} r
  first-coordinate : (pr₁ ∘ W) =₁ (pr₁ {X} {D})
  first-coordinate = comp-unitˡ pr₁ ∙ pair-β₁ (id X ∘ pr₁) (r ∘ pr₂)
  second-coordinate : (pr₂ ∘ W) =₁ (r ∘ pr₂ {X} {D})
  second-coordinate = pair-β₂ (id X ∘ pr₁) (r ∘ pr₂)
  nested-coordinate : ((r ∘ (l ∘ pr₂)) ∘ W) =₁ (r ∘ (l ∘ (r ∘ pr₂ {X} {D})))
  nested-coordinate = (r ◁ ((l ◁ second-coordinate) ∙ comp-assoc W pr₂ l)) ∙ comp-assoc W (l ∘ pr₂) r
  product-frame : (H ∘ W) =₁ pair (pr₁ {X} {D}) (r ∘ (l ∘ (r ∘ pr₂)))
  product-frame = pair-cong first-coordinate nested-coordinate ∙ pair-pre pr₁ (r ∘ (l ∘ pr₂)) W
  evaluation-frame : ((e ∘ H) ∘ W) =₁ middle-object
  evaluation-frame = (e ◁ product-frame) ∙ comp-assoc W H e
  restricted-frame : (funUncurry (R ∘ L) ∘ W) =₁ middle-object
  restricted-frame = evaluation-frame ∙ (u ▷ W)
  middle : funUncurry ((L ∘ R) ∘ L) =₁ middle-object
  middle = evaluation-frame ∙ ((u ▷ W) ∙
    (funPre-uncurry r (R ∘ L) ∙ funUncurryIso (comp-assoc L R L)))

  abstract
    post-comparison : (middle ∙ funUncurryIso ((comp-assoc L R L) ⁻¹)) =₂
      (restricted-frame ∙ funPre-uncurry r (R ∘ L))
    post-comparison = cancel-right (funUncurryIso (comp-assoc L R L))
        (restricted-frame ∙ funPre-uncurry r (R ∘ L)) ∙
      isoComp-cong
        ((isoComp-assoc-at restricted-frame (funPre-uncurry r (R ∘ L)) (funUncurryIso (comp-assoc L R L))) ⁻¹ ∙
          (isoComp-assoc-at evaluation-frame (u ▷ W)
            (funPre-uncurry r (R ∘ L) ∙ funUncurryIso (comp-assoc L R L))) ⁻¹)
        (funUncurryIso-inverse (comp-assoc L R L))
```
