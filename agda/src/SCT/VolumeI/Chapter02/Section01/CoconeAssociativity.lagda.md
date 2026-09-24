# Associativity of postcomposition on cocones

Postcomposing a whole cocone twice agrees with postcomposing by the
composite. Its leg comparisons are the associators, and the matching
comparison is the pentagon together with naturality of the associator.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section03.Structural as Structural

module SCT.VolumeI.Chapter02.Section01.CoconeAssociativity
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconePostcomposition 𝒯 public
open import SCT.VolumeI.Chapter01.Section04.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯 using (inverse-composite)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at)

module Post {A B C D E H : CAT} {u : MAP A B} {v : MAP A C}
  (F : MAP E H) (G : MAP D E) (s : Cocone u v D) where
  p : MAP B D
  p = Cocone.left s
  q : MAP C D
  q = Cocone.right s
  τ : (p ∘ u) =₁ (q ∘ v)
  τ = Cocone.match s

  module Leg {X : CAT} (r : MAP X D) (w : MAP A X) where
    assoc₀ = comp-assoc w r (F ∘ G)
    assoc₁ = comp-assoc w (G ∘ r) F
    assoc₂ = comp-assoc w r G
    composite = (F ◁ assoc₂) ∙ assoc₁
    middle = comp-assoc (r ∘ w) G F
    boundary = comp-assoc r G F ▷ w
    abstract
      pentagon : (composite ∙ boundary) =₂ (middle ∙ assoc₀)
      pentagon = (pentagon-whiskered w r G F) ⁻¹ ∙
        isoComp-assoc-at (F ◁ assoc₂) assoc₁ boundary

  module L = Leg p u
  module R = Leg q v
  raw₀ = (F ∘ G) ◁ τ
  raw₁ = F ◁ (G ◁ τ)
  normalized = R.composite ⁻¹ ∙ (raw₁ ∙ L.composite)

  abstract
    inner : (F ◁ (R.assoc₂ ⁻¹ ∙ ((G ◁ τ) ∙ L.assoc₂))) =₂
      ((F ◁ R.assoc₂) ⁻¹ ∙ (raw₁ ∙ (F ◁ L.assoc₂)))
    inner = isoComp-cong (post-inverse F R.assoc₂)
        (postWhisker-isoComp-at F (G ◁ τ) L.assoc₂) ∙
      postWhisker-isoComp-at F (R.assoc₂ ⁻¹) ((G ◁ τ) ∙ L.assoc₂)

    normalize : (Cocone.match (coconePost F (coconePost G s))) =₂ normalized
    normalize = isoComp-cong ((inverse-composite (F ◁ R.assoc₂) R.assoc₁) ⁻¹)
        (idIso (raw₁ ∙ L.composite)) ∙
      ((isoComp-assoc-at (R.assoc₁ ⁻¹) ((F ◁ R.assoc₂) ⁻¹) (raw₁ ∙ L.composite)) ⁻¹ ∙
      (isoComp-cong (idIso (R.assoc₁ ⁻¹))
        (isoComp-cong (idIso ((F ◁ R.assoc₂) ⁻¹))
          (isoComp-assoc-at raw₁ (F ◁ L.assoc₂) L.assoc₁)) ∙
      (isoComp-cong (idIso (R.assoc₁ ⁻¹))
        (isoComp-assoc-at ((F ◁ R.assoc₂) ⁻¹) (raw₁ ∙ (F ◁ L.assoc₂)) L.assoc₁) ∙
        isoComp-cong (idIso (R.assoc₁ ⁻¹)) (isoComp-cong inner (idIso L.assoc₁)))))

    compatible :
      (Cocone.match (coconePost F (coconePost G s)) ∙ L.boundary) =₂
      (R.boundary ∙ Cocone.match (coconePost (F ∘ G) s))
    compatible = paste-squares (raw₀ ∙ L.assoc₀) (raw₁ ∙ L.composite)
        (R.assoc₀ ⁻¹) (R.composite ⁻¹) L.boundary R.middle R.boundary
        (paste-squares L.assoc₀ L.composite raw₀ raw₁ L.boundary L.middle R.middle
          L.pentagon ((postWhisker-comp-at τ G F) ⁻¹))
        (move-square R.composite R.boundary R.middle R.assoc₀ R.pentagon) ∙
      isoComp-cong normalize (idIso L.boundary)

  comparison : CoconeIso (coconePost (F ∘ G) s) (coconePost F (coconePost G s))
  comparison = record
    { leftIso = comp-assoc p G F ; rightIso = comp-assoc q G F
    ; compatible = compatible }

coconePost-assoc : {A B C D E H : CAT} {u : MAP A B} {v : MAP A C}
  (F : MAP E H) (G : MAP D E) (s : Cocone u v D) →
  CoconeIso (coconePost (F ∘ G) s) (coconePost F (coconePost G s))
coconePost-assoc = Post.comparison
```
