# Common middle frames for postcomposition triangles

The two routes through a triangle of postcomposition functors have the
same middle endpoint comparison. This is an instance of substitution
coherence for uncurrying and naturality of whiskering.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PostcompositionTriangleFrames
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingSubstitution 𝒯 M ℱ using (funPost-uncurry-restrict)
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)

import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module At {C D : CAT} (K : CAT) (l : MAP C D) (r : MAP D C) where
  L : MAP (Fun K C) (Fun K D)
  L = funPost l
  R : MAP (Fun K D) (Fun K C)
  R = funPost r
  e : MAP (Fun K C × K) C
  e = funEval
  d : MAP (Fun K D × K) D
  d = funEval
  βl : funUncurry L =₁ (l ∘ e)
  βl = funPost-β l
  βr : funUncurry R =₁ (r ∘ d)
  βr = funPost-β r
  σ : MAP (Fun K C × K) (Fun K D × K)
  σ = productMap L (id K)
  u : funUncurry (R ∘ L) =₁ (r ∘ (l ∘ e))
  u = (r ◁ βl) ∙ funPost-uncurry r L
  v : funUncurry (L ∘ R) =₁ (l ∘ (r ∘ d))
  v = (l ◁ βr) ∙ funPost-uncurry l R
  middle : funUncurry ((L ∘ R) ∘ L) =₁ (l ∘ (r ∘ (l ∘ e)))
  middle = (l ◁ u) ∙ (funPost-uncurry l (R ∘ L) ∙ funUncurryIso (comp-assoc L R L))
  restricted : funUncurry ((L ∘ R) ∘ L) =₁ (l ∘ (r ∘ (l ∘ e)))
  restricted = (l ◁ (r ◁ βl)) ∙
    (((l ◁ comp-assoc σ d r) ∙ comp-assoc σ (r ∘ d) l) ∙
      ((v ▷ σ) ∙ funUncurry-restrict (L ∘ R) L))

  private
    lead = l ◁ (r ◁ βl)
    first = l ◁ comp-assoc σ d r
    beta = l ◁ (βr ▷ σ)
    restriction = l ◁ funUncurry-restrict R L
    post = funPost-uncurry l (R ∘ L)
    assoc = funUncurryIso (comp-assoc L R L)
    after = comp-assoc σ (funUncurry R) l
    shifted = comp-assoc σ (r ∘ d) l
    image = (l ◁ βr) ▷ σ
    other = funPost-uncurry l R ▷ σ
    last = funUncurry-restrict (L ∘ R) L

  abstract
    expanded-unit : (l ◁ u) =₂ (lead ∙ (first ∙ (beta ∙ restriction)))
    expanded-unit = isoComp-cong (idIso lead)
      (isoComp-cong (idIso first) (postWhisker-isoComp-at l (βr ▷ σ) (funUncurry-restrict R L)) ∙
        postWhisker-isoComp-at l (comp-assoc σ d r) ((βr ▷ σ) ∙ funUncurry-restrict R L)) ∙
      postWhisker-isoComp-at l (r ◁ βl) (funPost-uncurry r L)

    tail : (beta ∙ (after ∙ (other ∙ last))) =₂ (shifted ∙ ((v ▷ σ) ∙ last))
    tail = isoComp-cong (idIso shifted)
        (isoComp-cong ((preWhisker-isoComp-at (l ◁ βr) (funPost-uncurry l R) σ) ⁻¹) (idIso last) ∙
          (isoComp-assoc-at image other last) ⁻¹) ∙
      isoComp-assoc-at shifted image (other ∙ last) ∙
      isoComp-cong ((whisker-mixed-at (βr) σ l) ⁻¹) (idIso (other ∙ last)) ∙
      (isoComp-assoc-at beta after (other ∙ last)) ⁻¹

    comparison : middle =₂ restricted
    comparison = isoComp-cong (idIso lead) ((isoComp-assoc-at first shifted ((v ▷ σ) ∙ last)) ⁻¹) ∙
      isoComp-cong (idIso lead) (isoComp-cong (idIso first) tail) ∙
      isoComp-cong (idIso lead) (isoComp-cong (idIso first)
        (isoComp-cong (idIso beta) (funPost-uncurry-restrict l R L))) ∙
      isoComp-cong (idIso lead)
        (isoComp-cong (idIso first) (isoComp-assoc-at beta restriction (post ∙ assoc)) ∙
          isoComp-assoc-at first (beta ∙ restriction) (post ∙ assoc)) ∙
      isoComp-assoc-at lead (first ∙ (beta ∙ restriction)) (post ∙ assoc) ∙
      isoComp-cong expanded-unit (idIso (post ∙ assoc))

    post-comparison : (middle ∙ funUncurryIso ((comp-assoc L R L) ⁻¹)) =₂
      ((l ◁ u) ∙ funPost-uncurry l (R ∘ L))
    post-comparison = cancel-right (funUncurryIso (comp-assoc L R L))
        ((l ◁ u) ∙ funPost-uncurry l (R ∘ L)) ∙
      isoComp-cong
        ((isoComp-assoc-at (l ◁ u) (funPost-uncurry l (R ∘ L)) (funUncurryIso (comp-assoc L R L))) ⁻¹)
        (funUncurryIso-inverse (comp-assoc L R L))
```
