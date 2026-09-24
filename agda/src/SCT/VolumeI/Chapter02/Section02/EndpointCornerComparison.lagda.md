# Evaluating a whole corner square

A square with an absolute object at its upper-left corner induces a
restriction cone. Converting that cone by terminal-domain evaluation
recovers the cone built from the original endpoint comparisons. The two
leg functors stay fixed, and the specified matching is identified.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section02.EndpointBoundaryComposition as Boundary
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN

module SCT.VolumeI.Chapter02.Section02.EndpointCornerComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.RestrictionEvaluation 𝒯 M ℱ P
open import SCT.VolumeI.Chapter02.Section02.EndpointRestrictionCones 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯
open import SCT.VolumeI.Chapter01.Section04.CoherenceTransport 𝒯
open import SCT.VolumeI.Chapter01.Section04.ProjectionSquares 𝒯 using (post-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module At {A B D : CAT} {u : Obj-abs A} {v : Obj-abs B}
  {f : MAP A D} {g : MAP B D} (s : Square u v f g) (C : CAT) where
  open Endpoints C
  open PointBoundary C using (boundary; boundary-natural)
  δ = Square.commute s
  l = component u (funPre f)
  r = component v (funPre g)
  first = e ◁ preComp u f
  last = e ◁ preComp v g
  middle = e ◁ preCong δ
  left-endpoint = evaluate-pre {C = C} f u
  right-endpoint = evaluate-pre {C = C} g v
  vertex = evaluate-cong {C = C} δ
  left-boundary = boundary (f ∘ u)
  right-boundary = boundary (g ∘ v)
  raw = Cone.match (functorOut s C)
  expected = right-endpoint ⁻¹ ∙ (vertex ∙ left-endpoint)

  endpoint-cone : Cone (evaluate {C = C} u) (evaluate v) (Fun D C)
  endpoint-cone = record { left = funPre f ; right = funPre g ; match = expected }

  abstract
    evaluated-matching : (e ◁ raw) =₂ (last ⁻¹ ∙ (middle ∙ first))
    evaluated-matching = isoComp-cong (post-inverse e (preComp v g))
        (postWhisker-isoComp-at e (preCong δ) (preComp u f)) ∙
      postWhisker-isoComp-at e ((preComp v g) ⁻¹) (preCong δ ∙ preComp u f)

    first-two : ((vertex ∙ left-endpoint) ∙ l) =₂
      (right-boundary ∙ (middle ∙ first))
    first-two = paste-squares first left-endpoint middle vertex
      l left-boundary right-boundary
      ((Boundary.At.comparison 𝒯 M ℱ P u f) ⁻¹)
      ((boundary-natural δ) ⁻¹)

    whole-square : (expected ∙ l) =₂ (r ∙ (e ◁ raw))
    whole-square = isoComp-cong (idIso r) (evaluated-matching ⁻¹) ∙
      paste-squares (middle ∙ first) (vertex ∙ left-endpoint)
        (last ⁻¹) (right-endpoint ⁻¹) l right-boundary r first-two
        (move-square right-endpoint r right-boundary last
          ((Boundary.At.comparison 𝒯 M ℱ P v g) ⁻¹))

    matching : Cone.match (convert (functorOut s C)) =₂ expected
    matching = square-to-changeEndpoints l r (e ◁ raw) expected (whole-square ⁻¹)

  comparison : ConeIso (convert (functorOut s C)) endpoint-cone
  comparison = cone-match-change (funPre f) (funPre g) _ _ matching
```
