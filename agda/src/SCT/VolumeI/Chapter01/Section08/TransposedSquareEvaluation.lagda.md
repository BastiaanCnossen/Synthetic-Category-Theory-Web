# Transposing a postcomposed square

Transposition identifies the whole postcomposed cocone with evaluation
of the product square. The composition and restriction-naturality laws
account for its matching, including both associators.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section08.TranspositionComposition as TC
import SCT.VolumeI.Chapter01.Section08.TranspositionRestrictionNaturality as TN
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.TransposedSquareEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section06.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.Transposition 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.CoconeTransposition 𝒯 M ℱ using (transposeCocone)
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯
open import SCT.VolumeI.Chapter01.Section08.SquareCocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.EvaluationSquares 𝒯
open import SCT.VolumeI.Chapter01.Section03.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (pre-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

transposeIso-inverse : {X C E : CAT} {f g : MAP C (Fun X E)} (α : NatIso f g) →
  Iso₂ (transposeIso (invIso α)) (invIso (transposeIso α))
transposeIso-inverse α = (isoInv ◁ invIso (transposeIso-at α)) ∙
  (pre-inverse (funUncurryIso α) swap ∙
  ((preWhisker swap ◁ funUncurryIso-inverse α) ∙ transposeIso-at (invIso α)))

module Evaluation {X A B C D E : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) (k : MAP D (Fun X E)) where
  source = transposeCocone {X} (coconePost k (squareCocone s))
  target = restrictionCocone s (transpose k)
  e = transpose k
  Lu = productRestriction X u
  Ll = productRestriction X l
  Lr = productRestriction X r
  Lv = productRestriction X v
  qr = transpose-pre r k
  qv = transpose-pre v k
  leftEndpoint = transpose-pre u (k ∘ r)
  rightEndpoint = transpose-pre l (k ∘ v)
  leftLeg = qr ▷ Lu
  rightLeg = qv ▷ Ll
  leftAssociator = comp-assoc Lu Lr e
  rightAssociator = comp-assoc Ll Lv e
  leftTotal = leftAssociator ∙ (leftLeg ∙ leftEndpoint)
  rightTotal = rightAssociator ∙ (rightLeg ∙ rightEndpoint)
  qru = transpose-pre (r ∘ u) k
  qvl = transpose-pre (v ∘ l) k
  ar = comp-assoc u r k
  av = comp-assoc l v k
  kr = transposeIso ar
  kv = transposeIso av
  α = k ◁ Square.commute s
  image = transposeIso α
  raw = transposeIso (Cocone.match (coconePost k (squareCocone s)))
  pr = productRestriction-comp X u r
  pv = productRestriction-comp X l v
  pa = productMap-cong (idIso (id X)) (Square.commute s)
  er = e ◁ pr
  ev = e ◁ pv
  ea = e ◁ pa
  δ = e ◁ Cocone.match (productCocone X s)

  abstract
    raw-normal : Iso₂ raw (invIso kv ∙ (image ∙ kr))
    raw-normal = isoComp-cong (transposeIso-inverse av) (transposeIso-comp α ar) ∙
      transposeIso-comp (invIso av) (α ∙ ar)

    product-normal : Iso₂ δ (invIso ev ∙ (ea ∙ er))
    product-normal = isoComp-cong (post-inverse e pv) (postWhisker-isoComp-at e pa pr) ∙
      postWhisker-isoComp-at e (invIso pv) (pa ∙ pr)

    evaluated-square : Iso₂ (δ ∙ leftTotal) (rightTotal ∙ raw)
    evaluated-square = isoComp-cong (idIso rightTotal) (invIso raw-normal) ∙
      (paste-squares (image ∙ kr) (ea ∙ er) (invIso kv) (invIso ev)
        leftTotal qvl rightTotal
        (paste-squares kr er image ea leftTotal qru qvl
          (invIso (TC.CompositorEvaluation.comparison 𝒯 M ℱ u r k))
          (invIso (TN.Restriction.comparison 𝒯 M ℱ (Square.commute s) k)))
        (move-square ev rightTotal qvl kv
          (invIso (TC.CompositorEvaluation.comparison 𝒯 M ℱ l v k))) ∙
        isoComp-cong product-normal (idIso leftTotal))

    comparison : CoconeIso source target
    comparison = record
      { leftIso = qr ; rightIso = qv
      ; compatible = close-evaluation-square leftEndpoint rightEndpoint leftLeg rightLeg
          leftAssociator rightAssociator raw δ evaluated-square }
```
