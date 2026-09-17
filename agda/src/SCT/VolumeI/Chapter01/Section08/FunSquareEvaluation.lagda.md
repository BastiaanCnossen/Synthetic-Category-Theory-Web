# Evaluating the induced functor-category square

The composition comparison is the remaining input to this intermediate
calculation. Together with the proved isomorphism comparison, it identifies
the evaluated functor-category square with postcomposition of the product square.
The conclusion includes compatibility of the matchings.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.FunSquareEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section06.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section03.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section03.CoherenceTransport 𝒯
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section05.ConeRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯
open import SCT.VolumeI.Chapter01.Section08.FunRestrictionCones 𝒯 M ℱ using (uncurryRestriction)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.FunPrecompositionCongruence 𝒯 M ℱ P using (preCong-at)
open import SCT.VolumeI.Chapter01.Section08.EvaluationSquares 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

CompositorAt : {X A B C E : CAT} (f : MAP A B) (g : MAP B C)
  (h : MAP X (Fun C E)) → Set m
CompositorAt {X} f g h = =₂
  (funPre-uncurry (g ∘ f) h ∙ funUncurryIso (preComp f g ▷ h))
  ((funUncurry h ◁ productRestriction-comp X f g) ∙
    (comp-assoc (productRestriction X f) (productRestriction X g) (funUncurry h) ∙
      ((funPre-uncurry g h ▷ productRestriction X f) ∙
        (funPre-uncurry f (funPre g ∘ h) ∙ funUncurryIso (comp-assoc h (funPre g) (funPre f))))))

module Evaluation {A B C D E X : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) (h : MAP X (Fun D E))
  (left-composition : CompositorAt u r h)
  (right-composition : CompositorAt l v h) where

  source = uncurryRestriction {u = u} {v = l} (conePre h (functorOut s E))
  target = restrictionCocone s (funUncurry h)
  e = funUncurry h
  Lu = productRestriction X u
  Ll = productRestriction X l
  Lr = productRestriction X r
  Lv = productRestriction X v
  qr = funPre-uncurry r h
  qv = funPre-uncurry v h
  qu = funPre-uncurry u (funPre r ∘ h)
  ql = funPre-uncurry l (funPre v ∘ h)
  ar = comp-assoc h (funPre r) (funPre u)
  av = comp-assoc h (funPre v) (funPre l)
  Ar = funUncurryIso ar
  Av = funUncurryIso av
  leftEndpoint = qu ∙ Ar
  rightEndpoint = ql ∙ Av
  leftLeg = qr ▷ Lu
  rightLeg = qv ▷ Ll
  leftAssociator = comp-assoc Lu Lr e
  rightAssociator = comp-assoc Ll Lv e
  leftTotal = leftAssociator ∙ (leftLeg ∙ leftEndpoint)
  rightTotal = rightAssociator ∙ (rightLeg ∙ rightEndpoint)
  qru = funPre-uncurry (r ∘ u) h
  qvl = funPre-uncurry (v ∘ l) h
  κr = preComp {E = E} u r
  κv = preComp {E = E} l v
  α = preCong {E = E} (Square.commute s)
  kr = funUncurryIso (κr ▷ h)
  kv = funUncurryIso (κv ▷ h)
  image = funUncurryIso (α ▷ h)
  τ = Cone.match (functorOut s E)
  raw = funUncurryIso (τ ▷ h)
  pr = productRestriction-comp X u r
  pv = productRestriction-comp X l v
  pa = productMap-cong (idIso (id X)) (Square.commute s)
  er = e ◁ pr
  ev = e ◁ pv
  ea = e ◁ pa
  δ = e ◁ Cocone.match (productCocone X s)

  restricted-comp : {f g k : MAP (Fun D E) (Fun A E)}
    (β : =₁ g k) (α : =₁ f g) →
    =₂ (funUncurryIso ((β ∙ α) ▷ h))
      (funUncurryIso (β ▷ h) ∙ funUncurryIso (α ▷ h))
  restricted-comp β α = funUncurryIso-comp (β ▷ h) (α ▷ h) ∙
    funUncurry-Iso₂ (preWhisker-isoComp-at β α h)

  restricted-inverse : {f g : MAP (Fun D E) (Fun A E)} (α : =₁ f g) →
    =₂ (funUncurryIso (invIso α ▷ h)) (invIso (funUncurryIso (α ▷ h)))
  restricted-inverse α = funUncurryIso-inverse (α ▷ h) ∙ funUncurry-Iso₂ (pre-inverse α h)

  raw-normal : =₂ raw (invIso kv ∙ (image ∙ kr))
  raw-normal = isoComp-cong (restricted-inverse κv) (restricted-comp α κr) ∙
    restricted-comp (invIso κv) (α ∙ κr)

  product-normal : =₂ δ (invIso ev ∙ (ea ∙ er))
  product-normal = isoComp-cong (post-inverse e pv) (postWhisker-isoComp-at e pa pr) ∙
    postWhisker-isoComp-at e (invIso pv) (pa ∙ pr)

  source-normal : =₂ (changeEndpoints leftEndpoint rightEndpoint raw) (Cocone.match source)
  source-normal = changeEndpoints-cong qu ql (invIso inner-normal) ∙
    changeEndpoints-compose Ar qu Av ql raw
    where
    inner-normal : =₂ (funUncurryIso (Cone.match (conePre h (functorOut s E))))
      (changeEndpoints Ar Av raw)
    inner-normal = isoComp-cong (idIso Av)
      (isoComp-cong (idIso raw) (funUncurryIso-inverse ar) ∙
        funUncurryIso-comp (τ ▷ h) (invIso ar)) ∙
      funUncurryIso-comp av ((τ ▷ h) ∙ invIso ar)

  abstract
    evaluated-square : =₂ (δ ∙ leftTotal) (rightTotal ∙ raw)
    evaluated-square = isoComp-cong (idIso rightTotal) (invIso raw-normal) ∙
      (paste-squares (image ∙ kr) (ea ∙ er) (invIso kv) (invIso ev)
        leftTotal qvl rightTotal
        (paste-squares kr er image ea leftTotal qru qvl
          (invIso left-composition) (invIso (preCong-at (Square.commute s) h)))
        (move-square ev rightTotal qvl kv (invIso right-composition)) ∙
        isoComp-cong product-normal (idIso leftTotal))

    comparison : CoconeIso source target
    comparison = record
      { leftIso = qr ; rightIso = qv
      ; compatible = isoComp-cong (idIso rightLeg) source-normal ∙
          close-evaluation-square leftEndpoint rightEndpoint leftLeg rightLeg
            leftAssociator rightAssociator raw δ evaluated-square }
```

