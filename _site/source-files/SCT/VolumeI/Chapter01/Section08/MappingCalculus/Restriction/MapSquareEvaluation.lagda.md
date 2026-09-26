# Evaluating the induced mapping square

The composition comparison is the remaining input to this intermediate
calculation. Together with the proved isomorphism comparison, it identifies
the evaluated mapping square with postcomposition of the product square.
The conclusion includes compatibility of the matchings.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.MapSquareEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Substitution.ParameterChange 𝒯 M using (mapUncurryIso-inverse)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.MapRestrictionCones 𝒯 M using (uncurryRestriction)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.PrecompositionCongruence 𝒯 M using (mapPre-cong-at)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.EvaluationSquares 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

CompositorAt : {X A B C E : CAT} (f : MAP A B) (g : MAP B C)
  (h : MAP X (Map C E)) → Set m
CompositorAt {X} f g h =
  (mapPre-uncurry (g ∘ f) h ∙ mapUncurryIso (mapPre-comp f g ▷ h)) =₂
  ((mapUncurry h ◁ productRestriction-comp X f g) ∙
    (comp-assoc (productRestriction X f) (productRestriction X g) (mapUncurry h) ∙
      ((mapPre-uncurry g h ▷ productRestriction X f) ∙
        (mapPre-uncurry f (mapPre g ∘ h) ∙ mapUncurryIso (comp-assoc h (mapPre g) (mapPre f))))))

module Evaluation {A B C D E X : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) (h : MAP X (Map D E))
  (left-composition : CompositorAt u r h)
  (right-composition : CompositorAt l v h) where

  source = uncurryRestriction {u = u} {v = l} (conePre h (mappingOut s E))
  target = restrictionCocone s (mapUncurry h)
  e = mapUncurry h
  Lu = productRestriction X u
  Ll = productRestriction X l
  Lr = productRestriction X r
  Lv = productRestriction X v
  qr = mapPre-uncurry r h
  qv = mapPre-uncurry v h
  qu = mapPre-uncurry u (mapPre r ∘ h)
  ql = mapPre-uncurry l (mapPre v ∘ h)
  ar = comp-assoc h (mapPre r) (mapPre u)
  av = comp-assoc h (mapPre v) (mapPre l)
  Ar = mapUncurryIso ar
  Av = mapUncurryIso av
  leftEndpoint = qu ∙ Ar
  rightEndpoint = ql ∙ Av
  leftLeg = qr ▷ Lu
  rightLeg = qv ▷ Ll
  leftAssociator = comp-assoc Lu Lr e
  rightAssociator = comp-assoc Ll Lv e
  leftTotal = leftAssociator ∙ (leftLeg ∙ leftEndpoint)
  rightTotal = rightAssociator ∙ (rightLeg ∙ rightEndpoint)
  qru = mapPre-uncurry (r ∘ u) h
  qvl = mapPre-uncurry (v ∘ l) h
  κr = mapPre-comp {D = E} u r
  κv = mapPre-comp {D = E} l v
  α = mapPre-cong {D = E} (Square.commute s)
  kr = mapUncurryIso (κr ▷ h)
  kv = mapUncurryIso (κv ▷ h)
  image = mapUncurryIso (α ▷ h)
  τ = Cone.match (mappingOut s E)
  raw = mapUncurryIso (τ ▷ h)
  pr = productRestriction-comp X u r
  pv = productRestriction-comp X l v
  pa = productMap-cong (idIso (id X)) (Square.commute s)
  er = e ◁ pr
  ev = e ◁ pv
  ea = e ◁ pa
  δ = e ◁ Cocone.match (productCocone X s)

  restricted-comp : {f g k : MAP (Map D E) (Map A E)}
    (β : g =₁ k) (α : f =₁ g) →
    (mapUncurryIso ((β ∙ α) ▷ h)) =₂
      (mapUncurryIso (β ▷ h) ∙ mapUncurryIso (α ▷ h))
  restricted-comp β α = mapUncurryIso-comp (β ▷ h) (α ▷ h) ∙
    mapUncurry-Iso₂ (preWhisker-isoComp-at β α h)

  restricted-inverse : {f g : MAP (Map D E) (Map A E)} (α : f =₁ g) →
    (mapUncurryIso (α ⁻¹ ▷ h)) =₂ ((mapUncurryIso (α ▷ h)) ⁻¹)
  restricted-inverse α = mapUncurryIso-inverse (α ▷ h) ∙ mapUncurry-Iso₂ (pre-inverse α h)

  raw-normal : raw =₂ (kv ⁻¹ ∙ (image ∙ kr))
  raw-normal = isoComp-cong (restricted-inverse κv) (restricted-comp α κr) ∙
    restricted-comp (κv ⁻¹) (α ∙ κr)

  product-normal : δ =₂ (ev ⁻¹ ∙ (ea ∙ er))
  product-normal = isoComp-cong (post-inverse e pv) (postWhisker-isoComp-at e pa pr) ∙
    postWhisker-isoComp-at e (pv ⁻¹) (pa ∙ pr)

  source-normal : (changeEndpoints leftEndpoint rightEndpoint raw) =₂ (Cocone.match source)
  source-normal = changeEndpoints-cong qu ql (inner-normal ⁻¹) ∙
    changeEndpoints-compose Ar qu Av ql raw
    where
    inner-normal : (mapUncurryIso (Cone.match (conePre h (mappingOut s E)))) =₂
      (changeEndpoints Ar Av raw)
    inner-normal = isoComp-cong (idIso Av)
      (isoComp-cong (idIso raw) (mapUncurryIso-inverse ar) ∙
        mapUncurryIso-comp (τ ▷ h) (ar ⁻¹)) ∙
      mapUncurryIso-comp av ((τ ▷ h) ∙ ar ⁻¹)

  abstract
    evaluated-square : (δ ∙ leftTotal) =₂ (rightTotal ∙ raw)
    evaluated-square = isoComp-cong (idIso rightTotal) (raw-normal ⁻¹) ∙
      (paste-squares (image ∙ kr) (ea ∙ er) (kv ⁻¹) (ev ⁻¹)
        leftTotal qvl rightTotal
        (paste-squares kr er image ea leftTotal qru qvl
          (left-composition ⁻¹) ((mapPre-cong-at (Square.commute s) h) ⁻¹))
        (move-square ev rightTotal qvl kv (right-composition ⁻¹)) ∙
        isoComp-cong product-normal (idIso leftTotal))

    comparison : CoconeIso source target
    comparison = record
      { leftIso = qr ; rightIso = qv
      ; compatible = isoComp-cong (idIso rightLeg) source-normal ∙
          close-evaluation-square leftEndpoint rightEndpoint leftLeg rightLeg
            leftAssociator rightAssociator raw δ evaluated-square }

    comparison-compatibility : (Cocone.match target ∙ leftLeg) =₂
      (rightLeg ∙ Cocone.match source)
    comparison-compatibility = CoconeIso.compatible comparison
```
