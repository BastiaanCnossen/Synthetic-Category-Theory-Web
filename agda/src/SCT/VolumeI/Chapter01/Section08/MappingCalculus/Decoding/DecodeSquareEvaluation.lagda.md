# Decoding the induced mapping square

The composition and isomorphism comparisons identify the decoded mapping
square with postcomposition of the original square. The conclusion
includes compatibility of the matchings.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.DecodeSquareEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Substitution.ParameterChange 𝒯 M using (mapUncurryIso-inverse)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse; inverse-identity)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.DecodeRestrictionCones 𝒯 M using (decodeRestriction)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.DecodingCalculus 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯 using (squareCocone)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost)
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.DecodingComposition as DC
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.DecodingRestrictionNaturality as DN
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯

open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.EvaluationSquares 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

decodeMapIso-inverse : {C E : CAT} {f g : Obj-abs (Map C E)} (α : f =₁ g) →
  (decodeMapIso (α ⁻¹)) =₂ ((decodeMapIso α) ⁻¹)
decodeMapIso-inverse {C} α = (＝-inv ◁ (decodeMapIso-at α) ⁻¹) ∙
  (pre-inverse (mapUncurryIso α) (oneProduct-in C) ∙
  ((preWhisker (oneProduct-in C) ◁ mapUncurryIso-inverse α) ∙ decodeMapIso-at (α ⁻¹)))
module Evaluation {A B C D E : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) (h : Obj-abs (Map D E))
  where

  source = decodeRestriction {u = u} {v = l} (conePre h (mappingOut s E))
  target = coconePost (decodeMap h) (squareCocone s)
  e = decodeMap h
  Lu = u
  Ll = l
  Lr = r
  Lv = v
  qr = decodePre r h
  qv = decodePre v h
  qu = decodePre u (mapPre r ∘ h)
  ql = decodePre l (mapPre v ∘ h)
  ar = comp-assoc h (mapPre r) (mapPre u)
  av = comp-assoc h (mapPre v) (mapPre l)
  Ar = decodeMapIso ar
  Av = decodeMapIso av
  leftEndpoint = qu ∙ Ar
  rightEndpoint = ql ∙ Av
  leftLeg = qr ▷ Lu
  rightLeg = qv ▷ Ll
  leftAssociator = comp-assoc Lu Lr e
  rightAssociator = comp-assoc Ll Lv e
  leftTotal = leftAssociator ∙ (leftLeg ∙ leftEndpoint)
  rightTotal = rightAssociator ∙ (rightLeg ∙ rightEndpoint)
  qru = decodePre (r ∘ u) h
  qvl = decodePre (v ∘ l) h
  κr = mapPre-comp {D = E} u r
  κv = mapPre-comp {D = E} l v
  α = mapPre-cong {D = E} (Square.commute s)
  kr = decodeMapIso (κr ▷ h)
  kv = decodeMapIso (κv ▷ h)
  image = decodeMapIso (α ▷ h)
  τ = Cone.match (mappingOut s E)
  raw = decodeMapIso (τ ▷ h)
  er = idIso (e ∘ (r ∘ u))
  ev = idIso (e ∘ (v ∘ l))
  ea = e ◁ Square.commute s
  δ = ea
  left-composition = (isoComp-unitˡ-at leftTotal) ⁻¹ ∙ DC.CompositorEvaluation.comparison 𝒯 M u r h
  right-composition = (isoComp-unitˡ-at rightTotal) ⁻¹ ∙ DC.CompositorEvaluation.comparison 𝒯 M l v h
  restricted-comp : {f g k : MAP (Map D E) (Map A E)}
    (β : g =₁ k) (α : f =₁ g) →
    (decodeMapIso ((β ∙ α) ▷ h)) =₂
      (decodeMapIso (β ▷ h) ∙ decodeMapIso (α ▷ h))
  restricted-comp β α = decodeMapIso-comp (β ▷ h) (α ▷ h) ∙
    (decodeMap-isoMap _ _ ◁_) (preWhisker-isoComp-at β α h)

  restricted-inverse : {f g : MAP (Map D E) (Map A E)} (α : f =₁ g) →
    (decodeMapIso (α ⁻¹ ▷ h)) =₂ ((decodeMapIso (α ▷ h)) ⁻¹)
  restricted-inverse α = decodeMapIso-inverse (α ▷ h) ∙ (decodeMap-isoMap _ _ ◁_) (pre-inverse α h)

  raw-normal : raw =₂ (kv ⁻¹ ∙ (image ∙ kr))
  raw-normal = isoComp-cong (restricted-inverse κv) (restricted-comp α κr) ∙
    restricted-comp (κv ⁻¹) (α ∙ κr)

  product-normal : δ =₂ (ev ⁻¹ ∙ (ea ∙ er))
  product-normal = isoComp-cong ((inverse-identity (e ∘ (v ∘ l))) ⁻¹)
    ((isoComp-unitʳ-at ea) ⁻¹) ∙ (isoComp-unitˡ-at ea) ⁻¹
  source-normal : (changeEndpoints leftEndpoint rightEndpoint raw) =₂ (Cocone.match source)
  source-normal = changeEndpoints-cong qu ql (inner-normal ⁻¹) ∙
    changeEndpoints-compose Ar qu Av ql raw
    where
    inner-normal : (decodeMapIso (Cone.match (conePre h (mappingOut s E)))) =₂
      (changeEndpoints Ar Av raw)
    inner-normal = isoComp-cong (idIso Av)
      (isoComp-cong (idIso raw) (decodeMapIso-inverse ar) ∙
        decodeMapIso-comp (τ ▷ h) (ar ⁻¹)) ∙
      decodeMapIso-comp av ((τ ▷ h) ∙ ar ⁻¹)

  abstract
    evaluated-square : (δ ∙ leftTotal) =₂ (rightTotal ∙ raw)
    evaluated-square = isoComp-cong (idIso rightTotal) (raw-normal ⁻¹) ∙
      (paste-squares (image ∙ kr) (ea ∙ er) (kv ⁻¹) (ev ⁻¹)
        leftTotal qvl rightTotal
        (paste-squares kr er image ea leftTotal qru qvl
          (left-composition ⁻¹) ((DN.Restriction.comparison 𝒯 M (Square.commute s) h) ⁻¹))
        (move-square ev rightTotal qvl kv (right-composition ⁻¹)) ∙
        isoComp-cong product-normal (idIso leftTotal))

  comparison : CoconeIso source target
  comparison = record
    { leftIso = qr ; rightIso = qv
    ; compatible = isoComp-cong (idIso rightLeg) source-normal ∙
        close-evaluation-square leftEndpoint rightEndpoint leftLeg rightLeg
          leftAssociator rightAssociator raw δ evaluated-square }
```
