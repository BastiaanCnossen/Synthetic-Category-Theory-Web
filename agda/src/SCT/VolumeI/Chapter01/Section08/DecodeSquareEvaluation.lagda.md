# Decoding the induced mapping square

The composition and isomorphism comparisons identify the decoded mapping
square with postcomposition of the original square. The conclusion
includes compatibility of the matchings.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.DecodeSquareEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.ParameterChange 𝒯 M using (mapUncurryIso-inverse)
open import SCT.VolumeI.Chapter01.Section03.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section03.CoherenceTransport 𝒯
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (pre-inverse; inverse-identity)
open import SCT.VolumeI.Chapter01.Section05.ConeRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.DecodeRestrictionCones 𝒯 M using (decodeRestriction)
open import SCT.VolumeI.Chapter01.Section08.DecodingCalculus 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.SquareCocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconePostcomposition 𝒯 using (coconePost)
import SCT.VolumeI.Chapter01.Section08.DecodingComposition as DC
import SCT.VolumeI.Chapter01.Section08.DecodingRestrictionNaturality as DN
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯

open import SCT.VolumeI.Chapter01.Section08.EvaluationSquares 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

decodeMapIso-inverse : {C E : CAT} {f g : ObjAbs (Map C E)} (α : NatIso f g) →
  Iso₂ (decodeMapIso (invIso α)) (invIso (decodeMapIso α))
decodeMapIso-inverse {C} α = (isoInv ◁ invIso (decodeMapIso-at α)) ∙
  (pre-inverse (mapUncurryIso α) (oneProduct-in C) ∙
  ((preWhisker (oneProduct-in C) ◁ mapUncurryIso-inverse α) ∙ decodeMapIso-at (invIso α)))
module Evaluation {A B C D E : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) (h : ObjAbs (Map D E))
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
  left-composition = invIso (isoComp-unitˡ-at leftTotal) ∙ DC.CompositorEvaluation.comparison 𝒯 M u r h
  right-composition = invIso (isoComp-unitˡ-at rightTotal) ∙ DC.CompositorEvaluation.comparison 𝒯 M l v h
  restricted-comp : {f g k : MAP (Map D E) (Map A E)}
    (β : NatIso g k) (α : NatIso f g) →
    Iso₂ (decodeMapIso ((β ∙ α) ▷ h))
      (decodeMapIso (β ▷ h) ∙ decodeMapIso (α ▷ h))
  restricted-comp β α = decodeMapIso-comp (β ▷ h) (α ▷ h) ∙
    (decodeMap-isoMap _ _ ◁_) (preWhisker-isoComp-at β α h)

  restricted-inverse : {f g : MAP (Map D E) (Map A E)} (α : NatIso f g) →
    Iso₂ (decodeMapIso (invIso α ▷ h)) (invIso (decodeMapIso (α ▷ h)))
  restricted-inverse α = decodeMapIso-inverse (α ▷ h) ∙ (decodeMap-isoMap _ _ ◁_) (pre-inverse α h)

  raw-normal : Iso₂ raw (invIso kv ∙ (image ∙ kr))
  raw-normal = isoComp-cong (restricted-inverse κv) (restricted-comp α κr) ∙
    restricted-comp (invIso κv) (α ∙ κr)

  product-normal : Iso₂ δ (invIso ev ∙ (ea ∙ er))
  product-normal = isoComp-cong (invIso (inverse-identity (e ∘ (v ∘ l))))
    (invIso (isoComp-unitʳ-at ea)) ∙ invIso (isoComp-unitˡ-at ea)
  source-normal : Iso₂ (changeEndpoints leftEndpoint rightEndpoint raw) (Cocone.match source)
  source-normal = changeEndpoints-cong qu ql (invIso inner-normal) ∙
    changeEndpoints-compose Ar qu Av ql raw
    where
    inner-normal : Iso₂ (decodeMapIso (Cone.match (conePre h (mappingOut s E))))
      (changeEndpoints Ar Av raw)
    inner-normal = isoComp-cong (idIso Av)
      (isoComp-cong (idIso raw) (decodeMapIso-inverse ar) ∙
        decodeMapIso-comp (τ ▷ h) (invIso ar)) ∙
      decodeMapIso-comp av ((τ ▷ h) ∙ invIso ar)

  abstract
    evaluated-square : Iso₂ (δ ∙ leftTotal) (rightTotal ∙ raw)
    evaluated-square = isoComp-cong (idIso rightTotal) (invIso raw-normal) ∙
      (paste-squares (image ∙ kr) (ea ∙ er) (invIso kv) (invIso ev)
        leftTotal qvl rightTotal
        (paste-squares kr er image ea leftTotal qru qvl
          (invIso left-composition) (invIso (DN.Restriction.comparison 𝒯 M (Square.commute s) h)))
        (move-square ev rightTotal qvl kv (invIso right-composition)) ∙
        isoComp-cong product-normal (idIso leftTotal))

  comparison : CoconeIso source target
  comparison = record
    { leftIso = qr ; rightIso = qv
    ; compatible = isoComp-cong (idIso rightLeg) source-normal ∙
        close-evaluation-square leftEndpoint rightEndpoint leftLeg rightLeg
          leftAssociator rightAssociator raw δ evaluated-square }
```
