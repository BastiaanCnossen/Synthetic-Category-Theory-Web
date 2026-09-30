# Mapping whole cone comparisons

A map of cospans sends a cone comparison to a cone comparison. Normalize
its matching as the base action conjugated by the two square comparisons;
naturality of those squares and preservation of composition then prove
the compatibility. The normalization is compared with the existing
`CospanMap.mapCone`, so that the operation retains its specified matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanAction
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose; coneIso-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite; inverse-inverse; pre-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module Action {C D E C′ D′ E′ : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′) where
  open CospanMap F using (mapCone) renaming (left to u; right to v; base to w; leftSquare to α; rightSquare to β)
  left-square : Cone f′ w C
  left-square = record { left = u ; right = f ; match = α }
  right-square : Cone g′ w D
  right-square = record { left = v ; right = g ; match = β }
  left-change : {X : CAT} (s : Cone f g X) → (f′ ∘ (u ∘ Cone.left s)) =₁ (w ∘ (f ∘ Cone.left s))
  left-change s = Cone.match (conePre (Cone.left s) left-square)
  right-change : {X : CAT} (s : Cone f g X) → (g′ ∘ (v ∘ Cone.right s)) =₁ (w ∘ (g ∘ Cone.right s))
  right-change s = Cone.match (conePre (Cone.right s) right-square)
  normalized : {X : CAT} → Cone f g X → Cone f′ g′ X
  normalized s = record { left = u ∘ Cone.left s ; right = v ∘ Cone.right s
    ; match = right-change s ⁻¹ ∙ ((w ◁ Cone.match s) ∙ left-change s) }

  module Normalization {X : CAT} (s : Cone f g X) where
    r = Cone.right s
    A = comp-assoc r g w
    B = β ▷ r
    Rassoc = comp-assoc r v g′
    b = β ⁻¹ ▷ r
    rest = (w ◁ Cone.match s) ∙ left-change s
    abstract
      inverse-right : (right-change s ⁻¹) =₂ (Rassoc ∙ (b ∙ A ⁻¹))
      inverse-right = isoComp-assoc-at Rassoc b (A ⁻¹) ∙
        (isoComp-cong (isoComp-cong (inverse-inverse Rassoc) ((pre-inverse β r) ⁻¹)) (idIso (A ⁻¹)) ∙
          (isoComp-cong (inverse-composite B (Rassoc ⁻¹)) (idIso (A ⁻¹)) ∙
            inverse-composite A (B ∙ Rassoc ⁻¹)))
      matching : Cone.match (normalized s) =₂ Cone.match (mapCone s)
      matching = isoComp-cong (idIso Rassoc) (isoComp-assoc-at b (A ⁻¹) rest) ∙
        (isoComp-assoc-at Rassoc (b ∙ A ⁻¹) rest ∙ isoComp-cong inverse-right (idIso rest))
      comparison : ConeIso (normalized s) (mapCone s)
      comparison = cone-match-change _ _ _ _ matching
      comparison-left : ConeIso.leftIso comparison =₂ idIso (u ∘ Cone.left s)
      comparison-left = idIso _
      comparison-right : ConeIso.rightIso comparison =₂ idIso (v ∘ Cone.right s)
      comparison-right = idIso _

  module Identification {X : CAT} {s t : Cone f g X} (Φ : ConeIso s t) where
    δ = ConeIso.leftIso Φ
    ε = ConeIso.rightIso Φ
    Ls = left-change s
    Lt = left-change t
    Rs = right-change s
    Rt = right-change t
    Ms = w ◁ Cone.match s
    Mt = w ◁ Cone.match t
    first = f′ ◁ (u ◁ δ)
    middle₀ = w ◁ (f ◁ δ)
    middle₁ = w ◁ (g ◁ ε)
    last = g′ ◁ (v ◁ ε)
    abstract
      left-natural : (Lt ∙ first) =₂ (middle₀ ∙ Ls)
      left-natural = ConeIso.compatible (cone-action left-square δ)
      middle-natural : (Mt ∙ middle₀) =₂ (middle₁ ∙ Ms)
      middle-natural = postWhisker-isoComp-at w (g ◁ ε) (Cone.match s) ∙
        ((postWhisker w ◁ ConeIso.compatible Φ) ∙ (postWhisker-isoComp-at w (Cone.match t) (f ◁ δ)) ⁻¹)
      right-natural : ((Rt ⁻¹) ∙ middle₁) =₂ (last ∙ (Rs ⁻¹))
      right-natural = move-square Rt last middle₁ Rs (ConeIso.compatible (cone-action right-square ε))
      normalized-comparison : ConeIso (normalized s) (normalized t)
      normalized-comparison = record { leftIso = u ◁ δ ; rightIso = v ◁ ε
        ; compatible = paste-squares (Ms ∙ Ls) (Mt ∙ Lt) (Rs ⁻¹) (Rt ⁻¹) first middle₁ last
            (paste-squares Ls Lt Ms Mt first middle₀ middle₁ left-natural middle-natural) right-natural }
      comparison : ConeIso (mapCone s) (mapCone t)
      comparison = coneIso-compose (Normalization.comparison t)
        (coneIso-compose normalized-comparison (coneIso-inverse (Normalization.comparison s)))
```
