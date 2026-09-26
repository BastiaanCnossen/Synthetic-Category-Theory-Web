# Reflecting cone comparisons through uncurrying

For an arbitrary category of parameters, both leg comparisons lift through uncurrying.
Endpoint transport and naturality identify the uncurried compatibility
equation, which is then reflected by the derived uncurrying equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.Setup as Setup

import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeReflection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M) where

open Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯 using (coneIso-adjust)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingCompatibility 𝒯 M ℱ

module ReflectCone {X T C D E : CAT} {f : MAP C E} {g : MAP D E}
  (s t : Cone (funPost {C = T} f) (funPost g) X)
  (Φ : ConeIso (uncurryCone s) (uncurryCone t)) where

  left = funIsoReflect _ _ (ConeIso.leftIso Φ)
  right = funIsoReflect _ _ (ConeIso.rightIso Φ)
  adjusted = coneIso-adjust Φ (funUncurryIso left) (funUncurryIso right)
    ((funIsoReflect-β _ _ (ConeIso.leftIso Φ)) ⁻¹)
    ((funIsoReflect-β _ _ (ConeIso.rightIso Φ)) ⁻¹)
  fs = funPost-uncurry f (Cone.left s)
  ft = funPost-uncurry f (Cone.left t)
  gs = funPost-uncurry g (Cone.right s)
  gt = funPost-uncurry g (Cone.right t)
  τs = funUncurryIso (Cone.match s)
  τt = funUncurryIso (Cone.match t)
  α = funUncurryIso (funPost f ◁ left)
  β = funUncurryIso (funPost g ◁ right)

  rawSquare : (τt ∙ α) =₂ (β ∙ τs)
  rawSquare = changeEndpoints-reflect fs gt _ _
    (changeEndpoints-comp fs gs gt β τs ∙
    (isoComp-cong
      ((square-to-changeEndpoints gs gt β (g ◁ funUncurryIso right) (funPost-uncurry-natural g right)) ⁻¹)
      (idIso (Cone.match (uncurryCone s))) ∙
    (ConeIso.compatible adjusted ∙
    (isoComp-cong (idIso (Cone.match (uncurryCone t)))
      (square-to-changeEndpoints fs ft α (f ◁ funUncurryIso left) (funPost-uncurry-natural f left)) ∙
      (changeEndpoints-comp fs ft gt τt α) ⁻¹))))

  comparison : ConeIso s t
  comparison = record
    { leftIso = left ; rightIso = right
    ; compatible = funReflect-Iso₂ _ _
        ((funUncurryIso-comp (funPost g ◁ right) (Cone.match s)) ⁻¹ ∙
          (rawSquare ∙ funUncurryIso-comp (Cone.match t) (funPost f ◁ left))) }

reflect-cone-prescribed : {X T C D E : CAT} {f : MAP C E} {g : MAP D E}
  (s t : Cone (funPost {C = T} f) (funPost g) X)
  (Φ : ConeIso (uncurryCone s) (uncurryCone t))
  (α : Cone.left s =₁ Cone.left t) (β : Cone.right s =₁ Cone.right t) →
  ConeIso.leftIso Φ =₂ funUncurryIso α →
  ConeIso.rightIso Φ =₂ funUncurryIso β → ConeIso s t
reflect-cone-prescribed s t Φ α β first second =
  coneIso-adjust (ReflectCone.comparison s t Φ) α β
    (funReflect-Iso₂ _ _ (first ∙ funIsoReflect-β _ _ (ConeIso.leftIso Φ)))
    (funReflect-Iso₂ _ _ (second ∙ funIsoReflect-β _ _ (ConeIso.rightIso Φ)))
```

