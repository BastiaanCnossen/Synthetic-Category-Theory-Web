# Evaluating restriction cones

Uncurrying a cone of precomposition functors gives a compatible cocone
on the corresponding product diagram. Its matching and the compatibility
of each cone comparison are transported by the precomposition comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.FunRestrictionCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.FunPrecompositionNaturality 𝒯 M ℱ
  using (funPre-uncurry-natural)
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

uncurryRestriction : {X A B C E : CAT} {u : MAP A B} {v : MAP A C} →
  Cone (funPre {D = E} u) (funPre v) X →
  Cocone (productMap (id X) u) (productMap (id X) v) E
uncurryRestriction {u = u} {v} s = record
  { left = funUncurry (Cone.left s) ; right = funUncurry (Cone.right s)
  ; match = funPre-uncurry v (Cone.right s) ∙
      (funUncurryIso (Cone.match s) ∙ (funPre-uncurry u (Cone.left s)) ⁻¹) }

uncurryRestrictionIso : {X A B C E : CAT} {u : MAP A B} {v : MAP A C}
  {s t : Cone (funPre {D = E} u) (funPre v) X} → ConeIso s t →
  CoconeIso (uncurryRestriction {u = u} {v = v} s) (uncurryRestriction t)
uncurryRestrictionIso {X} {u = u} {v} {s} {t} Φ = record
  { leftIso = funUncurryIso α ; rightIso = funUncurryIso β
  ; compatible = paste-squares (τs ∙ fs ⁻¹) (τt ∙ ft ⁻¹) gs gt first third last
      (paste-squares (fs ⁻¹) (ft ⁻¹) τs τt first second third
        (move-square ft second first fs (funPre-uncurry-natural u α)) rawSquare)
      (funPre-uncurry-natural v β) }
  where
  α = ConeIso.leftIso Φ
  β = ConeIso.rightIso Φ
  fs = funPre-uncurry u (Cone.left s)
  ft = funPre-uncurry u (Cone.left t)
  gs = funPre-uncurry v (Cone.right s)
  gt = funPre-uncurry v (Cone.right t)
  τs = funUncurryIso (Cone.match s)
  τt = funUncurryIso (Cone.match t)
  first = funUncurryIso α ▷ productMap (id X) u
  second = funUncurryIso (funPre u ◁ α)
  third = funUncurryIso (funPre v ◁ β)
  last = funUncurryIso β ▷ productMap (id X) v
  rawSquare = funUncurryIso-comp (funPre v ◁ β) (Cone.match s) ∙
    ((funUncurry-isoMap _ _ ◁ ConeIso.compatible Φ) ∙
      (funUncurryIso-comp (Cone.match t) (funPre u ◁ α)) ⁻¹)
```

Currying the two legs lifts their matching through the actual uncurrying
equivalence. The beta comparison below is a comparison of whole cocones.

```agda
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open import SCT.VolumeI.Chapter01.Section04.CoherenceTransport 𝒯
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯 using (inverse-inverse)

module CurryRestriction {X A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (s : Cocone (productMap (id X) u) (productMap (id X) v) E) where

  left = funCurry (Cocone.left s)
  right = funCurry (Cocone.right s)
  left-β = funCurry-β (Cocone.left s)
  right-β = funCurry-β (Cocone.right s)
  wanted = coconeRetarget s (funUncurry left) (funUncurry right) (left-β ⁻¹) (right-β ⁻¹)
  desired = Cocone.match wanted
  leftChange = funPre-uncurry u left
  rightChange = funPre-uncurry v right
  rawMatch = rightChange ⁻¹ ∙ (desired ∙ leftChange)

  value : Cone (funPre {D = E} u) (funPre v) X
  value = record { left = left ; right = right ; match = funIsoReflect _ _ rawMatch }

  abstract
    match-β : (Cocone.match (uncurryRestriction {u = u} {v = v} value)) =₂ desired
    match-β = cancel-right leftChange desired ∙
      (isoComp-cong (cancel-inverse rightChange (desired ∙ leftChange)) (idIso (leftChange ⁻¹)) ∙
      ((isoComp-assoc-at rightChange rawMatch (leftChange ⁻¹)) ⁻¹ ∙
        isoComp-cong (idIso rightChange)
          (isoComp-cong (funIsoReflect-β _ _ rawMatch) (idIso (leftChange ⁻¹)))))

    comparison : CoconeIso (uncurryRestriction {u = u} {v = v} value) s
    comparison = coconeIso-compose
      (coconeIso-inverse (coconeRetarget-β s _ _ (left-β ⁻¹) (right-β ⁻¹)))
      (cocone-match-change _ _ _ _ match-β)

    comparison-left : CoconeIso.leftIso comparison =₂ left-β
    comparison-left = inverse-inverse left-β ∙ isoComp-unitʳ-at ((left-β ⁻¹) ⁻¹)

    comparison-right : CoconeIso.rightIso comparison =₂ right-β
    comparison-right = inverse-inverse right-β ∙ isoComp-unitʳ-at ((right-β ⁻¹) ⁻¹)

module ReflectRestriction {X A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (s t : Cone (funPre {D = E} u) (funPre v) X)
  (Φ : CoconeIso (uncurryRestriction {u = u} {v = v} s) (uncurryRestriction t)) where

  left = funIsoReflect _ _ (CoconeIso.leftIso Φ)
  right = funIsoReflect _ _ (CoconeIso.rightIso Φ)
  adjusted = coconeIso-adjust Φ (funUncurryIso left) (funUncurryIso right)
    ((funIsoReflect-β _ _ (CoconeIso.leftIso Φ)) ⁻¹)
    ((funIsoReflect-β _ _ (CoconeIso.rightIso Φ)) ⁻¹)
  fs = funPre-uncurry u (Cone.left s)
  ft = funPre-uncurry u (Cone.left t)
  gs = funPre-uncurry v (Cone.right s)
  gt = funPre-uncurry v (Cone.right t)
  τs = funUncurryIso (Cone.match s)
  τt = funUncurryIso (Cone.match t)
  α = funUncurryIso (funPre u ◁ left)
  β = funUncurryIso (funPre v ◁ right)

  abstract
    rawSquare : (τt ∙ α) =₂ (β ∙ τs)
    rawSquare = changeEndpoints-reflect fs gt _ _
      (changeEndpoints-comp fs gs gt β τs ∙
      (isoComp-cong
        ((square-to-changeEndpoints gs gt β
          (funUncurryIso right ▷ productMap (id X) v) (funPre-uncurry-natural v right)) ⁻¹)
        (idIso (Cocone.match (uncurryRestriction s))) ∙
      (CoconeIso.compatible adjusted ∙
      (isoComp-cong (idIso (Cocone.match (uncurryRestriction t)))
        (square-to-changeEndpoints fs ft α
          (funUncurryIso left ▷ productMap (id X) u) (funPre-uncurry-natural u left)) ∙
        (changeEndpoints-comp fs ft gt τt α) ⁻¹))))

    comparison : ConeIso s t
    comparison = record
      { leftIso = left ; rightIso = right
      ; compatible = funReflect-Iso₂ _ _
          ((funUncurryIso-comp (funPre v ◁ right) (Cone.match s)) ⁻¹ ∙
            (rawSquare ∙ funUncurryIso-comp (Cone.match t) (funPre u ◁ left))) }

    comparison-left : ConeIso.leftIso comparison =₂ left
    comparison-left = idIso left

    comparison-right : ConeIso.rightIso comparison =₂ right
    comparison-right = idIso right
```
