# Evaluating restriction cones

Uncurrying a cone of precomposition functors gives a compatible cocone
on the corresponding product diagram. Its matching and the compatibility
of each cone comparison are transported by the precomposition comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.FunRestrictionCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section06.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.FunPrecompositionNaturality 𝒯 M ℱ
  using (funPre-uncurry-natural)
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

uncurryRestriction : {X A B C E : CAT} {u : MAP A B} {v : MAP A C} →
  Cone (funPre {D = E} u) (funPre v) X →
  Cocone (productMap (id X) u) (productMap (id X) v) E
uncurryRestriction {u = u} {v} s = record
  { left = funUncurry (Cone.left s) ; right = funUncurry (Cone.right s)
  ; match = funPre-uncurry v (Cone.right s) ∙
      (funUncurryIso (Cone.match s) ∙ invIso (funPre-uncurry u (Cone.left s))) }

uncurryRestrictionIso : {X A B C E : CAT} {u : MAP A B} {v : MAP A C}
  {s t : Cone (funPre {D = E} u) (funPre v) X} → ConeIso s t →
  CoconeIso (uncurryRestriction {u = u} {v = v} s) (uncurryRestriction t)
uncurryRestrictionIso {X} {u = u} {v} {s} {t} Φ = record
  { leftIso = funUncurryIso α ; rightIso = funUncurryIso β
  ; compatible = paste-squares (τs ∙ invIso fs) (τt ∙ invIso ft) gs gt first third last
      (paste-squares (invIso fs) (invIso ft) τs τt first second third
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
      invIso (funUncurryIso-comp (Cone.match t) (funPre u ◁ α)))
```

Currying the two legs lifts their matching through the actual uncurrying
equivalence. The beta comparison below is a comparison of whole cocones.

```agda
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open import SCT.VolumeI.Chapter01.Section01.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open import SCT.VolumeI.Chapter01.Section03.CoherenceTransport 𝒯

module CurryRestriction {X A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (s : Cocone (productMap (id X) u) (productMap (id X) v) E) where

  left = funCurry (Cocone.left s)
  right = funCurry (Cocone.right s)
  left-β = funCurry-β (Cocone.left s)
  right-β = funCurry-β (Cocone.right s)
  wanted = coconeRetarget s (funUncurry left) (funUncurry right) (invIso left-β) (invIso right-β)
  desired = Cocone.match wanted
  leftChange = funPre-uncurry u left
  rightChange = funPre-uncurry v right
  rawMatch = invIso rightChange ∙ (desired ∙ leftChange)

  value : Cone (funPre {D = E} u) (funPre v) X
  value = record { left = left ; right = right ; match = funIsoReflect _ _ rawMatch }

  abstract
    match-β : =₂ (Cocone.match (uncurryRestriction {u = u} {v = v} value)) desired
    match-β = cancel-right leftChange desired ∙
      (isoComp-cong (cancel-inverse rightChange (desired ∙ leftChange)) (idIso (invIso leftChange)) ∙
      (invIso (isoComp-assoc-at rightChange rawMatch (invIso leftChange)) ∙
        isoComp-cong (idIso rightChange)
          (isoComp-cong (funIsoReflect-β _ _ rawMatch) (idIso (invIso leftChange)))))

    comparison : CoconeIso (uncurryRestriction {u = u} {v = v} value) s
    comparison = coconeIso-compose
      (coconeIso-inverse (coconeRetarget-β s _ _ (invIso left-β) (invIso right-β)))
      (cocone-match-change _ _ _ _ match-β)

module ReflectRestriction {X A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (s t : Cone (funPre {D = E} u) (funPre v) X)
  (Φ : CoconeIso (uncurryRestriction {u = u} {v = v} s) (uncurryRestriction t)) where

  left = funIsoReflect _ _ (CoconeIso.leftIso Φ)
  right = funIsoReflect _ _ (CoconeIso.rightIso Φ)
  adjusted = coconeIso-adjust Φ (funUncurryIso left) (funUncurryIso right)
    (invIso (funIsoReflect-β _ _ (CoconeIso.leftIso Φ)))
    (invIso (funIsoReflect-β _ _ (CoconeIso.rightIso Φ)))
  fs = funPre-uncurry u (Cone.left s)
  ft = funPre-uncurry u (Cone.left t)
  gs = funPre-uncurry v (Cone.right s)
  gt = funPre-uncurry v (Cone.right t)
  τs = funUncurryIso (Cone.match s)
  τt = funUncurryIso (Cone.match t)
  α = funUncurryIso (funPre u ◁ left)
  β = funUncurryIso (funPre v ◁ right)

  abstract
    rawSquare : =₂ (τt ∙ α) (β ∙ τs)
    rawSquare = changeEndpoints-reflect fs gt _ _
      (changeEndpoints-comp fs gs gt β τs ∙
      (isoComp-cong
        (invIso (square-to-changeEndpoints gs gt β
          (funUncurryIso right ▷ productMap (id X) v) (funPre-uncurry-natural v right)))
        (idIso (Cocone.match (uncurryRestriction s))) ∙
      (CoconeIso.compatible adjusted ∙
      (isoComp-cong (idIso (Cocone.match (uncurryRestriction t)))
        (square-to-changeEndpoints fs ft α
          (funUncurryIso left ▷ productMap (id X) u) (funPre-uncurry-natural u left)) ∙
        invIso (changeEndpoints-comp fs ft gt τt α)))))

    comparison : ConeIso s t
    comparison = record
      { leftIso = left ; rightIso = right
      ; compatible = funReflect-Iso₂ _ _
          (invIso (funUncurryIso-comp (funPre v ◁ right) (Cone.match s)) ∙
            (rawSquare ∙ funUncurryIso-comp (Cone.match t) (funPre u ◁ left))) }
```
