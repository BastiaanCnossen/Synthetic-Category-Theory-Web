# Evaluating mapping-anima restriction cones

Uncurrying a cone of precomposition functors gives a compatible cocone
on the corresponding product diagram. Its matching and the compatibility
of each cone comparison are transported by the precomposition comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.MapRestrictionCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.Compatibility 𝒯 M using (uncurryFamily-absolute)
open import SCT.VolumeI.Chapter01.Section03.PrecompositionNaturality 𝒯 M
  using (mapPre-uncurry-inputs)
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

mapPre-uncurry-natural : {X B C E : CAT} (i : MAP B C)
  {u v : MAP X (Map C E)} (γ : NatIso u v) →
  Iso₂ (mapPre-uncurry i v ∙ mapUncurryIso (mapPre i ◁ γ))
    ((mapUncurryIso γ ▷ productMap (id X) i) ∙ mapPre-uncurry i u)
mapPre-uncurry-natural {X} i {u} {v} γ =
  isoComp-cong (preWhisker (productMap (id X) i) ◁ uncurryFamily-absolute γ)
    (const-One (mapPre-uncurry i u)) ∙
  (mapPre-uncurry-inputs i γ ∙
    invIso (isoComp-cong (const-One (mapPre-uncurry i v)) (uncurryFamily-absolute (mapPre i ◁ γ))))
uncurryRestriction : {X A B C E : CAT} {u : MAP A B} {v : MAP A C} →
  Cone (mapPre {D = E} u) (mapPre v) X →
  Cocone (productMap (id X) u) (productMap (id X) v) E
uncurryRestriction {u = u} {v} s = record
  { left = mapUncurry (Cone.left s) ; right = mapUncurry (Cone.right s)
  ; match = mapPre-uncurry v (Cone.right s) ∙
      (mapUncurryIso (Cone.match s) ∙ invIso (mapPre-uncurry u (Cone.left s))) }

uncurryRestrictionIso : {X A B C E : CAT} {u : MAP A B} {v : MAP A C}
  {s t : Cone (mapPre {D = E} u) (mapPre v) X} → ConeIso s t →
  CoconeIso (uncurryRestriction {u = u} {v = v} s) (uncurryRestriction t)
uncurryRestrictionIso {X} {u = u} {v} {s} {t} Φ = record
  { leftIso = mapUncurryIso α ; rightIso = mapUncurryIso β
  ; compatible = paste-squares (τs ∙ invIso fs) (τt ∙ invIso ft) gs gt first third last
      (paste-squares (invIso fs) (invIso ft) τs τt first second third
        (move-square ft second first fs (mapPre-uncurry-natural u α)) rawSquare)
      (mapPre-uncurry-natural v β) }
  where
  α = ConeIso.leftIso Φ
  β = ConeIso.rightIso Φ
  fs = mapPre-uncurry u (Cone.left s)
  ft = mapPre-uncurry u (Cone.left t)
  gs = mapPre-uncurry v (Cone.right s)
  gt = mapPre-uncurry v (Cone.right t)
  τs = mapUncurryIso (Cone.match s)
  τt = mapUncurryIso (Cone.match t)
  first = mapUncurryIso α ▷ productMap (id X) u
  second = mapUncurryIso (mapPre u ◁ α)
  third = mapUncurryIso (mapPre v ◁ β)
  last = mapUncurryIso β ▷ productMap (id X) v
  rawSquare = mapUncurryIso-comp (mapPre v ◁ β) (Cone.match s) ∙
    ((mapUncurry-isoMap _ _ ◁ ConeIso.compatible Φ) ∙
      invIso (mapUncurryIso-comp (Cone.match t) (mapPre u ◁ α)))
```

For an anima of parameters, currying the two legs lifts their matching
through the actual uncurrying equivalence. The beta comparison below is
a comparison of whole cocones. Reflection uses the same anima hypothesis.

```agda
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open import SCT.VolumeI.Chapter01.Section01.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open import SCT.VolumeI.Chapter01.Section03.CoherenceTransport 𝒯

module CurryRestriction {X A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (xAn : isAn X) (s : Cocone (productMap (id X) u) (productMap (id X) v) E) where

  left = mapCurry xAn (Cocone.left s)
  right = mapCurry xAn (Cocone.right s)
  left-β = mapCurry-β xAn (Cocone.left s)
  right-β = mapCurry-β xAn (Cocone.right s)
  wanted = coconeRetarget s (mapUncurry left) (mapUncurry right) (invIso left-β) (invIso right-β)
  desired = Cocone.match wanted
  leftChange = mapPre-uncurry u left
  rightChange = mapPre-uncurry v right
  rawMatch = invIso rightChange ∙ (desired ∙ leftChange)

  value : Cone (mapPre {D = E} u) (mapPre v) X
  value = record { left = left ; right = right ; match = mapReflect xAn _ _ rawMatch }

  abstract
    match-β : Iso₂ (Cocone.match (uncurryRestriction {u = u} {v = v} value)) desired
    match-β = cancel-right leftChange desired ∙
      (isoComp-cong (cancel-inverse rightChange (desired ∙ leftChange)) (idIso (invIso leftChange)) ∙
      (invIso (isoComp-assoc-at rightChange rawMatch (invIso leftChange)) ∙
        isoComp-cong (idIso rightChange)
          (isoComp-cong (mapReflect-β xAn _ _ rawMatch) (idIso (invIso leftChange)))))

    comparison : CoconeIso (uncurryRestriction {u = u} {v = v} value) s
    comparison = coconeIso-compose
      (coconeIso-inverse (coconeRetarget-β s _ _ (invIso left-β) (invIso right-β)))
      (cocone-match-change _ _ _ _ match-β)

module ReflectRestriction {X A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (xAn : isAn X) (s t : Cone (mapPre {D = E} u) (mapPre v) X)
  (Φ : CoconeIso (uncurryRestriction {u = u} {v = v} s) (uncurryRestriction t)) where

  left = mapReflect xAn _ _ (CoconeIso.leftIso Φ)
  right = mapReflect xAn _ _ (CoconeIso.rightIso Φ)
  adjusted = coconeIso-adjust Φ (mapUncurryIso left) (mapUncurryIso right)
    (invIso (mapReflect-β xAn _ _ (CoconeIso.leftIso Φ)))
    (invIso (mapReflect-β xAn _ _ (CoconeIso.rightIso Φ)))
  fs = mapPre-uncurry u (Cone.left s)
  ft = mapPre-uncurry u (Cone.left t)
  gs = mapPre-uncurry v (Cone.right s)
  gt = mapPre-uncurry v (Cone.right t)
  τs = mapUncurryIso (Cone.match s)
  τt = mapUncurryIso (Cone.match t)
  α = mapUncurryIso (mapPre u ◁ left)
  β = mapUncurryIso (mapPre v ◁ right)

  abstract
    rawSquare : Iso₂ (τt ∙ α) (β ∙ τs)
    rawSquare = changeEndpoints-reflect fs gt _ _
      (changeEndpoints-comp fs gs gt β τs ∙
      (isoComp-cong
        (invIso (square-to-changeEndpoints gs gt β
          (mapUncurryIso right ▷ productMap (id X) v) (mapPre-uncurry-natural v right)))
        (idIso (Cocone.match (uncurryRestriction s))) ∙
      (CoconeIso.compatible adjusted ∙
      (isoComp-cong (idIso (Cocone.match (uncurryRestriction t)))
        (square-to-changeEndpoints fs ft α
          (mapUncurryIso left ▷ productMap (id X) u) (mapPre-uncurry-natural u left)) ∙
        invIso (changeEndpoints-comp fs ft gt τt α)))))

    comparison : ConeIso s t
    comparison = record
      { leftIso = left ; rightIso = right
      ; compatible = mapReflect-Iso₂ xAn _ _
          (invIso (mapUncurryIso-comp (mapPre v ◁ right) (Cone.match s)) ∙
            (rawSquare ∙ mapUncurryIso-comp (Cone.match t) (mapPre u ◁ left))) }
```

