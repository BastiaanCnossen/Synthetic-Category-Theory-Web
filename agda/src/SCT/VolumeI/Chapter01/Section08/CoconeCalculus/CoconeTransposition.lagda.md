# Transposing compatible cocones

Transposition sends a cocone with target `Fun X E` to a cocone on the
product of its span with `X`, with target `E`. Its matching and each
compatible comparison are transported by `transpose-pre`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeTransposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.Transposition 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.TranspositionNaturality 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯

open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

transposeCocone : {X A B C E : CAT} {u : MAP A B} {v : MAP A C} →
  Cocone u v (Fun X E) →
  Cocone (productMap (id X) u) (productMap (id X) v) E
transposeCocone {u = u} {v} s = record
  { left = transpose (Cocone.left s) ; right = transpose (Cocone.right s)
  ; match = transpose-pre v (Cocone.right s) ∙
      (transposeIso (Cocone.match s) ∙ (transpose-pre u (Cocone.left s)) ⁻¹) }

transposeCoconeIso : {X A B C E : CAT} {u : MAP A B} {v : MAP A C}
  {s t : Cocone u v (Fun X E)} → CoconeIso s t →
  CoconeIso (transposeCocone {u = u} {v = v} s) (transposeCocone t)
transposeCoconeIso {X} {u = u} {v} {s} {t} Φ = record
  { leftIso = transposeIso α ; rightIso = transposeIso β
  ; compatible = paste-squares (τs ∙ fs ⁻¹) (τt ∙ ft ⁻¹) gs gt first third last
      (paste-squares (fs ⁻¹) (ft ⁻¹) τs τt first second third
        (move-square ft second first fs (transpose-pre-natural u α)) rawSquare)
      (transpose-pre-natural v β) }
  where
  α = CoconeIso.leftIso Φ
  β = CoconeIso.rightIso Φ
  fs = transpose-pre u (Cocone.left s)
  ft = transpose-pre u (Cocone.left t)
  gs = transpose-pre v (Cocone.right s)
  gt = transpose-pre v (Cocone.right t)
  τs = transposeIso (Cocone.match s)
  τt = transposeIso (Cocone.match t)
  first = transposeIso α ▷ productMap (id X) u
  second = transposeIso (α ▷ u)
  third = transposeIso (β ▷ v)
  last = transposeIso β ▷ productMap (id X) v
  rawSquare = transposeIso-comp (β ▷ v) (Cocone.match s) ∙
    ((transpose-isoMap _ _ ◁ CoconeIso.compatible Φ) ∙
      (transposeIso-comp (Cocone.match t) (α ▷ u)) ⁻¹)
```

Transposing the two legs back lifts their matching through the actual
equivalence on isomorphism animae. The beta comparison is a comparison
of whole cocones.

```agda
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.BoundaryTransport
  vocabulary terminal products productLaws composition vertical using (restore-boundaries)
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯

module UntransposeCocone {X A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (s : Cocone (productMap (id X) u) (productMap (id X) v) E) where

  left = untranspose (Cocone.left s)
  right = untranspose (Cocone.right s)
  left-β = transpose-β (Cocone.left s)
  right-β = transpose-β (Cocone.right s)
  wanted = coconeRetarget s (transpose left) (transpose right) (left-β ⁻¹) (right-β ⁻¹)
  desired = Cocone.match wanted
  leftChange = transpose-pre u left
  rightChange = transpose-pre v right
  rawMatch = rightChange ⁻¹ ∙ (desired ∙ leftChange)

  value : Cocone u v (Fun X E)
  value = record { left = left ; right = right ; match = transpose-reflect _ _ rawMatch }

  abstract
    match-β : (Cocone.match (transposeCocone {u = u} {v = v} value)) =₂ desired
    match-β = restore-boundaries leftChange rightChange desired
      (transposeIso (Cocone.match value))
      (transpose-reflect-β _ _ rawMatch)

    comparison : CoconeIso (transposeCocone {u = u} {v = v} value) s
    comparison = coconeIso-compose
      (coconeIso-inverse (coconeRetarget-β s _ _ (left-β ⁻¹) (right-β ⁻¹)))
      (cocone-match-change _ _ _ _ match-β)

module ReflectTransposedCocone {X A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (s t : Cocone u v (Fun X E))
  (Φ : CoconeIso (transposeCocone {u = u} {v = v} s) (transposeCocone t)) where

  left = transpose-reflect _ _ (CoconeIso.leftIso Φ)
  right = transpose-reflect _ _ (CoconeIso.rightIso Φ)
  adjusted = coconeIso-adjust Φ (transposeIso left) (transposeIso right)
    ((transpose-reflect-β _ _ (CoconeIso.leftIso Φ)) ⁻¹)
    ((transpose-reflect-β _ _ (CoconeIso.rightIso Φ)) ⁻¹)
  fs = transpose-pre u (Cocone.left s)
  ft = transpose-pre u (Cocone.left t)
  gs = transpose-pre v (Cocone.right s)
  gt = transpose-pre v (Cocone.right t)
  τs = transposeIso (Cocone.match s)
  τt = transposeIso (Cocone.match t)
  α = transposeIso (left ▷ u)
  β = transposeIso (right ▷ v)

  abstract
    rawSquare : (τt ∙ α) =₂ (β ∙ τs)
    rawSquare = changeEndpoints-reflect fs gt _ _
      (changeEndpoints-comp fs gs gt β τs ∙
      (isoComp-cong
        ((square-to-changeEndpoints gs gt β
          (transposeIso right ▷ productMap (id X) v) (transpose-pre-natural v right)) ⁻¹)
        (idIso (Cocone.match (transposeCocone s))) ∙
      (CoconeIso.compatible adjusted ∙
      (isoComp-cong (idIso (Cocone.match (transposeCocone t)))
        (square-to-changeEndpoints fs ft α
          (transposeIso left ▷ productMap (id X) u) (transpose-pre-natural u left)) ∙
        (changeEndpoints-comp fs ft gt τt α) ⁻¹))))

    comparison : CoconeIso s t
    comparison = record
      { leftIso = left ; rightIso = right
      ; compatible = transpose-reflect-Iso₂ _ _
          ((transposeIso-comp (right ▷ v) (Cocone.match s)) ⁻¹ ∙
            (rawSquare ∙ transposeIso-comp (Cocone.match t) (left ▷ u))) }
```
