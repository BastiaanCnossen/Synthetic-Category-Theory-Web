# Lifting a cone across an embedding of the base

For a map of cospans whose base map is an embedding, specified lifts of
both legs of a cone determine a lift of its matching. The resulting
comparison is a whole cone comparison. No equivalence hypothesis on
the two end maps is required.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.ConeLifting
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (IsEmbedding)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.PrescribedLifting 𝒯 P using (embedding-lift)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (decode-encode)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectedCones as Coordinates

module At {C D B C′ D′ B′ Γ : CAT}
  (f : MAP C B) (g : MAP D B) (f′ : MAP C′ B′) (g′ : MAP D′ B′)
  (u : MAP C C′) (v : MAP D D′) (w : MAP B B′)
  (α : (w ∘ f) =₁ (f′ ∘ u)) (β : (w ∘ g) =₁ (g′ ∘ v))
  (ew : IsEmbedding w) (L : Cone f′ g′ Γ)
  (h : MAP Γ C) (k : MAP Γ D)
  (δ : (u ∘ h) =₁ Cone.left L) (ε : (v ∘ k) =₁ Cone.right L) where

  module Coordinate = Coordinates.Coordinate 𝒯 f g f′ g′ u v w α β
    using (left-normal; right-normal; read)
  adjusted : Cone f′ g′ Γ
  adjusted = coneRetarget L (u ∘ h) (v ∘ k) (δ ⁻¹) (ε ⁻¹)
  left-frame = Coordinate.left-normal h
  right-frame = Coordinate.right-normal k
  matching : (w ∘ (f ∘ h)) =₁ (w ∘ (g ∘ k))
  matching = right-frame ⁻¹ ∙ (Cone.match adjusted ∙ left-frame)
  chosen = embedding-lift w ew (f ∘ h) (g ∘ k) matching

  value : Cone f g Γ
  value = record { left = h ; right = k ; match = FunctorLift.lift chosen }

  abstract
    matching-image : Cone.match (Coordinate.read value) =₂ Cone.match adjusted
    matching-image = decode-encode left-frame right-frame (Cone.match adjusted) ∙
      isoComp-cong (idIso right-frame)
        (isoComp-cong (FunctorLift.comparison chosen) (idIso (left-frame ⁻¹)))

    comparison : ConeIso (Coordinate.read value) L
    comparison = coneIso-compose
      (coneIso-inverse (coneRetarget-β L (u ∘ h) (v ∘ k) (δ ⁻¹) (ε ⁻¹)))
      (cone-match-change _ _ _ _ matching-image)
```


If the two cospans have pullback cones and their comparison is specified
on the whole cone, lifting both projected components also lifts a map
into the second pullback. The base embedding lifts the matching first;
the two pullback universal properties then give the required factorization.

```agda
module PullbackComparison {C D B C′ D′ B′ T T′ : CAT}
  (f : MAP C B) (g : MAP D B) (f′ : MAP C′ B′) (g′ : MAP D′ B′)
  (u : MAP C C′) (v : MAP D D′) (w : MAP B B′)
  (α : (w ∘ f) =₁ (f′ ∘ u)) (β : (w ∘ g) =₁ (g′ ∘ v))
  (ew : IsEmbedding w)
  (t : Cone f g T) (et : IsPullback t)
  (t′ : Cone f′ g′ T′) (et′ : IsPullback t′) (κ : MAP T T′) where
  module Coordinate = Coordinates.Coordinate 𝒯 f g f′ g′ u v w α β
    using (read; read-iso; read-pre)

  module WithComparison (Φ : ConeIso (Coordinate.read t) (conePre κ t′))
    {Γ : CAT} (z : MAP Γ T′) (h : MAP Γ C) (k : MAP Γ D)
    (δ : (u ∘ h) =₁ (Cone.left t′ ∘ z))
    (ε : (v ∘ k) =₁ (Cone.right t′ ∘ z)) where
    module Lift = At f g f′ g′ u v w α β ew (conePre z t′) h k δ ε
      using (value; comparison)
    module Original = UniversalCone t et using (factor; factor-β)
    value : MAP Γ T
    value = Original.factor Lift.value

    abstract
      cone-comparison : ConeIso (conePre (κ ∘ value) t′) (conePre z t′)
      cone-comparison = coneIso-compose Lift.comparison
        (coneIso-compose (Coordinate.read-iso (Original.factor-β Lift.value))
        (coneIso-compose (coneIso-inverse (Coordinate.read-pre value t))
        (coneIso-compose (coneIso-pre value (coneIso-inverse Φ))
          (coneIso-inverse (conePre-assoc value κ t′)))))

      comparison : (κ ∘ value) =₁ z
      comparison = UniversalCone.reflect t′ et′ (κ ∘ value) z cone-comparison

    lift : FunctorLift κ z
    lift = record { lift = value ; comparison = comparison }
```
