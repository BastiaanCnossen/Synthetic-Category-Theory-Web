# Composing with identity morphisms

For `ex:Composite_With_Identity`, the interval degeneracies are the two
unit triangles. Applying the given interval diagram to these triangles
proves the assertion in every category. The comparisons with the original
morphism and with the constant identity morphism preserve both endpoints;
the witnesses retain the equations at all three vertices.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking
import SCT.VolumeI.Chapter01.Section09.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter01.Section09.IdentityComposites
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter01.Section09.CompositeWitnesses 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter01.Section09.DegenerateCocones 𝒯 M ℱ P I E
  using (left-degeneracy; right-degeneracy; left-source; right-source; left-target; right-target)

interval-left-unit : CompositeWitness (identity-morphism zero) interval-morphism interval-morphism
interval-left-unit = record
  { triangle = s₀
  ; first-edge = s₀-d₂ ; second-edge = s₀-d₀ ; long-edge = s₀-d₁
  ; middle-vertex = CoconeIso.compatible left-degeneracy
  ; source-vertex = CoconeIso.compatible left-source
  ; target-vertex = CoconeIso.compatible left-target }

interval-right-unit : CompositeWitness interval-morphism (identity-morphism one) interval-morphism
interval-right-unit = record
  { triangle = s₁
  ; first-edge = s₁-d₂ ; second-edge = s₁-d₀ ; long-edge = s₁-d₁
  ; middle-vertex = CoconeIso.compatible right-degeneracy
  ; source-vertex = CoconeIso.compatible right-source
  ; target-vertex = CoconeIso.compatible right-target }

compose-left-identity : {C : CAT} (f : Mor C) →
  CompositeWitness (identity-morphism (source f)) (underlying-morphism f) (underlying-morphism f)
compose-left-identity f = retarget-witness
  (post-identity-morphism f zero) (post-interval-morphism f) (post-interval-morphism f)
  (post-witness f interval-left-unit)

compose-right-identity : {C : CAT} (f : Mor C) →
  CompositeWitness (underlying-morphism f) (identity-morphism (target f)) (underlying-morphism f)
compose-right-identity f = retarget-witness
  (post-interval-morphism f) (post-identity-morphism f one) (post-interval-morphism f)
  (post-witness f interval-right-unit)
```
