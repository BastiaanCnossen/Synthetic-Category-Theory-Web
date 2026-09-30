# Associativity of relative families

Three relative functor families on one common parameter can be composed
in either order. The comparison between the two retained composites,
followed by the native associator, gives an identification including the
triangle over the base. Currying identifies their names.

The universal construction chooses this identification once over the
product of the three relative functor categories. Its restrictions are
not identified here with separately recomputed pointwise choices.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyAssociator
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.RetainedRelativeFamilies 𝒯 M ℱ P
  using (module Retained; module RetainedComposite)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
  using (family; curried-beta)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P
  using (module Curry)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyReflection 𝒯 M ℱ P
  using (reflect-family)

-- A family comparison, not a proof of its restriction or pentagon law.
module Families {X A B C D S : CAT}
  (f : MAP A S) (g : MAP B S) (h : MAP C S) (k : MAP D S)
  (u : FunctorOver (f ∘ pr₂ {C = X}) g)
  (v : FunctorOver (g ∘ pr₂ {C = X}) h)
  (w : FunctorOver (h ∘ pr₂ {C = X}) k) where
  module U = Retained f g u
  module V = Retained g h v
  module UV = RetainedComposite f g h u v

  left : FunctorOver (f ∘ pr₂ {C = X}) k
  left = compose-over (compose-over w V.over) U.over

  right : FunctorOver (f ∘ pr₂ {C = X}) k
  right = compose-over w UV.target

  opaque
    comparison : FunctorOverIso left right
    comparison = compose-iso-over (postwhisker-over w UV.comparison)
      (associator-over U.over V.over w)

  left-name : MAP X (FunOver f k)
  left-name = Curry.functor f k (FunctorLift.lift left) (FunctorLift.comparison left)

  right-name : MAP X (FunOver f k)
  right-name = Curry.functor f k (FunctorLift.lift right) (FunctorLift.comparison right)

  opaque
    named : left-name =₁ right-name
    named = reflect-family f k left-name right-name
      (compose-iso-over (inverse-iso-over (curried-beta f k right))
        (compose-iso-over comparison (curried-beta f k left)))

-- This produces one choice on a single universal category of parameters.
-- Its restrictions are not identified with the old pointwise choices.
module Universal {A B C D S : CAT}
  (f : MAP A S) (g : MAP B S) (h : MAP C S) (k : MAP D S) where
  parameter = (FunOver h k × FunOver g h) × FunOver f g
  first : MAP parameter (FunOver f g)
  first = pr₂
  second : MAP parameter (FunOver g h)
  second = pr₂ ∘ pr₁
  third : MAP parameter (FunOver h k)
  third = pr₁ ∘ pr₁

  module Choice = Families f g h k
    (family f g first) (family g h second) (family h k third)

  restriction : {Y : CAT} (σ : MAP Y parameter) →
    (Choice.left-name ∘ σ) =₁ (Choice.right-name ∘ σ)
  restriction σ = Choice.named ▷ σ
```
