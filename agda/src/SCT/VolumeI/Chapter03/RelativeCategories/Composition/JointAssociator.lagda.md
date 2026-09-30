# A jointly chosen relative associator

The evaluation comparison for joint composition identifies its two
iterates with the two bracketings of a common relative family. The
family associator therefore gives an identification of those iterates.
Coherent lifting retains its full computation after evaluation, including
the base triangle. Choose it once on the product of three relative
functor categories. Its restrictions are natural by interchange.

This proves naturality of the restricted universal choice. It does not
identify that choice with the old pointwise native associator, prove a
pentagon, or supply a base-change compositor. In particular, the
specified matching in the dependent-pullback comparison remains open.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter03.RelativeCategories.Composition.JointComposition as JointComposition
import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyAssociator as FamilyAssociator
import SCT.VolumeI.Chapter03.RelativeCategories.Families.CoherentRelativeFamilyLifting as CoherentLifting

module SCT.VolumeI.Chapter03.RelativeCategories.Composition.JointAssociator
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.RetainedRelativeFamilies 𝒯 M ℱ P
  using (module Retained; module Identification)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P using (family)
open JointComposition 𝒯 M ℱ P using (module Joint)
open FamilyAssociator 𝒯 M ℱ P using (module Families)

module At {X A B C D S : CAT}
  (f : MAP A S) (g : MAP B S) (h : MAP C S) (k : MAP D S)
  (F : MAP X (FunOver f g)) (G : MAP X (FunOver g h)) (H : MAP X (FunOver h k)) where
  module FG = Joint f g h
  module GH = Joint g h k
  module FH = Joint f h k
  module GK = Joint f g k
  inner-name = FG.functor ∘ pair G F
  outer-name = GH.functor ∘ pair H G
  left = FH.functor ∘ pair H inner-name
  right = GK.functor ∘ pair outer-name F
  u = family f g F
  v = family g h G
  w = family h k H
  module U = Retained f g u
  module A = Families f g h k u v w

  opaque
    left-to-common : FunctorOverIso (family f k left) A.right
    left-to-common = compose-iso-over
      (postwhisker-over w
        (Identification.comparison f h (family f h inner-name) (FG.At.actual F G)
          (FG.At.evaluation F G)))
      (FH.At.evaluation inner-name H)

    right-to-common : FunctorOverIso (family f k right) A.left
    right-to-common = compose-iso-over (prewhisker-over U.over (GH.At.evaluation G H))
      (GK.At.evaluation F outer-name)

    family-comparison : FunctorOverIso (family f k left) (family f k right)
    family-comparison = compose-iso-over (inverse-iso-over right-to-common)
      (compose-iso-over (inverse-iso-over A.comparison) left-to-common)

  module Lifted = CoherentLifting.Families 𝒯 M ℱ P f k left right
    using (action; lift; computation)

  opaque
    comparison : left =₁ right
    comparison = Lifted.lift family-comparison

    comparison-computation : FunctorOverIso₂ (Lifted.action comparison) family-comparison
    comparison-computation = Lifted.computation family-comparison

-- The sole associator choice below is made over this common parameter.
-- Its restrictions have naturality by interchange. No identification
-- with previously chosen pointwise native associators is included.
module Universal {A B C D S : CAT}
  (f : MAP A S) (g : MAP B S) (h : MAP C S) (k : MAP D S) where
  parameter = (FunOver h k × FunOver g h) × FunOver f g
  first : MAP parameter (FunOver f g)
  first = pr₂
  second : MAP parameter (FunOver g h)
  second = pr₂ ∘ pr₁
  third : MAP parameter (FunOver h k)
  third = pr₁ ∘ pr₁
  module Chosen = At f g h k first second third

  restriction : {Y : CAT} (σ : MAP Y parameter) → (Chosen.left ∘ σ) =₁ (Chosen.right ∘ σ)
  restriction σ = Chosen.comparison ▷ σ

  naturality : {Y : CAT} {σ τ : MAP Y parameter} (α : σ =₁ τ) →
    (restriction τ ∙ (Chosen.left ◁ α)) =₂ ((Chosen.right ◁ α) ∙ restriction σ)
  naturality α = interchange-at Chosen.comparison α
```
