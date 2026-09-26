# Localization cocones and inverting functors

An inverting functor sends the chosen family of arrows to a family of
constant arrows, by Rezk. Uncurrying gives a cocone on the arrow family
and its projection to the parameter anima. Conversely, a cocone makes
each chosen arrow constant after applying its left leg, so that leg
inverts the collection. Both constructions retain the given matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter03.Section03.PushoutCalculus.LocalizationCocones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core; coreInclusion; module CoreLift)
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q
  using (constantMap; constantMap-evaluation; isomorphismInclusion; module WithRezk)
open WithRezk R
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (Inverts)

abstract
  constant-family : {X D : CAT} (a : MAP X (Core D)) →
    mapUncurry (constantMap D ∘ a) =₁ ((coreInclusion D ∘ a) ∘ pr₁)
  constant-family {D = D} a = (comp-assoc pr₁ a (coreInclusion D)) ⁻¹ ∙
    ((coreInclusion D ◁ pair-β₁ (a ∘ pr₁) (id [1] ∘ pr₂)) ∙
      (comp-assoc (productMap a (id [1])) pr₁ (coreInclusion D) ∙
        ((constantMap-evaluation D ▷ productMap a (id [1])) ∙
          mapUncurry-restrict (constantMap D) a)))

module Family {C : CAT} (W : MorphismCollection C) where
  X = MorphismCollection.collection W
  xAn = MorphismCollection.collection-isAn W
  w = MorphismCollection.inclusion W
  arrows : MAP (X × [1]) C
  arrows = mapUncurry w
  projection : MAP (X × [1]) X
  projection = pr₁

  module FromInverting {D : CAT} (f : MAP C D) (inverts : Inverts f W) where
    chosen = equiv-lift (identityComparison-isEquiv D) (FunctorLift.lift inverts)
    objects : MAP X (Core D)
    objects = FunctorLift.lift chosen
    right : MAP X D
    right = coreInclusion D ∘ objects
    abstract
      constants : (constantMap D ∘ objects) =₁ (mapPost f ∘ w)
      constants = FunctorLift.comparison inverts ∙
        ((isomorphismInclusion D ◁ FunctorLift.comparison chosen) ∙
          (comp-assoc objects (identityComparison D) (isomorphismInclusion D) ∙
            (identityComparison-over-morphisms D ⁻¹ ▷ objects)))
      matching : (f ∘ arrows) =₁ (right ∘ projection)
      matching = constant-family objects ∙
        (mapUncurry-cong (constants ⁻¹) ∙ (mapPost-uncurry f w) ⁻¹)
    cocone : Cocone arrows projection D
    cocone = record { left = f ; right = right ; match = matching }

  module FromCocone {D : CAT} (s : Cocone arrows projection D) where
    f = Cocone.left s
    b = Cocone.right s
    module Objects = CoreLift xAn b
    objects = Objects.lift
    abstract
      constant-evaluation : mapUncurry (constantMap D ∘ objects) =₁ (b ∘ projection)
      constant-evaluation = (Objects.comparison ▷ projection) ∙ constant-family objects
      constants : (constantMap D ∘ objects) =₁ (mapPost f ∘ w)
      constants = mapReflect xAn _ _
        ((mapPost-uncurry f w) ⁻¹ ∙ ((Cocone.match s) ⁻¹ ∙ constant-evaluation))
    inverts : Inverts f W
    inverts = record { lift = identityComparison D ∘ objects
      ; comparison = constants ∙
          ((identityComparison-over-morphisms D ▷ objects) ∙
            (comp-assoc objects (identityComparison D) (isomorphismInclusion D)) ⁻¹) }
```
