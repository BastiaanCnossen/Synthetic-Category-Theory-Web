# The terminal mapping-anima test

A pullback after applying `Map One` supplies factorization and reflection
for cones with an anima of parameters. This does not assert that the
original square of arbitrary categories is a pullback. It is the terminal
parameter comparison used in the reverse pushout criterion.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.MappingCalculus.TerminalPullbackTest
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.MappedCones 𝒯 M P using (mappedCone; module MappedCone)
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.ConeUncurrying 𝒯 M using (uncurryCone; uncurryConeIso)
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.ConeCurrying 𝒯 M using (module CurryCone)
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.ConeReflection 𝒯 M using (module ReflectCone)

module Test {C D E S : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g S) (universal : IsPullback (mappedCone One s)) where

  module U = UniversalCone (mappedCone One s) universal

  module Factor {X : CAT} (xAn : isAn X) (t : Cone f g X) where
    module Curried = CurryCone xAn (conePre (pr₁ {X} {One}) t)
    lifted = U.factor Curried.value
    value : MAP X S
    value = mapUncurry lifted ∘ product-unitʳ-inverse X

    abstract
      comparison : ConeIso (conePre value s) t
      comparison = coneIso-compose (conePre-id t)
        (coneIso-compose (cone-action t (pair-β₁ (id X) (terminate X)))
        (coneIso-compose (conePre-assoc (product-unitʳ-inverse X) pr₁ t)
        (coneIso-compose (coneIso-pre (product-unitʳ-inverse X)
          (coneIso-compose Curried.comparison
            (coneIso-compose (uncurryConeIso (U.factor-β Curried.value))
              (coneIso-inverse (MappedCone.evaluate One s lifted)))))
          (coneIso-inverse (conePre-assoc (product-unitʳ-inverse X) (mapUncurry lifted) s)))))

  factor : {X : CAT} → isAn X → Cone f g X → MAP X S
  factor = Factor.value

  factor-β : {X : CAT} (xAn : isAn X) (t : Cone f g X) →
    ConeIso (conePre (factor xAn t) s) t
  factor-β = Factor.comparison

  module Compare {X : CAT} (xAn : isAn X) (h k : MAP X S)
    (Φ : ConeIso (conePre h s) (conePre k s)) where
    h′ = mapCurry xAn (h ∘ pr₁ {X} {One})
    k′ = mapCurry xAn (k ∘ pr₁ {X} {One})
    evaluate : (z : MAP X S) → ConeIso
      (uncurryCone (conePre (mapCurry xAn (z ∘ pr₁ {X} {One})) (mappedCone One s)))
      (conePre pr₁ (conePre z s))
    evaluate z = coneIso-compose (coneIso-inverse (conePre-assoc pr₁ z s))
      (coneIso-compose (cone-action s (mapCurry-β xAn (z ∘ pr₁)))
        (MappedCone.evaluate One s (mapCurry xAn (z ∘ pr₁))))

    lifted-comparison : h′ =₁ k′
    lifted-comparison = U.reflect h′ k′ (ReflectCone.comparison xAn _ _
      (coneIso-compose (coneIso-inverse (evaluate k))
        (coneIso-compose (coneIso-pre pr₁ Φ) (evaluate h))))

    comparison : h =₁ k
    comparison = FunctorLift.lift (preWhisker-lift (pr₁ {X} {One})
      (product-unitʳ-isEquiv X)
      (mapCurry-β xAn (k ∘ pr₁) ∙
        (mapUncurryIso lifted-comparison ∙ (mapCurry-β xAn (h ∘ pr₁)) ⁻¹)))

  reflect : {X : CAT} (xAn : isAn X) (h k : MAP X S) →
    ConeIso (conePre h s) (conePre k s) → h =₁ k
  reflect = Compare.comparison
```
