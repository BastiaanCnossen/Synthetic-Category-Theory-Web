# Evaluating whole relative cones

A cone over the defining cospan of `FunOver` evaluates to a functor over
the base. Cone comparisons evaluate to identifications of these native
triangles. For a cone on `One`, inserting the terminal coordinate gives
its corresponding functor on the original domain.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.PointReductionCoherence as Reduction
import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.EvaluationRestriction as Restriction

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M using (oneProduct-in; oneProduct-retraction)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ParameterSecondCoordinate 𝒯 M using (parameter-over)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeUncurrying 𝒯 M ℱ P

EvaluatedCone : {X C D S : CAT} {f : MAP C S} {g : MAP D S} →
  Cone (funPost g) (nameFun f) X → FunctorOver (f ∘ pr₂) g
EvaluatedCone s = record { lift = funUncurry (Cone.left s) ; comparison = evalMatch s }

evaluated-comparison : {X C D S : CAT} {f : MAP C S} {g : MAP D S}
  {s t : Cone (funPost g) (nameFun f) X} → ConeIso s t →
  FunctorOverIso (EvaluatedCone s) (EvaluatedCone t)
evaluated-comparison Φ = record
  { underlying = funUncurryIso (ConeIso.leftIso Φ)
  ; compatible = relative-cone-comparison Φ }

parameter-over-functor : {X Y C S : CAT} (f : MAP C S) (r : MAP Y X) →
  FunctorOver (f ∘ pr₂ {C = Y}) (f ∘ pr₂ {C = X})
parameter-over-functor {C = C} f r = record
  { lift = productMap r (id C) ; comparison = parameter-over r f }

evaluated-restriction : {X Y C D S : CAT} {f : MAP C S} {g : MAP D S}
  (r : MAP Y X) (s : Cone (funPost g) (nameFun f) X) →
  FunctorOverIso (EvaluatedCone (conePre r s))
    (compose-over (EvaluatedCone s) (parameter-over-functor f r))
evaluated-restriction r s = record
  { underlying = funUncurry-restrict (Cone.left s) r
  ; compatible = Restriction.Restriction.comparison 𝒯 M ℱ P r s }

terminal-insertion : {C S : CAT} (f : MAP C S) → FunctorOver f (f ∘ pr₂ {C = One})
terminal-insertion {C} f = record
  { lift = oneProduct-in C
  ; comparison = Reduction.Reduction.reduce 𝒯 (oneProduct-in C) pr₂ (oneProduct-retraction C) f }

PointTriangle : {C D S : CAT} {f : MAP C S} {g : MAP D S} →
  Cone (funPost g) (nameFun f) One → FunctorOver f g
PointTriangle {f = f} s = compose-over (EvaluatedCone s) (terminal-insertion f)

point-comparison : {C D S : CAT} {f : MAP C S} {g : MAP D S}
  {s t : Cone (funPost g) (nameFun f) One} → ConeIso s t →
  FunctorOverIso (PointTriangle s) (PointTriangle t)
point-comparison {f = f} Φ = prewhisker-over (terminal-insertion f) (evaluated-comparison Φ)
```
