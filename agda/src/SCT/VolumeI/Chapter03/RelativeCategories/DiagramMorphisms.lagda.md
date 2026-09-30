# Relative transformations from interval diagrams

A diagram over the base with specified relative endpoint identifications
defines a transformation over that base. Its base equation follows from
the full endpoint triangles and currying, with no objectwise criterion.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter03.RelativeCategories.DiagramMorphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter03.RelativeCategories.Morphisms 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
  using (FunctorOverIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DiagramExpressionIdentifications as Diagrams
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Postcomposition.CurryPostcomposition as Post

module FromDiagram {C D B : CAT} {p : MAP C B} {q : MAP D B}
  (family : FunctorOver (p ∘ pr₁ {C = C} {D = [1]}) q)
  (u v : FunctorOver p q) where
  module F = FunctorLift family
  H = F.lift
  K = p ∘ pr₁ {C = C} {D = [1]}

  insertion : (z : Obj-abs [1]) → FunctorOver p K
  insertion z = record { lift = insert z ; comparison = identity-boundary z p }

  module Endpoint (z : Obj-abs [1]) (w : FunctorOver p q)
    (ξ : FunctorOverIso (compose-over family (insertion z)) w) where
    private module W = FunctorLift w
    i = insert {X = C} z
    boundary = FunctorOverIso.underlying ξ
    edge = q ◁ boundary
    associator = comp-assoc i H q
    d = F.comparison ▷ i
    end = identity-boundary z p

    abstract
      cancel-frame : ((end ∙ (d ∙ associator ⁻¹)) ∙ associator) =₂ (end ∙ d)
      cancel-frame = isoComp-cong (idIso end)
        (isoComp-unitʳ-at d ∙ isoComp-cong (idIso d) (isoComp-inverseˡ-at associator) ∙
          isoComp-assoc-at d (associator ⁻¹) associator) ∙
        isoComp-assoc-at end (d ∙ associator ⁻¹) associator

      comparison : (end ∙ (F.comparison ▷ i)) =₂
        (W.comparison ∙ ((q ◁ boundary) ∙ comp-assoc i H q))
      comparison = (cancel-frame ∙ isoComp-cong (FunctorOverIso.compatible ξ) (idIso associator) ∙
        (isoComp-assoc-at W.comparison edge associator) ⁻¹) ⁻¹

  module WithEndpoints
    (source : FunctorOverIso (compose-over family (insertion zero)) u)
    (target : FunctorOverIso (compose-over family (insertion one)) v) where
    private
      module U = FunctorLift u
      module V = FunctorLift v
    module Source = Endpoint zero u source
    module Target = Endpoint one v target
    module Posted = Post.At 𝒯 M ℱ P I E q H Source.boundary Target.boundary
    module Compared = Diagrams.At 𝒯 M ℱ P I E (q ∘ H) K F.comparison
      (U.comparison ∙ ((q ◁ Source.boundary) ∙ comp-assoc (insert zero) H q))
      (V.comparison ∙ ((q ◁ Target.boundary) ∙ comp-assoc (insert one) H q))
      (identity-boundary zero p) (identity-boundary one p) Source.comparison Target.comparison

    underlying : MorphismExpression U.lift V.lift
    underlying = expression H Source.boundary Target.boundary

    abstract
      over-base : Over.IsOver p q u v underlying
      over-base = expressionIso-compose Compared.comparison
        (expressionIso-compose (Diagrams.retarget-curried 𝒯 M ℱ P I E (q ∘ H)
          ((q ◁ Source.boundary) ∙ comp-assoc (insert zero) H q)
          ((q ◁ Target.boundary) ∙ comp-assoc (insert one) H q) U.comparison V.comparison)
          (retarget-expressionIso Posted.comparison U.comparison V.comparison))

    value : Over.MorphismOver p q u v
    value = record { underlying = underlying ; over-base = over-base }
```
