# Composition of adjunctions and adjoint sections

The composite unit and counit satisfy both triangle identities. Invertible
units and counits remain invertible, giving closure of left and right
adjoint sections and Bousfield localizations under composition.
This covers `prop:Composite_Of_Adjunctions`,
`exercise:Composite_Of_Adjunctions`, and
`prop:Left_Reflectors_Closed_Under_Composition`.
No functoriality of universals or pointwise recognition principle is used.

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
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section04.CompositeAdjunctions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations 𝒯 M ℱ P I E S
  using (retarget-invertible; restrict-invertible; post-invertible; identified-invertible)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionInverseLaws 𝒯 M ℱ P I E S Q
  using (compose-invertible)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CompositeTriangles as Triangles
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.RawComponentTriangles as Raw

module Composite {C D T : CAT} {l : MAP C D} {r : MAP D C}
  {k : MAP D T} {s : MAP T D} (adjA : Adjunction l r) (adjB : Adjunction k s) where
  module A = Adjunction adjA
  module B = Adjunction adjB
  module Proof = Triangles.Composite 𝒯 M ℱ P I E S Q adjA adjB
  module Data = Proof.Data
  module Components = Raw.Components 𝒯 M ℱ P I E S Data.L Data.R Data.unit Data.counit
  module Result = Components.FromComponents (Proof.Left.triangle (id C)) (Proof.Right.triangle (id T))

  adjunction : Adjunction (k ∘ l) (r ∘ s)
  adjunction = Result.adjunction

  unit-comparison : ExpressionIso (Adjunction.unit adjunction) Data.unit
  unit-comparison = Result.unit-comparison

  counit-comparison : ExpressionIso (Adjunction.counit adjunction) Data.counit
  counit-comparison = Result.counit-comparison

  abstract
    unit-invertible : IsInvertibleExpression A.unit → IsInvertibleExpression B.unit →
      IsInvertibleExpression (Adjunction.unit adjunction)
    unit-invertible ea eb = identified-invertible (expressionIso-inverse unit-comparison)
      (retarget-invertible Data.raw-unit (idIso (id C)) ((comp-assoc Data.L s r) ⁻¹)
        (compose-invertible A.unit (post-expression r (B.unit-at l)) ea
          (post-invertible r (B.unit-at l)
            (retarget-invertible (restrict-expression B.unit l) (comp-unitˡ l) (comp-assoc l k s)
              (restrict-invertible B.unit l eb)))))

    counit-invertible : IsInvertibleExpression A.counit → IsInvertibleExpression B.counit →
      IsInvertibleExpression (Adjunction.counit adjunction)
    counit-invertible ea eb = identified-invertible (expressionIso-inverse counit-comparison)
      (retarget-invertible Data.raw-counit ((comp-assoc Data.R l k) ⁻¹) (idIso (id T))
        (compose-invertible (post-expression k (A.counit-at s)) B.counit
          (post-invertible k (A.counit-at s)
            (retarget-invertible (restrict-expression A.counit s) (comp-assoc s r l) (comp-unitˡ s)
              (restrict-invertible A.counit s ea))) eb))

compose-adjunction : {C D T : CAT} {l : MAP C D} {r : MAP D C}
  {k : MAP D T} {s : MAP T D} → Adjunction l r → Adjunction k s → Adjunction (k ∘ l) (r ∘ s)
compose-adjunction = Composite.adjunction

compose-left-adjoint-section : {C D T : CAT} {p : MAP C D} {q : MAP D T}
  {u : MAP D C} {v : MAP T D} → LeftAdjointSection p u → LeftAdjointSection q v →
  LeftAdjointSection (q ∘ p) (u ∘ v)
compose-left-adjoint-section ea eb = record
  { adjunction = Composite.adjunction B.adjunction A.adjunction
  ; unit-invertible = Composite.unit-invertible B.adjunction A.adjunction B.unit-invertible A.unit-invertible }
  where
    module A = LeftAdjointSection ea
    module B = LeftAdjointSection eb

compose-right-adjoint-section : {C D T : CAT} {p : MAP C D} {q : MAP D T}
  {u : MAP D C} {v : MAP T D} → RightAdjointSection p u → RightAdjointSection q v →
  RightAdjointSection (q ∘ p) (u ∘ v)
compose-right-adjoint-section ea eb = record
  { adjunction = Composite.adjunction A.adjunction B.adjunction
  ; counit-invertible = Composite.counit-invertible A.adjunction B.adjunction A.counit-invertible B.counit-invertible }
  where
    module A = RightAdjointSection ea
    module B = RightAdjointSection eb

compose-left-localization : {C D T : CAT} {p : MAP C D} {q : MAP D T} →
  LeftBousfieldLocalization p → LeftBousfieldLocalization q → LeftBousfieldLocalization (q ∘ p)
compose-left-localization ea eb = record
  { section = A.section ∘ B.section
  ; right-adjoint-section = compose-right-adjoint-section A.right-adjoint-section B.right-adjoint-section }
  where
    module A = LeftBousfieldLocalization ea
    module B = LeftBousfieldLocalization eb

compose-right-localization : {C D T : CAT} {p : MAP C D} {q : MAP D T} →
  RightBousfieldLocalization p → RightBousfieldLocalization q → RightBousfieldLocalization (q ∘ p)
compose-right-localization ea eb = record
  { section = A.section ∘ B.section
  ; left-adjoint-section = compose-left-adjoint-section A.left-adjoint-section B.left-adjoint-section }
  where
    module A = RightBousfieldLocalization ea
    module B = RightBousfieldLocalization eb
```
