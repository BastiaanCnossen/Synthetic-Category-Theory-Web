# Uniqueness of initial and terminal objects

For the original uniqueness assertion of `cor:Terminal_Objects_Are_Unique`, construct the canonical arrows
in both directions. Their composites are identities by the universal
property of the source or target. These are comparisons with fixed
endpoints. The two inverse triangles then give a family in `Iso C`,
and Rezk recognition gives the asserted identification of objects.

The live manuscript strengthened this corollary during formalization to a
statement about the full subcategory of terminal objects. That additional
assertion uses Chapter 3 and is not asserted by this module.

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
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.UniversalObjects
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.InvertibleExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.UniversalComparisons 𝒯 M ℱ P I
  using (initial-comparison; terminal-comparison)
open import SCT.VolumeI.Chapter02.Section03.RezkIdentification 𝒯 M ℱ P I E R using (module Identify)

module InitialObjects {C : CAT} (x y : Obj-abs C) (ex : IsInitial x) (ey : IsInitial y) where
  forward : MorphismExpression (const {P = One} x) (const y)
  forward = initial-expression x ex (const y)
  backward : MorphismExpression (const {P = One} y) (const x)
  backward = initial-expression y ey (const x)

  right-law : ExpressionIso (compose-expression backward forward) (identity-expression (const y))
  right-law = initial-comparison y ey (const y) _ _

  left-law : ExpressionIso (compose-expression forward backward) (identity-expression (const x))
  left-law = initial-comparison x ex (const x) _ _

  identification : x =₁ y
  identification = const-One y ∙
    (Identify.identification forward (LiftInverse.lift forward backward backward right-law left-law) ∙
      (const-One x) ⁻¹)

module TerminalObjects {C : CAT} (x y : Obj-abs C) (ex : IsTerminal x) (ey : IsTerminal y) where
  forward : MorphismExpression (const {P = One} x) (const y)
  forward = terminal-expression y ey (const x)
  backward : MorphismExpression (const {P = One} y) (const x)
  backward = terminal-expression x ex (const y)

  right-law : ExpressionIso (compose-expression backward forward) (identity-expression (const y))
  right-law = terminal-comparison y ey (const y) _ _

  left-law : ExpressionIso (compose-expression forward backward) (identity-expression (const x))
  left-law = terminal-comparison x ex (const x) _ _

  identification : x =₁ y
  identification = const-One y ∙
    (Identify.identification forward (LiftInverse.lift forward backward backward right-law left-law) ∙
      (const-One x) ⁻¹)
```
