# The section identifications of adjoint sections

Rezk recognition turns the invertible unit or counit into an
identification of functors. In particular, the chosen adjoint really is
a section of the original functor. The identification is obtained from
the specified transformation, not chosen independently of it.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SectionIdentifications
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section03.InvertibleExpressions 𝒯 M ℱ P I E S
  using (invertible-expression-lift)
open import SCT.VolumeI.Chapter02.Section03.RezkIdentification 𝒯 M ℱ P I E R
  using (module Identify)
import SCT.VolumeI.Chapter02.Section03.InverseCalculus.RetractionsReflectInverses as Reflection

left-section-identification : {C D : CAT} {f : MAP C D} {s : MAP D C} →
  LeftAdjointSection f s → (f ∘ s) =₁ id D
left-section-identification w = (Identify.identification W.A.unit
  (invertible-expression-lift W.A.unit W.unit-invertible)) ⁻¹
  where module W = LeftAdjointSection w

right-section-identification : {C D : CAT} {f : MAP C D} {s : MAP D C} →
  RightAdjointSection f s → (f ∘ s) =₁ id D
right-section-identification w = Identify.identification W.A.counit
  (invertible-expression-lift W.A.counit W.counit-invertible)
  where module W = RightAdjointSection w
```

An adjoint section reflects invertibility of morphism expressions. This
uses its derived section identification and works on a whole family of
morphisms, without an objectwise criterion.

```agda
left-section-reflects-invertible : {C D Γ : CAT} {f : MAP C D} {s : MAP D C}
  (w : LeftAdjointSection f s) {x y : MAP Γ D} (α : MorphismExpression x y) →
  IsInvertibleExpression (post-expression s α) → IsInvertibleExpression α
left-section-reflects-invertible {f = f} {s} w =
  Reflection.WithRetraction.reflect-invertible 𝒯 M ℱ P I E S s f (left-section-identification w)

right-section-reflects-invertible : {C D Γ : CAT} {f : MAP C D} {s : MAP D C}
  (w : RightAdjointSection f s) {x y : MAP Γ D} (α : MorphismExpression x y) →
  IsInvertibleExpression (post-expression s α) → IsInvertibleExpression α
right-section-reflects-invertible {f = f} {s} w =
  Reflection.WithRetraction.reflect-invertible 𝒯 M ℱ P I E S s f (right-section-identification w)
```
