# Adjoint sections and Bousfield localizations

For `def:Left_Adjoint_Section`, a left adjoint section is an adjunction
whose unit is invertible. The right adjoint version asks that the counit
be invertible. Invertibility means two framed inverse equations for the
whole natural transformation, not an objectwise condition.

The last two records package the existential data in
`def:Left_And_Right_Bousfield_Localizations`. A left Bousfield localization has a
right adjoint section; a right Bousfield localization has a left adjoint
section.

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

module SCT.VolumeI.Chapter04.Section04.AdjointSections
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations 𝒯 M ℱ P I E S
  public using (IsInvertibleExpression)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations 𝒯 M ℱ P I E S
  using (retarget-invertible; restrict-invertible)

record LeftAdjointSection {C D : CAT} (f : MAP C D) (s : MAP D C) : Set m where
  field
    adjunction : Adjunction s f
    unit-invertible : IsInvertibleExpression (Adjunction.unit adjunction)

  module A = Adjunction adjunction

  unit-at-invertible : {Γ : CAT} (x : MAP Γ D) → IsInvertibleExpression (A.unit-at x)
  unit-at-invertible x = retarget-invertible (restrict-expression A.unit x)
    (comp-unitˡ x) (comp-assoc x s f) (restrict-invertible A.unit x unit-invertible)

record RightAdjointSection {C D : CAT} (f : MAP C D) (s : MAP D C) : Set m where
  field
    adjunction : Adjunction f s
    counit-invertible : IsInvertibleExpression (Adjunction.counit adjunction)

  module A = Adjunction adjunction

  counit-at-invertible : {Γ : CAT} (x : MAP Γ D) → IsInvertibleExpression (A.counit-at x)
  counit-at-invertible x = retarget-invertible (restrict-expression A.counit x)
    (comp-assoc x s f) (comp-unitˡ x) (restrict-invertible A.counit x counit-invertible)

record LeftBousfieldLocalization {C D : CAT} (f : MAP C D) : Set m where
  field
    section : MAP D C
    right-adjoint-section : RightAdjointSection f section

record RightBousfieldLocalization {C D : CAT} (f : MAP C D) : Set m where
  field
    section : MAP D C
    left-adjoint-section : LeftAdjointSection f section
```
