# Relative units and counits as morphisms

The normalized relative adjunction supplies actual unit and counit
morphisms in the two relative endofunctor categories. This construction
uses the full relative interval diagrams. Compatibility of naming with
composition and the resulting triangle comparisons there are separate.

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

module SCT.VolumeI.Chapter04.Section04.RelativeAdjunctionMorphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.RelativeAdjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter04.Section04.RelativeUnitCriterion 𝒯 M ℱ P I E S
  using (counit-to-unit)
import SCT.VolumeI.Chapter03.RelativeCategories.Functors as Functors
import SCT.VolumeI.Chapter03.RelativeCategories.NamedMorphisms as Names

module At {C D B : CAT} {p : MAP C B} {q : MAP D B}
  {L : FunctorOver p q} {R : FunctorOver q p} (w : RelativeAdjunction p q L R) where
  private
    module W = RelativeAdjunction w
    module U = UnitRelativeAdjunction (counit-to-unit w)
    module Source = Functors.Over 𝒯 M ℱ P p p
    module Target = Functors.Over 𝒯 M ℱ P q q

  unit : Morphism (Source.Name.object (identity-over p)) (Source.Name.object (compose-over R L))
  unit = Names.Name.value 𝒯 M ℱ P I E S U.unit

  counit : Morphism (Target.Name.object (compose-over L R)) (Target.Name.object (identity-over q))
  counit = Names.Name.value 𝒯 M ℱ P I E S W.counit
```
