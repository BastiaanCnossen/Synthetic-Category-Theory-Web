# Absolute morphisms and their hom objects

The specified endpoint identifications turn an interval diagram into an
absolute object of the corresponding hom category. The identity is the
constant interval diagram, with its terminal-category boundary comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking

module SCT.VolumeI.Chapter01.Section09.AbsoluteMorphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section09.HomAndSlices 𝒯 M ℱ P I public

morphism-expression : {C : CAT} {x y : Obj-abs C} →
  Morphism x y → MorphismExpression (const x) (const y)
morphism-expression {x = x} {y} f = record
  { arrow = nameFun (Morphism.diagram f)
  ; source-frame = invIso (const-One x) ∙
      (Morphism.source-identification f ∙ evaluate-name zero (Morphism.diagram f))
  ; target-frame = invIso (const-One y) ∙
      (Morphism.target-identification f ∙ evaluate-name one (Morphism.diagram f)) }

morphism-in-hom : {C : CAT} {x y : Obj-abs C} → Morphism x y → Obj-abs (Hom C x y)
morphism-in-hom f = hom-intro (morphism-expression f)

identity-morphism : {C : CAT} (x : Obj-abs C) → Morphism x x
identity-morphism x = record
  { diagram = const x
  ; source-identification = constant-boundary zero x
  ; target-identification = constant-boundary one x }

identity-in-hom : {C : CAT} (x : Obj-abs C) → Obj-abs (Hom C x x)
identity-in-hom x = morphism-in-hom (identity-morphism x)

underlying-morphism : {C : CAT} (f : Mor C) → Morphism (source f) (target f)
underlying-morphism f = record
  { diagram = f
  ; source-identification = idIso (source f)
  ; target-identification = idIso (target f) }
```
