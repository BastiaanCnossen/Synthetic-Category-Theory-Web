# Ordinary relative slices

The two pullbacks in `def:Relative_Slice` use the ordinary slice
categories already defined in Chapter 2. These definitions require
neither Chapter 3's general slices nor a contextual category syntax.
The fibration theorem for these projections is not asserted here.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section03.RelativeSlices
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 public
open Laws.PullbackStructure P public

module RelativeSlice {C D : CAT} (f : MAP C D) (d : Obj-abs D) where
  category : CAT
  category = Pullback (slice-projection d) f

  projection : MAP category C
  projection = pullback₂

  diagram : MAP category (Slice D d)
  diagram = pullback₁

  matching : (slice-projection d ∘ diagram) =₁ (f ∘ projection)
  matching = pullbackMatch

  intro : {Γ : CAT} → Cone (slice-projection d) f Γ → MAP Γ category
  intro = pullbackLift

  intro-β : {Γ : CAT} (s : Cone (slice-projection d) f Γ) →
    ConeIso (conePre (intro s) (pullbackCone (slice-projection d) f)) s
  intro-β = pullbackLift-β

module RelativeCoslice {C D : CAT} (f : MAP C D) (d : Obj-abs D) where
  category : CAT
  category = Pullback (coslice-projection d) f

  projection : MAP category C
  projection = pullback₂

  diagram : MAP category (Coslice D d)
  diagram = pullback₁

  matching : (coslice-projection d ∘ diagram) =₁ (f ∘ projection)
  matching = pullbackMatch

  intro : {Γ : CAT} → Cone (coslice-projection d) f Γ → MAP Γ category
  intro = pullbackLift

  intro-β : {Γ : CAT} (s : Cone (coslice-projection d) f Γ) →
    ConeIso (conePre (intro s) (pullbackCone (coslice-projection d) f)) s
  intro-β = pullbackLift-β
```

