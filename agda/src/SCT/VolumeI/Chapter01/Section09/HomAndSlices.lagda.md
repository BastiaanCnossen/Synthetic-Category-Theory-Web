# Hom categories, slices, and universal objects

These are the pullbacks in `def:Hom_Groupoid` and `def:Slice_Categories`.
At this stage `Hom C x y` is a category; its anima property is not assumed.
The definitions of initial and terminal objects are equivalences of the
slice projections, exactly as in `def:Initial_Object`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking

module SCT.VolumeI.Chapter01.Section09.HomAndSlices
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section09.EndpointFibers 𝒯 M ℱ P I public

Hom : (C : CAT) → Obj-abs C → Obj-abs C → CAT
Hom C x y = EndpointFiber.category x y

Slice Coslice : (C : CAT) → Obj-abs C → CAT
Slice C x = EndpointFiber.category (id C) (const x)
Coslice C x = EndpointFiber.category (const x) (id C)

slice-projection : {C : CAT} (x : Obj-abs C) → MAP (Slice C x) C
slice-projection {C} x = EndpointFiber.base (id C) (const x)

coslice-projection : {C : CAT} (x : Obj-abs C) → MAP (Coslice C x) C
coslice-projection {C} x = EndpointFiber.base (const x) (id C)

IsTerminal IsInitial : {C : CAT} → Obj-abs C → Set m
IsTerminal x = IsEquiv (slice-projection x)
IsInitial x = IsEquiv (coslice-projection x)

hom-intro : {Γ C : CAT} {x y : Obj-abs C} →
  MorphismExpression (const {P = Γ} x) (const y) → MAP Γ (Hom C x y)
hom-intro {Γ} {x = x} {y} = EndpointFiber.lift x y (terminate Γ)

hom-expression : {Γ C : CAT} {x y : Obj-abs C} →
  MAP Γ (Hom C x y) → MorphismExpression (const x) (const y)
hom-expression {x = x} {y} h = record
  { arrow = H.arrow ∘ h
  ; source-frame = (x ◁ terminal-iso _ _) ∙
      (comp-assoc h H.base x ∙ ((H.source-frame ▷ h) ∙ invIso (comp-assoc h H.arrow ev₀)))
  ; target-frame = (y ◁ terminal-iso _ _) ∙
      (comp-assoc h H.base y ∙ ((H.target-frame ▷ h) ∙ invIso (comp-assoc h H.arrow ev₁))) }
  where module H = EndpointFiber x y

hom-post : {C D : CAT} (F : MAP C D) (x y : Obj-abs C) →
  MAP (Hom C x y) (Hom D (F ∘ x) (F ∘ y))
hom-post F x y = hom-intro (record
  { arrow = MorphismExpression.arrow image
  ; source-frame = invIso (comp-assoc (terminate (Hom _ x y)) x F) ∙ MorphismExpression.source-frame image
  ; target-frame = invIso (comp-assoc (terminate (Hom _ x y)) y F) ∙ MorphismExpression.target-frame image })
  where
  image = post-expression F (hom-expression (id (Hom _ x y)))

slice-intro : {Γ C : CAT} (x : Obj-abs C) (y : MAP Γ C) →
  MorphismExpression y (const x) → MAP Γ (Slice C x)
slice-intro {C = C} x y α = EndpointFiber.lift (id C) (const x) y (record
  { arrow = MorphismExpression.arrow α
  ; source-frame = invIso (comp-unitˡ y) ∙ MorphismExpression.source-frame α
  ; target-frame = invIso (const-pre x y) ∙ MorphismExpression.target-frame α })

coslice-intro : {Γ C : CAT} (x : Obj-abs C) (y : MAP Γ C) →
  MorphismExpression (const x) y → MAP Γ (Coslice C x)
coslice-intro {C = C} x y α = EndpointFiber.lift (const x) (id C) y (record
  { arrow = MorphismExpression.arrow α
  ; source-frame = invIso (const-pre x y) ∙ MorphismExpression.source-frame α
  ; target-frame = invIso (comp-unitˡ y) ∙ MorphismExpression.target-frame α })
```
