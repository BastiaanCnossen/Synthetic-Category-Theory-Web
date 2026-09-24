# The chosen short edges under a change of parameters

The universal-cone factorization and the globally chosen Segal inverse
use the same counit. Their short-edge comparisons agree after restriction,
including the input cone's prescribed pullback beta comparisons.

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

module SCT.VolumeI.Chapter02.Section02.CompositionShortEdges
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.CompositionExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯 using (pre-inverse)
import SCT.VolumeI.Chapter01.Section04.SectionComparisonRestriction as Restriction
open Laws.PullbackStructure P

module At {Γ C : CAT} (t : Cone (ev₁ {C}) ev₀ Γ) where
  q = composable-restriction C
  j = completeTriangle C
  k = pullbackLift t
  ε = completeTriangle-β C
  γ = FunctorLift.comparison (equiv-lift (Segal.SegalAxiom.segal-isPullback S C) k)
  module U = UniversalCone (triangle-cone C) (Segal.SegalAxiom.segal-isPullback S C)

  module Edge (r : MAP (Composable C) (Ar C)) (e : MAP (Triangles C) (Ar C))
    (β : (r ∘ q) =₁ e) where
    module R = Restriction.At 𝒯 q j ε r e (β ⁻¹) k
    short = Completion.short-edge C r e β

    abstract
      section-normal : (R.along-section ∙ (β ⁻¹ ▷ j)) =₂ short
      section-normal =
        isoComp-cong (idIso (comp-unitʳ r))
          (isoComp-assoc-at (r ◁ ε) (comp-assoc j q r) (β ⁻¹ ▷ j)) ∙
        isoComp-assoc-at (comp-unitʳ r) ((r ◁ ε) ∙ comp-assoc j q r) (β ⁻¹ ▷ j)

      comparison :
        ((r ◁ γ) ∙ (comp-assoc (j ∘ k) q r ∙ (β ▷ (j ∘ k)) ⁻¹)) =₂
        ((short ▷ k) ∙ (comp-assoc k j e) ⁻¹)
      comparison =
        isoComp-cong (preWhisker k ◁ section-normal) (idIso ((comp-assoc k j e) ⁻¹)) ∙
        (R.comparison ∙
        (isoComp-cong (idIso ((r ◁ γ) ∙ comp-assoc (j ∘ k) q r))
          ((pre-inverse β (j ∘ k)) ⁻¹) ∙
          (isoComp-assoc-at (r ◁ γ) (comp-assoc (j ∘ k) q r) ((β ▷ (j ∘ k)) ⁻¹)) ⁻¹))

  module First = Edge pullback₁ edge₂ (ConeIso.leftIso (composable-restriction-β C))
  module Second = Edge pullback₂ edge₀ (ConeIso.rightIso (composable-restriction-β C))

  abstract
    first-edge : (ConeIso.leftIso (Complete.short-edges t)) =₂
      (ConeIso.leftIso (pullbackLift-β t) ∙
        ((Completion.first-edge C ▷ k) ∙ (comp-assoc k j edge₂) ⁻¹))
    first-edge = isoComp-cong (idIso (ConeIso.leftIso (pullbackLift-β t))) First.comparison ∙
      U.factor-β-left t

    second-edge : (ConeIso.rightIso (Complete.short-edges t)) =₂
      (ConeIso.rightIso (pullbackLift-β t) ∙
        ((Completion.second-edge C ▷ k) ∙ (comp-assoc k j edge₀) ⁻¹))
    second-edge = isoComp-cong (idIso (ConeIso.rightIso (pullbackLift-β t))) Second.comparison ∙
      U.factor-β-right t
```
