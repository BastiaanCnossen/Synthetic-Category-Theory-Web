# Composition from the Segal inverse

For `cons:Composition_Functor`, complete the two short edges to a triangle
and take its long edge. The counit supplies the short-edge comparisons.
The two outer vertex identifications then give the source and target
of composition, as in the displayed formulas in the book.

The endpoint-preserving calculations are collected in `MorphismCalculus/`.
The construction of composition itself remains here; its unit and associativity
laws are developed in the neighboring main modules.

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

module SCT.VolumeI.Chapter02.Section02.Composition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open Segal 𝒯 M ℱ P I E public
open SegalAxiom S
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-equivalenceʳ)

completeTriangle : (C : CAT) → MAP (Composable C) (Triangles C)
completeTriangle C = IsEquiv.inverse (segal-isEquiv C)

completeTriangle-β : (C : CAT) →
  (composable-restriction C ∘ completeTriangle C) =₁ (id (Composable C))
completeTriangle-β C = (IsEquiv.retractionIso (segal-isEquiv C)) ⁻¹

completeTriangle-η : (C : CAT) →
  (completeTriangle C ∘ composable-restriction C) =₁ (id (Triangles C))
completeTriangle-η C = (IsEquiv.sectionIso (segal-isEquiv C)) ⁻¹

compose : (C : CAT) → MAP (Composable C) (Ar C)
compose C = edge₁ ∘ completeTriangle C

module Completion (C : CAT) where
  q = composable-restriction C
  j = completeTriangle C

  short-edge : (r : MAP (Composable C) (Ar C))
    (e : MAP (Triangles C) (Ar C)) → (r ∘ q) =₁ e → (e ∘ j) =₁ r
  short-edge r e β = comp-unitʳ r ∙
    ((r ◁ completeTriangle-β C) ∙ (comp-assoc j q r ∙ (β ⁻¹ ▷ j)))

  first-edge : (edge₂ ∘ j) =₁ (pullback₁ {f = ev₁} {ev₀})
  first-edge = short-edge pullback₁ edge₂ (ConeIso.leftIso (composable-restriction-β C))

  second-edge : (edge₀ ∘ j) =₁ (pullback₂ {f = ev₁} {ev₀})
  second-edge = short-edge pullback₂ edge₀ (ConeIso.rightIso (composable-restriction-β C))

  source-vertex : (ev₀ ∘ edge₁) =₁ (ev₀ ∘ edge₂ {C})
  source-vertex = (evaluate-pre d₂ zero) ⁻¹ ∙
    (evaluate-cong face-bottom ∙ evaluate-pre d₁ zero)

  target-vertex : (ev₁ ∘ edge₁) =₁ (ev₁ ∘ edge₀ {C})
  target-vertex = (evaluate-pre d₀ one) ⁻¹ ∙
    (evaluate-cong (face-top ⁻¹) ∙ evaluate-pre d₁ one)

  compose-source : (ev₀ ∘ compose C) =₁ (ev₀ ∘ pullback₁ {f = ev₁} {ev₀})
  compose-source = (ev₀ ◁ first-edge) ∙
    (comp-assoc j edge₂ ev₀ ∙ ((source-vertex ▷ j) ∙ (comp-assoc j edge₁ ev₀) ⁻¹))

  compose-target : (ev₁ ∘ compose C) =₁ (ev₁ ∘ pullback₂ {f = ev₁} {ev₀})
  compose-target = (ev₁ ◁ second-edge) ∙
    (comp-assoc j edge₀ ev₁ ∙ ((target-vertex ▷ j) ∙ (comp-assoc j edge₁ ev₁) ⁻¹))
```

The fiber of the Segal equivalence over a prescribed pair is contractible.
This proves the assertion immediately following the Segal axiom, for the
category of composites already defined in Section 2.1.

```agda
composites-contractible : (C : CAT) (p : Obj-abs (Composable C)) → IsContractible (Composites C p)
composites-contractible C p = equiv-transport (terminal-iso _ _)
  (pullback-equivalenceʳ (composable-restriction C) p (segal-isEquiv C))

comp-contractible : {C : CAT} {x y z : Obj-abs C}
  (f : Morphism x y) (g : Morphism y z) → IsContractible (Comp f g)
comp-contractible {C} f g = composites-contractible C (PairOfMorphisms.value f g)
```
