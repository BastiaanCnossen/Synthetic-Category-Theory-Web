# The core anima and its universal property

In the book's subsection on collections of objects, `def:Animated_Core`
defines `Core C = Map One C`. Its canonical inclusion `coreInclusion` is
evaluation after inserting the terminal factor.

The main result is `core-universal`, corresponding to
`cor:Animated_Core_Is_Universal`. The calculation in `Universality`
proves it by uncurrying and the terminal-product equivalence, using only
the mapping-anima structure available in this section.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section04.Core
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Mapping.MappingAnimae M
open import SCT.VolumeI.Chapter01.Section04.Currying 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.TerminalInsertion 𝒯
  using (module TerminalInsertion)
open TerminalInsertion
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M
  using (unnamedIso; mapPost-name; post-tests-animae)

Core : CAT → CAT
Core C = Map One C

core-isAn : (C : CAT) → isAn (Core C)
core-isAn C = map-isAn One C

coreInclusion : (C : CAT) → MAP (Core C) C
coreInclusion C = mapEval ∘ product-unitʳ-inverse (Core C)

core-evaluation : {X C : CAT} (f : MAP X (Core C))
  → (mapUncurry f ∘ product-unitʳ-inverse X) =₁ (coreInclusion C ∘ f)
core-evaluation {X} {C} f =
  (comp-assoc f (product-unitʳ-inverse (Core C)) mapEval) ⁻¹ ∙
  ((mapEval ◁ insert-terminal-natural f) ∙
    comp-assoc (product-unitʳ-inverse X) (productMap f (id One)) mapEval)

module Universality (X C : CAT) (xAn : isAn X) where
  private
    N : CAT
    N = Map X (Core C)

    insert : MAP (N × X) ((N × X) × One)
    insert = product-unitʳ-inverse (N × X)

    change : MAP (N × X) (N × (X × One))
    change = productMap (id N) (product-unitʳ-inverse X)

    first : (pr₁ ∘ change) =₁ pr₁
    first = comp-unitˡ pr₁ ∙ pair-β₁ (id N ∘ pr₁) (product-unitʳ-inverse X ∘ pr₂)

    second : ((pr₁ ∘ pr₂) ∘ change) =₁ pr₂
    second = comp-unitˡ pr₂ ∙
      ((pair-β₁ (id X) (terminate X) ▷ pr₂) ∙
      ((comp-assoc pr₂ (product-unitʳ-inverse X) pr₁) ⁻¹ ∙
      ((pr₁ ◁ pair-β₂ (id N ∘ pr₁) (product-unitʳ-inverse X ∘ pr₂)) ∙
        comp-assoc change pr₂ pr₁)))

    regroup-insert : (Associativity.backward N X One ∘ change) =₁ insert
    regroup-insert = pair-iso
      ((pair-β₁ (id (N × X)) (terminate (N × X))) ⁻¹ ∙
      (pair-projections ∙
      (pair-cong first second ∙
      (pair-pre pr₁ (pr₁ ∘ pr₂) change ∙
        project-pair₁ (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) change))))
      (terminal-iso _ _)

  uncurrying-route : MAP (Map X (Core C)) (Map X C)
  uncurrying-route = mapPre (product-unitʳ-inverse X) ∘ mapUncurrying X One C xAn

  route-is-postcomposition : uncurrying-route =₁ (mapPost (coreInclusion C))
  route-is-postcomposition = mapReflect (map-isAn X (Core C)) _ _
    ((mapPost-β (coreInclusion C)) ⁻¹ ∙
    (core-evaluation (mapEval {X} {Core C}) ∙
    ((mapUncurry (mapEval {X} {Core C}) ◁ regroup-insert) ∙
    (comp-assoc (productMap (id N) (product-unitʳ-inverse X))
      (Associativity.backward N X One) (mapUncurry (mapEval {X} {Core C})) ∙
    ((ExponentialLaw.forward-β X One C xAn ▷ productMap (id N) (product-unitʳ-inverse X)) ∙
      mapPre-uncurry (product-unitʳ-inverse X) (mapUncurrying X One C xAn))))))

  postcomposition-isEquiv : IsEquiv (mapPost (coreInclusion C))
  postcomposition-isEquiv = equiv-transport route-is-postcomposition
    (equiv-compose (mapUncurrying X One C xAn) (mapPre (product-unitʳ-inverse X))
      (mapUncurrying-isEquiv X One C xAn)
      (mapPre-isEquiv (product-unitʳ-inverse X) (equiv-inverse (product-unitʳ-isEquiv X))))

core-universal : (X C : CAT) → isAn X → IsEquiv (mapPost {C = X} (coreInclusion C))
core-universal = Universality.postcomposition-isEquiv

module CoreLift {X C : CAT} (xAn : isAn X) (f : MAP X C) where
  chosen = equiv-lift (core-universal X C xAn) (nameMap f)
  point = FunctorLift.lift chosen
  lift : MAP X (Core C)
  lift = decodeMap point
  comparison : (coreInclusion C ∘ lift) =₁ f
  comparison = unnamedIso (FunctorLift.comparison chosen ∙
    ((mapPost (coreInclusion C) ◁ name-decode point) ∙ (mapPost-name (coreInclusion C) lift) ⁻¹))

core-of-anima : (C : CAT) → isAn C → IsEquiv (coreInclusion C)
core-of-anima C cAn = post-tests-animae (core-isAn C) cAn
  (coreInclusion C) (λ X xAn → core-universal X C xAn)

```
