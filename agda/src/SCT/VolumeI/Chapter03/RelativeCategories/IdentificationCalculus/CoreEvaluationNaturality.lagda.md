# Naturality of core evaluation

The existing `core-evaluation` comparison is natural for the actual
`mapUncurryIso` action. Paste terminal-insertion naturality with the
associator squares, then use the computation comparing the raw and
specified uncurrying actions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.CoreEvaluationNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.TerminalInsertion 𝒯
  using (module TerminalInsertion)
open TerminalInsertion using (insert-terminal-natural)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (post-square)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; whisker-mixed-at)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (move-square)
import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.TerminalInsertionNaturality as Insertion

module Naturality {X C : CAT} {u v : MAP X (Core C)} (α : u =₁ v) where
  module Insert = Insertion.Naturality 𝒯 M α using (comparison)
  IX = product-unitʳ-inverse X
  IC = product-unitʳ-inverse (Core C)
  δ = productMap-cong α (idIso (id One))
  raw-action = (mapEval ◁ δ) ▷ IX
  first-action = mapEval ◁ (δ ▷ IX)
  second-action = mapEval ◁ (IC ◁ α)
  final-action = coreInclusion C ◁ α
  associate : (w : MAP X (Core C)) →
    (mapUncurry w ∘ IX) =₁ (mapEval ∘ (productMap w (id One) ∘ IX))
  associate w = comp-assoc IX (productMap w (id One)) mapEval
  insert : (w : MAP X (Core C)) →
    (mapEval ∘ (productMap w (id One) ∘ IX)) =₁ (mapEval ∘ (IC ∘ w))
  insert w = mapEval ◁ insert-terminal-natural w
  unassociate : (w : MAP X (Core C)) →
    (mapEval ∘ (IC ∘ w)) =₁ (coreInclusion C ∘ w)
  unassociate w = (comp-assoc w IC mapEval) ⁻¹

  opaque
    first-square : (associate v ∙ raw-action) =₂ (first-action ∙ associate u)
    first-square = whisker-mixed-at δ IX mapEval

    second-square : (insert v ∙ first-action) =₂ (second-action ∙ insert u)
    second-square = post-square mapEval (insert-terminal-natural u) (insert-terminal-natural v)
      (δ ▷ IX) (IC ◁ α) Insert.comparison

    third-square : (unassociate v ∙ second-action) =₂ (final-action ∙ unassociate u)
    third-square = move-square (comp-assoc v IC mapEval) final-action second-action
      (comp-assoc u IC mapEval) (postWhisker-comp-at α IC mapEval)

    raw-comparison : (core-evaluation v ∙ raw-action) =₂ (final-action ∙ core-evaluation u)
    raw-comparison = paste-squares (insert u ∙ associate u) (insert v ∙ associate v) (unassociate u) (unassociate v)
      raw-action second-action final-action
      (paste-squares (associate u) (associate v) (insert u) (insert v) raw-action first-action second-action
        first-square second-square) third-square

    comparison : (core-evaluation v ∙ (mapUncurryIso α ▷ IX)) =₂
      ((coreInclusion C ◁ α) ∙ core-evaluation u)
    comparison = raw-comparison ∙ isoComp-cong (idIso (core-evaluation v))
      (preWhisker IX ◁ mapUncurry-actions-agree α)
```
