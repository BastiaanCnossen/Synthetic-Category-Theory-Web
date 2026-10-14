# Product comparisons with their projection witnesses

Applying a product functor to a pair is computed coordinatewise. The
comparison below retains both specified projection witnesses. Its proof
uses the pairing operations, their composition comparison, and the two
projection triangles as parameters; no mapping-anima structure is needed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingInterface as Interface
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ChosenPairing as ChosenPairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductPairing
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S) where

open Vocabulary V
open Operations V
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Specialization V T P PL S hiding (pair-cong; pair-pre)
open Specialization.Units V T P PL S VC
open Specialization.Whiskering V T P PL S W
open Structural V T P PL S W using (postWhisker-id-at)

module Calculation (O : Interface.PairingOperations V T P S)
  (cong-composition : {X C D : CAT}
    {f₀ f₁ f₂ : MAP X C} {g₀ g₁ g₂ : MAP X D}
    (α₂ : f₁ =₁ f₂) (α₁ : f₀ =₁ f₁) (β₂ : g₁ =₁ g₂) (β₁ : g₀ =₁ g₁)
    → (Interface.PairingOperations.pair-cong O (α₂ ∙ α₁) (β₂ ∙ β₁)) =₂
      (Interface.PairingOperations.pair-cong O α₂ β₂ ∙ Interface.PairingOperations.pair-cong O α₁ β₁))
  (triangle₁ : {R X C D : CAT} (f : MAP X C) (g : MAP X D) (r : MAP R X)
    {f′ : MAP R C} {g′ : MAP R D} (α : (f ∘ r) =₁ f′) (β : (g ∘ r) =₁ g′)
    → (pair-β₁ f′ g′ ∙ (pr₁ ◁ (Interface.PairingOperations.pair-cong O α β ∙ Interface.PairingOperations.pair-pre O f g r))) =₂
      (α ∙ ((pair-β₁ f g ▷ r) ∙ (comp-assoc r (pair f g) pr₁) ⁻¹)))
  (triangle₂ : {R X C D : CAT} (f : MAP X C) (g : MAP X D) (r : MAP R X)
    {f′ : MAP R C} {g′ : MAP R D} (α : (f ∘ r) =₁ f′) (β : (g ∘ r) =₁ g′)
    → (pair-β₂ f′ g′ ∙ (pr₂ ◁ (Interface.PairingOperations.pair-cong O α β ∙ Interface.PairingOperations.pair-pre O f g r))) =₂
      (β ∙ ((pair-β₂ f g ▷ r) ∙ (comp-assoc r (pair f g) pr₂) ⁻¹))) where

  open Interface.PairingOperations O
  open Interface.Constructions V T P S O

  module ProductPair {X A B C D : CAT}
    (f : MAP A C) (g : MAP B D) (u : MAP X A) (v : MAP X B)
    {u′ : MAP X C} {v′ : MAP X D}
    (α : (f ∘ u) =₁ u′) (β : (g ∘ v) =₁ v′) where

    comparison = pair-cong α β ∙ productMap-pair f g u v
    first = α ∙ ((f ◁ pair-β₁ u v) ∙ comp-assoc (pair u v) pr₁ f)
    second = β ∙ ((g ◁ pair-β₂ u v) ∙ comp-assoc (pair u v) pr₂ g)
    normalized = pair-cong first second ∙ pair-pre (f ∘ pr₁) (g ∘ pr₂) (pair u v)

    abstract
      normalization : comparison =₂ normalized
      normalization = isoComp-cong
        ((cong-composition α ((f ◁ pair-β₁ u v) ∙ comp-assoc (pair u v) pr₁ f)
          β ((g ◁ pair-β₂ u v) ∙ comp-assoc (pair u v) pr₂ g)) ⁻¹)
        (idIso (pair-pre (f ∘ pr₁) (g ∘ pr₂) (pair u v))) ∙
        (isoComp-assoc-at (pair-cong α β) _ _) ⁻¹

      projection₁ :
        (pair-β₁ u′ v′ ∙ (pr₁ ◁ comparison)) =₂
        (first ∙ ((pair-β₁ (f ∘ pr₁) (g ∘ pr₂) ▷ pair u v) ∙
          (comp-assoc (pair u v) (productMap f g) pr₁) ⁻¹))
      projection₁ = triangle₁ (f ∘ pr₁) (g ∘ pr₂) (pair u v) first second ∙
        isoComp-cong (idIso (pair-β₁ u′ v′)) (postWhisker pr₁ ◁ normalization)

      projection₂ :
        (pair-β₂ u′ v′ ∙ (pr₂ ◁ comparison)) =₂
        (second ∙ ((pair-β₂ (f ∘ pr₁) (g ∘ pr₂) ▷ pair u v) ∙
          (comp-assoc (pair u v) (productMap f g) pr₂) ⁻¹))
      projection₂ = triangle₂ (f ∘ pr₁) (g ∘ pr₂) (pair u v) first second ∙
        isoComp-cong (idIso (pair-β₂ u′ v′)) (postWhisker pr₂ ◁ normalization)

```

The chosen realization passes the existing higher comparisons literally.
In particular, neither projection triangle is replaced by a new witness.

```agda
private
  module Selected = ChosenPairing V T P PL S VC W using (operations)
  module Pairing = PairingCoherence V T P PL S VC W using (pair-cong-comp)
open Interface.Constructions V T P S Selected.operations public using (productMap-pair)

module ChosenComparisons (PT : Coherence.PentagonTriangleCoherence V T P S) where
  private
    module Projections = ProductUnits V T P PL S VC W PT
      using (pair-pre-cong-triangle₁; pair-pre-cong-triangle₂)
    module Realized = Calculation Selected.operations Pairing.pair-cong-comp
      Projections.pair-pre-cong-triangle₁ Projections.pair-pre-cong-triangle₂
  open Realized public using (module ProductPair)
  open ProductUnits V T P PL S VC W PT using (left-unitor-comp)
```

The unit in an unchanged coordinate can be absorbed into its projection
witness. This is the normalization used when pasting insertion squares.

```agda
  abstract
    identity-coordinate : {X Y A : CAT} (π : MAP Y A) (t : MAP X Y)
      {q : MAP X A} (b : (π ∘ t) =₁ q) →
      (comp-unitˡ q ∙ ((id A ◁ b) ∙ comp-assoc t π (id A))) =₂
        (b ∙ (comp-unitˡ π ▷ t))
    identity-coordinate π t b = isoComp-cong (idIso b) (left-unitor-comp t π) ∙
      (isoComp-assoc-at b (comp-unitˡ (π ∘ t)) (comp-assoc t π (id _)) ∙
      (isoComp-cong (postWhisker-id-at b) (idIso (comp-assoc t π (id _))) ∙
        (isoComp-assoc-at (comp-unitˡ _) (id _ ◁ b) (comp-assoc t π (id _))) ⁻¹))
```
