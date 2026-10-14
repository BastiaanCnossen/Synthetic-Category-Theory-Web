# Pairing and iterated precomposition

The comparison concerns the already chosen `pair-pre`, with the primitive
external associator retained on both the product and its two components.

The argument is now parameterized by the chosen pairing comparisons and
all their projection laws. The adapter retains the original choices. The main
proof still compares the two explicit pastings by projecting them; it never
opens the construction of a pairing comparison through the product inverse.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.Whiskering as WhiskeringEquivalences
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality

import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingInterface as Interface
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ChosenPairing as ChosenPairing
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence as FunctorCoherence


module SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S)
  (PT : Coherence.PentagonTriangleCoherence V T P S) where

open Vocabulary V
open Operations V
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.WhiskeringCoherence W
open Coherence.PentagonTriangleCoherence PT
open Specialization V T P PL S hiding (pair-cong; pair-pre)
open Specialization.Units V T P PL S VC
open Specialization.Whiskering V T P PL S W
open PairingCoherence V T P PL S VC W using (equiv-reflect)
open WhiskeringEquivalences V T P PL S VC W using
  (leftMultiply; rightMultiply; leftMultiply-isEquiv; rightMultiply-isEquiv;
   left-evaluate; right-evaluate)
open Isomorphisms V T P PL S VC W using (reassociateFour; cancel-inverse)
open PairingNaturality V T P PL S VC W using
  (move-square; project-composite; pre-square-projection)

open FunctorCoherence V T P PL S VC W PT public using
  (hcomp-idOuter; hcomp-idInner; pentagon-whiskered; leftMultiply-at; rightMultiply-at; cancel-left; cancel-right; pre-assoc-at; mixed-at; pre-inverse-at; inverse-tail; solve-pentagon; transport-pre; transport-pre-assoc)

module Calculation
  (O : Interface.PairingOperations V T P S)
  (L : Interface.PairingLaws V T P S O) where

  open Interface.PairingOperations O
  open Interface.PairingLaws L

  module Boundaries {Q R X C D : CAT}
    (f : MAP X C) (g : MAP X D) (σ : MAP R X) (τ : MAP Q R) where

    source : MAP Q (C × D)
    source = (pair f g ∘ σ) ∘ τ

    target : MAP Q (C × D)
    target = pair (f ∘ (σ ∘ τ)) (g ∘ (σ ∘ τ))

    together : source =₁ target
    together = pair-pre f g (σ ∘ τ) ∙ comp-assoc τ σ (pair f g)

    successively : source =₁ target
    successively = pair-cong (comp-assoc τ σ f) (comp-assoc τ σ g) ∙
      (pair-pre (f ∘ σ) (g ∘ σ) τ ∙ (pair-pre f g σ ▷ τ))

    project-successively : {Z : CAT} (π : MAP (C × D) Z) (z : MAP X Z)
      (b₀ : (π ∘ pair f g) =₁ z)
      (b₁ : (π ∘ pair (f ∘ σ) (g ∘ σ)) =₁ (z ∘ σ))
      (b₂ : (π ∘ pair ((f ∘ σ) ∘ τ) ((g ∘ σ) ∘ τ)) =₁ ((z ∘ σ) ∘ τ))
      (b₃ : (π ∘ target) =₁ (z ∘ (σ ∘ τ)))
      → (b₁ ∙ (π ◁ pair-pre f g σ)) =₂ (transport-pre π (pair f g) b₀ σ)
      → (b₂ ∙ (π ◁ pair-pre (f ∘ σ) (g ∘ σ) τ)) =₂
          (transport-pre π (pair (f ∘ σ) (g ∘ σ)) b₁ τ)
      → (b₃ ∙ (π ◁ pair-cong (comp-assoc τ σ f) (comp-assoc τ σ g))) =₂
          (comp-assoc τ σ z ∙ b₂)
      → (b₃ ∙ (π ◁ successively)) =₂
          (transport-pre π (pair f g) b₀ (σ ∘ τ) ∙ (π ◁ comp-assoc τ σ (pair f g)))
    project-successively π z b₀ b₁ b₂ b₃ first second last =
      let before = pair-pre f g σ
          after = pair-pre (f ∘ σ) (g ∘ σ) τ
          top = pair-cong (comp-assoc τ σ f) (comp-assoc τ σ g)
          inner = after ∙ (before ▷ τ)
          transported = transport-pre π (pair f g) b₀ σ
          moved = pre-square-projection π before (idIso (z ∘ σ))
            transported b₁ τ ((isoComp-unitˡ-at transported) ⁻¹ ∙ first)
          remove-id = isoComp-unitˡ-at (transport-pre π (pair f g ∘ σ) transported τ) ∙
            isoComp-cong (preWhisker-idIso (z ∘ σ) τ) (idIso _)
          inner-normal = remove-id ∙
            (moved ∙
              (isoComp-cong second (idIso (π ◁ (before ▷ τ))) ∙
                project-composite π after (before ▷ τ) b₂))
          outer-normal = isoComp-cong (idIso (comp-assoc τ σ z)) inner-normal ∙
            (isoComp-assoc-at (comp-assoc τ σ z) b₂ (π ◁ inner) ∙
              (isoComp-cong last (idIso (π ◁ inner)) ∙
                project-composite π top inner b₃))
      in transport-pre-assoc π (pair f g) z b₀ σ τ ∙
        ((isoComp-assoc-at (comp-assoc τ σ z) (transported ▷ τ)
          ((comp-assoc τ (pair f g ∘ σ) π) ⁻¹)) ⁻¹ ∙ outer-normal)

    project-together : {Z : CAT} (π : MAP (C × D) Z) (z : MAP X Z)
      (b₀ : (π ∘ pair f g) =₁ z)
      (b₃ : (π ∘ target) =₁ (z ∘ (σ ∘ τ)))
      → (b₃ ∙ (π ◁ pair-pre f g (σ ∘ τ))) =₂
          (transport-pre π (pair f g) b₀ (σ ∘ τ))
      → (b₃ ∙ (π ◁ together)) =₂
          (transport-pre π (pair f g) b₀ (σ ∘ τ) ∙ (π ◁ comp-assoc τ σ (pair f g)))
    project-together π z b₀ b₃ triangle =
      isoComp-cong triangle (idIso _) ∙
        project-composite π (pair-pre f g (σ ∘ τ)) (comp-assoc τ σ (pair f g)) b₃

    compatibility : together =₂ successively
    compatibility = pair-iso-extensionality
      (cancel-left (pair-β₁ (f ∘ (σ ∘ τ)) (g ∘ (σ ∘ τ)))
        ((project-successively pr₁ f
          (pair-β₁ f g)
          (pair-β₁ (f ∘ σ) (g ∘ σ))
          (pair-β₁ ((f ∘ σ) ∘ τ) ((g ∘ σ) ∘ τ))
          (pair-β₁ (f ∘ (σ ∘ τ)) (g ∘ (σ ∘ τ)))
          (pair-pre-triangle₁ f g σ)
          (pair-pre-triangle₁ (f ∘ σ) (g ∘ σ) τ)
          (pair-cong-triangle₁ (comp-assoc τ σ f) (comp-assoc τ σ g))) ⁻¹ ∙
         project-together pr₁ f (pair-β₁ f g)
          (pair-β₁ (f ∘ (σ ∘ τ)) (g ∘ (σ ∘ τ)))
          (pair-pre-triangle₁ f g (σ ∘ τ))))
      (cancel-left (pair-β₂ (f ∘ (σ ∘ τ)) (g ∘ (σ ∘ τ)))
        ((project-successively pr₂ g
          (pair-β₂ f g)
          (pair-β₂ (f ∘ σ) (g ∘ σ))
          (pair-β₂ ((f ∘ σ) ∘ τ) ((g ∘ σ) ∘ τ))
          (pair-β₂ (f ∘ (σ ∘ τ)) (g ∘ (σ ∘ τ)))
          (pair-pre-triangle₂ f g σ)
          (pair-pre-triangle₂ (f ∘ σ) (g ∘ σ) τ)
          (pair-cong-triangle₂ (comp-assoc τ σ f) (comp-assoc τ σ g))) ⁻¹ ∙
         project-together pr₂ g (pair-β₂ f g)
          (pair-β₂ (f ∘ (σ ∘ τ)) (g ∘ (σ ∘ τ)))
          (pair-pre-triangle₂ f g (σ ∘ τ))))

  pair-pre-iterated : {Q R X C D : CAT}
    (f : MAP X C) (g : MAP X D) (σ : MAP R X) (τ : MAP Q R)
    → (Boundaries.together f g σ τ) =₂ (Boundaries.successively f g σ τ)
  pair-pre-iterated = Boundaries.compatibility
```


The same argument applies to the specified pairing comparisons. The following
boundary diagram and theorem retain the concrete notation of the construction.

```agda
private
  module Chosen = ChosenPairing V T P PL S VC W using (operations; laws)
  module Realized = Calculation Chosen.operations Chosen.laws
open Specialization V T P PL S using (pair-cong; pair-pre)

module Boundaries {Q R X C D : CAT}
  (f : MAP X C) (g : MAP X D) (σ : MAP R X) (τ : MAP Q R) where

  source : MAP Q (C × D)
  source = (pair f g ∘ σ) ∘ τ

  target : MAP Q (C × D)
  target = pair (f ∘ (σ ∘ τ)) (g ∘ (σ ∘ τ))

  together : source =₁ target
  together = pair-pre f g (σ ∘ τ) ∙ comp-assoc τ σ (pair f g)

  successively : source =₁ target
  successively = pair-cong (comp-assoc τ σ f) (comp-assoc τ σ g) ∙
    (pair-pre (f ∘ σ) (g ∘ σ) τ ∙ (pair-pre f g σ ▷ τ))

  open Realized.Boundaries f g σ τ public
    using (project-successively; project-together)

  compatibility : together =₂ successively
  compatibility = Realized.Boundaries.compatibility f g σ τ

pair-pre-iterated : {Q R X C D : CAT}
  (f : MAP X C) (g : MAP X D) (σ : MAP R X) (τ : MAP Q R)
  → (Boundaries.together f g σ τ) =₂ (Boundaries.successively f g σ τ)
pair-pre-iterated = Boundaries.compatibility
```

