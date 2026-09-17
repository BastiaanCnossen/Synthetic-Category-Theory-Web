# Pairing and iterated precomposition

The comparison concerns the already chosen `pair-pre`, with the primitive
external associator retained on both the product and its two components.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section01.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section02.Whiskering as WhiskeringEquivalences
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality

module SCT.VolumeI.Chapter01.Section02.IteratedPairing
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
open Specialization V T P PL S
open Specialization.Units V T P PL S VC
open Specialization.Whiskering V T P PL S W
open PairingCoherence V T P PL S VC W
open WhiskeringEquivalences V T P PL S VC W using
  (leftMultiply; rightMultiply; leftMultiply-isEquiv; rightMultiply-isEquiv;
   left-evaluate; right-evaluate)
open Isomorphisms V T P PL S VC W using (reassociateFour; cancel-inverse)
open PairingNaturality V T P PL S VC W using
  (move-square; project-composite; pre-square-projection)

hcomp-idOuter : {C D E : CAT} {f f′ : MAP C D}
  (g : MAP D E) (α : =₁ f f′)
  → =₂ (idIso g ⋆ α) (g ◁ α)
hcomp-idOuter {f′ = f′} g α = isoComp-unitˡ-at (g ◁ α) ∙
  isoComp-cong (preWhisker-idIso g f′) (idIso (g ◁ α))

hcomp-idInner : {C D E : CAT} {g g′ : MAP D E}
  (β : =₁ g g′) (f : MAP C D)
  → =₂ (β ⋆ idIso f) (β ▷ f)
hcomp-idInner {g = g} β f = isoComp-unitʳ-at (β ▷ f) ∙
  isoComp-cong (idIso (β ▷ f)) (postWhisker-idIso g f)

pentagon-whiskered : {A B C D E : CAT}
  (f : MAP A B) (g : MAP B C) (h : MAP C D) (k : MAP D E)
  → =₂ (comp-assoc (g ∘ f) h k ∙ comp-assoc f g (k ∘ h))
      ((k ◁ comp-assoc f g h) ∙
        (comp-assoc f (h ∘ g) k ∙ (comp-assoc g h k ▷ f)))
pentagon-whiskered f g h k =
  isoComp-assoc-at (k ◁ comp-assoc f g h)
    (comp-assoc f (h ∘ g) k) (comp-assoc g h k ▷ f)
  ∙ (isoComp-cong
      (isoComp-cong (hcomp-idOuter k (comp-assoc f g h)) (idIso _))
      (hcomp-idInner (comp-assoc g h k) f)
    ∙ comp-pentagon f g h k)

leftMultiply-at : {C D : CAT} {f g h : MAP C D}
  (β : =₁ g h) (α : =₁ f g)
  → =₂ (leftMultiply β ∘ α) (β ∙ α)
leftMultiply-at β α = isoComp-cong (const-One β) (idIso α) ∙ left-evaluate β α

rightMultiply-at : {C D : CAT} {f g h : MAP C D}
  (β : =₁ f g) (α : =₁ g h)
  → =₂ (rightMultiply β ∘ α) (α ∙ β)
rightMultiply-at β α = isoComp-cong (idIso α) (const-One β) ∙ right-evaluate β α

cancel-left : {C D : CAT} {f g h : MAP C D}
  (β : =₁ g h) {α α′ : =₁ f g}
  → =₂ (β ∙ α) (β ∙ α′) → =₂ α α′
cancel-left β {α} {α′} p = equiv-reflect (leftMultiply-isEquiv β)
  (invIso (leftMultiply-at β α′) ∙ (p ∙ leftMultiply-at β α))

cancel-right : {C D : CAT} {f g h : MAP C D}
  (β : =₁ f g) {α α′ : =₁ g h}
  → =₂ (α ∙ β) (α′ ∙ β) → =₂ α α′
cancel-right β {α} {α′} p = equiv-reflect (rightMultiply-isEquiv β)
  (invIso (rightMultiply-at β α′) ∙ (p ∙ rightMultiply-at β α))

pre-assoc-at : {A B C D : CAT} {f g : MAP C D}
  (α : =₁ f g) (σ : MAP B C) (τ : MAP A B)
  → =₂ (comp-assoc τ σ g ∙ ((α ▷ σ) ▷ τ))
      ((α ▷ (σ ∘ τ)) ∙ comp-assoc τ σ f)
pre-assoc-at {f = f} {g} α σ τ =
  specialize (preWhisker-comp f g σ τ) α
    (isoComp-evaluate _ _ α
      (const-evaluate (comp-assoc τ σ g) α)
      (preWhisker-evaluate _ τ α
        (preWhisker-evaluate _ σ α (comp-unitˡ α))))
    (isoComp-evaluate _ _ α
      (preWhisker-evaluate _ (σ ∘ τ) α (comp-unitˡ α))
      (const-evaluate (comp-assoc τ σ f) α))

mixed-at : {A B C D : CAT} {f g : MAP B C}
  (u : MAP C D) (α : =₁ f g) (τ : MAP A B)
  → =₂ (comp-assoc τ g u ∙ ((u ◁ α) ▷ τ))
      ((u ◁ (α ▷ τ)) ∙ comp-assoc τ f u)
mixed-at {f = f} {g} u α τ =
  specialize (whisker-mixed f g τ u) α
    (isoComp-evaluate _ _ α
      (const-evaluate (comp-assoc τ g u) α)
      (preWhisker-evaluate _ τ α
        (postWhisker-evaluate u _ α (comp-unitˡ α))))
    (isoComp-evaluate _ _ α
      (postWhisker-evaluate u _ α
        (preWhisker-evaluate _ τ α (comp-unitˡ α)))
      (const-evaluate (comp-assoc τ f u) α))

pre-inverse-at : {A B C : CAT} {f g : MAP B C}
  (α : =₁ f g) (τ : MAP A B)
  → =₂ (invIso α ▷ τ) (invIso (α ▷ τ))
pre-inverse-at {f = f} α τ = cancel-right (α ▷ τ)
  (invIso (isoComp-inverseˡ-at (α ▷ τ)) ∙
    (preWhisker-idIso f τ ∙
      ((preWhisker τ ◁ isoComp-inverseˡ-at α) ∙
        invIso (preWhisker-isoComp-at (invIso α) α τ))))

inverse-tail : {C D : CAT} {f g h : MAP C D}
  (β : =₁ g h) (α : =₁ f g)
  → =₂ ((β ∙ α) ∙ (invIso α ∙ invIso β)) (idIso h)
inverse-tail β α = isoComp-inverseʳ-at β ∙
  (isoComp-cong (idIso β)
    (isoComp-unitˡ-at (invIso β) ∙
      isoComp-cong (isoComp-inverseʳ-at α) (idIso (invIso β))) ∙
    reassociateFour β α (invIso α) (invIso β))

solve-pentagon : {C D : CAT} {x₀ x₁ x₂ x₃ x₄ : MAP C D}
  (A : =₁ x₁ x₄) (B : =₁ x₀ x₁)
  (C′ : =₁ x₃ x₄) (D′ : =₁ x₂ x₃) (E : =₁ x₀ x₂)
  → =₂ (A ∙ B) (C′ ∙ (D′ ∙ E))
  → =₂ (B ∙ (invIso E ∙ invIso D′)) (invIso A ∙ C′)
solve-pentagon A B C′ D′ E p =
  let tail = invIso E ∙ invIso D′
      cleared = isoComp-unitʳ-at C′ ∙
        (isoComp-cong (idIso C′) (inverse-tail D′ E) ∙
          (isoComp-assoc-at C′ (D′ ∙ E) tail ∙
            (isoComp-cong p (idIso tail) ∙ invIso (isoComp-assoc-at A B tail))))
  in cancel-left A (invIso (cancel-inverse A C′) ∙ cleared)

transport-pre : {R X K C : CAT} (u : MAP K C)
  (p : MAP X K) {f : MAP X C} (β : =₁ (u ∘ p) f)
  (σ : MAP R X) → =₁ (u ∘ (p ∘ σ)) (f ∘ σ)
transport-pre u p β σ = (β ▷ σ) ∙ invIso (comp-assoc σ p u)

transport-pre-assoc : {Q R X K C : CAT}
  (u : MAP K C) (p : MAP X K) (f : MAP X C)
  (β : =₁ (u ∘ p) f) (σ : MAP R X) (τ : MAP Q R)
  → =₂
      ((comp-assoc τ σ f ∙ (transport-pre u p β σ ▷ τ)) ∙
        invIso (comp-assoc τ (p ∘ σ) u))
      (transport-pre u p β (σ ∘ τ) ∙ (u ◁ comp-assoc τ σ p))
transport-pre-assoc u p f β σ τ =
  let A = comp-assoc τ σ f
      B = (β ▷ σ) ▷ τ
      E = comp-assoc σ p u ▷ τ
      D′ = comp-assoc τ (p ∘ σ) u
      B′ = comp-assoc τ σ (u ∘ p)
      A′ = comp-assoc (σ ∘ τ) p u
      C′ = u ◁ comp-assoc τ σ p
      β′ = β ▷ (σ ∘ τ)
      tail = invIso E ∙ invIso D′
      expand = isoComp-cong
        (invIso (isoComp-assoc-at A B (invIso E)) ∙
          isoComp-cong (idIso A)
            (isoComp-cong (idIso B) (pre-inverse-at (comp-assoc σ p u) τ) ∙
              preWhisker-isoComp-at (β ▷ σ) (invIso (comp-assoc σ p u)) τ))
        (idIso (invIso D′))
      exchange = isoComp-cong
        (isoComp-cong (pre-assoc-at β σ τ) (idIso (invIso E)))
        (idIso (invIso D′))
      regroup = isoComp-assoc-at β′ B′ tail ∙
        isoComp-assoc-at (β′ ∙ B′) (invIso E) (invIso D′)
      pentagon = solve-pentagon A′ B′ C′ D′ E (pentagon-whiskered τ σ p u)
  in invIso (isoComp-assoc-at β′ (invIso A′) C′) ∙
    (isoComp-cong (idIso β′) pentagon ∙ (regroup ∙ (exchange ∙ expand)))

module Boundaries {Q R X C D : CAT}
  (f : MAP X C) (g : MAP X D) (σ : MAP R X) (τ : MAP Q R) where

  source : MAP Q (C × D)
  source = (pair f g ∘ σ) ∘ τ

  target : MAP Q (C × D)
  target = pair (f ∘ (σ ∘ τ)) (g ∘ (σ ∘ τ))

  together : =₁ source target
  together = pair-pre f g (σ ∘ τ) ∙ comp-assoc τ σ (pair f g)

  successively : =₁ source target
  successively = pair-cong (comp-assoc τ σ f) (comp-assoc τ σ g) ∙
    (pair-pre (f ∘ σ) (g ∘ σ) τ ∙ (pair-pre f g σ ▷ τ))

  project-successively : {Z : CAT} (π : MAP (C × D) Z) (z : MAP X Z)
    (b₀ : =₁ (π ∘ pair f g) z)
    (b₁ : =₁ (π ∘ pair (f ∘ σ) (g ∘ σ)) (z ∘ σ))
    (b₂ : =₁ (π ∘ pair ((f ∘ σ) ∘ τ) ((g ∘ σ) ∘ τ)) ((z ∘ σ) ∘ τ))
    (b₃ : =₁ (π ∘ target) (z ∘ (σ ∘ τ)))
    → =₂ (b₁ ∙ (π ◁ pair-pre f g σ)) (transport-pre π (pair f g) b₀ σ)
    → =₂ (b₂ ∙ (π ◁ pair-pre (f ∘ σ) (g ∘ σ) τ))
        (transport-pre π (pair (f ∘ σ) (g ∘ σ)) b₁ τ)
    → =₂ (b₃ ∙ (π ◁ pair-cong (comp-assoc τ σ f) (comp-assoc τ σ g)))
        (comp-assoc τ σ z ∙ b₂)
    → =₂ (b₃ ∙ (π ◁ successively))
        (transport-pre π (pair f g) b₀ (σ ∘ τ) ∙ (π ◁ comp-assoc τ σ (pair f g)))
  project-successively π z b₀ b₁ b₂ b₃ first second last =
    let before = pair-pre f g σ
        after = pair-pre (f ∘ σ) (g ∘ σ) τ
        top = pair-cong (comp-assoc τ σ f) (comp-assoc τ σ g)
        inner = after ∙ (before ▷ τ)
        transported = transport-pre π (pair f g) b₀ σ
        moved = pre-square-projection π before (idIso (z ∘ σ))
          transported b₁ τ (invIso (isoComp-unitˡ-at transported) ∙ first)
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
      (invIso (isoComp-assoc-at (comp-assoc τ σ z) (transported ▷ τ)
        (invIso (comp-assoc τ (pair f g ∘ σ) π))) ∙ outer-normal)

  project-together : {Z : CAT} (π : MAP (C × D) Z) (z : MAP X Z)
    (b₀ : =₁ (π ∘ pair f g) z)
    (b₃ : =₁ (π ∘ target) (z ∘ (σ ∘ τ)))
    → =₂ (b₃ ∙ (π ◁ pair-pre f g (σ ∘ τ)))
        (transport-pre π (pair f g) b₀ (σ ∘ τ))
    → =₂ (b₃ ∙ (π ◁ together))
        (transport-pre π (pair f g) b₀ (σ ∘ τ) ∙ (π ◁ comp-assoc τ σ (pair f g)))
  project-together π z b₀ b₃ triangle =
    isoComp-cong triangle (idIso _) ∙
      project-composite π (pair-pre f g (σ ∘ τ)) (comp-assoc τ σ (pair f g)) b₃

  compatibility : =₂ together successively
  compatibility = pair-iso-extensionality
    (cancel-left (pair-β₁ (f ∘ (σ ∘ τ)) (g ∘ (σ ∘ τ)))
      (invIso (project-successively pr₁ f
        (pair-β₁ f g)
        (pair-β₁ (f ∘ σ) (g ∘ σ))
        (pair-β₁ ((f ∘ σ) ∘ τ) ((g ∘ σ) ∘ τ))
        (pair-β₁ (f ∘ (σ ∘ τ)) (g ∘ (σ ∘ τ)))
        (pair-pre-triangle₁ f g σ)
        (pair-pre-triangle₁ (f ∘ σ) (g ∘ σ) τ)
        (pair-cong-triangle₁ (comp-assoc τ σ f) (comp-assoc τ σ g))) ∙
       project-together pr₁ f (pair-β₁ f g)
        (pair-β₁ (f ∘ (σ ∘ τ)) (g ∘ (σ ∘ τ)))
        (pair-pre-triangle₁ f g (σ ∘ τ))))
    (cancel-left (pair-β₂ (f ∘ (σ ∘ τ)) (g ∘ (σ ∘ τ)))
      (invIso (project-successively pr₂ g
        (pair-β₂ f g)
        (pair-β₂ (f ∘ σ) (g ∘ σ))
        (pair-β₂ ((f ∘ σ) ∘ τ) ((g ∘ σ) ∘ τ))
        (pair-β₂ (f ∘ (σ ∘ τ)) (g ∘ (σ ∘ τ)))
        (pair-pre-triangle₂ f g σ)
        (pair-pre-triangle₂ (f ∘ σ) (g ∘ σ) τ)
        (pair-cong-triangle₂ (comp-assoc τ σ f) (comp-assoc τ σ g))) ∙
       project-together pr₂ g (pair-β₂ f g)
        (pair-β₂ (f ∘ (σ ∘ τ)) (g ∘ (σ ∘ τ)))
        (pair-pre-triangle₂ f g (σ ∘ τ))))

pair-pre-iterated : {Q R X C D : CAT}
  (f : MAP X C) (g : MAP X D) (σ : MAP R X) (τ : MAP Q R)
  → =₂ (Boundaries.together f g σ τ) (Boundaries.successively f g σ τ)
pair-pre-iterated = Boundaries.compatibility
```

