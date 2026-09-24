# Pairing and iterated precomposition

The comparison concerns the already chosen `pair-pre`, with the primitive
external associator retained on both the product and its two components.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.Whiskering as WhiskeringEquivalences
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PairingNaturality

module SCT.VolumeI.Chapter01.Section03.IteratedPairing
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
  (g : MAP D E) (α : f =₁ f′)
  → (idIso g ⋆ α) =₂ (g ◁ α)
hcomp-idOuter {f′ = f′} g α = isoComp-unitˡ-at (g ◁ α) ∙
  isoComp-cong (preWhisker-idIso g f′) (idIso (g ◁ α))

hcomp-idInner : {C D E : CAT} {g g′ : MAP D E}
  (β : g =₁ g′) (f : MAP C D)
  → (β ⋆ idIso f) =₂ (β ▷ f)
hcomp-idInner {g = g} β f = isoComp-unitʳ-at (β ▷ f) ∙
  isoComp-cong (idIso (β ▷ f)) (postWhisker-idIso g f)

pentagon-whiskered : {A B C D E : CAT}
  (f : MAP A B) (g : MAP B C) (h : MAP C D) (k : MAP D E)
  → (comp-assoc (g ∘ f) h k ∙ comp-assoc f g (k ∘ h)) =₂
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
  (β : g =₁ h) (α : f =₁ g)
  → (leftMultiply β ∘ α) =₂ (β ∙ α)
leftMultiply-at β α = isoComp-cong (const-One β) (idIso α) ∙ left-evaluate β α

rightMultiply-at : {C D : CAT} {f g h : MAP C D}
  (β : f =₁ g) (α : g =₁ h)
  → (rightMultiply β ∘ α) =₂ (α ∙ β)
rightMultiply-at β α = isoComp-cong (idIso α) (const-One β) ∙ right-evaluate β α

cancel-left : {C D : CAT} {f g h : MAP C D}
  (β : g =₁ h) {α α′ : f =₁ g}
  → (β ∙ α) =₂ (β ∙ α′) → α =₂ α′
cancel-left β {α} {α′} p = equiv-reflect (leftMultiply-isEquiv β)
  ((leftMultiply-at β α′) ⁻¹ ∙ (p ∙ leftMultiply-at β α))

cancel-right : {C D : CAT} {f g h : MAP C D}
  (β : f =₁ g) {α α′ : g =₁ h}
  → (α ∙ β) =₂ (α′ ∙ β) → α =₂ α′
cancel-right β {α} {α′} p = equiv-reflect (rightMultiply-isEquiv β)
  ((rightMultiply-at β α′) ⁻¹ ∙ (p ∙ rightMultiply-at β α))

pre-assoc-at : {A B C D : CAT} {f g : MAP C D}
  (α : f =₁ g) (σ : MAP B C) (τ : MAP A B)
  → (comp-assoc τ σ g ∙ ((α ▷ σ) ▷ τ)) =₂
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
  (u : MAP C D) (α : f =₁ g) (τ : MAP A B)
  → (comp-assoc τ g u ∙ ((u ◁ α) ▷ τ)) =₂
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
  (α : f =₁ g) (τ : MAP A B)
  → (α ⁻¹ ▷ τ) =₂ ((α ▷ τ) ⁻¹)
pre-inverse-at {f = f} α τ = cancel-right (α ▷ τ)
  ((isoComp-inverseˡ-at (α ▷ τ)) ⁻¹ ∙
    (preWhisker-idIso f τ ∙
      ((preWhisker τ ◁ isoComp-inverseˡ-at α) ∙
        (preWhisker-isoComp-at (α ⁻¹) α τ) ⁻¹)))

inverse-tail : {C D : CAT} {f g h : MAP C D}
  (β : g =₁ h) (α : f =₁ g)
  → ((β ∙ α) ∙ (α ⁻¹ ∙ β ⁻¹)) =₂ (idIso h)
inverse-tail β α = isoComp-inverseʳ-at β ∙
  (isoComp-cong (idIso β)
    (isoComp-unitˡ-at (β ⁻¹) ∙
      isoComp-cong (isoComp-inverseʳ-at α) (idIso (β ⁻¹))) ∙
    reassociateFour β α (α ⁻¹) (β ⁻¹))

solve-pentagon : {C D : CAT} {x₀ x₁ x₂ x₃ x₄ : MAP C D}
  (A : x₁ =₁ x₄) (B : x₀ =₁ x₁)
  (C′ : x₃ =₁ x₄) (D′ : x₂ =₁ x₃) (E : x₀ =₁ x₂)
  → (A ∙ B) =₂ (C′ ∙ (D′ ∙ E))
  → (B ∙ (E ⁻¹ ∙ D′ ⁻¹)) =₂ (A ⁻¹ ∙ C′)
solve-pentagon A B C′ D′ E p =
  let tail = E ⁻¹ ∙ D′ ⁻¹
      cleared = isoComp-unitʳ-at C′ ∙
        (isoComp-cong (idIso C′) (inverse-tail D′ E) ∙
          (isoComp-assoc-at C′ (D′ ∙ E) tail ∙
            (isoComp-cong p (idIso tail) ∙ (isoComp-assoc-at A B tail) ⁻¹)))
  in cancel-left A ((cancel-inverse A C′) ⁻¹ ∙ cleared)

transport-pre : {R X K C : CAT} (u : MAP K C)
  (p : MAP X K) {f : MAP X C} (β : (u ∘ p) =₁ f)
  (σ : MAP R X) → (u ∘ (p ∘ σ)) =₁ (f ∘ σ)
transport-pre u p β σ = (β ▷ σ) ∙ (comp-assoc σ p u) ⁻¹

transport-pre-assoc : {Q R X K C : CAT}
  (u : MAP K C) (p : MAP X K) (f : MAP X C)
  (β : (u ∘ p) =₁ f) (σ : MAP R X) (τ : MAP Q R)
  →
      ((comp-assoc τ σ f ∙ (transport-pre u p β σ ▷ τ)) ∙
        (comp-assoc τ (p ∘ σ) u) ⁻¹) =₂
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
      tail = E ⁻¹ ∙ D′ ⁻¹
      expand = isoComp-cong
        ((isoComp-assoc-at A B (E ⁻¹)) ⁻¹ ∙
          isoComp-cong (idIso A)
            (isoComp-cong (idIso B) (pre-inverse-at (comp-assoc σ p u) τ) ∙
              preWhisker-isoComp-at (β ▷ σ) ((comp-assoc σ p u) ⁻¹) τ))
        (idIso (D′ ⁻¹))
      exchange = isoComp-cong
        (isoComp-cong (pre-assoc-at β σ τ) (idIso (E ⁻¹)))
        (idIso (D′ ⁻¹))
      regroup = isoComp-assoc-at β′ B′ tail ∙
        isoComp-assoc-at (β′ ∙ B′) (E ⁻¹) (D′ ⁻¹)
      pentagon = solve-pentagon A′ B′ C′ D′ E (pentagon-whiskered τ σ p u)
  in (isoComp-assoc-at β′ (A′ ⁻¹) C′) ⁻¹ ∙
    (isoComp-cong (idIso β′) pentagon ∙ (regroup ∙ (exchange ∙ expand)))

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

