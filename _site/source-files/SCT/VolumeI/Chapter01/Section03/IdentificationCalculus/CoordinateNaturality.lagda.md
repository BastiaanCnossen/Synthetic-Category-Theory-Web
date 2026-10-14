# Naturality of coordinate comparisons

Postcomposition carries a specified coordinate identification to one in the
target category. Its naturality squares account explicitly for the associator
and for changes of either the outer functor or the source coordinate.
These calculations do not require the pentagon.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.CoordinateNaturality
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S) where

open Vocabulary V
open Operations V
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.WhiskeringCoherence W
open Specialization V T P PL S
open Specialization.Units V T P PL S VC
open Specialization.Whiskering V T P PL S W
open Structural V T P PL S W using (whisker-mixed-at; postWhisker-comp-at; preWhisker-comp-at)

paste-squares : {X Y : CAT} {a a′ b b′ c c′ : MAP X Y}
  (u : a =₁ b) (u′ : a′ =₁ b′)
  (v : b =₁ c) (v′ : b′ =₁ c′)
  (α : a =₁ a′) (β : b =₁ b′) (γ : c =₁ c′)
  → (u′ ∙ α) =₂ (β ∙ u) → (v′ ∙ β) =₂ (γ ∙ v)
  → ((v′ ∙ u′) ∙ α) =₂ (γ ∙ (v ∙ u))
paste-squares u u′ v v′ α β γ p q =
  isoComp-assoc-at γ v u ∙
  (isoComp-cong q (idIso u) ∙
  ((isoComp-assoc-at v′ β u) ⁻¹ ∙
  (isoComp-cong (idIso v′) p ∙ isoComp-assoc-at v′ u′ α)))

post-square : {X Y Z : CAT} (F : MAP Y Z)
  {a a′ b b′ : MAP X Y}
  (u : a =₁ b) (u′ : a′ =₁ b′)
  (α : a =₁ a′) (β : b =₁ b′)
  → (u′ ∙ α) =₂ (β ∙ u)
  → ((F ◁ u′) ∙ (F ◁ α)) =₂ ((F ◁ β) ∙ (F ◁ u))
post-square F u u′ α β p = postWhisker-isoComp-at F β u ∙
  ((postWhisker F ◁ p) ∙ (postWhisker-isoComp-at F u′ α) ⁻¹)

identity-square : {X Y : CAT} {f g : MAP X Y} (α : f =₁ g)
  → (idIso g ∙ α) =₂ (α ∙ idIso f)
identity-square α = (isoComp-unitʳ-at α) ⁻¹ ∙ isoComp-unitˡ-at α

coordinate-at : {X K A B : CAT} (F : MAP A B) (π : MAP K A)
  (t : MAP X K) {p : MAP X A} → (π ∘ t) =₁ p
  → ((F ∘ π) ∘ t) =₁ (F ∘ p)
coordinate-at F π t b = (F ◁ b) ∙ comp-assoc t π F

coordinate-at-outer : {X K A B : CAT} {F G : MAP A B}
  (α : F =₁ G) (π : MAP K A) (t : MAP X K)
  {p : MAP X A} (b : (π ∘ t) =₁ p)
  → (coordinate-at G π t b ∙ ((α ▷ π) ▷ t)) =₂
      ((α ▷ p) ∙ coordinate-at F π t b)
coordinate-at-outer {F = F} {G} α π t {p} b =
  paste-squares (comp-assoc t π F) (comp-assoc t π G) (F ◁ b) (G ◁ b)
    ((α ▷ π) ▷ t) (α ▷ (π ∘ t)) (α ▷ p)
    (preWhisker-comp-at α π t) ((interchange-at α b) ⁻¹)

coordinate-at-inner : {X K A B : CAT} (F : MAP A B) (π : MAP K A)
  {t t′ : MAP X K} {p p′ : MAP X A}
  (b : (π ∘ t) =₁ p) (b′ : (π ∘ t′) =₁ p′)
  (δ : t =₁ t′) (α : p =₁ p′)
  → (b′ ∙ (π ◁ δ)) =₂ (α ∙ b)
  → (coordinate-at F π t′ b′ ∙ ((F ∘ π) ◁ δ)) =₂
      ((F ◁ α) ∙ coordinate-at F π t b)
coordinate-at-inner F π {t} {t′} b b′ δ α p =
  paste-squares (comp-assoc t π F) (comp-assoc t′ π F) (F ◁ b) (F ◁ b′)
    ((F ∘ π) ◁ δ) (F ◁ (π ◁ δ)) (F ◁ α)
    (postWhisker-comp-at δ π F) (post-square F b b′ (π ◁ δ) α p)

```
