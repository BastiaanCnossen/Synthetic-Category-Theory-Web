# Naturality of the structural comparisons

These are specializations of the parameterized whiskering axioms, with both
boundaries normalized explicitly. They introduce no additional coherence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section01.Specialization as Specialization

module SCT.VolumeI.Chapter01.Section02.Structural
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (W : Coherence.WhiskeringCoherence V T P S) where

open Vocabulary V
open Operations V
open Terminal.Constructions V T
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.WhiskeringCoherence W
open Specialization V T P PL S

postWhisker-id-at : {C D : CAT} {f g : MAP C D} (α : NatIso f g)
  → Iso₂ (comp-unitˡ g ∙ (id D ◁ α)) (α ∙ comp-unitˡ f)
postWhisker-id-at {D = D} {f} {g} α =
  specialize (postWhisker-id f g) α
    (isoComp-evaluate (const (comp-unitˡ g)) (id D ◁ id (f ≅ g)) α
      (const-evaluate (comp-unitˡ g) α)
      (postWhisker-evaluate (id D) (id (f ≅ g)) α (comp-unitˡ α)))
    (isoComp-evaluate (id (f ≅ g)) (const (comp-unitˡ f)) α
      (comp-unitˡ α) (const-evaluate (comp-unitˡ f) α))

preWhisker-id-at : {C D : CAT} {f g : MAP C D} (α : NatIso f g)
  → Iso₂ (comp-unitʳ g ∙ (α ▷ id C)) (α ∙ comp-unitʳ f)
preWhisker-id-at {C} {f = f} {g} α =
  specialize (preWhisker-id f g) α
    (isoComp-evaluate (const (comp-unitʳ g)) (id (f ≅ g) ▷ id C) α
      (const-evaluate (comp-unitʳ g) α)
      (preWhisker-evaluate (id (f ≅ g)) (id C) α (comp-unitˡ α)))
    (isoComp-evaluate (id (f ≅ g)) (const (comp-unitʳ f)) α
      (comp-unitˡ α) (const-evaluate (comp-unitʳ f) α))

postWhisker-comp-at : {C D E F : CAT} {f g : MAP C D}
  (α : NatIso f g) (u : MAP D E) (v : MAP E F)
  → Iso₂ (comp-assoc g u v ∙ ((v ∘ u) ◁ α))
          ((v ◁ (u ◁ α)) ∙ comp-assoc f u v)
postWhisker-comp-at {f = f} {g} α u v =
  specialize (postWhisker-comp f g u v) α
    (isoComp-evaluate (const (comp-assoc g u v)) ((v ∘ u) ◁ id (f ≅ g)) α
      (const-evaluate (comp-assoc g u v) α)
      (postWhisker-evaluate (v ∘ u) (id (f ≅ g)) α (comp-unitˡ α)))
    (isoComp-evaluate (v ◁ (u ◁ id (f ≅ g))) (const (comp-assoc f u v)) α
      (postWhisker-evaluate v (u ◁ id (f ≅ g)) α
        (postWhisker-evaluate u (id (f ≅ g)) α (comp-unitˡ α)))
      (const-evaluate (comp-assoc f u v) α))

preWhisker-comp-at : {A B C D : CAT} {f g : MAP C D}
  (α : NatIso f g) (k : MAP B C) (l : MAP A B)
  → Iso₂ (comp-assoc l k g ∙ ((α ▷ k) ▷ l))
          ((α ▷ (k ∘ l)) ∙ comp-assoc l k f)
preWhisker-comp-at {f = f} {g} α k l =
  specialize (preWhisker-comp f g k l) α
    (isoComp-evaluate (const (comp-assoc l k g)) ((id (f ≅ g) ▷ k) ▷ l) α
      (const-evaluate (comp-assoc l k g) α)
      (preWhisker-evaluate (id (f ≅ g) ▷ k) l α
        (preWhisker-evaluate (id (f ≅ g)) k α (comp-unitˡ α))))
    (isoComp-evaluate (id (f ≅ g) ▷ (k ∘ l)) (const (comp-assoc l k f)) α
      (preWhisker-evaluate (id (f ≅ g)) (k ∘ l) α (comp-unitˡ α))
      (const-evaluate (comp-assoc l k f) α))

whisker-mixed-at : {B C D E : CAT} {f g : MAP C D}
  (α : NatIso f g) (k : MAP B C) (u : MAP D E)
  → Iso₂ (comp-assoc k g u ∙ ((u ◁ α) ▷ k))
          ((u ◁ (α ▷ k)) ∙ comp-assoc k f u)
whisker-mixed-at {f = f} {g} α k u =
  specialize (whisker-mixed f g k u) α
    (isoComp-evaluate (const (comp-assoc k g u)) ((u ◁ id (f ≅ g)) ▷ k) α
      (const-evaluate (comp-assoc k g u) α)
      (preWhisker-evaluate (u ◁ id (f ≅ g)) k α
        (postWhisker-evaluate u (id (f ≅ g)) α (comp-unitˡ α))))
    (isoComp-evaluate (u ◁ (id (f ≅ g) ▷ k)) (const (comp-assoc k f u)) α
      (postWhisker-evaluate u (id (f ≅ g) ▷ k) α
        (preWhisker-evaluate (id (f ≅ g)) k α (comp-unitˡ α)))
      (const-evaluate (comp-assoc k f u) α))
```
