# Vertical calculus with an arbitrary parameter category

These comparisons are obtained by substituting into the universal laws of
Section 1.1. These particular calculations do not invoke interchange.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section01.Specialization as Specialization

module SCT.VolumeI.Chapter01.Section02.Parameterized
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S) where

open Vocabulary V
open Operations V
open Terminal.TerminalStructure T
open Terminal.Constructions V T
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.VerticalCoherence VC
open Specialization V T P PL S
open Units VC

unitˡ : {X C D : CAT} {f g : MAP C D} (α : MAP X (f ≅ g))
  → NatIso (const (idIso g) ∙ α) α
unitˡ {f = f} {g} α = specialize (isoComp-unitˡ f g) α
  (isoComp-evaluate (const (idIso g)) (id (f ≅ g)) α
    (const-pre (idIso g) α) (comp-unitˡ α)) (comp-unitˡ α)

unitʳ : {X C D : CAT} {f g : MAP C D} (α : MAP X (f ≅ g))
  → NatIso (α ∙ const (idIso f)) α
unitʳ {f = f} {g} α = specialize (isoComp-unitʳ f g) α
  (isoComp-evaluate (id (f ≅ g)) (const (idIso f)) α
    (comp-unitˡ α) (const-pre (idIso f) α)) (comp-unitˡ α)

assoc : {X C D : CAT} {f g h k : MAP C D}
  (γ : MAP X (h ≅ k)) (β : MAP X (g ≅ h)) (α : MAP X (f ≅ g))
  → NatIso ((γ ∙ β) ∙ α) (γ ∙ (β ∙ α))
assoc {f = f} {g} {h} {k} γ β α =
  let point = pair (pair γ β) α
      first = pair-β₁ γ β ∙ ((pr₁ ◁ pair-β₁ (pair γ β) α) ∙ comp-assoc point pr₁ pr₁)
      second = pair-β₂ γ β ∙ ((pr₂ ◁ pair-β₁ (pair γ β) α) ∙ comp-assoc point pr₁ pr₂)
      third = pair-β₂ (pair γ β) α
  in specialize (isoComp-assoc f g h k) point
    (isoComp-evaluate ((pr₁ ∘ pr₁) ∙ (pr₂ ∘ pr₁)) pr₂ point
      (isoComp-evaluate (pr₁ ∘ pr₁) (pr₂ ∘ pr₁) point first second) third)
    (isoComp-evaluate (pr₁ ∘ pr₁) ((pr₂ ∘ pr₁) ∙ pr₂) point first
      (isoComp-evaluate (pr₂ ∘ pr₁) pr₂ point second third))

const-comp : {X C D : CAT} {f g h : MAP C D}
  (β : NatIso g h) (α : NatIso f g)
  → NatIso (const {P = X} β ∙ const α) (const (β ∙ α))
const-comp {X} β α = invIso (isoComp-pre β α (terminate X))

const-cong : {X C : CAT} {x y : ObjAbs C}
  → NatIso x y → NatIso (const {P = X} x) (const y)
const-cong {X} p = p ▷ terminate X

left-cancel : {X C D : CAT} {f g h : MAP C D}
  (β : NatIso g h) (α : MAP X (f ≅ g))
  → NatIso (const (invIso β) ∙ (const β ∙ α)) α
left-cancel β α = unitˡ α ∙
  (isoComp-cong (const-cong (isoComp-inverseˡ-at β) ∙ const-comp (invIso β) β) (idIso α)
   ∙ invIso (assoc (const (invIso β)) (const β) α))

left-cancelʳ : {X C D : CAT} {f g h : MAP C D}
  (β : NatIso g h) (α : MAP X (f ≅ h))
  → NatIso (const β ∙ (const (invIso β) ∙ α)) α
left-cancelʳ β α = unitˡ α ∙
  (isoComp-cong (const-cong (isoComp-inverseʳ-at β) ∙ const-comp β (invIso β)) (idIso α)
   ∙ invIso (assoc (const β) (const (invIso β)) α))

right-cancel : {X C D : CAT} {f g h : MAP C D}
  (β : NatIso f g) (α : MAP X (g ≅ h))
  → NatIso ((α ∙ const β) ∙ const (invIso β)) α
right-cancel β α = unitʳ α ∙
  (isoComp-cong (idIso α) (const-cong (isoComp-inverseʳ-at β) ∙ const-comp β (invIso β))
   ∙ assoc α (const β) (const (invIso β)))

right-cancelʳ : {X C D : CAT} {f g h : MAP C D}
  (β : NatIso f g) (α : MAP X (f ≅ h))
  → NatIso ((α ∙ const (invIso β)) ∙ const β) α
right-cancelʳ β α = unitʳ α ∙
  (isoComp-cong (idIso α) (const-cong (isoComp-inverseˡ-at β) ∙ const-comp (invIso β) β)
   ∙ assoc α (const (invIso β)) (const β))
```

The corresponding whiskering comparisons can also be substituted at any
parameter category. Constants in their boundaries remain explicit.

```agda
module WhiskeringLaws (W : Coherence.WhiskeringCoherence V T P S) where
  open Coherence.WhiskeringCoherence W

  postWhisker-id-general : {X C D : CAT} {f g : MAP C D}
    (α : MAP X (f ≅ g))
    → NatIso (const (comp-unitˡ g) ∙ (id D ◁ α)) (α ∙ const (comp-unitˡ f))
  postWhisker-id-general {C = C} {D} {f} {g} α = specialize (postWhisker-id f g) α
    (isoComp-evaluate (const (comp-unitˡ g)) (id D ◁ id _) α
      (const-pre (comp-unitˡ g) α)
      (postWhisker-evaluate (id D) (id _) α (comp-unitˡ α)))
    (isoComp-evaluate (id _) (const (comp-unitˡ f)) α
      (comp-unitˡ α) (const-pre (comp-unitˡ f) α))

  preWhisker-id-general : {X C D : CAT} {f g : MAP C D}
    (α : MAP X (f ≅ g))
    → NatIso (const (comp-unitʳ g) ∙ (α ▷ id C)) (α ∙ const (comp-unitʳ f))
  preWhisker-id-general {C = C} {f = f} {g} α = specialize (preWhisker-id f g) α
    (isoComp-evaluate (const (comp-unitʳ g)) (id _ ▷ id C) α
      (const-pre (comp-unitʳ g) α)
      (preWhisker-evaluate (id _) (id C) α (comp-unitˡ α)))
    (isoComp-evaluate (id _) (const (comp-unitʳ f)) α
      (comp-unitˡ α) (const-pre (comp-unitʳ f) α))

  postWhisker-comp-general : {X C D E F : CAT} {f g : MAP C D}
    (α : MAP X (f ≅ g)) (u : MAP D E) (v : MAP E F)
    → NatIso (const (comp-assoc g u v) ∙ ((v ∘ u) ◁ α))
              ((v ◁ (u ◁ α)) ∙ const (comp-assoc f u v))
  postWhisker-comp-general {f = f} {g} α u v = specialize (postWhisker-comp f g u v) α
    (isoComp-evaluate (const (comp-assoc g u v)) ((v ∘ u) ◁ id _) α
      (const-pre (comp-assoc g u v) α)
      (postWhisker-evaluate (v ∘ u) (id _) α (comp-unitˡ α)))
    (isoComp-evaluate (v ◁ (u ◁ id _)) (const (comp-assoc f u v)) α
      (postWhisker-evaluate v (u ◁ id _) α
        (postWhisker-evaluate u (id _) α (comp-unitˡ α)))
      (const-pre (comp-assoc f u v) α))

  preWhisker-comp-general : {X A B C D : CAT} {f g : MAP C D}
    (α : MAP X (f ≅ g)) (k : MAP B C) (l : MAP A B)
    → NatIso (const (comp-assoc l k g) ∙ ((α ▷ k) ▷ l))
              ((α ▷ (k ∘ l)) ∙ const (comp-assoc l k f))
  preWhisker-comp-general {f = f} {g} α k l = specialize (preWhisker-comp f g k l) α
    (isoComp-evaluate (const (comp-assoc l k g)) ((id _ ▷ k) ▷ l) α
      (const-pre (comp-assoc l k g) α)
      (preWhisker-evaluate (id _ ▷ k) l α
        (preWhisker-evaluate (id _) k α (comp-unitˡ α))))
    (isoComp-evaluate (id _ ▷ (k ∘ l)) (const (comp-assoc l k f)) α
      (preWhisker-evaluate (id _) (k ∘ l) α (comp-unitˡ α))
      (const-pre (comp-assoc l k f) α))

  whisker-mixed-general : {X B C D E : CAT} {f g : MAP C D}
    (α : MAP X (f ≅ g)) (k : MAP B C) (u : MAP D E)
    → NatIso (const (comp-assoc k g u) ∙ ((u ◁ α) ▷ k))
              ((u ◁ (α ▷ k)) ∙ const (comp-assoc k f u))
  whisker-mixed-general {f = f} {g} α k u = specialize (whisker-mixed f g k u) α
    (isoComp-evaluate (const (comp-assoc k g u)) ((u ◁ id _) ▷ k) α
      (const-pre (comp-assoc k g u) α)
      (preWhisker-evaluate (u ◁ id _) k α
        (postWhisker-evaluate u (id _) α (comp-unitˡ α))))
    (isoComp-evaluate (u ◁ (id _ ▷ k)) (const (comp-assoc k f u)) α
      (postWhisker-evaluate u (id _ ▷ k) α
        (preWhisker-evaluate (id _) k α (comp-unitˡ α)))
      (const-pre (comp-assoc k f u) α))

  postWhisker-id-at : {C D : CAT} {f g : MAP C D} (α : NatIso f g)
    → Iso₂ (comp-unitˡ g ∙ (id D ◁ α)) (α ∙ comp-unitˡ f)
  postWhisker-id-at {f = f} {g} α =
    isoComp-cong (idIso _) (const-One (comp-unitˡ f)) ∙
    (postWhisker-id-general α ∙
     invIso (isoComp-cong (const-One (comp-unitˡ g)) (idIso _)))

  preWhisker-id-at : {C D : CAT} {f g : MAP C D} (α : NatIso f g)
    → Iso₂ (comp-unitʳ g ∙ (α ▷ id C)) (α ∙ comp-unitʳ f)
  preWhisker-id-at {f = f} {g} α =
    isoComp-cong (idIso _) (const-One (comp-unitʳ f)) ∙
    (preWhisker-id-general α ∙
     invIso (isoComp-cong (const-One (comp-unitʳ g)) (idIso _)))

  postWhisker-comp-at : {C D E F : CAT} {f g : MAP C D}
    (α : NatIso f g) (u : MAP D E) (v : MAP E F)
    → Iso₂ (comp-assoc g u v ∙ ((v ∘ u) ◁ α))
            ((v ◁ (u ◁ α)) ∙ comp-assoc f u v)
  postWhisker-comp-at {f = f} {g} α u v =
    isoComp-cong (idIso _) (const-One (comp-assoc f u v)) ∙
    (postWhisker-comp-general α u v ∙
     invIso (isoComp-cong (const-One (comp-assoc g u v)) (idIso _)))

  preWhisker-comp-at : {A B C D : CAT} {f g : MAP C D}
    (α : NatIso f g) (k : MAP B C) (l : MAP A B)
    → Iso₂ (comp-assoc l k g ∙ ((α ▷ k) ▷ l))
            ((α ▷ (k ∘ l)) ∙ comp-assoc l k f)
  preWhisker-comp-at {f = f} {g} α k l =
    isoComp-cong (idIso _) (const-One (comp-assoc l k f)) ∙
    (preWhisker-comp-general α k l ∙
     invIso (isoComp-cong (const-One (comp-assoc l k g)) (idIso _)))

  whisker-mixed-at : {B C D E : CAT} {f g : MAP C D}
    (α : NatIso f g) (k : MAP B C) (u : MAP D E)
    → Iso₂ (comp-assoc k g u ∙ ((u ◁ α) ▷ k))
            ((u ◁ (α ▷ k)) ∙ comp-assoc k f u)
  whisker-mixed-at {f = f} {g} α k u =
    isoComp-cong (idIso _) (const-One (comp-assoc k f u)) ∙
    (whisker-mixed-general α k u ∙
     invIso (isoComp-cong (const-One (comp-assoc k g u)) (idIso _)))
```
