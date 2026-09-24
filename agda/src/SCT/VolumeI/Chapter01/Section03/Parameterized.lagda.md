# Vertical calculus with an arbitrary parameter category

These comparisons are obtained by substituting into the universal laws of
Section 1.1. These particular calculations do not invoke interchange.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization

module SCT.VolumeI.Chapter01.Section03.Parameterized
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

unitˡ : {X C D : CAT} {f g : MAP C D} (α : MAP X (f ＝ g))
  → (const (idIso g) ∙ α) =₁ α
unitˡ {f = f} {g} α = specialize (isoComp-unitˡ f g) α
  (isoComp-evaluate (const (idIso g)) (id (f ＝ g)) α
    (const-pre (idIso g) α) (comp-unitˡ α)) (comp-unitˡ α)

unitʳ : {X C D : CAT} {f g : MAP C D} (α : MAP X (f ＝ g))
  → (α ∙ const (idIso f)) =₁ α
unitʳ {f = f} {g} α = specialize (isoComp-unitʳ f g) α
  (isoComp-evaluate (id (f ＝ g)) (const (idIso f)) α
    (comp-unitˡ α) (const-pre (idIso f) α)) (comp-unitˡ α)

assoc : {X C D : CAT} {f g h k : MAP C D}
  (γ : MAP X (h ＝ k)) (β : MAP X (g ＝ h)) (α : MAP X (f ＝ g))
  → ((γ ∙ β) ∙ α) =₁ (γ ∙ (β ∙ α))
assoc {f = f} {g} {h} {k} γ β α =
  let point = pair (pair γ β) α
      first = pair-β₁ γ β ∙ ((pr₁ ◁ pair-β₁ (pair γ β) α) ∙ comp-assoc point pr₁ pr₁)
      second = pair-β₂ γ β ∙ ((pr₂ ◁ pair-β₁ (pair γ β) α) ∙ comp-assoc point pr₁ pr₂)
      third = pair-β₂ (pair γ β) α
  in specialize (Units.isoComp-assoc-left VC f g h k) point
    (isoComp-evaluate ((pr₁ ∘ pr₁) ∙ (pr₂ ∘ pr₁)) pr₂ point
      (isoComp-evaluate (pr₁ ∘ pr₁) (pr₂ ∘ pr₁) point first second) third)
    (isoComp-evaluate (pr₁ ∘ pr₁) ((pr₂ ∘ pr₁) ∙ pr₂) point first
      (isoComp-evaluate (pr₂ ∘ pr₁) pr₂ point second third))

const-comp : {X C D : CAT} {f g h : MAP C D}
  (β : g =₁ h) (α : f =₁ g)
  → (const {P = X} β ∙ const α) =₁ (const (β ∙ α))
const-comp {X} β α = (isoComp-pre β α (terminate X)) ⁻¹

const-cong : {X C : CAT} {x y : Obj-abs C}
  → x =₁ y → (const {P = X} x) =₁ (const y)
const-cong {X} p = p ▷ terminate X

left-cancel : {X C D : CAT} {f g h : MAP C D}
  (β : g =₁ h) (α : MAP X (f ＝ g))
  → (const (β ⁻¹) ∙ (const β ∙ α)) =₁ α
left-cancel β α = unitˡ α ∙
  (isoComp-cong (const-cong (isoComp-inverseˡ-at β) ∙ const-comp (β ⁻¹) β) (idIso α)
   ∙ (assoc (const (β ⁻¹)) (const β) α) ⁻¹)

left-cancelʳ : {X C D : CAT} {f g h : MAP C D}
  (β : g =₁ h) (α : MAP X (f ＝ h))
  → (const β ∙ (const (β ⁻¹) ∙ α)) =₁ α
left-cancelʳ β α = unitˡ α ∙
  (isoComp-cong (const-cong (isoComp-inverseʳ-at β) ∙ const-comp β (β ⁻¹)) (idIso α)
   ∙ (assoc (const β) (const (β ⁻¹)) α) ⁻¹)

right-cancel : {X C D : CAT} {f g h : MAP C D}
  (β : f =₁ g) (α : MAP X (g ＝ h))
  → ((α ∙ const β) ∙ const (β ⁻¹)) =₁ α
right-cancel β α = unitʳ α ∙
  (isoComp-cong (idIso α) (const-cong (isoComp-inverseʳ-at β) ∙ const-comp β (β ⁻¹))
   ∙ assoc α (const β) (const (β ⁻¹)))

right-cancelʳ : {X C D : CAT} {f g h : MAP C D}
  (β : f =₁ g) (α : MAP X (f ＝ h))
  → ((α ∙ const (β ⁻¹)) ∙ const β) =₁ α
right-cancelʳ β α = unitʳ α ∙
  (isoComp-cong (idIso α) (const-cong (isoComp-inverseˡ-at β) ∙ const-comp (β ⁻¹) β)
   ∙ assoc α (const (β ⁻¹)) (const β))
```

The corresponding whiskering comparisons can also be substituted at any
parameter category. Constants in their boundaries remain explicit.

```agda
module WhiskeringLaws (W : Coherence.WhiskeringCoherence V T P S) where
  open Coherence.WhiskeringCoherence W

  postWhisker-id-general : {X C D : CAT} {f g : MAP C D}
    (α : MAP X (f ＝ g))
    → (const (comp-unitˡ g) ∙ (id D ◁ α)) =₁ (α ∙ const (comp-unitˡ f))
  postWhisker-id-general {C = C} {D} {f} {g} α = specialize (postWhisker-id f g) α
    (isoComp-evaluate (const (comp-unitˡ g)) (id D ◁ id _) α
      (const-pre (comp-unitˡ g) α)
      (postWhisker-evaluate (id D) (id _) α (comp-unitˡ α)))
    (isoComp-evaluate (id _) (const (comp-unitˡ f)) α
      (comp-unitˡ α) (const-pre (comp-unitˡ f) α))

  preWhisker-id-general : {X C D : CAT} {f g : MAP C D}
    (α : MAP X (f ＝ g))
    → (const (comp-unitʳ g) ∙ (α ▷ id C)) =₁ (α ∙ const (comp-unitʳ f))
  preWhisker-id-general {C = C} {f = f} {g} α = specialize (preWhisker-id f g) α
    (isoComp-evaluate (const (comp-unitʳ g)) (id _ ▷ id C) α
      (const-pre (comp-unitʳ g) α)
      (preWhisker-evaluate (id _) (id C) α (comp-unitˡ α)))
    (isoComp-evaluate (id _) (const (comp-unitʳ f)) α
      (comp-unitˡ α) (const-pre (comp-unitʳ f) α))

  postWhisker-comp-general : {X C D E F : CAT} {f g : MAP C D}
    (α : MAP X (f ＝ g)) (u : MAP D E) (v : MAP E F)
    → (const (comp-assoc g u v) ∙ ((v ∘ u) ◁ α)) =₁
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
    (α : MAP X (f ＝ g)) (k : MAP B C) (l : MAP A B)
    → (const (comp-assoc l k g) ∙ ((α ▷ k) ▷ l)) =₁
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
    (α : MAP X (f ＝ g)) (k : MAP B C) (u : MAP D E)
    → (const (comp-assoc k g u) ∙ ((u ◁ α) ▷ k)) =₁
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

  postWhisker-id-at : {C D : CAT} {f g : MAP C D} (α : f =₁ g)
    → (comp-unitˡ g ∙ (id D ◁ α)) =₂ (α ∙ comp-unitˡ f)
  postWhisker-id-at {f = f} {g} α =
    isoComp-cong (idIso _) (const-One (comp-unitˡ f)) ∙
    (postWhisker-id-general α ∙
     (isoComp-cong (const-One (comp-unitˡ g)) (idIso _)) ⁻¹)

  preWhisker-id-at : {C D : CAT} {f g : MAP C D} (α : f =₁ g)
    → (comp-unitʳ g ∙ (α ▷ id C)) =₂ (α ∙ comp-unitʳ f)
  preWhisker-id-at {f = f} {g} α =
    isoComp-cong (idIso _) (const-One (comp-unitʳ f)) ∙
    (preWhisker-id-general α ∙
     (isoComp-cong (const-One (comp-unitʳ g)) (idIso _)) ⁻¹)

  postWhisker-comp-at : {C D E F : CAT} {f g : MAP C D}
    (α : f =₁ g) (u : MAP D E) (v : MAP E F)
    → (comp-assoc g u v ∙ ((v ∘ u) ◁ α)) =₂
            ((v ◁ (u ◁ α)) ∙ comp-assoc f u v)
  postWhisker-comp-at {f = f} {g} α u v =
    isoComp-cong (idIso _) (const-One (comp-assoc f u v)) ∙
    (postWhisker-comp-general α u v ∙
     (isoComp-cong (const-One (comp-assoc g u v)) (idIso _)) ⁻¹)

  preWhisker-comp-at : {A B C D : CAT} {f g : MAP C D}
    (α : f =₁ g) (k : MAP B C) (l : MAP A B)
    → (comp-assoc l k g ∙ ((α ▷ k) ▷ l)) =₂
            ((α ▷ (k ∘ l)) ∙ comp-assoc l k f)
  preWhisker-comp-at {f = f} {g} α k l =
    isoComp-cong (idIso _) (const-One (comp-assoc l k f)) ∙
    (preWhisker-comp-general α k l ∙
     (isoComp-cong (const-One (comp-assoc l k g)) (idIso _)) ⁻¹)

  whisker-mixed-at : {B C D E : CAT} {f g : MAP C D}
    (α : f =₁ g) (k : MAP B C) (u : MAP D E)
    → (comp-assoc k g u ∙ ((u ◁ α) ▷ k)) =₂
            ((u ◁ (α ▷ k)) ∙ comp-assoc k f u)
  whisker-mixed-at {f = f} {g} α k u =
    isoComp-cong (idIso _) (const-One (comp-assoc k f u)) ∙
    (whisker-mixed-general α k u ∙
     (isoComp-cong (const-One (comp-assoc k g u)) (idIso _)) ⁻¹)
```
