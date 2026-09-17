# Pairing with a common parameter category

The inputs in this module are actual functors from an arbitrary common
category `A`. In particular, the composition law can be applied to the four
projections of the product of the input isomorphism animae. This records more
than separate choices of identifications at absolute inputs.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section01.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section02.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence

module SCT.VolumeI.Chapter01.Section02.FamilyPairing
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S) where

open Vocabulary V
open Operations V
open Terminal.TerminalStructure T
open Terminal.Constructions V T
open Products.ProductData P
open Products.Comparison V P
open Products.ProductLaws PL
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.WhiskeringCoherence W
open Specialization V T P PL S
open Specialization.Units V T P PL S VC
open Parameterized V T P PL S VC using (assoc; unitʳ; const-comp; const-cong; left-cancelʳ)
open PairingCoherence V T P PL S VC W using (equiv-reflect; pair-cong-id)

module Lift {A X C D : CAT} {f g : MAP X (C × D)}
  (α : MAP A ((pr₁ ∘ f) ≅ (pr₁ ∘ g)))
  (β : MAP A ((pr₂ ∘ f) ≅ (pr₂ ∘ g))) where

  private
    comparison = product-isoMap f g
    witness = product-isoMap-isEquiv f g
    back = IsEquiv.inverse witness
    input = pair α β

  lift : MAP A (f ≅ g)
  lift = back ∘ input

  image : NatIso (comparison ∘ lift) input
  image = comp-unitˡ input ∙
    (invIso (IsEquiv.retractionIso witness ▷ input) ∙
      invIso (comp-assoc input back comparison))

  β₁ : NatIso (pr₁ ◁ lift) α
  β₁ = ((pair-β₁ α β ∙ (pr₁ ◁ image)) ∙ comp-assoc lift comparison pr₁)
    ∙ invIso (pair-β₁ (postWhisker pr₁) (postWhisker pr₂) ▷ lift)

  β₂ : NatIso (pr₂ ◁ lift) β
  β₂ = ((pair-β₂ α β ∙ (pr₂ ◁ image)) ∙ comp-assoc lift comparison pr₂)
    ∙ invIso (pair-β₂ (postWhisker pr₁) (postWhisker pr₂) ▷ lift)

family-extensionality : {A X C D : CAT} {f g : MAP X (C × D)}
  {α β : MAP A (f ≅ g)}
  → NatIso (pr₁ ◁ α) (pr₁ ◁ β) → NatIso (pr₂ ◁ α) (pr₂ ◁ β) → NatIso α β
family-extensionality {f = f} {g} {α} {β} p q =
  equiv-reflect (product-isoMap-isEquiv f g)
    (invIso (pair-pre (postWhisker pr₁) (postWhisker pr₂) β) ∙
      (pair-cong p q ∙ pair-pre (postWhisker pr₁) (postWhisker pr₂) α))

pairing : {A X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  → MAP A (f ≅ f′) → MAP A (g ≅ g′) → MAP A (pair f g ≅ pair f′ g′)
pairing {f = f} {f′} {g} {g′} α β = Lift.lift
  (const (invIso (pair-β₁ f′ g′)) ∙ (α ∙ const (pair-β₁ f g)))
  (const (invIso (pair-β₂ f′ g′)) ∙ (β ∙ const (pair-β₂ f g)))

pairing-β₁ : {A X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : MAP A (f ≅ f′)) (β : MAP A (g ≅ g′))
  → NatIso (pr₁ ◁ pairing α β)
      (const (invIso (pair-β₁ f′ g′)) ∙ (α ∙ const (pair-β₁ f g)))
pairing-β₁ {f = f} {f′} {g} {g′} α β = Lift.β₁
  (const (invIso (pair-β₁ f′ g′)) ∙ (α ∙ const (pair-β₁ f g)))
  (const (invIso (pair-β₂ f′ g′)) ∙ (β ∙ const (pair-β₂ f g)))

pairing-β₂ : {A X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : MAP A (f ≅ f′)) (β : MAP A (g ≅ g′))
  → NatIso (pr₂ ◁ pairing α β)
      (const (invIso (pair-β₂ f′ g′)) ∙ (β ∙ const (pair-β₂ f g)))
pairing-β₂ {f = f} {f′} {g} {g′} α β = Lift.β₂
  (const (invIso (pair-β₁ f′ g′)) ∙ (α ∙ const (pair-β₁ f g)))
  (const (invIso (pair-β₂ f′ g′)) ∙ (β ∙ const (pair-β₂ f g)))

post-composition : {A X C D : CAT} {f g h : MAP X C}
  (u : MAP C D) (β : MAP A (g ≅ h)) (α : MAP A (f ≅ g))
  → NatIso (u ◁ (β ∙ α)) ((u ◁ β) ∙ (u ◁ α))
post-composition {f = f} {g} {h} u β α =
  let input = pair β α
  in specialize (postWhisker-isoComp f g h u) input
    (postWhisker-evaluate u (pr₁ ∙ pr₂) input
      (isoComp-evaluate pr₁ pr₂ input (pair-β₁ β α) (pair-β₂ β α)))
    (isoComp-evaluate (u ◁ pr₁) (u ◁ pr₂) input
      (postWhisker-evaluate u pr₁ input (pair-β₁ β α))
      (postWhisker-evaluate u pr₂ input (pair-β₂ β α)))

reassociate-four : {A X C : CAT} {f g h i j : MAP X C}
  (δ : MAP A (i ≅ j)) (γ : MAP A (h ≅ i)) (β : MAP A (g ≅ h)) (α : MAP A (f ≅ g))
  → NatIso ((δ ∙ γ) ∙ (β ∙ α)) (δ ∙ ((γ ∙ β) ∙ α))
reassociate-four δ γ β α = isoComp-cong (idIso δ) (invIso (assoc γ β α)) ∙ assoc δ γ (β ∙ α)

conjugate-composition : {A X C : CAT} {p₀ p₁ p₂ f₀ f₁ f₂ : MAP X C}
  (c₀ : NatIso p₀ f₀) (c₁ : NatIso p₁ f₁) (c₂ : NatIso p₂ f₂)
  (α₂ : MAP A (f₁ ≅ f₂)) (α₁ : MAP A (f₀ ≅ f₁))
  → NatIso (const (invIso c₂) ∙ ((α₂ ∙ α₁) ∙ const c₀))
      ((const (invIso c₂) ∙ (α₂ ∙ const c₁)) ∙ (const (invIso c₁) ∙ (α₁ ∙ const c₀)))
conjugate-composition c₀ c₁ c₂ α₂ α₁ =
  let cancel = unitʳ α₂ ∙
        (isoComp-cong (idIso α₂)
          (const-cong (isoComp-inverseʳ-at c₁) ∙ const-comp c₁ (invIso c₁)) ∙
          assoc α₂ (const c₁) (const (invIso c₁)))
  in invIso
    (isoComp-cong (idIso (const (invIso c₂))) (invIso (assoc α₂ α₁ (const c₀))) ∙
      (isoComp-cong (idIso (const (invIso c₂)))
        (isoComp-cong cancel (idIso (α₁ ∙ const c₀))) ∙
        reassociate-four (const (invIso c₂)) (α₂ ∙ const c₁)
          (const (invIso c₁)) (α₁ ∙ const c₀)))

pairing-composition : {A X C D : CAT}
  {f₀ f₁ f₂ : MAP X C} {g₀ g₁ g₂ : MAP X D}
  (α₂ : MAP A (f₁ ≅ f₂)) (α₁ : MAP A (f₀ ≅ f₁))
  (β₂ : MAP A (g₁ ≅ g₂)) (β₁ : MAP A (g₀ ≅ g₁))
  → NatIso (pairing (α₂ ∙ α₁) (β₂ ∙ β₁)) (pairing α₂ β₂ ∙ pairing α₁ β₁)
pairing-composition {f₀ = f₀} {f₁} {f₂} {g₀} {g₁} {g₂} α₂ α₁ β₂ β₁ =
  family-extensionality
    (invIso (post-composition pr₁ (pairing α₂ β₂) (pairing α₁ β₁)) ∙
      (invIso (isoComp-cong (pairing-β₁ α₂ β₂) (pairing-β₁ α₁ β₁)) ∙
        (conjugate-composition (pair-β₁ f₀ g₀) (pair-β₁ f₁ g₁) (pair-β₁ f₂ g₂) α₂ α₁ ∙
          pairing-β₁ (α₂ ∙ α₁) (β₂ ∙ β₁))))
    (invIso (post-composition pr₂ (pairing α₂ β₂) (pairing α₁ β₁)) ∙
      (invIso (isoComp-cong (pairing-β₂ α₂ β₂) (pairing-β₂ α₁ β₁)) ∙
        (conjugate-composition (pair-β₂ f₀ g₀) (pair-β₂ f₁ g₁) (pair-β₂ f₂ g₂) β₂ β₁ ∙
          pairing-β₂ (α₂ ∙ α₁) (β₂ ∙ β₁))))

pairing-absolute : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : NatIso f f′) (β : NatIso g g′) → Iso₂ (pairing α β) (pair-cong α β)
pairing-absolute {f = f} {f′} {g} {g′} α β =
  let first = isoComp-cong (const-One (invIso (pair-β₁ f′ g′)))
        (isoComp-cong (idIso α) (const-One (pair-β₁ f g)))
      second = isoComp-cong (const-One (invIso (pair-β₂ f′ g′)))
        (isoComp-cong (idIso β) (const-One (pair-β₂ f g)))
      back = IsEquiv.inverse (product-isoMap-isEquiv (pair f g) (pair f′ g′))
  in back ◁ pair-cong first second

pairing-cong : {A X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  {α α′ : MAP A (f ≅ f′)} {β β′ : MAP A (g ≅ g′)}
  → NatIso α α′ → NatIso β β′ → NatIso (pairing α β) (pairing α′ β′)
pairing-cong {f = f} {f′} {g} {g′} p q =
  let first = isoComp-cong (idIso (const (invIso (pair-β₁ f′ g′))))
        (isoComp-cong p (idIso (const (pair-β₁ f g))))
      second = isoComp-cong (idIso (const (invIso (pair-β₂ f′ g′))))
        (isoComp-cong q (idIso (const (pair-β₂ f g))))
      back = IsEquiv.inverse (product-isoMap-isEquiv (pair f g) (pair f′ g′))
  in back ◁ pair-cong first second

pairing-triangle₁ : {A X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : MAP A (f ≅ f′)) (β : MAP A (g ≅ g′))
  → NatIso (const (pair-β₁ f′ g′) ∙ (pr₁ ◁ pairing α β)) (α ∙ const (pair-β₁ f g))
pairing-triangle₁ {f = f} {f′} {g} {g′} α β =
  left-cancelʳ (pair-β₁ f′ g′) (α ∙ const (pair-β₁ f g)) ∙
    isoComp-cong (idIso (const (pair-β₁ f′ g′))) (pairing-β₁ α β)

pairing-triangle₂ : {A X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : MAP A (f ≅ f′)) (β : MAP A (g ≅ g′))
  → NatIso (const (pair-β₂ f′ g′) ∙ (pr₂ ◁ pairing α β)) (β ∙ const (pair-β₂ f g))
pairing-triangle₂ {f = f} {f′} {g} {g′} α β =
  left-cancelʳ (pair-β₂ f′ g′) (β ∙ const (pair-β₂ f g)) ∙
    isoComp-cong (idIso (const (pair-β₂ f′ g′))) (pairing-β₂ α β)

pairing-pre : {A B X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : MAP A (f ≅ f′)) (β : MAP A (g ≅ g′)) (r : MAP B A)
  → NatIso (pairing α β ∘ r) (pairing (α ∘ r) (β ∘ r))
pairing-pre {f = f} {f′} {g} {g′} α β r =
  let first = const (invIso (pair-β₁ f′ g′)) ∙ (α ∙ const (pair-β₁ f g))
      second = const (invIso (pair-β₂ f′ g′)) ∙ (β ∙ const (pair-β₂ f g))
      first-normal = isoComp-evaluate (const (invIso (pair-β₁ f′ g′)))
        (α ∙ const (pair-β₁ f g)) r (const-pre (invIso (pair-β₁ f′ g′)) r)
        (isoComp-evaluate α (const (pair-β₁ f g)) r (idIso (α ∘ r)) (const-pre (pair-β₁ f g) r))
      second-normal = isoComp-evaluate (const (invIso (pair-β₂ f′ g′)))
        (β ∙ const (pair-β₂ f g)) r (const-pre (invIso (pair-β₂ f′ g′)) r)
        (isoComp-evaluate β (const (pair-β₂ f g)) r (idIso (β ∘ r)) (const-pre (pair-β₂ f g) r))
      back = IsEquiv.inverse (product-isoMap-isEquiv (pair f g) (pair f′ g′))
  in (back ◁ (pair-cong first-normal second-normal ∙ pair-pre first second r)) ∙
    comp-assoc r (pair first second) back

pairing-constant : {A X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : NatIso f f′) (β : NatIso g g′)
  → NatIso (pairing (const {P = A} α) (const β)) (const (pair-cong α β))
pairing-constant {A} α β = (pairing-absolute α β ▷ terminate A) ∙
  invIso (pairing-pre α β (terminate A))

pairing-identity : {A X C D : CAT} (f : MAP X C) (g : MAP X D)
  → NatIso (pairing (const {P = A} (idIso f)) (const (idIso g))) (const (idIso (pair f g)))
pairing-identity f g = const-cong (pair-cong-id f g) ∙ pairing-constant (idIso f) (idIso g)

post-constant : {A X C D : CAT} {f g : MAP X C} (u : MAP C D) (α : NatIso f g)
  → NatIso (u ◁ const {P = A} α) (const (u ◁ α))
post-constant {A} u α = invIso (comp-assoc (terminate A) α (postWhisker u))

pre-constant : {A R X C : CAT} {f g : MAP X C} (α : NatIso f g) (r : MAP R X)
  → NatIso (const {P = A} α ▷ r) (const (α ▷ r))
pre-constant {A} α r = invIso (comp-assoc (terminate A) α (preWhisker r))

pairing-at : {A X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : MAP A (f ≅ f′)) (β : MAP A (g ≅ g′))
  → NatIso (pairing pr₁ pr₂ ∘ pair α β) (pairing α β)
pairing-at α β = pairing-cong (pair-β₁ α β) (pair-β₂ α β) ∙ pairing-pre pr₁ pr₂ (pair α β)
```
