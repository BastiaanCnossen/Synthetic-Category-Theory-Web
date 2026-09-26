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
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence

module SCT.VolumeI.Chapter01.Section03.ProductCalculus.FamilyPairing
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
  (α : MAP A ((pr₁ ∘ f) ＝ (pr₁ ∘ g)))
  (β : MAP A ((pr₂ ∘ f) ＝ (pr₂ ∘ g))) where

  private
    comparison = product-isoMap f g
    witness = product-isoMap-isEquiv f g
    back = IsEquiv.inverse witness
    input = pair α β

  lift : MAP A (f ＝ g)
  lift = back ∘ input

  image : (comparison ∘ lift) =₁ input
  image = comp-unitˡ input ∙
    ((IsEquiv.retractionIso witness ▷ input) ⁻¹ ∙
      (comp-assoc input back comparison) ⁻¹)

  β₁ : (pr₁ ◁ lift) =₁ α
  β₁ = ((pair-β₁ α β ∙ (pr₁ ◁ image)) ∙ comp-assoc lift comparison pr₁)
    ∙ (pair-β₁ (postWhisker pr₁) (postWhisker pr₂) ▷ lift) ⁻¹

  β₂ : (pr₂ ◁ lift) =₁ β
  β₂ = ((pair-β₂ α β ∙ (pr₂ ◁ image)) ∙ comp-assoc lift comparison pr₂)
    ∙ (pair-β₂ (postWhisker pr₁) (postWhisker pr₂) ▷ lift) ⁻¹

family-extensionality : {A X C D : CAT} {f g : MAP X (C × D)}
  {α β : MAP A (f ＝ g)}
  → (pr₁ ◁ α) =₁ (pr₁ ◁ β) → (pr₂ ◁ α) =₁ (pr₂ ◁ β) → α =₁ β
family-extensionality {f = f} {g} {α} {β} p q =
  equiv-reflect (product-isoMap-isEquiv f g)
    ((pair-pre (postWhisker pr₁) (postWhisker pr₂) β) ⁻¹ ∙
      (pair-cong p q ∙ pair-pre (postWhisker pr₁) (postWhisker pr₂) α))

pairing : {A X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  → MAP A (f ＝ f′) → MAP A (g ＝ g′) → MAP A (pair f g ＝ pair f′ g′)
pairing {f = f} {f′} {g} {g′} α β = Lift.lift
  (const ((pair-β₁ f′ g′) ⁻¹) ∙ (α ∙ const (pair-β₁ f g)))
  (const ((pair-β₂ f′ g′) ⁻¹) ∙ (β ∙ const (pair-β₂ f g)))

pairing-β₁ : {A X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : MAP A (f ＝ f′)) (β : MAP A (g ＝ g′))
  → (pr₁ ◁ pairing α β) =₁
      (const ((pair-β₁ f′ g′) ⁻¹) ∙ (α ∙ const (pair-β₁ f g)))
pairing-β₁ {f = f} {f′} {g} {g′} α β = Lift.β₁
  (const ((pair-β₁ f′ g′) ⁻¹) ∙ (α ∙ const (pair-β₁ f g)))
  (const ((pair-β₂ f′ g′) ⁻¹) ∙ (β ∙ const (pair-β₂ f g)))

pairing-β₂ : {A X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : MAP A (f ＝ f′)) (β : MAP A (g ＝ g′))
  → (pr₂ ◁ pairing α β) =₁
      (const ((pair-β₂ f′ g′) ⁻¹) ∙ (β ∙ const (pair-β₂ f g)))
pairing-β₂ {f = f} {f′} {g} {g′} α β = Lift.β₂
  (const ((pair-β₁ f′ g′) ⁻¹) ∙ (α ∙ const (pair-β₁ f g)))
  (const ((pair-β₂ f′ g′) ⁻¹) ∙ (β ∙ const (pair-β₂ f g)))

post-composition : {A X C D : CAT} {f g h : MAP X C}
  (u : MAP C D) (β : MAP A (g ＝ h)) (α : MAP A (f ＝ g))
  → (u ◁ (β ∙ α)) =₁ ((u ◁ β) ∙ (u ◁ α))
post-composition {f = f} {g} {h} u β α =
  let input = pair β α
  in specialize (postWhisker-isoComp f g h u) input
    (postWhisker-evaluate u (pr₁ ∙ pr₂) input
      (isoComp-evaluate pr₁ pr₂ input (pair-β₁ β α) (pair-β₂ β α)))
    (isoComp-evaluate (u ◁ pr₁) (u ◁ pr₂) input
      (postWhisker-evaluate u pr₁ input (pair-β₁ β α))
      (postWhisker-evaluate u pr₂ input (pair-β₂ β α)))

reassociate-four : {A X C : CAT} {f g h i j : MAP X C}
  (δ : MAP A (i ＝ j)) (γ : MAP A (h ＝ i)) (β : MAP A (g ＝ h)) (α : MAP A (f ＝ g))
  → ((δ ∙ γ) ∙ (β ∙ α)) =₁ (δ ∙ ((γ ∙ β) ∙ α))
reassociate-four δ γ β α = isoComp-cong (idIso δ) ((assoc γ β α) ⁻¹) ∙ assoc δ γ (β ∙ α)

conjugate-composition : {A X C : CAT} {p₀ p₁ p₂ f₀ f₁ f₂ : MAP X C}
  (c₀ : p₀ =₁ f₀) (c₁ : p₁ =₁ f₁) (c₂ : p₂ =₁ f₂)
  (α₂ : MAP A (f₁ ＝ f₂)) (α₁ : MAP A (f₀ ＝ f₁))
  → (const (c₂ ⁻¹) ∙ ((α₂ ∙ α₁) ∙ const c₀)) =₁
      ((const (c₂ ⁻¹) ∙ (α₂ ∙ const c₁)) ∙ (const (c₁ ⁻¹) ∙ (α₁ ∙ const c₀)))
conjugate-composition c₀ c₁ c₂ α₂ α₁ =
  let cancel = unitʳ α₂ ∙
        (isoComp-cong (idIso α₂)
          (const-cong (isoComp-inverseʳ-at c₁) ∙ const-comp c₁ (c₁ ⁻¹)) ∙
          assoc α₂ (const c₁) (const (c₁ ⁻¹)))
  in
    (isoComp-cong (idIso (const (c₂ ⁻¹))) ((assoc α₂ α₁ (const c₀)) ⁻¹) ∙
      (isoComp-cong (idIso (const (c₂ ⁻¹)))
        (isoComp-cong cancel (idIso (α₁ ∙ const c₀))) ∙
        reassociate-four (const (c₂ ⁻¹)) (α₂ ∙ const c₁)
          (const (c₁ ⁻¹)) (α₁ ∙ const c₀))) ⁻¹

pairing-composition : {A X C D : CAT}
  {f₀ f₁ f₂ : MAP X C} {g₀ g₁ g₂ : MAP X D}
  (α₂ : MAP A (f₁ ＝ f₂)) (α₁ : MAP A (f₀ ＝ f₁))
  (β₂ : MAP A (g₁ ＝ g₂)) (β₁ : MAP A (g₀ ＝ g₁))
  → (pairing (α₂ ∙ α₁) (β₂ ∙ β₁)) =₁ (pairing α₂ β₂ ∙ pairing α₁ β₁)
pairing-composition {f₀ = f₀} {f₁} {f₂} {g₀} {g₁} {g₂} α₂ α₁ β₂ β₁ =
  family-extensionality
    ((post-composition pr₁ (pairing α₂ β₂) (pairing α₁ β₁)) ⁻¹ ∙
      ((isoComp-cong (pairing-β₁ α₂ β₂) (pairing-β₁ α₁ β₁)) ⁻¹ ∙
        (conjugate-composition (pair-β₁ f₀ g₀) (pair-β₁ f₁ g₁) (pair-β₁ f₂ g₂) α₂ α₁ ∙
          pairing-β₁ (α₂ ∙ α₁) (β₂ ∙ β₁))))
    ((post-composition pr₂ (pairing α₂ β₂) (pairing α₁ β₁)) ⁻¹ ∙
      ((isoComp-cong (pairing-β₂ α₂ β₂) (pairing-β₂ α₁ β₁)) ⁻¹ ∙
        (conjugate-composition (pair-β₂ f₀ g₀) (pair-β₂ f₁ g₁) (pair-β₂ f₂ g₂) β₂ β₁ ∙
          pairing-β₂ (α₂ ∙ α₁) (β₂ ∙ β₁))))

pairing-absolute : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : f =₁ f′) (β : g =₁ g′) → (pairing α β) =₂ (pair-cong α β)
pairing-absolute {f = f} {f′} {g} {g′} α β =
  let first = isoComp-cong (const-One ((pair-β₁ f′ g′) ⁻¹))
        (isoComp-cong (idIso α) (const-One (pair-β₁ f g)))
      second = isoComp-cong (const-One ((pair-β₂ f′ g′) ⁻¹))
        (isoComp-cong (idIso β) (const-One (pair-β₂ f g)))
      back = IsEquiv.inverse (product-isoMap-isEquiv (pair f g) (pair f′ g′))
  in back ◁ pair-cong first second

pairing-cong : {A X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  {α α′ : MAP A (f ＝ f′)} {β β′ : MAP A (g ＝ g′)}
  → α =₁ α′ → β =₁ β′ → (pairing α β) =₁ (pairing α′ β′)
pairing-cong {f = f} {f′} {g} {g′} p q =
  let first = isoComp-cong (idIso (const ((pair-β₁ f′ g′) ⁻¹)))
        (isoComp-cong p (idIso (const (pair-β₁ f g))))
      second = isoComp-cong (idIso (const ((pair-β₂ f′ g′) ⁻¹)))
        (isoComp-cong q (idIso (const (pair-β₂ f g))))
      back = IsEquiv.inverse (product-isoMap-isEquiv (pair f g) (pair f′ g′))
  in back ◁ pair-cong first second

pairing-triangle₁ : {A X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : MAP A (f ＝ f′)) (β : MAP A (g ＝ g′))
  → (const (pair-β₁ f′ g′) ∙ (pr₁ ◁ pairing α β)) =₁ (α ∙ const (pair-β₁ f g))
pairing-triangle₁ {f = f} {f′} {g} {g′} α β =
  left-cancelʳ (pair-β₁ f′ g′) (α ∙ const (pair-β₁ f g)) ∙
    isoComp-cong (idIso (const (pair-β₁ f′ g′))) (pairing-β₁ α β)

pairing-triangle₂ : {A X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : MAP A (f ＝ f′)) (β : MAP A (g ＝ g′))
  → (const (pair-β₂ f′ g′) ∙ (pr₂ ◁ pairing α β)) =₁ (β ∙ const (pair-β₂ f g))
pairing-triangle₂ {f = f} {f′} {g} {g′} α β =
  left-cancelʳ (pair-β₂ f′ g′) (β ∙ const (pair-β₂ f g)) ∙
    isoComp-cong (idIso (const (pair-β₂ f′ g′))) (pairing-β₂ α β)

pairing-pre : {A B X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : MAP A (f ＝ f′)) (β : MAP A (g ＝ g′)) (r : MAP B A)
  → (pairing α β ∘ r) =₁ (pairing (α ∘ r) (β ∘ r))
pairing-pre {f = f} {f′} {g} {g′} α β r =
  let first = const ((pair-β₁ f′ g′) ⁻¹) ∙ (α ∙ const (pair-β₁ f g))
      second = const ((pair-β₂ f′ g′) ⁻¹) ∙ (β ∙ const (pair-β₂ f g))
      first-normal = isoComp-evaluate (const ((pair-β₁ f′ g′) ⁻¹))
        (α ∙ const (pair-β₁ f g)) r (const-pre ((pair-β₁ f′ g′) ⁻¹) r)
        (isoComp-evaluate α (const (pair-β₁ f g)) r (idIso (α ∘ r)) (const-pre (pair-β₁ f g) r))
      second-normal = isoComp-evaluate (const ((pair-β₂ f′ g′) ⁻¹))
        (β ∙ const (pair-β₂ f g)) r (const-pre ((pair-β₂ f′ g′) ⁻¹) r)
        (isoComp-evaluate β (const (pair-β₂ f g)) r (idIso (β ∘ r)) (const-pre (pair-β₂ f g) r))
      back = IsEquiv.inverse (product-isoMap-isEquiv (pair f g) (pair f′ g′))
  in (back ◁ (pair-cong first-normal second-normal ∙ pair-pre first second r)) ∙
    comp-assoc r (pair first second) back

pairing-constant : {A X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : f =₁ f′) (β : g =₁ g′)
  → (pairing (const {P = A} α) (const β)) =₁ (const (pair-cong α β))
pairing-constant {A} α β = (pairing-absolute α β ▷ terminate A) ∙
  (pairing-pre α β (terminate A)) ⁻¹

pairing-identity : {A X C D : CAT} (f : MAP X C) (g : MAP X D)
  → (pairing (const {P = A} (idIso f)) (const (idIso g))) =₁ (const (idIso (pair f g)))
pairing-identity f g = const-cong (pair-cong-id f g) ∙ pairing-constant (idIso f) (idIso g)

post-constant : {A X C D : CAT} {f g : MAP X C} (u : MAP C D) (α : f =₁ g)
  → (u ◁ const {P = A} α) =₁ (const (u ◁ α))
post-constant {A} u α = (comp-assoc (terminate A) α (postWhisker u)) ⁻¹

pre-constant : {A R X C : CAT} {f g : MAP X C} (α : f =₁ g) (r : MAP R X)
  → (const {P = A} α ▷ r) =₁ (const (α ▷ r))
pre-constant {A} α r = (comp-assoc (terminate A) α (preWhisker r)) ⁻¹

pairing-at : {A X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : MAP A (f ＝ f′)) (β : MAP A (g ＝ g′))
  → (pairing pr₁ pr₂ ∘ pair α β) =₁ (pairing α β)
pairing-at α β = pairing-cong (pair-β₁ α β) (pair-β₂ α β) ∙ pairing-pre pr₁ pr₂ (pair α β)
```
