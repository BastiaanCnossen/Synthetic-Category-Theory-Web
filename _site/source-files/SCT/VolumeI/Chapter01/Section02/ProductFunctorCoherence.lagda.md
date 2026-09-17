# Isomorphisms between product functors

The operation on natural isomorphisms is obtained from prewhiskering and
pairing. Its identity, composition, and higher-comparison laws below are
derived, with the chosen pairing operation retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section01.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section02.Products as ProductConstructions
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality

module SCT.VolumeI.Chapter01.Section02.ProductFunctorCoherence
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
open Coherence.WhiskeringCoherence W
open Specialization V T P PL S
open Specialization.Whiskering V T P PL S W
open ProductConstructions V T P PL S
open PairingCoherence V T P PL S VC W
open Specialization.Units V T P PL S VC
open Structural V T P PL S W
open PairingNaturality V T P PL S VC W using (move-square; pair-pre-natural-inputs; pair-pre-natural-substitution)

productMap-cong : {C C′ D D′ : CAT} {f f′ : MAP C C′} {g g′ : MAP D D′}
  → NatIso f f′ → NatIso g g′ → NatIso (productMap f g) (productMap f′ g′)
productMap-cong α β = pair-cong (α ▷ pr₁) (β ▷ pr₂)

productMap-cong-id : {C C′ D D′ : CAT} (f : MAP C C′) (g : MAP D D′)
  → Iso₂ (productMap-cong (idIso f) (idIso g)) (idIso (productMap f g))
productMap-cong-id f g = pair-cong-id (f ∘ pr₁) (g ∘ pr₂) ∙
  pair-cong-Iso₂ (preWhisker-idIso f pr₁) (preWhisker-idIso g pr₂)

productMap-cong-comp : {C C′ D D′ : CAT}
  {f₀ f₁ f₂ : MAP C C′} {g₀ g₁ g₂ : MAP D D′}
  (α₂ : NatIso f₁ f₂) (α₁ : NatIso f₀ f₁)
  (β₂ : NatIso g₁ g₂) (β₁ : NatIso g₀ g₁)
  → Iso₂ (productMap-cong (α₂ ∙ α₁) (β₂ ∙ β₁))
      (productMap-cong α₂ β₂ ∙ productMap-cong α₁ β₁)
productMap-cong-comp α₂ α₁ β₂ β₁ =
  pair-cong-comp (α₂ ▷ pr₁) (α₁ ▷ pr₁) (β₂ ▷ pr₂) (β₁ ▷ pr₂) ∙
  pair-cong-Iso₂ (preWhisker-isoComp-at α₂ α₁ pr₁)
    (preWhisker-isoComp-at β₂ β₁ pr₂)

productMap-cong-Iso₂ : {C C′ D D′ : CAT}
  {f f′ : MAP C C′} {g g′ : MAP D D′}
  {α α′ : NatIso f f′} {β β′ : NatIso g g′}
  → Iso₂ α α′ → Iso₂ β β′
  → Iso₂ (productMap-cong α β) (productMap-cong α′ β′)
productMap-cong-Iso₂ p q = pair-cong-Iso₂ (preWhisker pr₁ ◁ p) (preWhisker pr₂ ◁ q)

productIsoMap : {C C′ D D′ : CAT}
  (f f′ : MAP C C′) (g g′ : MAP D D′)
  → MAP ((f ≅ f′) × (g ≅ g′)) (productMap f g ≅ productMap f′ g′)
productIsoMap f f′ g g′ = pairIsoMap (f ∘ pr₁) (f′ ∘ pr₁) (g ∘ pr₂) (g′ ∘ pr₂)
  ∘ pair (preWhisker pr₁ ∘ pr₁) (preWhisker pr₂ ∘ pr₂)

productIsoMap-at : {C C′ D D′ : CAT}
  {f f′ : MAP C C′} {g g′ : MAP D D′}
  (α : NatIso f f′) (β : NatIso g g′)
  → Iso₂ (productIsoMap f f′ g g′ ∘ pair α β) (productMap-cong α β)
productIsoMap-at {f = f} {f′} {g} {g′} α β =
  let input = pair (preWhisker pr₁ ∘ pr₁) (preWhisker pr₂ ∘ pr₂)
      output = pairIsoMap (f ∘ pr₁) (f′ ∘ pr₁) (g ∘ pr₂) (g′ ∘ pr₂)
      point = pair α β
      first = (preWhisker pr₁ ◁ pair-β₁ α β) ∙ comp-assoc point pr₁ (preWhisker pr₁)
      second = (preWhisker pr₂ ◁ pair-β₂ α β) ∙ comp-assoc point pr₂ (preWhisker pr₂)
  in pairIsoMap-at (α ▷ pr₁) (β ▷ pr₂) ∙
    ((output ◁ (pair-cong first second ∙
      pair-pre (preWhisker pr₁ ∘ pr₁) (preWhisker pr₂ ∘ pr₂) point)) ∙
      comp-assoc point input output)
```

The following pasting calculation assembles naturality squares, retaining
their specified vertical comparisons.

```agda
paste-squares : {X Y : CAT} {a a′ b b′ c c′ : MAP X Y}
  (u : NatIso a b) (u′ : NatIso a′ b′)
  (v : NatIso b c) (v′ : NatIso b′ c′)
  (α : NatIso a a′) (β : NatIso b b′) (γ : NatIso c c′)
  → Iso₂ (u′ ∙ α) (β ∙ u) → Iso₂ (v′ ∙ β) (γ ∙ v)
  → Iso₂ ((v′ ∙ u′) ∙ α) (γ ∙ (v ∙ u))
paste-squares u u′ v v′ α β γ p q =
  isoComp-assoc-at γ v u ∙
  (isoComp-cong q (idIso u) ∙
  (invIso (isoComp-assoc-at v′ β u) ∙
  (isoComp-cong (idIso v′) p ∙ isoComp-assoc-at v′ u′ α)))

pair-square : {X C D : CAT}
  {a a′ b b′ : MAP X C} {d d′ e e′ : MAP X D}
  (u : NatIso a b) (u′ : NatIso a′ b′)
  (v : NatIso d e) (v′ : NatIso d′ e′)
  (α : NatIso a a′) (β : NatIso b b′)
  (γ : NatIso d d′) (δ : NatIso e e′)
  → Iso₂ (u′ ∙ α) (β ∙ u) → Iso₂ (v′ ∙ γ) (δ ∙ v)
  → Iso₂ (pair-cong u′ v′ ∙ pair-cong α γ)
      (pair-cong β δ ∙ pair-cong u v)
pair-square u u′ v v′ α β γ δ p q =
  pair-cong-comp β u δ v ∙
  (pair-cong-Iso₂ p q ∙ invIso (pair-cong-comp u′ α v′ γ))

coordinate-comparison : {R X K C D : CAT}
  (ρ : MAP R X) (f : MAP X C) (π : MAP K C) (h : MAP R K)
  → NatIso (π ∘ h) (f ∘ ρ) → (F : MAP C D)
  → NatIso ((F ∘ π) ∘ h) ((F ∘ f) ∘ ρ)
coordinate-comparison ρ f π h b F =
  invIso (comp-assoc ρ f F) ∙ ((F ◁ b) ∙ comp-assoc h π F)

coordinate-outer-natural : {R X K C D : CAT}
  (ρ : MAP R X) (f : MAP X C) (π : MAP K C) (h : MAP R K)
  (b : NatIso (π ∘ h) (f ∘ ρ)) {F F′ : MAP C D} (θ : NatIso F F′)
  → Iso₂
      (coordinate-comparison ρ f π h b F′ ∙ ((θ ▷ π) ▷ h))
      (((θ ▷ f) ▷ ρ) ∙ coordinate-comparison ρ f π h b F)
coordinate-outer-natural ρ f π h b {F} {F′} θ =
  let first = preWhisker-comp-at θ π h
      middle = invIso (interchange-at θ b)
      last = move-square (comp-assoc ρ f F′) ((θ ▷ f) ▷ ρ)
        (θ ▷ (f ∘ ρ)) (comp-assoc ρ f F) (preWhisker-comp-at θ f ρ)
      initial = paste-squares (comp-assoc h π F) (comp-assoc h π F′)
        (F ◁ b) (F′ ◁ b) ((θ ▷ π) ▷ h) (θ ▷ (π ∘ h)) (θ ▷ (f ∘ ρ))
        first middle
  in paste-squares ((F ◁ b) ∙ comp-assoc h π F) ((F′ ◁ b) ∙ comp-assoc h π F′)
    (invIso (comp-assoc ρ f F)) (invIso (comp-assoc ρ f F′))
    ((θ ▷ π) ▷ h) (θ ▷ (f ∘ ρ)) ((θ ▷ f) ▷ ρ) initial last

productMap-comp-natural-outer : {C C′ C″ D D′ D″ : CAT}
  (f : MAP C C′) (g : MAP D D′)
  {F F′ : MAP C′ C″} {G G′ : MAP D′ D″}
  (θ : NatIso F F′) (ψ : NatIso G G′)
  → Iso₂
      (productMap-comp f F′ g G′ ∙ (productMap-cong θ ψ ▷ productMap f g))
      (productMap-cong (θ ▷ f) (ψ ▷ g) ∙ productMap-comp f F g G)
productMap-comp-natural-outer f g {F} {F′} {G} {G′} θ ψ =
  let h = productMap f g
      b = pair-β₁ (f ∘ pr₁) (g ∘ pr₂)
      d = pair-β₂ (f ∘ pr₁) (g ∘ pr₂)
      e = coordinate-comparison pr₁ f pr₁ h b F
      e′ = coordinate-comparison pr₁ f pr₁ h b F′
      k = coordinate-comparison pr₂ g pr₂ h d G
      k′ = coordinate-comparison pr₂ g pr₂ h d G′
      middle = pair-cong ((θ ▷ pr₁) ▷ h) ((ψ ▷ pr₂) ▷ h)
      last = productMap-cong (θ ▷ f) (ψ ▷ g)
      first-square = invIso (pair-pre-natural-inputs (θ ▷ pr₁) (ψ ▷ pr₂) h)
      last-square = pair-square e e′ k k′ ((θ ▷ pr₁) ▷ h) ((θ ▷ f) ▷ pr₁)
        ((ψ ▷ pr₂) ▷ h) ((ψ ▷ g) ▷ pr₂)
        (coordinate-outer-natural pr₁ f pr₁ h b θ)
        (coordinate-outer-natural pr₂ g pr₂ h d ψ)
  in paste-squares (pair-pre (F ∘ pr₁) (G ∘ pr₂) h)
    (pair-pre (F′ ∘ pr₁) (G′ ∘ pr₂) h)
    (pair-cong e k) (pair-cong e′ k′)
    (productMap-cong θ ψ ▷ h) middle last first-square last-square

coordinate-inner-natural : {R X K C D : CAT}
  (ρ : MAP R X) (π : MAP K C) (F : MAP C D)
  {f f′ : MAP X C} {h h′ : MAP R K}
  (b : NatIso (π ∘ h) (f ∘ ρ)) (b′ : NatIso (π ∘ h′) (f′ ∘ ρ))
  (α : NatIso f f′) (δ : NatIso h h′)
  → Iso₂ (b′ ∙ (π ◁ δ)) ((α ▷ ρ) ∙ b)
  → Iso₂
      (coordinate-comparison ρ f′ π h′ b′ F ∙ ((F ∘ π) ◁ δ))
      (((F ◁ α) ▷ ρ) ∙ coordinate-comparison ρ f π h b F)
coordinate-inner-natural ρ π F {f} {f′} {h} {h′} b b′ α δ square =
  let first = postWhisker-comp-at δ π F
      middle = postWhisker-isoComp-at F (α ▷ ρ) b ∙
        ((postWhisker F ◁ square) ∙ invIso (postWhisker-isoComp-at F b′ (π ◁ δ)))
      last = move-square (comp-assoc ρ f′ F) ((F ◁ α) ▷ ρ)
        (F ◁ (α ▷ ρ)) (comp-assoc ρ f F) (whisker-mixed-at α ρ F)
      initial = paste-squares (comp-assoc h π F) (comp-assoc h′ π F)
        (F ◁ b) (F ◁ b′) ((F ∘ π) ◁ δ) (F ◁ (π ◁ δ)) (F ◁ (α ▷ ρ))
        first middle
  in paste-squares ((F ◁ b) ∙ comp-assoc h π F) ((F ◁ b′) ∙ comp-assoc h′ π F)
    (invIso (comp-assoc ρ f F)) (invIso (comp-assoc ρ f′ F))
    ((F ∘ π) ◁ δ) (F ◁ (α ▷ ρ)) ((F ◁ α) ▷ ρ) initial last

productMap-comp-natural-inner : {C C′ C″ D D′ D″ : CAT}
  {f f′ : MAP C C′} {g g′ : MAP D D′}
  (α : NatIso f f′) (β : NatIso g g′) (F : MAP C′ C″) (G : MAP D′ D″)
  → Iso₂
      (productMap-comp f′ F g′ G ∙ (productMap F G ◁ productMap-cong α β))
      (productMap-cong (F ◁ α) (G ◁ β) ∙ productMap-comp f F g G)
productMap-comp-natural-inner {f = f} {f′} {g} {g′} α β F G =
  let h = productMap f g
      h′ = productMap f′ g′
      δ = productMap-cong α β
      b = pair-β₁ (f ∘ pr₁) (g ∘ pr₂)
      b′ = pair-β₁ (f′ ∘ pr₁) (g′ ∘ pr₂)
      d = pair-β₂ (f ∘ pr₁) (g ∘ pr₂)
      d′ = pair-β₂ (f′ ∘ pr₁) (g′ ∘ pr₂)
      e = coordinate-comparison pr₁ f pr₁ h b F
      e′ = coordinate-comparison pr₁ f′ pr₁ h′ b′ F
      k = coordinate-comparison pr₂ g pr₂ h d G
      k′ = coordinate-comparison pr₂ g′ pr₂ h′ d′ G
      middle = pair-cong ((F ∘ pr₁) ◁ δ) ((G ∘ pr₂) ◁ δ)
      last = productMap-cong (F ◁ α) (G ◁ β)
      first-square = invIso (pair-pre-natural-substitution (F ∘ pr₁) (G ∘ pr₂) δ)
      last-square = pair-square e e′ k k′ ((F ∘ pr₁) ◁ δ) ((F ◁ α) ▷ pr₁)
        ((G ∘ pr₂) ◁ δ) ((G ◁ β) ▷ pr₂)
        (coordinate-inner-natural pr₁ pr₁ F b b′ α δ
          (pair-cong-triangle₁ (α ▷ pr₁) (β ▷ pr₂)))
        (coordinate-inner-natural pr₂ pr₂ G d d′ β δ
          (pair-cong-triangle₂ (α ▷ pr₁) (β ▷ pr₂)))
  in paste-squares (pair-pre (F ∘ pr₁) (G ∘ pr₂) h)
    (pair-pre (F ∘ pr₁) (G ∘ pr₂) h′)
    (pair-cong e k) (pair-cong e′ k′)
    (productMap F G ◁ δ) middle last first-square last-square

productMap-comp-natural : {C C′ C″ D D′ D″ : CAT}
  {f f′ : MAP C C′} {g g′ : MAP D D′}
  {F F′ : MAP C′ C″} {G G′ : MAP D′ D″}
  (α : NatIso f f′) (β : NatIso g g′)
  (θ : NatIso F F′) (ψ : NatIso G G′)
  → Iso₂
      (productMap-comp f′ F′ g′ G′ ∙ (productMap-cong θ ψ ⋆ productMap-cong α β))
      (productMap-cong (θ ⋆ α) (ψ ⋆ β) ∙ productMap-comp f F g G)
productMap-comp-natural {f = f} {f′} {g} {g′} {F} {F′} {G} {G′} α β θ ψ =
  let c = productMap-comp f F g G
      c₁ = productMap-comp f′ F g′ G
      c₂ = productMap-comp f′ F′ g′ G′
      u = productMap F G ◁ productMap-cong α β
      v = productMap-cong θ ψ ▷ productMap f′ g′
      a = productMap-cong (F ◁ α) (G ◁ β)
      b = productMap-cong (θ ▷ f′) (ψ ▷ g′)
  in isoComp-cong (invIso (productMap-cong-comp (θ ▷ f′) (F ◁ α) (ψ ▷ g′) (G ◁ β))) (idIso c) ∙
    (invIso (isoComp-assoc-at b a c) ∙
    (isoComp-cong (idIso b) (productMap-comp-natural-inner α β F G) ∙
    (isoComp-assoc-at b c₁ u ∙
    (isoComp-cong (productMap-comp-natural-outer f′ g′ θ ψ) (idIso u) ∙
     invIso (isoComp-assoc-at c₂ v u)))))

productMap-cong-pre : {R C C′ D D′ : CAT}
  {f f′ : MAP C C′} {g g′ : MAP D D′}
  (α : NatIso f f′) (β : NatIso g g′) (r : MAP R (C × D))
  → Iso₂
      (pair-pre (f′ ∘ pr₁) (g′ ∘ pr₂) r ∙ (productMap-cong α β ▷ r))
      (pair-cong ((α ▷ pr₁) ▷ r) ((β ▷ pr₂) ▷ r) ∙
        pair-pre (f ∘ pr₁) (g ∘ pr₂) r)
productMap-cong-pre α β r = invIso (pair-pre-natural-inputs (α ▷ pr₁) (β ▷ pr₂) r)

prewhisker-square : {R X Y : CAT} {f f′ g g′ : MAP X Y}
  (u : NatIso f g) (u′ : NatIso f′ g′)
  (α : NatIso f f′) (β : NatIso g g′)
  → Iso₂ (u′ ∙ α) (β ∙ u) → (r : MAP R X)
  → Iso₂ ((u′ ▷ r) ∙ (α ▷ r)) ((β ▷ r) ∙ (u ▷ r))
prewhisker-square u u′ α β p r = preWhisker-isoComp-at β u r ∙
  ((preWhisker r ◁ p) ∙ invIso (preWhisker-isoComp-at u′ α r))
```

