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
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductConstructions
import SCT.VolumeI.Chapter01.Section03.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PairingNaturality

module SCT.VolumeI.Chapter01.Section03.ProductFunctorCoherence
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
  → f =₁ f′ → g =₁ g′ → (productMap f g) =₁ (productMap f′ g′)
productMap-cong α β = pair-cong (α ▷ pr₁) (β ▷ pr₂)

productMap-cong-id : {C C′ D D′ : CAT} (f : MAP C C′) (g : MAP D D′)
  → (productMap-cong (idIso f) (idIso g)) =₂ (idIso (productMap f g))
productMap-cong-id f g = pair-cong-id (f ∘ pr₁) (g ∘ pr₂) ∙
  pair-cong-Iso₂ (preWhisker-idIso f pr₁) (preWhisker-idIso g pr₂)

productMap-cong-comp : {C C′ D D′ : CAT}
  {f₀ f₁ f₂ : MAP C C′} {g₀ g₁ g₂ : MAP D D′}
  (α₂ : f₁ =₁ f₂) (α₁ : f₀ =₁ f₁)
  (β₂ : g₁ =₁ g₂) (β₁ : g₀ =₁ g₁)
  → (productMap-cong (α₂ ∙ α₁) (β₂ ∙ β₁)) =₂
      (productMap-cong α₂ β₂ ∙ productMap-cong α₁ β₁)
productMap-cong-comp α₂ α₁ β₂ β₁ =
  pair-cong-comp (α₂ ▷ pr₁) (α₁ ▷ pr₁) (β₂ ▷ pr₂) (β₁ ▷ pr₂) ∙
  pair-cong-Iso₂ (preWhisker-isoComp-at α₂ α₁ pr₁)
    (preWhisker-isoComp-at β₂ β₁ pr₂)

productMap-cong-Iso₂ : {C C′ D D′ : CAT}
  {f f′ : MAP C C′} {g g′ : MAP D D′}
  {α α′ : f =₁ f′} {β β′ : g =₁ g′}
  → α =₂ α′ → β =₂ β′
  → (productMap-cong α β) =₂ (productMap-cong α′ β′)
productMap-cong-Iso₂ p q = pair-cong-Iso₂ (preWhisker pr₁ ◁ p) (preWhisker pr₂ ◁ q)

productIsoMap : {C C′ D D′ : CAT}
  (f f′ : MAP C C′) (g g′ : MAP D D′)
  → MAP ((f ＝ f′) × (g ＝ g′)) (productMap f g ＝ productMap f′ g′)
productIsoMap f f′ g g′ = pairIsoMap (f ∘ pr₁) (f′ ∘ pr₁) (g ∘ pr₂) (g′ ∘ pr₂)
  ∘ pair (preWhisker pr₁ ∘ pr₁) (preWhisker pr₂ ∘ pr₂)

productIsoMap-at : {C C′ D D′ : CAT}
  {f f′ : MAP C C′} {g g′ : MAP D D′}
  (α : f =₁ f′) (β : g =₁ g′)
  → (productIsoMap f f′ g g′ ∘ pair α β) =₂ (productMap-cong α β)
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

pair-square : {X C D : CAT}
  {a a′ b b′ : MAP X C} {d d′ e e′ : MAP X D}
  (u : a =₁ b) (u′ : a′ =₁ b′)
  (v : d =₁ e) (v′ : d′ =₁ e′)
  (α : a =₁ a′) (β : b =₁ b′)
  (γ : d =₁ d′) (δ : e =₁ e′)
  → (u′ ∙ α) =₂ (β ∙ u) → (v′ ∙ γ) =₂ (δ ∙ v)
  → (pair-cong u′ v′ ∙ pair-cong α γ) =₂
      (pair-cong β δ ∙ pair-cong u v)
pair-square u u′ v v′ α β γ δ p q =
  pair-cong-comp β u δ v ∙
  (pair-cong-Iso₂ p q ∙ (pair-cong-comp u′ α v′ γ) ⁻¹)

coordinate-comparison : {R X K C D : CAT}
  (ρ : MAP R X) (f : MAP X C) (π : MAP K C) (h : MAP R K)
  → (π ∘ h) =₁ (f ∘ ρ) → (F : MAP C D)
  → ((F ∘ π) ∘ h) =₁ ((F ∘ f) ∘ ρ)
coordinate-comparison ρ f π h b F =
  (comp-assoc ρ f F) ⁻¹ ∙ ((F ◁ b) ∙ comp-assoc h π F)

coordinate-outer-natural : {R X K C D : CAT}
  (ρ : MAP R X) (f : MAP X C) (π : MAP K C) (h : MAP R K)
  (b : (π ∘ h) =₁ (f ∘ ρ)) {F F′ : MAP C D} (θ : F =₁ F′)
  →
      (coordinate-comparison ρ f π h b F′ ∙ ((θ ▷ π) ▷ h)) =₂
      (((θ ▷ f) ▷ ρ) ∙ coordinate-comparison ρ f π h b F)
coordinate-outer-natural ρ f π h b {F} {F′} θ =
  let first = preWhisker-comp-at θ π h
      middle = (interchange-at θ b) ⁻¹
      last = move-square (comp-assoc ρ f F′) ((θ ▷ f) ▷ ρ)
        (θ ▷ (f ∘ ρ)) (comp-assoc ρ f F) (preWhisker-comp-at θ f ρ)
      initial = paste-squares (comp-assoc h π F) (comp-assoc h π F′)
        (F ◁ b) (F′ ◁ b) ((θ ▷ π) ▷ h) (θ ▷ (π ∘ h)) (θ ▷ (f ∘ ρ))
        first middle
  in paste-squares ((F ◁ b) ∙ comp-assoc h π F) ((F′ ◁ b) ∙ comp-assoc h π F′)
    ((comp-assoc ρ f F) ⁻¹) ((comp-assoc ρ f F′) ⁻¹)
    ((θ ▷ π) ▷ h) (θ ▷ (f ∘ ρ)) ((θ ▷ f) ▷ ρ) initial last

productMap-comp-natural-outer : {C C′ C″ D D′ D″ : CAT}
  (f : MAP C C′) (g : MAP D D′)
  {F F′ : MAP C′ C″} {G G′ : MAP D′ D″}
  (θ : F =₁ F′) (ψ : G =₁ G′)
  →
      (productMap-comp f F′ g G′ ∙ (productMap-cong θ ψ ▷ productMap f g)) =₂
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
      first-square = (pair-pre-natural-inputs (θ ▷ pr₁) (ψ ▷ pr₂) h) ⁻¹
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
  (b : (π ∘ h) =₁ (f ∘ ρ)) (b′ : (π ∘ h′) =₁ (f′ ∘ ρ))
  (α : f =₁ f′) (δ : h =₁ h′)
  → (b′ ∙ (π ◁ δ)) =₂ ((α ▷ ρ) ∙ b)
  →
      (coordinate-comparison ρ f′ π h′ b′ F ∙ ((F ∘ π) ◁ δ)) =₂
      (((F ◁ α) ▷ ρ) ∙ coordinate-comparison ρ f π h b F)
coordinate-inner-natural ρ π F {f} {f′} {h} {h′} b b′ α δ square =
  let first = postWhisker-comp-at δ π F
      middle = postWhisker-isoComp-at F (α ▷ ρ) b ∙
        ((postWhisker F ◁ square) ∙ (postWhisker-isoComp-at F b′ (π ◁ δ)) ⁻¹)
      last = move-square (comp-assoc ρ f′ F) ((F ◁ α) ▷ ρ)
        (F ◁ (α ▷ ρ)) (comp-assoc ρ f F) (whisker-mixed-at α ρ F)
      initial = paste-squares (comp-assoc h π F) (comp-assoc h′ π F)
        (F ◁ b) (F ◁ b′) ((F ∘ π) ◁ δ) (F ◁ (π ◁ δ)) (F ◁ (α ▷ ρ))
        first middle
  in paste-squares ((F ◁ b) ∙ comp-assoc h π F) ((F ◁ b′) ∙ comp-assoc h′ π F)
    ((comp-assoc ρ f F) ⁻¹) ((comp-assoc ρ f′ F) ⁻¹)
    ((F ∘ π) ◁ δ) (F ◁ (α ▷ ρ)) ((F ◁ α) ▷ ρ) initial last

productMap-comp-natural-inner : {C C′ C″ D D′ D″ : CAT}
  {f f′ : MAP C C′} {g g′ : MAP D D′}
  (α : f =₁ f′) (β : g =₁ g′) (F : MAP C′ C″) (G : MAP D′ D″)
  →
      (productMap-comp f′ F g′ G ∙ (productMap F G ◁ productMap-cong α β)) =₂
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
      first-square = (pair-pre-natural-substitution (F ∘ pr₁) (G ∘ pr₂) δ) ⁻¹
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
  (α : f =₁ f′) (β : g =₁ g′)
  (θ : F =₁ F′) (ψ : G =₁ G′)
  →
      (productMap-comp f′ F′ g′ G′ ∙ (productMap-cong θ ψ ⋆ productMap-cong α β)) =₂
      (productMap-cong (θ ⋆ α) (ψ ⋆ β) ∙ productMap-comp f F g G)
productMap-comp-natural {f = f} {f′} {g} {g′} {F} {F′} {G} {G′} α β θ ψ =
  let c = productMap-comp f F g G
      c₁ = productMap-comp f′ F g′ G
      c₂ = productMap-comp f′ F′ g′ G′
      u = productMap F G ◁ productMap-cong α β
      v = productMap-cong θ ψ ▷ productMap f′ g′
      a = productMap-cong (F ◁ α) (G ◁ β)
      b = productMap-cong (θ ▷ f′) (ψ ▷ g′)
  in isoComp-cong ((productMap-cong-comp (θ ▷ f′) (F ◁ α) (ψ ▷ g′) (G ◁ β)) ⁻¹) (idIso c) ∙
    ((isoComp-assoc-at b a c) ⁻¹ ∙
    (isoComp-cong (idIso b) (productMap-comp-natural-inner α β F G) ∙
    (isoComp-assoc-at b c₁ u ∙
    (isoComp-cong (productMap-comp-natural-outer f′ g′ θ ψ) (idIso u) ∙
     (isoComp-assoc-at c₂ v u) ⁻¹))))

productMap-cong-pre : {R C C′ D D′ : CAT}
  {f f′ : MAP C C′} {g g′ : MAP D D′}
  (α : f =₁ f′) (β : g =₁ g′) (r : MAP R (C × D))
  →
      (pair-pre (f′ ∘ pr₁) (g′ ∘ pr₂) r ∙ (productMap-cong α β ▷ r)) =₂
      (pair-cong ((α ▷ pr₁) ▷ r) ((β ▷ pr₂) ▷ r) ∙
        pair-pre (f ∘ pr₁) (g ∘ pr₂) r)
productMap-cong-pre α β r = (pair-pre-natural-inputs (α ▷ pr₁) (β ▷ pr₂) r) ⁻¹

prewhisker-square : {R X Y : CAT} {f f′ g g′ : MAP X Y}
  (u : f =₁ g) (u′ : f′ =₁ g′)
  (α : f =₁ f′) (β : g =₁ g′)
  → (u′ ∙ α) =₂ (β ∙ u) → (r : MAP R X)
  → ((u′ ▷ r) ∙ (α ▷ r)) =₂ ((β ▷ r) ∙ (u ▷ r))
prewhisker-square u u′ α β p r = preWhisker-isoComp-at β u r ∙
  ((preWhisker r ◁ p) ∙ (preWhisker-isoComp-at u′ α r) ⁻¹)
```

