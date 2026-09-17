# Identity and composition for pairing

The comparison `pair-cong` from Section 1.1 preserves identities and vertical
composition through specified identifications. The proof first records its
projection witnesses, then reflects the required higher comparisons through
the product comparison equivalence. This reflection needs no new axiom.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section01.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section02.PairingCoherence
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S) where

open Vocabulary V
open Operations V
open Terminal.Constructions V T
open Products.ProductData P
open Products.Comparison V P
open Products.ProductLaws PL
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.WhiskeringCoherence W
open Specialization V T P PL S
open Specialization.Units V T P PL S VC
open Specialization.Whiskering V T P PL S W
open Isomorphisms V T P PL S VC W using (reassociateFour; cancel-inverse)

equiv-reflect : {X C D : CAT} {F : MAP C D} (e : IsEquiv F)
  {u v : MAP X C} → =₁ (F ∘ u) (F ∘ v) → =₁ u v
equiv-reflect {F = F} e {u} {v} α =
  let G = IsEquiv.inverse e
      at-u = comp-assoc u F G ∙ ((IsEquiv.sectionIso e ▷ u) ∙ invIso (comp-unitˡ u))
      at-v = comp-assoc v F G ∙ ((IsEquiv.sectionIso e ▷ v) ∙ invIso (comp-unitˡ v))
  in invIso at-v ∙ ((G ◁ α) ∙ at-u)

pair-iso-extensionality : {X C D : CAT} {f g : MAP X (C × D)}
  {α β : =₁ f g}
  → =₂ (pr₁ ◁ α) (pr₁ ◁ β)
  → =₂ (pr₂ ◁ α) (pr₂ ◁ β)
  → =₂ α β
pair-iso-extensionality {f = f} {g} {α} {β} p q =
  equiv-reflect (product-isoMap-isEquiv f g)
    (invIso (pair-pre (postWhisker pr₁) (postWhisker pr₂) β) ∙
      (pair-cong p q ∙ pair-pre (postWhisker pr₁) (postWhisker pr₂) α))
```

The projection of `pair-cong` is conjugation by the two product beta
comparisons. The next elementary calculation is therefore shared by both
projections.

```agda
conjugate-id : {X C : CAT} {f g : MAP X C} (β : =₁ f g)
  → =₂ (invIso β ∙ (idIso g ∙ β)) (idIso f)
conjugate-id β = isoComp-inverseˡ-at β ∙
  isoComp-cong (idIso (invIso β)) (isoComp-unitˡ-at β)

conjugate-comp : {X C : CAT} {p₀ p₁ p₂ f₀ f₁ f₂ : MAP X C}
  (c₀ : =₁ p₀ f₀) (c₁ : =₁ p₁ f₁) (c₂ : =₁ p₂ f₂)
  (α₂ : =₁ f₁ f₂) (α₁ : =₁ f₀ f₁)
  → =₂ (invIso c₂ ∙ ((α₂ ∙ α₁) ∙ c₀))
      ((invIso c₂ ∙ (α₂ ∙ c₁)) ∙ (invIso c₁ ∙ (α₁ ∙ c₀)))
conjugate-comp c₀ c₁ c₂ α₂ α₁ =
  let cancel = isoComp-unitʳ-at α₂ ∙
        (isoComp-cong (idIso α₂) (isoComp-inverseʳ-at c₁) ∙
          isoComp-assoc-at α₂ c₁ (invIso c₁))
  in invIso
    (isoComp-cong (idIso (invIso c₂)) (invIso (isoComp-assoc-at α₂ α₁ c₀)) ∙
      (isoComp-cong (idIso (invIso c₂))
        (isoComp-cong cancel (idIso (α₁ ∙ c₀))) ∙
        reassociateFour (invIso c₂) (α₂ ∙ c₁) (invIso c₁) (α₁ ∙ c₀)))

pair-cong-β₁ : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : =₁ f f′) (β : =₁ g g′)
  → =₂ (pr₁ ◁ pair-cong α β)
      (invIso (pair-β₁ f′ g′) ∙ (α ∙ pair-β₁ f g))
pair-cong-β₁ {f = f} {f′} {g} {g′} α β = pair-iso-β₁
  (invIso (pair-β₁ f′ g′) ∙ (α ∙ pair-β₁ f g))
  (invIso (pair-β₂ f′ g′) ∙ (β ∙ pair-β₂ f g))

pair-cong-β₂ : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : =₁ f f′) (β : =₁ g g′)
  → =₂ (pr₂ ◁ pair-cong α β)
      (invIso (pair-β₂ f′ g′) ∙ (β ∙ pair-β₂ f g))
pair-cong-β₂ {f = f} {f′} {g} {g′} α β = pair-iso-β₂
  (invIso (pair-β₁ f′ g′) ∙ (α ∙ pair-β₁ f g))
  (invIso (pair-β₂ f′ g′) ∙ (β ∙ pair-β₂ f g))

pair-cong-triangle₁ : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : =₁ f f′) (β : =₁ g g′)
  → =₂ (pair-β₁ f′ g′ ∙ (pr₁ ◁ pair-cong α β)) (α ∙ pair-β₁ f g)
pair-cong-triangle₁ {f = f} {f′} {g} {g′} α β =
  cancel-inverse (pair-β₁ f′ g′) (α ∙ pair-β₁ f g) ∙
    isoComp-cong (idIso (pair-β₁ f′ g′)) (pair-cong-β₁ α β)

pair-cong-triangle₂ : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : =₁ f f′) (β : =₁ g g′)
  → =₂ (pair-β₂ f′ g′ ∙ (pr₂ ◁ pair-cong α β)) (β ∙ pair-β₂ f g)
pair-cong-triangle₂ {f = f} {f′} {g} {g′} α β =
  cancel-inverse (pair-β₂ f′ g′) (β ∙ pair-β₂ f g) ∙
    isoComp-cong (idIso (pair-β₂ f′ g′)) (pair-cong-β₂ α β)

pair-pre-β₁ : {R X C D : CAT} (f : MAP X C) (g : MAP X D) (σ : MAP R X)
  → =₂ (pr₁ ◁ pair-pre f g σ)
      (invIso (pair-β₁ (f ∘ σ) (g ∘ σ)) ∙
        ((pair-β₁ f g ▷ σ) ∙ invIso (comp-assoc σ (pair f g) pr₁)))
pair-pre-β₁ f g σ = pair-iso-β₁
  (invIso (pair-β₁ (f ∘ σ) (g ∘ σ)) ∙
    ((pair-β₁ f g ▷ σ) ∙ invIso (comp-assoc σ (pair f g) pr₁)))
  (invIso (pair-β₂ (f ∘ σ) (g ∘ σ)) ∙
    ((pair-β₂ f g ▷ σ) ∙ invIso (comp-assoc σ (pair f g) pr₂)))

pair-pre-β₂ : {R X C D : CAT} (f : MAP X C) (g : MAP X D) (σ : MAP R X)
  → =₂ (pr₂ ◁ pair-pre f g σ)
      (invIso (pair-β₂ (f ∘ σ) (g ∘ σ)) ∙
        ((pair-β₂ f g ▷ σ) ∙ invIso (comp-assoc σ (pair f g) pr₂)))
pair-pre-β₂ f g σ = pair-iso-β₂
  (invIso (pair-β₁ (f ∘ σ) (g ∘ σ)) ∙
    ((pair-β₁ f g ▷ σ) ∙ invIso (comp-assoc σ (pair f g) pr₁)))
  (invIso (pair-β₂ (f ∘ σ) (g ∘ σ)) ∙
    ((pair-β₂ f g ▷ σ) ∙ invIso (comp-assoc σ (pair f g) pr₂)))

pair-pre-triangle₁ : {R X C D : CAT} (f : MAP X C) (g : MAP X D) (σ : MAP R X)
  → =₂ (pair-β₁ (f ∘ σ) (g ∘ σ) ∙ (pr₁ ◁ pair-pre f g σ))
      ((pair-β₁ f g ▷ σ) ∙ invIso (comp-assoc σ (pair f g) pr₁))
pair-pre-triangle₁ f g σ =
  cancel-inverse (pair-β₁ (f ∘ σ) (g ∘ σ))
    ((pair-β₁ f g ▷ σ) ∙ invIso (comp-assoc σ (pair f g) pr₁)) ∙
    isoComp-cong (idIso (pair-β₁ (f ∘ σ) (g ∘ σ))) (pair-pre-β₁ f g σ)

pair-pre-triangle₂ : {R X C D : CAT} (f : MAP X C) (g : MAP X D) (σ : MAP R X)
  → =₂ (pair-β₂ (f ∘ σ) (g ∘ σ) ∙ (pr₂ ◁ pair-pre f g σ))
      ((pair-β₂ f g ▷ σ) ∙ invIso (comp-assoc σ (pair f g) pr₂))
pair-pre-triangle₂ f g σ =
  cancel-inverse (pair-β₂ (f ∘ σ) (g ∘ σ))
    ((pair-β₂ f g ▷ σ) ∙ invIso (comp-assoc σ (pair f g) pr₂)) ∙
    isoComp-cong (idIso (pair-β₂ (f ∘ σ) (g ∘ σ))) (pair-pre-β₂ f g σ)

pair-cong-id : {X C D : CAT} (f : MAP X C) (g : MAP X D)
  → =₂ (pair-cong (idIso f) (idIso g)) (idIso (pair f g))
pair-cong-id f g = pair-iso-extensionality
  (invIso (postWhisker-idIso pr₁ (pair f g)) ∙
    (conjugate-id (pair-β₁ f g) ∙ pair-cong-β₁ (idIso f) (idIso g)))
  (invIso (postWhisker-idIso pr₂ (pair f g)) ∙
    (conjugate-id (pair-β₂ f g) ∙ pair-cong-β₂ (idIso f) (idIso g)))

pair-cong-comp : {X C D : CAT}
  {f₀ f₁ f₂ : MAP X C} {g₀ g₁ g₂ : MAP X D}
  (α₂ : =₁ f₁ f₂) (α₁ : =₁ f₀ f₁)
  (β₂ : =₁ g₁ g₂) (β₁ : =₁ g₀ g₁)
  → =₂ (pair-cong (α₂ ∙ α₁) (β₂ ∙ β₁))
      (pair-cong α₂ β₂ ∙ pair-cong α₁ β₁)
pair-cong-comp {f₀ = f₀} {f₁} {f₂} {g₀} {g₁} {g₂} α₂ α₁ β₂ β₁ =
  pair-iso-extensionality
    (invIso (postWhisker-isoComp-at pr₁ (pair-cong α₂ β₂) (pair-cong α₁ β₁)) ∙
      (invIso (isoComp-cong (pair-cong-β₁ α₂ β₂) (pair-cong-β₁ α₁ β₁)) ∙
        (conjugate-comp (pair-β₁ f₀ g₀) (pair-β₁ f₁ g₁) (pair-β₁ f₂ g₂) α₂ α₁ ∙
          pair-cong-β₁ (α₂ ∙ α₁) (β₂ ∙ β₁))))
    (invIso (postWhisker-isoComp-at pr₂ (pair-cong α₂ β₂) (pair-cong α₁ β₁)) ∙
      (invIso (isoComp-cong (pair-cong-β₂ α₂ β₂) (pair-cong-β₂ α₁ β₁)) ∙
        (conjugate-comp (pair-β₂ f₀ g₀) (pair-β₂ f₁ g₁) (pair-β₂ f₂ g₂) β₂ β₁ ∙
          pair-cong-β₂ (α₂ ∙ α₁) (β₂ ∙ β₁))))
```

Pairing of natural isomorphisms is represented by an actual functor from
the product of their isomorphism animae. Its action on identifications is
ordinary postwhiskering. The comparison `pairIsoMap-at` relates its value at
the paired input to the already chosen `pair-cong`, so this action applies
to precisely the comparisons used above.

```agda
module PairIsoMap {X C D : CAT}
  (f f′ : MAP X C) (g g′ : MAP X D) where

  source = (f ＝ f′) × (g ＝ g′)
  target = pair f g ＝ pair f′ g′

  first : MAP source ((pr₁ ∘ pair f g) ＝ (pr₁ ∘ pair f′ g′))
  first = const (invIso (pair-β₁ f′ g′)) ∙ (pr₁ ∙ const (pair-β₁ f g))

  second : MAP source ((pr₂ ∘ pair f g) ＝ (pr₂ ∘ pair f′ g′))
  second = const (invIso (pair-β₂ f′ g′)) ∙ (pr₂ ∙ const (pair-β₂ f g))

  back = IsEquiv.inverse (product-isoMap-isEquiv (pair f g) (pair f′ g′))

  comparison : MAP source target
  comparison = back ∘ pair first second

  at : (α : =₁ f f′) (β : =₁ g g′)
    → =₂ (comparison ∘ pair α β) (pair-cong α β)
  at α β =
    let point = pair α β
        first-at = isoComp-evaluate (const (invIso (pair-β₁ f′ g′)))
          (pr₁ ∙ const (pair-β₁ f g)) point
          (const-evaluate (invIso (pair-β₁ f′ g′)) point)
          (isoComp-evaluate pr₁ (const (pair-β₁ f g)) point
            (pair-β₁ α β) (const-evaluate (pair-β₁ f g) point))
        second-at = isoComp-evaluate (const (invIso (pair-β₂ f′ g′)))
          (pr₂ ∙ const (pair-β₂ f g)) point
          (const-evaluate (invIso (pair-β₂ f′ g′)) point)
          (isoComp-evaluate pr₂ (const (pair-β₂ f g)) point
            (pair-β₂ α β) (const-evaluate (pair-β₂ f g) point))
    in (back ◁ (pair-cong first-at second-at ∙ pair-pre first second point)) ∙
      comp-assoc point (pair first second) back

pairIsoMap : {X C D : CAT} (f f′ : MAP X C) (g g′ : MAP X D)
  → MAP ((f ＝ f′) × (g ＝ g′)) (pair f g ＝ pair f′ g′)
pairIsoMap = PairIsoMap.comparison

pairIsoMap-at : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : =₁ f f′) (β : =₁ g g′)
  → =₂ (pairIsoMap f f′ g g′ ∘ pair α β) (pair-cong α β)
pairIsoMap-at {f = f} {f′} {g} {g′} = PairIsoMap.at f f′ g g′

pair-cong-Iso₂ : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  {α α′ : =₁ f f′} {β β′ : =₁ g g′}
  → =₂ α α′ → =₂ β β′
  → =₂ (pair-cong α β) (pair-cong α′ β′)
pair-cong-Iso₂ {f = f} {f′} {g} {g′} {α} {α′} {β} {β′} p q =
  pairIsoMap-at α′ β′ ∙
    ((pairIsoMap f f′ g g′ ◁ pair-cong p q) ∙ invIso (pairIsoMap-at α β))
```
