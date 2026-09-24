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
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section03.PairingCoherence
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
  {u v : MAP X C} → (F ∘ u) =₁ (F ∘ v) → u =₁ v
equiv-reflect {F = F} e {u} {v} α =
  let G = IsEquiv.inverse e
      at-u = comp-assoc u F G ∙ ((IsEquiv.sectionIso e ▷ u) ∙ (comp-unitˡ u) ⁻¹)
      at-v = comp-assoc v F G ∙ ((IsEquiv.sectionIso e ▷ v) ∙ (comp-unitˡ v) ⁻¹)
  in at-v ⁻¹ ∙ ((G ◁ α) ∙ at-u)

pair-iso-extensionality : {X C D : CAT} {f g : MAP X (C × D)}
  {α β : f =₁ g}
  → (pr₁ ◁ α) =₂ (pr₁ ◁ β)
  → (pr₂ ◁ α) =₂ (pr₂ ◁ β)
  → α =₂ β
pair-iso-extensionality {f = f} {g} {α} {β} p q =
  equiv-reflect (product-isoMap-isEquiv f g)
    ((pair-pre (postWhisker pr₁) (postWhisker pr₂) β) ⁻¹ ∙
      (pair-cong p q ∙ pair-pre (postWhisker pr₁) (postWhisker pr₂) α))
```

The projection of `pair-cong` is conjugation by the two product beta
comparisons. The next elementary calculation is therefore shared by both
projections.

```agda
conjugate-id : {X C : CAT} {f g : MAP X C} (β : f =₁ g)
  → (β ⁻¹ ∙ (idIso g ∙ β)) =₂ (idIso f)
conjugate-id β = isoComp-inverseˡ-at β ∙
  isoComp-cong (idIso (β ⁻¹)) (isoComp-unitˡ-at β)

conjugate-comp : {X C : CAT} {p₀ p₁ p₂ f₀ f₁ f₂ : MAP X C}
  (c₀ : p₀ =₁ f₀) (c₁ : p₁ =₁ f₁) (c₂ : p₂ =₁ f₂)
  (α₂ : f₁ =₁ f₂) (α₁ : f₀ =₁ f₁)
  → (c₂ ⁻¹ ∙ ((α₂ ∙ α₁) ∙ c₀)) =₂
      ((c₂ ⁻¹ ∙ (α₂ ∙ c₁)) ∙ (c₁ ⁻¹ ∙ (α₁ ∙ c₀)))
conjugate-comp c₀ c₁ c₂ α₂ α₁ =
  let cancel = isoComp-unitʳ-at α₂ ∙
        (isoComp-cong (idIso α₂) (isoComp-inverseʳ-at c₁) ∙
          isoComp-assoc-at α₂ c₁ (c₁ ⁻¹))
  in
    (isoComp-cong (idIso (c₂ ⁻¹)) ((isoComp-assoc-at α₂ α₁ c₀) ⁻¹) ∙
      (isoComp-cong (idIso (c₂ ⁻¹))
        (isoComp-cong cancel (idIso (α₁ ∙ c₀))) ∙
        reassociateFour (c₂ ⁻¹) (α₂ ∙ c₁) (c₁ ⁻¹) (α₁ ∙ c₀))) ⁻¹

pair-cong-β₁ : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : f =₁ f′) (β : g =₁ g′)
  → (pr₁ ◁ pair-cong α β) =₂
      ((pair-β₁ f′ g′) ⁻¹ ∙ (α ∙ pair-β₁ f g))
pair-cong-β₁ {f = f} {f′} {g} {g′} α β = pair-iso-β₁
  ((pair-β₁ f′ g′) ⁻¹ ∙ (α ∙ pair-β₁ f g))
  ((pair-β₂ f′ g′) ⁻¹ ∙ (β ∙ pair-β₂ f g))

pair-cong-β₂ : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : f =₁ f′) (β : g =₁ g′)
  → (pr₂ ◁ pair-cong α β) =₂
      ((pair-β₂ f′ g′) ⁻¹ ∙ (β ∙ pair-β₂ f g))
pair-cong-β₂ {f = f} {f′} {g} {g′} α β = pair-iso-β₂
  ((pair-β₁ f′ g′) ⁻¹ ∙ (α ∙ pair-β₁ f g))
  ((pair-β₂ f′ g′) ⁻¹ ∙ (β ∙ pair-β₂ f g))

pair-cong-triangle₁ : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : f =₁ f′) (β : g =₁ g′)
  → (pair-β₁ f′ g′ ∙ (pr₁ ◁ pair-cong α β)) =₂ (α ∙ pair-β₁ f g)
pair-cong-triangle₁ {f = f} {f′} {g} {g′} α β =
  cancel-inverse (pair-β₁ f′ g′) (α ∙ pair-β₁ f g) ∙
    isoComp-cong (idIso (pair-β₁ f′ g′)) (pair-cong-β₁ α β)

pair-cong-triangle₂ : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : f =₁ f′) (β : g =₁ g′)
  → (pair-β₂ f′ g′ ∙ (pr₂ ◁ pair-cong α β)) =₂ (β ∙ pair-β₂ f g)
pair-cong-triangle₂ {f = f} {f′} {g} {g′} α β =
  cancel-inverse (pair-β₂ f′ g′) (β ∙ pair-β₂ f g) ∙
    isoComp-cong (idIso (pair-β₂ f′ g′)) (pair-cong-β₂ α β)

pair-pre-β₁ : {R X C D : CAT} (f : MAP X C) (g : MAP X D) (σ : MAP R X)
  → (pr₁ ◁ pair-pre f g σ) =₂
      ((pair-β₁ (f ∘ σ) (g ∘ σ)) ⁻¹ ∙
        ((pair-β₁ f g ▷ σ) ∙ (comp-assoc σ (pair f g) pr₁) ⁻¹))
pair-pre-β₁ f g σ = pair-iso-β₁
  ((pair-β₁ (f ∘ σ) (g ∘ σ)) ⁻¹ ∙
    ((pair-β₁ f g ▷ σ) ∙ (comp-assoc σ (pair f g) pr₁) ⁻¹))
  ((pair-β₂ (f ∘ σ) (g ∘ σ)) ⁻¹ ∙
    ((pair-β₂ f g ▷ σ) ∙ (comp-assoc σ (pair f g) pr₂) ⁻¹))

pair-pre-β₂ : {R X C D : CAT} (f : MAP X C) (g : MAP X D) (σ : MAP R X)
  → (pr₂ ◁ pair-pre f g σ) =₂
      ((pair-β₂ (f ∘ σ) (g ∘ σ)) ⁻¹ ∙
        ((pair-β₂ f g ▷ σ) ∙ (comp-assoc σ (pair f g) pr₂) ⁻¹))
pair-pre-β₂ f g σ = pair-iso-β₂
  ((pair-β₁ (f ∘ σ) (g ∘ σ)) ⁻¹ ∙
    ((pair-β₁ f g ▷ σ) ∙ (comp-assoc σ (pair f g) pr₁) ⁻¹))
  ((pair-β₂ (f ∘ σ) (g ∘ σ)) ⁻¹ ∙
    ((pair-β₂ f g ▷ σ) ∙ (comp-assoc σ (pair f g) pr₂) ⁻¹))

pair-pre-triangle₁ : {R X C D : CAT} (f : MAP X C) (g : MAP X D) (σ : MAP R X)
  → (pair-β₁ (f ∘ σ) (g ∘ σ) ∙ (pr₁ ◁ pair-pre f g σ)) =₂
      ((pair-β₁ f g ▷ σ) ∙ (comp-assoc σ (pair f g) pr₁) ⁻¹)
pair-pre-triangle₁ f g σ =
  cancel-inverse (pair-β₁ (f ∘ σ) (g ∘ σ))
    ((pair-β₁ f g ▷ σ) ∙ (comp-assoc σ (pair f g) pr₁) ⁻¹) ∙
    isoComp-cong (idIso (pair-β₁ (f ∘ σ) (g ∘ σ))) (pair-pre-β₁ f g σ)

pair-pre-triangle₂ : {R X C D : CAT} (f : MAP X C) (g : MAP X D) (σ : MAP R X)
  → (pair-β₂ (f ∘ σ) (g ∘ σ) ∙ (pr₂ ◁ pair-pre f g σ)) =₂
      ((pair-β₂ f g ▷ σ) ∙ (comp-assoc σ (pair f g) pr₂) ⁻¹)
pair-pre-triangle₂ f g σ =
  cancel-inverse (pair-β₂ (f ∘ σ) (g ∘ σ))
    ((pair-β₂ f g ▷ σ) ∙ (comp-assoc σ (pair f g) pr₂) ⁻¹) ∙
    isoComp-cong (idIso (pair-β₂ (f ∘ σ) (g ∘ σ))) (pair-pre-β₂ f g σ)

pair-cong-id : {X C D : CAT} (f : MAP X C) (g : MAP X D)
  → (pair-cong (idIso f) (idIso g)) =₂ (idIso (pair f g))
pair-cong-id f g = pair-iso-extensionality
  ((postWhisker-idIso pr₁ (pair f g)) ⁻¹ ∙
    (conjugate-id (pair-β₁ f g) ∙ pair-cong-β₁ (idIso f) (idIso g)))
  ((postWhisker-idIso pr₂ (pair f g)) ⁻¹ ∙
    (conjugate-id (pair-β₂ f g) ∙ pair-cong-β₂ (idIso f) (idIso g)))

pair-cong-comp : {X C D : CAT}
  {f₀ f₁ f₂ : MAP X C} {g₀ g₁ g₂ : MAP X D}
  (α₂ : f₁ =₁ f₂) (α₁ : f₀ =₁ f₁)
  (β₂ : g₁ =₁ g₂) (β₁ : g₀ =₁ g₁)
  → (pair-cong (α₂ ∙ α₁) (β₂ ∙ β₁)) =₂
      (pair-cong α₂ β₂ ∙ pair-cong α₁ β₁)
pair-cong-comp {f₀ = f₀} {f₁} {f₂} {g₀} {g₁} {g₂} α₂ α₁ β₂ β₁ =
  pair-iso-extensionality
    ((postWhisker-isoComp-at pr₁ (pair-cong α₂ β₂) (pair-cong α₁ β₁)) ⁻¹ ∙
      ((isoComp-cong (pair-cong-β₁ α₂ β₂) (pair-cong-β₁ α₁ β₁)) ⁻¹ ∙
        (conjugate-comp (pair-β₁ f₀ g₀) (pair-β₁ f₁ g₁) (pair-β₁ f₂ g₂) α₂ α₁ ∙
          pair-cong-β₁ (α₂ ∙ α₁) (β₂ ∙ β₁))))
    ((postWhisker-isoComp-at pr₂ (pair-cong α₂ β₂) (pair-cong α₁ β₁)) ⁻¹ ∙
      ((isoComp-cong (pair-cong-β₂ α₂ β₂) (pair-cong-β₂ α₁ β₁)) ⁻¹ ∙
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
  first = const ((pair-β₁ f′ g′) ⁻¹) ∙ (pr₁ ∙ const (pair-β₁ f g))

  second : MAP source ((pr₂ ∘ pair f g) ＝ (pr₂ ∘ pair f′ g′))
  second = const ((pair-β₂ f′ g′) ⁻¹) ∙ (pr₂ ∙ const (pair-β₂ f g))

  back = IsEquiv.inverse (product-isoMap-isEquiv (pair f g) (pair f′ g′))

  comparison : MAP source target
  comparison = back ∘ pair first second

  at : (α : f =₁ f′) (β : g =₁ g′)
    → (comparison ∘ pair α β) =₂ (pair-cong α β)
  at α β =
    let point = pair α β
        first-at = isoComp-evaluate (const ((pair-β₁ f′ g′) ⁻¹))
          (pr₁ ∙ const (pair-β₁ f g)) point
          (const-evaluate ((pair-β₁ f′ g′) ⁻¹) point)
          (isoComp-evaluate pr₁ (const (pair-β₁ f g)) point
            (pair-β₁ α β) (const-evaluate (pair-β₁ f g) point))
        second-at = isoComp-evaluate (const ((pair-β₂ f′ g′) ⁻¹))
          (pr₂ ∙ const (pair-β₂ f g)) point
          (const-evaluate ((pair-β₂ f′ g′) ⁻¹) point)
          (isoComp-evaluate pr₂ (const (pair-β₂ f g)) point
            (pair-β₂ α β) (const-evaluate (pair-β₂ f g) point))
    in (back ◁ (pair-cong first-at second-at ∙ pair-pre first second point)) ∙
      comp-assoc point (pair first second) back

pairIsoMap : {X C D : CAT} (f f′ : MAP X C) (g g′ : MAP X D)
  → MAP ((f ＝ f′) × (g ＝ g′)) (pair f g ＝ pair f′ g′)
pairIsoMap = PairIsoMap.comparison

pairIsoMap-at : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : f =₁ f′) (β : g =₁ g′)
  → (pairIsoMap f f′ g g′ ∘ pair α β) =₂ (pair-cong α β)
pairIsoMap-at {f = f} {f′} {g} {g′} = PairIsoMap.at f f′ g g′

pair-cong-Iso₂ : {X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  {α α′ : f =₁ f′} {β β′ : g =₁ g′}
  → α =₂ α′ → β =₂ β′
  → (pair-cong α β) =₂ (pair-cong α′ β′)
pair-cong-Iso₂ {f = f} {f′} {g} {g′} {α} {α′} {β} {β′} p q =
  pairIsoMap-at α′ β′ ∙
    ((pairIsoMap f f′ g g′ ◁ pair-cong p q) ∙ (pairIsoMap-at α β) ⁻¹)
```
