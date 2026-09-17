# Pasting squares between varying parameters

The comparison for two composable squares retains all four external
associators and whiskerings in its boundary. This module uses only the
finite categorical calculus of `Theory`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section02.ProductFunctorCoherence as ProductFunctorCoherence
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre; transport-pre-assoc; pentagon-whiskered)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left-reflect)
open Structural vocabulary terminal products productLaws composition whiskering
  using (whisker-mixed-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)

paste : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
  {f : MAP A₀ A₁} {g : MAP A₁ A₂} {F : MAP B₀ B₁} {G : MAP B₁ B₂}
  {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
  → NatIso (x₂ ∘ g) (G ∘ x₁) → NatIso (x₁ ∘ f) (F ∘ x₀)
  → NatIso (x₂ ∘ (g ∘ f)) ((G ∘ F) ∘ x₀)
paste {f = f} {g} {F} {G} {x₀} {x₁} {x₂} β α =
  invIso (comp-assoc x₀ F G) ∙
    ((G ◁ α) ∙ (comp-assoc f x₁ G ∙ ((β ▷ f) ∙ invIso (comp-assoc f g x₂))))

abstract
  paste-factor : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f : MAP A₀ A₁} {g : MAP A₁ A₂} {F : MAP B₀ B₁} {G : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : NatIso (x₂ ∘ g) (G ∘ x₁)) (α : NatIso (x₁ ∘ f) (F ∘ x₀))
    → Iso₂ (paste β α)
        (coordinate-comparison x₀ F x₁ f α G ∙ transport-pre x₂ g β f)
  paste-factor {f = f} {g} {F} {G} {x₀} {x₁} {x₂} β α =
    invIso (isoComp-assoc-at (invIso (comp-assoc x₀ F G)) ((G ◁ α) ∙ comp-assoc f x₁ G)
      (transport-pre x₂ g β f)) ∙
      isoComp-cong (idIso (invIso (comp-assoc x₀ F G)))
        (invIso (isoComp-assoc-at (G ◁ α) (comp-assoc f x₁ G) (transport-pre x₂ g β f)))
  
  pre-cancel-inverse : {R X Y : CAT} {u v w : MAP X Y}
    (β : NatIso v w) (α : NatIso u w) (r : MAP R X)
    → Iso₂ ((β ▷ r) ∙ ((invIso β ∙ α) ▷ r)) (α ▷ r)
  pre-cancel-inverse β α r = (preWhisker r ◁ cancel-inverse β α) ∙
    invIso (preWhisker-isoComp-at β (invIso β ∙ α) r)
  
  post-cancel-inverse : {X Y Z : CAT} (F : MAP Y Z) {u v : MAP X Y}
    (β : NatIso u v) {w : MAP X Z} (α : NatIso w (F ∘ v))
    → Iso₂ ((F ◁ β) ∙ ((F ◁ invIso β) ∙ α)) α
  post-cancel-inverse F {v = v} β α = isoComp-unitˡ-at α ∙
    (isoComp-cong
      (postWhisker-idIso F v ∙
        ((postWhisker F ◁ isoComp-inverseʳ-at β) ∙
          invIso (postWhisker-isoComp-at F β (invIso β)))) (idIso α) ∙
      invIso (isoComp-assoc-at (F ◁ β) (F ◁ invIso β) α))
  
  transport-paste : {A₀ A₁ A₂ A₃ B₁ B₂ B₃ : CAT}
    (f : MAP A₀ A₁) {g : MAP A₁ A₂} {h : MAP A₂ A₃}
    {G : MAP B₁ B₂} {H : MAP B₂ B₃}
    {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂} {x₃ : MAP A₃ B₃}
    (γ : NatIso (x₃ ∘ h) (H ∘ x₂)) (β : NatIso (x₂ ∘ g) (G ∘ x₁))
    → Iso₂
        (comp-assoc f (G ∘ x₁) H ∙
          ((comp-assoc x₁ G H ▷ f) ∙ transport-pre x₃ (h ∘ g) (paste γ β) f))
        ((H ◁ transport-pre x₂ g β f) ∙
          (comp-assoc (g ∘ f) x₂ H ∙
            (transport-pre x₃ h γ (g ∘ f) ∙ (x₃ ◁ comp-assoc f g h))))
  transport-paste f {g} {h} {G} {H} {x₁} {x₂} {x₃} γ β =
    let A = comp-assoc f (G ∘ x₁) H
        B = comp-assoc x₁ G H
        C = comp-assoc g x₂ H
        T = transport-pre x₃ h γ g
        tail = invIso (comp-assoc f (h ∘ g) x₃)
        S = (H ◁ β) ∙ (C ∙ T)
        β′ = (H ◁ β) ▷ f
        C′ = C ▷ f
        T′ = T ▷ f
        βImage = H ◁ (β ▷ f)
        middle = comp-assoc f (x₂ ∘ g) H
        inputA = comp-assoc f g x₂
        nextA = comp-assoc (g ∘ f) x₂ H
        endA = comp-assoc f g (H ∘ x₂)
        end = transport-pre x₃ h γ (g ∘ f) ∙ (x₃ ◁ comp-assoc f g h)
        corner = cancel-left-reflect (H ◁ inputA)
          (invIso (post-cancel-inverse H inputA (nextA ∙ endA)) ∙
            invIso (pentagon-whiskered f g x₂ H))
        transport = transport-pre-assoc x₃ h (H ∘ x₂) γ g f
        expandS = isoComp-cong (idIso β′) (preWhisker-isoComp-at C T f) ∙
          preWhisker-isoComp-at (H ◁ β) (C ∙ T) f
        cancelB = isoComp-cong (pre-cancel-inverse B S f) (idIso tail) ∙
          invIso (isoComp-assoc-at (B ▷ f) (paste γ β ▷ f) tail)
        expand = isoComp-cong (idIso A)
          (isoComp-cong (idIso β′) (isoComp-assoc-at C′ T′ tail) ∙
            (isoComp-assoc-at β′ (C′ ∙ T′) tail ∙
              isoComp-cong expandS (idIso tail)))
        firstExchange = isoComp-cong (whisker-mixed-at β f H) (idIso (C′ ∙ (T′ ∙ tail))) ∙
          invIso (isoComp-assoc-at A β′ (C′ ∙ (T′ ∙ tail)))
        secondExchange = isoComp-assoc-at βImage middle (C′ ∙ (T′ ∙ tail))
        useCorner = isoComp-cong (idIso βImage)
          (isoComp-cong corner (idIso (T′ ∙ tail)) ∙
            invIso (isoComp-assoc-at middle C′ (T′ ∙ tail)))
        finishTail = isoComp-cong (idIso βImage)
          (isoComp-cong (idIso (H ◁ invIso inputA))
              (isoComp-cong (idIso nextA)
                  (transport ∙ invIso (isoComp-assoc-at endA T′ tail)) ∙
                isoComp-assoc-at nextA endA (T′ ∙ tail)) ∙
            isoComp-assoc-at (H ◁ invIso inputA) (nextA ∙ endA) (T′ ∙ tail))
    in isoComp-cong (invIso (postWhisker-isoComp-at H (β ▷ f) (invIso inputA))) (idIso (nextA ∙ end)) ∙
      (invIso (isoComp-assoc-at βImage (H ◁ invIso inputA) (nextA ∙ end)) ∙
      (finishTail ∙ (useCorner ∙ (secondExchange ∙ (firstExchange ∙
        (expand ∙ isoComp-cong (idIso A) cancelB))))))
```

The associativity proof reuses the already verified coordinate transport
calculation. Its module carries `M` solely because that helper currently
lives in `ProductSubstitution`; the calculation itself uses only `Theory`.

```agda
module Coherence (M : Mapping.MappingAnimae 𝒯) where
  open ProductSubstitution 𝒯 M using (coordinate-outer-comp)

  abstract
    paste-assoc : {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : CAT}
      {f : MAP A₀ A₁} {g : MAP A₁ A₂} {h : MAP A₂ A₃}
      {F : MAP B₀ B₁} {G : MAP B₁ B₂} {H : MAP B₂ B₃}
      {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂} {x₃ : MAP A₃ B₃}
      (γ : NatIso (x₃ ∘ h) (H ∘ x₂)) (β : NatIso (x₂ ∘ g) (G ∘ x₁))
      (α : NatIso (x₁ ∘ f) (F ∘ x₀))
      → Iso₂
          ((comp-assoc F G H ▷ x₀) ∙ paste (paste γ β) α)
          (paste γ (paste β α) ∙ (x₃ ◁ comp-assoc f g h))
    paste-assoc {f = f} {g} {h} {F} {G} {H} {x₀} {x₁} {x₂} {x₃} γ β α =
      let c = coordinate-comparison x₀ F x₁ f α G
          cHG = coordinate-comparison x₀ F x₁ f α (H ∘ G)
          nested = coordinate-comparison x₀ (G ∘ F) (G ∘ x₁) f c H
          lead = comp-assoc F G H ▷ x₀
          B = comp-assoc x₁ G H ▷ f
          t = transport-pre x₃ (h ∘ g) (paste γ β) f
          tβ = transport-pre x₂ g β f
          tγ = transport-pre x₃ h γ (g ∘ f)
          last = x₃ ◁ comp-assoc f g h
          I = invIso (comp-assoc x₀ (G ∘ F) H)
          A = comp-assoc f (G ∘ x₁) H
          N = comp-assoc (g ∘ f) x₂ H
          hc = H ◁ c
          hβ = H ◁ tβ
          hp = H ◁ paste β α
          start = isoComp-cong (idIso lead) (paste-factor (paste γ β) α)
          outer = isoComp-assoc-at nested B t ∙
            (isoComp-cong (coordinate-outer-comp x₀ F x₁ f α G H) (idIso t) ∙
              invIso (isoComp-assoc-at lead cHG t))
          expand = isoComp-cong (idIso I) (isoComp-assoc-at hc A (B ∙ t)) ∙
            isoComp-assoc-at I (hc ∙ A) (B ∙ t)
          transport = isoComp-cong (idIso I)
            (isoComp-cong (idIso hc) (transport-paste f γ β))
          merge = isoComp-cong (idIso I)
            (isoComp-cong
              ((postWhisker H ◁ invIso (paste-factor β α)) ∙
                invIso (postWhisker-isoComp-at H c tβ))
              (idIso (N ∙ (tγ ∙ last))) ∙
              invIso (isoComp-assoc-at hc hβ (N ∙ (tγ ∙ last))))
          finish = invIso (isoComp-assoc-at I (hp ∙ (N ∙ tγ)) last) ∙
            (isoComp-cong (idIso I)
              (invIso (isoComp-assoc-at hp (N ∙ tγ) last) ∙
                isoComp-cong (idIso hp) (invIso (isoComp-assoc-at N tγ last))))
      in finish ∙ (merge ∙ (transport ∙ (expand ∙ (outer ∙ start))))
```
