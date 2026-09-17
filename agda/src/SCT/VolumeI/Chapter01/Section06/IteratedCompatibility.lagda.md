# Transferring iterated substitution through evaluation

The calculation in this module isolates the exact product associativity
comparison needed for iterated uncurrying. Its final transfer theorem is
conditional on that explicitly displayed comparison; the condition is not
an added axiom of the theory.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section06.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section06.IteratedCompatibility
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M) where

open Setup 𝒯 M ℱ



open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered; pre-inverse-at; solve-pentagon; mixed-at)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (move-square)
import SCT.VolumeI.Chapter01.Section02.Parameterized as Parameterized
open Parameterized.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
  using (postWhisker-comp-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (reassociateFour)

exchange-middle : {X Y : CAT} {a b c d e c′ : MAP X Y}
  (δ : NatIso d e) (γ : NatIso c d) (β : NatIso b c) (α : NatIso a b)
  (γ′ : NatIso c′ d) (β′ : NatIso b c′)
  → Iso₂ (γ ∙ β) (γ′ ∙ β′)
  → Iso₂ ((δ ∙ γ) ∙ (β ∙ α)) ((δ ∙ γ′) ∙ (β′ ∙ α))
exchange-middle δ γ β α γ′ β′ p =
  invIso (reassociateFour δ γ′ β′ α) ∙
    (isoComp-cong (idIso δ) (isoComp-cong p (idIso α)) ∙ reassociateFour δ γ β α)

evaluation-step : {R X Z D : CAT} (e : MAP Z D) (p : MAP X Z) (s : MAP R X)
  {q : MAP R Z} → NatIso q (p ∘ s) → NatIso (e ∘ q) ((e ∘ p) ∘ s)
evaluation-step e p s a = invIso (comp-assoc s p e) ∙ (e ◁ a)

evaluation-step-iterated : {Q R X Z D : CAT}
  (e : MAP Z D) (p : MAP X Z) (s : MAP R X) (t : MAP Q R)
  {q : MAP R Z} {r : MAP Q Z} (a : NatIso q (p ∘ s)) (b : NatIso r (q ∘ t))
  → Iso₂
      (comp-assoc t s (e ∘ p) ∙
        ((evaluation-step e p s a ▷ t) ∙ evaluation-step e q t b))
      (invIso (comp-assoc (s ∘ t) p e) ∙
        (e ◁ (comp-assoc t s p ∙ ((a ▷ t) ∙ b))))
evaluation-step-iterated e p s t {q} {r} a b =
  let A = comp-assoc t s (e ∘ p)
      B = invIso (comp-assoc s p e) ▷ t
      C = (e ◁ a) ▷ t
      D = invIso (comp-assoc t q e)
      E = e ◁ b
      D′ = invIso (comp-assoc t (p ∘ s) e)
      C′ = e ◁ (a ▷ t)
      total = invIso (comp-assoc (s ∘ t) p e)
      inner = comp-assoc t s p
      exchange = invIso (move-square (comp-assoc t (p ∘ s) e)
        C C′ (comp-assoc t q e) (mixed-at e a t))
      pentagon = solve-pentagon (comp-assoc (s ∘ t) p e) A
        (e ◁ inner) (comp-assoc t (p ∘ s) e) (comp-assoc s p e ▷ t)
        (pentagon-whiskered t s p e) ∙
        isoComp-cong (idIso A) (isoComp-cong (pre-inverse-at (comp-assoc s p e) t) (idIso D′))
  in isoComp-cong (idIso total)
      (invIso (postWhisker-isoComp-at e inner ((a ▷ t) ∙ b)) ∙
        isoComp-cong (idIso (e ◁ inner)) (invIso (postWhisker-isoComp-at e (a ▷ t) b))) ∙
    (isoComp-assoc-at total (e ◁ inner) (C′ ∙ E) ∙
    (isoComp-cong pentagon (idIso (C′ ∙ E)) ∙
    (invIso (isoComp-assoc-at A (B ∙ D′) (C′ ∙ E)) ∙
    (isoComp-cong (idIso A) (exchange-middle B C D E D′ C′ exchange) ∙
      isoComp-cong (idIso A)
        (isoComp-cong (preWhisker-isoComp-at (invIso (comp-assoc s p e)) (e ◁ a) t)
          (idIso (D ∙ E)))))))

module Iteration {W Y X C D : CAT}
  (f : MAP X (Fun C D)) (σ : MAP Y X) (τ : MAP W Y) where

  F : {A B : CAT} → MAP A B → MAP (A × C) (B × C)
  F h = productMap h (id C)

  κ : {A B Z : CAT} (h : MAP B Z) (r : MAP A B)
    → NatIso (F h ∘ F r) (F (h ∘ r))
  κ = slice-comparison

  ProductAssociativity : Set m
  ProductAssociativity = Iso₂
    (κ f (σ ∘ τ) ∙ ((F f ◁ κ σ τ) ∙ comp-assoc (F τ) (F σ) (F f)))
    (productMap-cong (comp-assoc τ σ f) (idIso (id C)) ∙
      (κ (f ∘ σ) τ ∙ (κ f σ ▷ F τ)))

  together : NatIso (funUncurry ((f ∘ σ) ∘ τ)) (funUncurry f ∘ F (σ ∘ τ))
  together = funUncurry-pre f (σ ∘ τ) ∙ funUncurryIso (comp-assoc τ σ f)

  successively : NatIso (funUncurry ((f ∘ σ) ∘ τ)) (funUncurry f ∘ F (σ ∘ τ))
  successively = (funUncurry f ◁ κ σ τ) ∙
    (comp-assoc (F τ) (F σ) (funUncurry f) ∙
      ((funUncurry-pre f σ ▷ F τ) ∙ funUncurry-pre (f ∘ σ) τ))

  transfer : ProductAssociativity → Iso₂ together successively
  transfer product-assoc = invIso
    (isoComp-cong (idIso (funUncurry-pre f (σ ∘ τ))) (invIso (funUncurryIso-at (comp-assoc τ σ f))) ∙
    let p = F f
        s = F σ
        t = F τ
        e = funEval
        k = κ σ τ
        a = invIso (κ f σ)
        b = invIso (κ (f ∘ σ) τ)
        inner = comp-assoc t s p ∙ ((a ▷ t) ∙ b)
        outside = invIso (comp-assoc (F (σ ∘ τ)) p e)
        middle = invIso (comp-assoc (s ∘ t) p e)
        whiskered-k = p ◁ k
        associator = productMap-cong (comp-assoc τ σ f) (idIso (id C))
        commute = invIso (move-square (comp-assoc (F (σ ∘ τ)) p e)
          (funUncurry f ◁ k) (e ◁ whiskered-k) (comp-assoc (s ∘ t) p e)
          (postWhisker-comp-at k p e))
        solve = solve-pentagon (κ f (σ ∘ τ)) (whiskered-k ∙ comp-assoc t s p)
          associator (κ (f ∘ σ) τ) (κ f σ ▷ t) product-assoc ∙
          (invIso (isoComp-assoc-at whiskered-k (comp-assoc t s p)
            (invIso (κ f σ ▷ t) ∙ b)) ∙
            isoComp-cong (idIso whiskered-k)
              (isoComp-cong (idIso (comp-assoc t s p))
                (isoComp-cong (pre-inverse-at (κ f σ) t) (idIso b))))
    in invIso (isoComp-assoc-at outside (e ◁ invIso (κ f (σ ∘ τ))) (e ◁ associator)) ∙
      (isoComp-cong (idIso outside) (postWhisker-isoComp-at e (invIso (κ f (σ ∘ τ))) associator) ∙
      (isoComp-cong (idIso outside) (postWhisker e ◁ solve) ∙
      (isoComp-cong (idIso outside) (invIso (postWhisker-isoComp-at e whiskered-k inner)) ∙
      (isoComp-assoc-at outside (e ◁ whiskered-k) (e ◁ inner) ∙
      (isoComp-cong commute (idIso (e ◁ inner)) ∙
      (invIso (isoComp-assoc-at (funUncurry f ◁ k) middle (e ◁ inner)) ∙
        isoComp-cong (idIso (funUncurry f ◁ k))
          (evaluation-step-iterated e p s t a b))))))))
```

