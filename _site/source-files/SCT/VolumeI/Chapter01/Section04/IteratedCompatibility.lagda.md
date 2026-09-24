# Transferring iterated substitution through evaluation

The calculation in this module isolates the exact product associativity
comparison needed for iterated uncurrying. Its final transfer theorem is
conditional on that explicitly displayed comparison; the condition is not
an added axiom of the theory.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section03.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section04.IteratedCompatibility
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open Currying 𝒯 M
open Compatibility 𝒯 M
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered; pre-inverse-at; solve-pentagon; mixed-at)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (move-square)
import SCT.VolumeI.Chapter01.Section03.Parameterized as Parameterized
open Parameterized.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
  using (postWhisker-comp-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (reassociateFour)

exchange-middle : {X Y : CAT} {a b c d e c′ : MAP X Y}
  (δ : d =₁ e) (γ : c =₁ d) (β : b =₁ c) (α : a =₁ b)
  (γ′ : c′ =₁ d) (β′ : b =₁ c′)
  → (γ ∙ β) =₂ (γ′ ∙ β′)
  → ((δ ∙ γ) ∙ (β ∙ α)) =₂ ((δ ∙ γ′) ∙ (β′ ∙ α))
exchange-middle δ γ β α γ′ β′ p =
  (reassociateFour δ γ′ β′ α) ⁻¹ ∙
    (isoComp-cong (idIso δ) (isoComp-cong p (idIso α)) ∙ reassociateFour δ γ β α)

evaluation-step : {R X Z D : CAT} (e : MAP Z D) (p : MAP X Z) (s : MAP R X)
  {q : MAP R Z} → q =₁ (p ∘ s) → (e ∘ q) =₁ ((e ∘ p) ∘ s)
evaluation-step e p s a = (comp-assoc s p e) ⁻¹ ∙ (e ◁ a)

evaluation-step-iterated : {Q R X Z D : CAT}
  (e : MAP Z D) (p : MAP X Z) (s : MAP R X) (t : MAP Q R)
  {q : MAP R Z} {r : MAP Q Z} (a : q =₁ (p ∘ s)) (b : r =₁ (q ∘ t))
  →
      (comp-assoc t s (e ∘ p) ∙
        ((evaluation-step e p s a ▷ t) ∙ evaluation-step e q t b)) =₂
      ((comp-assoc (s ∘ t) p e) ⁻¹ ∙
        (e ◁ (comp-assoc t s p ∙ ((a ▷ t) ∙ b))))
evaluation-step-iterated e p s t {q} {r} a b =
  let A = comp-assoc t s (e ∘ p)
      B = (comp-assoc s p e) ⁻¹ ▷ t
      C = (e ◁ a) ▷ t
      D = (comp-assoc t q e) ⁻¹
      E = e ◁ b
      D′ = (comp-assoc t (p ∘ s) e) ⁻¹
      C′ = e ◁ (a ▷ t)
      total = (comp-assoc (s ∘ t) p e) ⁻¹
      inner = comp-assoc t s p
      exchange = (move-square (comp-assoc t (p ∘ s) e)
        C C′ (comp-assoc t q e) (mixed-at e a t)) ⁻¹
      pentagon = solve-pentagon (comp-assoc (s ∘ t) p e) A
        (e ◁ inner) (comp-assoc t (p ∘ s) e) (comp-assoc s p e ▷ t)
        (pentagon-whiskered t s p e) ∙
        isoComp-cong (idIso A) (isoComp-cong (pre-inverse-at (comp-assoc s p e) t) (idIso D′))
  in isoComp-cong (idIso total)
      ((postWhisker-isoComp-at e inner ((a ▷ t) ∙ b)) ⁻¹ ∙
        isoComp-cong (idIso (e ◁ inner)) ((postWhisker-isoComp-at e (a ▷ t) b) ⁻¹)) ∙
    (isoComp-assoc-at total (e ◁ inner) (C′ ∙ E) ∙
    (isoComp-cong pentagon (idIso (C′ ∙ E)) ∙
    ((isoComp-assoc-at A (B ∙ D′) (C′ ∙ E)) ⁻¹ ∙
    (isoComp-cong (idIso A) (exchange-middle B C D E D′ C′ exchange) ∙
      isoComp-cong (idIso A)
        (isoComp-cong (preWhisker-isoComp-at ((comp-assoc s p e) ⁻¹) (e ◁ a) t)
          (idIso (D ∙ E)))))))

module Iteration {W Y X C D : CAT}
  (f : MAP X (Map C D)) (σ : MAP Y X) (τ : MAP W Y) where

  F : {A B : CAT} → MAP A B → MAP (A × C) (B × C)
  F h = productMap h (id C)

  κ : {A B Z : CAT} (h : MAP B Z) (r : MAP A B)
    → (F h ∘ F r) =₁ (F (h ∘ r))
  κ = slice-comparison

  ProductAssociativity : Set m
  ProductAssociativity =
    (κ f (σ ∘ τ) ∙ ((F f ◁ κ σ τ) ∙ comp-assoc (F τ) (F σ) (F f))) =₂
    (productMap-cong (comp-assoc τ σ f) (idIso (id C)) ∙
      (κ (f ∘ σ) τ ∙ (κ f σ ▷ F τ)))

  together : (mapUncurry ((f ∘ σ) ∘ τ)) =₁ (mapUncurry f ∘ F (σ ∘ τ))
  together = mapUncurry-restrict f (σ ∘ τ) ∙ mapUncurryIso (comp-assoc τ σ f)

  successively : (mapUncurry ((f ∘ σ) ∘ τ)) =₁ (mapUncurry f ∘ F (σ ∘ τ))
  successively = (mapUncurry f ◁ κ σ τ) ∙
    (comp-assoc (F τ) (F σ) (mapUncurry f) ∙
      ((mapUncurry-restrict f σ ▷ F τ) ∙ mapUncurry-restrict (f ∘ σ) τ))

  transfer : ProductAssociativity → together =₂ successively
  transfer product-assoc =
    (isoComp-cong (idIso (mapUncurry-restrict f (σ ∘ τ))) ((mapUncurry-actions-agree (comp-assoc τ σ f)) ⁻¹) ∙
    let p = F f
        s = F σ
        t = F τ
        e = mapEval
        k = κ σ τ
        a = (κ f σ) ⁻¹
        b = (κ (f ∘ σ) τ) ⁻¹
        inner = comp-assoc t s p ∙ ((a ▷ t) ∙ b)
        outside = (comp-assoc (F (σ ∘ τ)) p e) ⁻¹
        middle = (comp-assoc (s ∘ t) p e) ⁻¹
        whiskered-k = p ◁ k
        associator = productMap-cong (comp-assoc τ σ f) (idIso (id C))
        commute = (move-square (comp-assoc (F (σ ∘ τ)) p e)
          (mapUncurry f ◁ k) (e ◁ whiskered-k) (comp-assoc (s ∘ t) p e)
          (postWhisker-comp-at k p e)) ⁻¹
        solve = solve-pentagon (κ f (σ ∘ τ)) (whiskered-k ∙ comp-assoc t s p)
          associator (κ (f ∘ σ) τ) (κ f σ ▷ t) product-assoc ∙
          ((isoComp-assoc-at whiskered-k (comp-assoc t s p)
            ((κ f σ ▷ t) ⁻¹ ∙ b)) ⁻¹ ∙
            isoComp-cong (idIso whiskered-k)
              (isoComp-cong (idIso (comp-assoc t s p))
                (isoComp-cong (pre-inverse-at (κ f σ) t) (idIso b))))
    in (isoComp-assoc-at outside (e ◁ (κ f (σ ∘ τ)) ⁻¹) (e ◁ associator)) ⁻¹ ∙
      (isoComp-cong (idIso outside) (postWhisker-isoComp-at e ((κ f (σ ∘ τ)) ⁻¹) associator) ∙
      (isoComp-cong (idIso outside) (postWhisker e ◁ solve) ∙
      (isoComp-cong (idIso outside) ((postWhisker-isoComp-at e whiskered-k inner) ⁻¹) ∙
      (isoComp-assoc-at outside (e ◁ whiskered-k) (e ◁ inner) ∙
      (isoComp-cong commute (idIso (e ◁ inner)) ∙
      ((isoComp-assoc-at (mapUncurry f ◁ k) middle (e ◁ inner)) ⁻¹ ∙
        isoComp-cong (idIso (mapUncurry f ◁ k))
          (evaluation-step-iterated e p s t a b)))))))) ⁻¹
```
