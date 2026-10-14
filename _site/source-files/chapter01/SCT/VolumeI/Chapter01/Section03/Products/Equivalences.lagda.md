# Equivalences involving products

Product functors preserve equivalences, and so does postcomposing the two
components of a pairing with equivalences. An equivalence given by a pair of
identification families is transported along squares that change the
endpoints of both families. Applied to the postwhiskering functors, this
shows that postwhiskering by the two components of an equivalence into a
product is jointly an equivalence.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Products.Equivalences where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitʳ; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Products
open Coordinates
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-transport; equiv-compose)
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence using (postWhisker-isEquiv)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
  using (productMap; productMap-id; productMap-comp)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-change-square)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
  using (changeEndpoints₌; changeEndpoints₌-isEquiv; square-to-changeEndpoints₌)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair)
```

```agda
module _ {Γ : Context} where
  productMap-isEquiv : {C C′ D D′ : CAT Γ} (f : MAP C C′) (g : MAP D D′)
    → IsEquiv f → IsEquiv g → IsEquiv (productMap f g)
  productMap-isEquiv {C} {C′} {D} {D′} f g ef eg = record
    { inverse = productMap (IsEquiv.inverse ef) (IsEquiv.inverse eg)
    ; left-inverse-law = (productMap-comp f (IsEquiv.inverse ef) g (IsEquiv.inverse eg)) ⁻¹ ∙
        (productMap-cong (IsEquiv.left-inverse-law ef) (IsEquiv.left-inverse-law eg) ∙
          (productMap-id C D) ⁻¹)
    ; right-inverse-law = (productMap-comp (IsEquiv.inverse ef) f (IsEquiv.inverse eg) g) ⁻¹ ∙
        (productMap-cong (IsEquiv.right-inverse-law ef) (IsEquiv.right-inverse-law eg) ∙
          (productMap-id C′ D′) ⁻¹) }

  pair-post-isEquiv : {A B C D E : CAT Γ} (f : MAP B D) (g : MAP C E)
    (u : MAP A B) (v : MAP A C)
    → IsEquiv f → IsEquiv g → IsEquiv (pair u v) → IsEquiv (pair (f ∘ u) (g ∘ v))
  pair-post-isEquiv f g u v ef eg e = equiv-transport (productMap-pair f g u v)
    (equiv-compose (pair u v) (productMap f g) e (productMap-isEquiv f g ef eg))

  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    pair-squares-isEquiv : {C D C′ D′ : CAT Γ}
      {f₁ f₁′ g₁ g₁′ : MAP C D} {f₂ f₂′ g₂ g₂′ : MAP C′ D′}
      (p₁ : f₁ =₁ f₁′) (q₁ : g₁ =₁ g₁′) (p₂ : f₂ =₁ f₂′) (q₂ : g₂ =₁ g₂′)
      (u₁ : f₁ ＝ g₁) (u₂ : f₂ ＝ g₂)
      (v₁ : f₁′ ＝ g₁′) (v₂ : f₂′ ＝ g₂′)
      → SquareCell₌ u₁ v₁ (const p₁) (const q₁) → SquareCell₌ u₂ v₂ (const p₂) (const q₂)
      → IsEquiv (pair u₁ u₂) → IsEquiv (pair v₁ v₂)
    pair-squares-isEquiv p₁ q₁ p₂ q₂ u₁ u₂ v₁ v₂ κ₁ κ₂ e = equiv-transport
      (pair⁼ (square-to-changeEndpoints₌ p₁ q₁ u₁ v₁ κ₁)
        (square-to-changeEndpoints₌ p₂ q₂ u₂ v₂ κ₂))
      (pair-post-isEquiv (changeEndpoints₌ p₁ q₁) (changeEndpoints₌ p₂ q₂) u₁ u₂
        (changeEndpoints₌-isEquiv p₁ q₁) (changeEndpoints₌-isEquiv p₂ q₂) e)

  paired-postWhisker-isEquiv : {X Y Z T : CAT Γ} (F : MAP X Y) (G : MAP X Z)
    → IsEquiv (pair F G) → (u v : MAP T X)
    → IsEquiv (pair (postWhisker {f = u} {v} F) (postWhisker G))
  paired-postWhisker-isEquiv {X} {Y} {Z} {T} F G e u v =
    let H = pair F G
        bu = (pair-β₁ F G ▷ u) ∙ (comp-assoc u H pr₁) ⁻¹
        bv = (pair-β₁ F G ▷ v) ∙ (comp-assoc v H pr₁) ⁻¹
        cu = (pair-β₂ F G ▷ u) ∙ (comp-assoc u H pr₂) ⁻¹
        cv = (pair-β₂ F G ▷ v) ∙ (comp-assoc v H pr₂) ⁻¹
        leftSquare = comp₌-cong (comp-unitʳ (postWhisker F)) (id₌ (const bu)) ∙
          (restrict-change-square pr₁ H F (pair-β₁ F G) (id (Equal u v)) ∙
            comp₌-cong (id₌ (const bv)) (postWhisker pr₁ ◁ (comp-unitʳ (postWhisker H)) ⁻¹))
        rightSquare = comp₌-cong (comp-unitʳ (postWhisker G)) (id₌ (const cu)) ∙
          (restrict-change-square pr₂ H G (pair-β₂ F G) (id (Equal u v)) ∙
            comp₌-cong (id₌ (const cv)) (postWhisker pr₂ ◁ (comp-unitʳ (postWhisker H)) ⁻¹))
    in pair-squares-isEquiv bu bv cu cv
      (postWhisker pr₁ ∘ postWhisker H) (postWhisker pr₂ ∘ postWhisker H)
      (postWhisker F) (postWhisker G) leftSquare rightSquare
      (equiv-transport (pair-pre (postWhisker pr₁) (postWhisker pr₂) (postWhisker H))
        (equiv-compose (postWhisker H) (product-coordinates (H ∘ u) (H ∘ v))
          (postWhisker-isEquiv H e u v) (product-coordinates-isEquiv (H ∘ u) (H ∘ v))))
```
