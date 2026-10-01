# Postcomposition under dependent uncurrying

The comparison with postcomposition is natural on identifications. Its
proof uses the comparison for whiskering, the evaluation identification
of the dependent product, and interchange in the local theory.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductIdentifications as Identifications
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing

module SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductPostcomposition
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (P : Products.DependentProducts W) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Products.DependentProducts P using (Π; evaluation; uncurry)
open Action W P using (Π-map; Π-map-β; uncurry-pre)
open Identifications W K P using (action)
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T
open Pairing T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering
  using (move-square)

paste : {C D : T.CAT} {x₀ x₁ y₀ y₁ z₀ z₁ : T.MAP C D}
  (u₀ : T._=₁_ x₀ y₀) (u₁ : T._=₁_ x₁ y₁)
  (v₀ : T._=₁_ y₀ z₀) (v₁ : T._=₁_ y₁ z₁)
  (α : T._=₁_ x₀ x₁) (β : T._=₁_ y₀ y₁) (γ : T._=₁_ z₀ z₁)
  → T._=₂_ (u₁ ∙ α) (β ∙ u₀) → T._=₂_ (v₁ ∙ β) (γ ∙ v₀)
  → T._=₂_ ((v₁ ∙ u₁) ∙ α) (γ ∙ (v₀ ∙ u₀))
paste u₀ u₁ v₀ v₁ α β γ p q = isoComp-assoc-at v₁ u₁ α then
  isoComp-cong (T.idIso _) p then (isoComp-assoc-at v₁ β u₀) ⁻¹ then
  isoComp-cong q (T.idIso _) then isoComp-assoc-at γ v₀ u₀

post-square : {C D E : T.CAT} {x₀ x₁ y₀ y₁ : T.MAP C D}
  (u : T.MAP D E) (p : T._=₁_ x₀ y₀) (q : T._=₁_ x₁ y₁)
  (α : T._=₁_ x₀ x₁) (β : T._=₁_ y₀ y₁)
  → T._=₂_ (q ∙ α) (β ∙ p)
  → T._=₂_ ((u ◁ q) ∙ (u ◁ α)) ((u ◁ β) ∙ (u ◁ p))
post-square u p q α β s = (postWhisker-isoComp-at u q α) ⁻¹ then
  (T.postWhisker u ◁ s) then postWhisker-isoComp-at u β p

comparison : {X : S.CAT} {B C : T.CAT} (f : T.MAP B C) (h : S.MAP X (Π B))
  → T._=₁_ (uncurry (S._∘_ (Π-map f) h)) (f ∘ uncurry h)
comparison {B = B} f h =
  T.comp-assoc (W.map h) (evaluation B) f ∙
    (((Π-map-β f) ⁻¹ ▷ W.map h) ∙ uncurry-pre (Π-map f) h)

naturality : {X : S.CAT} {B C : T.CAT} (f : T.MAP B C)
  {h k : S.MAP X (Π B)} (α : S._=₁_ h k)
  → T._=₂_ (comparison f k ∙ action (S._◁_ (Π-map f) α))
      ((f ◁ action α) ∙ comparison f h)
naturality {B = B} {C} f {h} {k} α =
  isoComp-cong ((isoComp-assoc-at dk bk ak) ⁻¹) (T.idIso a₀) then
  paste ah ak (dh ∙ bh) (dk ∙ bk) a₀ a₂ a₄
    first (paste bh bk dh dk a₂ a₃ a₄
      (interchange-at ((Π-map-β f) ⁻¹) (W.term α))
      (postWhisker-comp-at (W.term α) (evaluation B) f)) then
  isoComp-cong (T.idIso a₄) (isoComp-assoc-at dh bh ah)
  where
  e = evaluation C
  m = W.map (Π-map f)
  a₀ = action (S._◁_ (Π-map f) α)
  a₁ = e ◁ (m ◁ W.term α)
  a₂ = (e ∘ m) ◁ W.term α
  a₃ = (f ∘ evaluation B) ◁ W.term α
  a₄ = f ◁ action α
  ch = e ◁ W.comp h (Π-map f)
  ck = e ◁ W.comp k (Π-map f)
  rh = (T.comp-assoc (W.map h) m e) ⁻¹
  rk = (T.comp-assoc (W.map k) m e) ⁻¹
  ah = uncurry-pre (Π-map f) h
  ak = uncurry-pre (Π-map f) k
  bh = (Π-map-β f) ⁻¹ ▷ W.map h
  bk = (Π-map-β f) ⁻¹ ▷ W.map k
  dh = T.comp-assoc (W.map h) (evaluation B) f
  dk = T.comp-assoc (W.map k) (evaluation B) f
  first = paste ch ck rh rk a₀ a₁ a₂
    (post-square e (W.comp h (Π-map f)) (W.comp k (Π-map f))
      (W.term (S._◁_ (Π-map f) α)) (m ◁ W.term α)
      (Operations.post-term-square W K (Π-map f) α))
    (move-square (T.comp-assoc (W.map k) m e) a₂ a₁
      (T.comp-assoc (W.map h) m e) (postWhisker-comp-at (W.term α) m e))
```
