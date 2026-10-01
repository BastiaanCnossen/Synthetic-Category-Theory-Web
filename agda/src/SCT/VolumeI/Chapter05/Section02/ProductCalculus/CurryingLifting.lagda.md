# Lifting along an equivalence obtained by currying

Suppose the curry of a local functor is an equivalence. Every local
family with a weakened parameter then lifts through that functor. The
comparison below computes the image of the selected lift. It applies to
both identification comparisons of the dependent universal properties.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as ProductAction
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus

module SCT.VolumeI.Chapter05.Section02.ProductCalculus.CurryingLifting
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Products.DependentProducts P
open ProductAction W P using (curry-cong; curry-pre)
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)

module Along {X : S.CAT} {Y : T.CAT} (f : T.MAP (W.cat X) Y)
  (e : S.IsEquiv (curry f)) where

  lift : {R : S.CAT} → T.MAP (W.cat R) Y → S.MAP R X
  lift g = S._∘_ (S.IsEquiv.inverse e) (curry g)

  cancel : {R : S.CAT} (g : T.MAP (W.cat R) Y)
    → S._=₁_ (S._∘_ (curry f) (lift g)) (curry g)
  cancel g = S._∙_ (S.comp-unitˡ (curry g))
    (S._∙_ (S._▷_ (S._⁻¹ (S.IsEquiv.retractionIso e)) (curry g))
      (S._⁻¹ (S.comp-assoc (curry g) (S.IsEquiv.inverse e) (curry f))))

  lift-β : {R : S.CAT} (g : T.MAP (W.cat R) Y)
    → T._=₁_ (f ∘ W.map (lift g)) g
  lift-β g = (curry-β f ▷ W.map (lift g)) then
    T.comp-assoc (W.map (lift g)) (W.map (curry f)) (evaluation Y) then
    (evaluation Y ◁ (W.comp (lift g) (curry f)) ⁻¹) then
    (evaluation Y ◁ W.term (cancel g)) then (curry-β g) ⁻¹

  lift-η : {R : S.CAT} (h : S.MAP R X) → S._=₁_ (lift (f ∘ W.map h)) h
  lift-η h = S._∙_ (S.comp-unitˡ h)
    (S._∙_ (S._▷_ (S._⁻¹ (S.IsEquiv.sectionIso e)) h)
      (S._∙_ (S._⁻¹ (S.comp-assoc h (curry f) (S.IsEquiv.inverse e)))
        (S._◁_ (S.IsEquiv.inverse e) (curry-pre f h))))

  lift-cong : {R : S.CAT} {g h : T.MAP (W.cat R) Y}
    → T._=₁_ g h → S._=₁_ (lift g) (lift h)
  lift-cong α = S._◁_ (S.IsEquiv.inverse e) (curry-cong α)

  reflect : {R : S.CAT} {g h : S.MAP R X}
    → T._=₁_ (f ∘ W.map g) (f ∘ W.map h) → S._=₁_ g h
  reflect {g = g} {h} α = S._∙_ (lift-η h) (S._∙_ (lift-cong α) (S._⁻¹ (lift-η g)))

  point : T.Obj-abs Y → S.Obj-abs X
  point α = lift (α ∘ T.terminate (W.cat S.One))

  point-β : (α : T.Obj-abs Y) → T._=₁_ ((f ∘ W.map (point α)) ∘ W.back) α
  point-β α = (lift-β (α ∘ T.terminate (W.cat S.One)) ▷ W.back) then
    T.comp-assoc W.back (T.terminate (W.cat S.One)) α then
    (α ◁ T.terminal-iso _ (T.id T.One)) then T.comp-unitʳ α
```
