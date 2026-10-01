# Interchanging diagram variables and evaluating a boundary

The exponential law exchanges the two variables of an iterated functor
category. The evaluation comparisons proved here are used to identify
functors into a slice with slices of a functor category.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section07.ExponentialLaw as Exponentials

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.DiagramInterchange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public

private
  after : {W A B D : CAT} (h : MAP A B) (π : MAP B D)
    {p : MAP A D} → (π ∘ h) =₁ p → (k : MAP W A) → (π ∘ (h ∘ k)) =₁ (p ∘ k)
  after h π β k = (β ▷ k) ∙ (comp-assoc k h π) ⁻¹

module Flatten (X Y C : CAT) where
  module Exp = Exponentials.ExponentialLaw 𝒯 M ℱ X Y C
    using (forward; forward-β; forward-isEquiv; backward; forward-backward)
  N = Fun X (Fun Y C)
  module Assoc = Associativity N X Y
  double = funUncurry (funEval {X} {Fun Y C})

  module Inner (b : Obj-abs Y) where
    private
      s = productMap (id N) (insert {X = X} b)
      k = Assoc.backward
      parameter : (pr₁ ∘ s) =₁ (pr₁ {N} {X})
      parameter = comp-unitˡ pr₁ ∙ pair-β₁ (id N ∘ pr₁) (insert b ∘ pr₂)
      outer = comp-unitˡ pr₂ ∙
        ((pair-β₁ (id X) (const b) ▷ pr₂) ∙
          ((comp-assoc pr₂ (insert b) pr₁) ⁻¹ ∙
            ((pr₁ ◁ pair-β₂ (id N ∘ pr₁) (insert b ∘ pr₂)) ∙ comp-assoc s pr₂ pr₁)))
      inner = const-pre b pr₂ ∙
        ((pair-β₂ (id X) (const b) ▷ pr₂) ∙
          ((comp-assoc pr₂ (insert b) pr₂) ⁻¹ ∙
            ((pr₂ ◁ pair-β₂ (id N ∘ pr₁) (insert b ∘ pr₂)) ∙ comp-assoc s pr₂ pr₂)))
      first = pair-projections ∙
        (pair-cong parameter outer ∙
          (pair-pre pr₁ (pr₁ ∘ pr₂) s ∙
            after k pr₁ (pair-β₁ (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)) s))
      last = inner ∙ after k pr₂ (pair-β₂ (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)) s

    coordinates : (Assoc.backward ∘ s) =₁ (insert {X = N × X} b)
    coordinates = pair-iso
      ((pair-β₁ (id (N × X)) (const b)) ⁻¹ ∙ first)
      ((pair-β₂ (id (N × X)) (const b)) ⁻¹ ∙ last)

    boundary : (funPre (insert b) ∘ Exp.forward) =₁ (funPost (evaluate b))
    boundary = funReflect _ _
      ((funPost-β (evaluate b)) ⁻¹ ∙
        ((evaluate-uncurry b (funEval {X} {Fun Y C})) ⁻¹ ∙
          ((double ◁ coordinates) ∙
            (comp-assoc s Assoc.backward double ∙
              ((Exp.forward-β ▷ s) ∙ funPre-uncurry (insert b) Exp.forward)))))

  module Outer (b : Obj-abs X) where
    coinsert = pair (const b) (id Y)
    private
      s = productMap (id N) coinsert
      k = Assoc.backward
      parameter : (pr₁ ∘ s) =₁ (pr₁ {N} {Y})
      parameter = comp-unitˡ pr₁ ∙ pair-β₁ (id N ∘ pr₁) (coinsert ∘ pr₂)
      outer = const-pre b pr₂ ∙
        ((pair-β₁ (const b) (id Y) ▷ pr₂) ∙
          ((comp-assoc pr₂ coinsert pr₁) ⁻¹ ∙
            ((pr₁ ◁ pair-β₂ (id N ∘ pr₁) (coinsert ∘ pr₂)) ∙ comp-assoc s pr₂ pr₁)))
      inner = comp-unitˡ pr₂ ∙
        ((pair-β₂ (const b) (id Y) ▷ pr₂) ∙
          ((comp-assoc pr₂ coinsert pr₂) ⁻¹ ∙
            ((pr₂ ◁ pair-β₂ (id N ∘ pr₁) (coinsert ∘ pr₂)) ∙ comp-assoc s pr₂ pr₂)))
      first = pair-cong parameter outer ∙
        (pair-pre pr₁ (pr₁ ∘ pr₂) s ∙
          after k pr₁ (pair-β₁ (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)) s)
      last = inner ∙ after k pr₂ (pair-β₂ (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)) s
      first-target : (insert b ∘ pr₁ {N} {Y}) =₁ (pair pr₁ (const b))
      first-target = pair-cong (comp-unitˡ pr₁) (const-pre b pr₁) ∙
        pair-pre (id N) (const b) pr₁
      step = productMap (insert {X = N} b) (id Y)

    coordinates : (Assoc.backward ∘ s) =₁ step
    coordinates = pair-iso
      ((pair-β₁ (insert b ∘ pr₁) (id Y ∘ pr₂)) ⁻¹ ∙ (first-target ⁻¹ ∙ first))
      ((pair-β₂ (insert b ∘ pr₁) (id Y ∘ pr₂)) ⁻¹ ∙ ((comp-unitˡ pr₂) ⁻¹ ∙ last))

    boundary : (funPre coinsert ∘ Exp.forward) =₁ (evaluate b)
    boundary = funReflect _ _
      ((funUncurry-restrict (funEval {X} {Fun Y C}) (insert b)) ⁻¹ ∙
        ((double ◁ coordinates) ∙
          (comp-assoc s Assoc.backward double ∙
            ((Exp.forward-β ▷ s) ∙ funPre-uncurry coinsert Exp.forward))))

module Exchange (X Y C : CAT) where
  module Source = Flatten X Y C
  module Target = Flatten Y X C
  open Source.Exp using () renaming (forward to f)
  open Target.Exp using () renaming (forward to g; backward to h)
  swap-diagrams : MAP (Fun (X × Y) C) (Fun (Y × X) C)
  swap-diagrams = funPre swap
  forward : MAP (Fun X (Fun Y C)) (Fun Y (Fun X C))
  forward = h ∘ (swap-diagrams ∘ f)

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = equiv-compose (swap-diagrams ∘ f) h
    (equiv-compose f swap-diagrams Source.Exp.forward-isEquiv
      (funPre-isEquiv swap (swap-isEquiv Y X)))
    (equiv-cancel-left h g Target.Exp.forward-isEquiv
      (equiv-transport (Target.Exp.forward-backward ⁻¹) (id-isEquiv (Fun (Y × X) C))))

  module At (b : Obj-abs Y) where
    module Boundary = Target.Outer b
    private
      co = Boundary.coinsert
      p = funPre {D = C} (insert {X = X} b)
      q = funPre {D = C} co
      coordinate : (swap {Y} {X} ∘ co) =₁ (insert {X = X} b)
      coordinate = pair-cong (pair-β₂ (const b) (id X)) (pair-β₁ (const b) (id X)) ∙
        pair-pre pr₂ pr₁ co
      restriction : (q ∘ swap-diagrams) =₁ p
      restriction = funPre-cong coordinate ∙ funPre-comp co swap
      flattened : (g ∘ forward) =₁ (swap-diagrams ∘ f)
      flattened = comp-unitˡ (swap-diagrams ∘ f) ∙
        ((Target.Exp.forward-backward ▷ (swap-diagrams ∘ f)) ∙
          (comp-assoc (swap-diagrams ∘ f) h g) ⁻¹)

    boundary : (evaluate b ∘ forward) =₁ (funPost (evaluate b))
    boundary = Source.Inner.boundary b ∙
      ((restriction ▷ f) ∙
        ((comp-assoc f swap-diagrams q) ⁻¹ ∙
          ((q ◁ flattened) ∙
            (comp-assoc forward g q ∙ (Boundary.boundary ⁻¹ ▷ forward)))))

  module Other (b : Obj-abs X) where
    module Boundary = Source.Outer b
    private
      co = Boundary.coinsert
      p = funPre {D = C} co
      q = funPre {D = C} (insert {X = Y} b)
      coordinate : (swap {Y} {X} ∘ insert {X = Y} b) =₁ co
      coordinate = pair-cong (pair-β₂ (id Y) (const b)) (pair-β₁ (id Y) (const b)) ∙
        pair-pre pr₂ pr₁ (insert b)
      restriction : (q ∘ swap-diagrams) =₁ p
      restriction = funPre-cong coordinate ∙ funPre-comp (insert b) swap
      flattened : (g ∘ forward) =₁ (swap-diagrams ∘ f)
      flattened = comp-unitˡ (swap-diagrams ∘ f) ∙
        ((Target.Exp.forward-backward ▷ (swap-diagrams ∘ f)) ∙
          (comp-assoc (swap-diagrams ∘ f) h g) ⁻¹)

    boundary : (funPost (evaluate b) ∘ forward) =₁ (evaluate b)
    boundary = Boundary.boundary ∙
      ((restriction ▷ f) ∙
        ((comp-assoc f swap-diagrams q) ⁻¹ ∙
          ((q ◁ flattened) ∙
            (comp-assoc forward g q ∙ (Target.Inner.boundary b ⁻¹ ▷ forward)))))
```
