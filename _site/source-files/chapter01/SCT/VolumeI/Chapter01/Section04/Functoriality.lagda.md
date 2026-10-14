# Functoriality of mapping animae

Fixed external functors induce postcomposition and precomposition on mapping
animae. Their defining beta identifications compute uncurrying at any source;
reflection occurs at the mapping anima, not at an arbitrary testing category.
The actions on varying external arrows retain the same curried formulas.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.Functoriality where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Currying
open import SCT.VolumeI.Chapter01.Section04.Points using (name)
import SCT.VolumeI.Chapter01.Section02.Naturality as N

module _ {Γ : Context} where
  mapPost : {C D E : CAT Γ} → MAP D E → MAP (Map C D) (Map C E)
  mapPost {C} {D} g = mapCurry (map-isAn C D) (g ∘ mapEval)

  mapPre : {B C D : CAT Γ} → MAP B C → MAP (Map C D) (Map B D)
  mapPre {C = C} {D} f = mapCurry (map-isAn C D)
    (mapEval ∘ productMap (id (Map C D)) f)

  mapPost-β : {C D E : CAT Γ} (g : MAP D E)
    → (uncurry (mapPost {C = C} g)) =₁ (g ∘ mapEval)
  mapPost-β {C} {D} g = mapCurry-β (map-isAn C D) (g ∘ mapEval)

  mapPre-β : {B C D : CAT Γ} (f : MAP B C)
    → (uncurry (mapPre {D = D} f)) =₁
        (mapEval ∘ productMap (id (Map C D)) f)
  mapPre-β {C = C} {D} f = mapCurry-β (map-isAn C D)
    (mapEval ∘ productMap (id (Map C D)) f)

  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    mapPost⁼ : {C D E : CAT Γ} {f g : MAP D E}
      → f ＝ g → mapPost {C = C} f ＝ mapPost g
    mapPost⁼ {C} {D} α = curry⁼ (map-isAn C D) (α ▷ mapEval)

    mapPre⁼ : {B C D : CAT Γ} {f g : MAP B C}
      → f ＝ g → mapPre {D = D} f ＝ mapPre g
    mapPre⁼ {C = C} {D} α = curry⁼ (map-isAn C D)
      (mapEval ◁ productMap-cong (const (id₌ (id (Map C D)))) α)

    mapPost-β-natural : {C D E : CAT Γ} {f g : MAP D E} (α : f ＝ g)
      → SquareCell₌ (uncurry⁼ (mapPost⁼ {C = C} α)) (α ▷ mapEval)
          (const (mapPost-β f)) (const (mapPost-β g))
    mapPost-β-natural {C} {D} α = curry⁼-evaluation (map-isAn C D) (α ▷ mapEval)

    mapPre-β-natural : {B C D : CAT Γ} {f g : MAP B C} (α : f ＝ g)
      → SquareCell₌ (uncurry⁼ (mapPre⁼ {D = D} α))
          (mapEval ◁ productMap-cong (const (id₌ (id (Map C D)))) α)
          (const (mapPre-β f)) (const (mapPre-β g))
    mapPre-β-natural {C = C} {D} α = curry⁼-evaluation (map-isAn C D)
      (mapEval ◁ productMap-cong (const (id₌ (id (Map C D)))) α)

  mapPost-uncurry : {X C D E : CAT Γ} (g : MAP D E) (h : MAP X (Map C D))
    → (uncurry (mapPost g ∘ h)) =₁ (g ∘ uncurry h)
  mapPost-uncurry {C = C} g h =
    comp-assoc (productMap h (id C)) mapEval g ∙
      ((mapPost-β g ▷ productMap h (id C)) ∙ uncurry-restrict (mapPost g) h)
```

Precomposition changes the second coordinate; productMap-separate, in the
product calculus, compares its order with a change in the first coordinate.

```agda
module _ {Γ : Context} where
  mapPre-uncurry : {X B C D : CAT Γ} (f : MAP B C) (h : MAP X (Map C D))
    → (uncurry (mapPre f ∘ h)) =₁
        (uncurry h ∘ productMap (id X) f)
  mapPre-uncurry {X} {B} {C} {D} f h =
    (comp-assoc (productMap (id X) f) (productMap h (id C)) mapEval) ⁻¹ ∙
    ((mapEval ◁ productMap-separate h f) ∙
    (comp-assoc (productMap h (id B)) (productMap (id (Map C D)) f) mapEval ∙
    ((mapPre-β f ▷ productMap h (id B)) ∙ uncurry-restrict (mapPre f) h)))
```

Identity and composition laws follow by uncurrying and reflection through
the specified action on an anima of parameters.

```agda
module _ {Γ : Context} where
  mapPost-id : (C D : CAT Γ) → (mapPost {C = C} (id D)) =₁ (id (Map C D))
  mapPost-id C D = uncurry-reflect (map-isAn C D) _ _
    ((uncurry-id C D) ⁻¹ ∙ (comp-unitˡ mapEval ∙ mapPost-β (id D)))

  mapPre-id : (C D : CAT Γ) → (mapPre {D = D} (id C)) =₁ (id (Map C D))
  mapPre-id C D = uncurry-reflect (map-isAn C D) _ _
    ((uncurry-id C D) ⁻¹ ∙
      (comp-unitʳ mapEval ∙ ((mapEval ◁ productMap-id (Map C D) C) ∙ mapPre-β (id C))))

  mapPost-comp : {A B C D : CAT Γ} (f : MAP B C) (g : MAP C D)
    → (mapPost {C = A} g ∘ mapPost f) =₁ (mapPost (g ∘ f))
  mapPost-comp {A} {B} f g = uncurry-reflect (map-isAn A B) _ _
    ((mapPost-β (g ∘ f)) ⁻¹ ∙
    ((comp-assoc mapEval f g) ⁻¹ ∙
    ((g ◁ mapPost-β f) ∙ mapPost-uncurry g (mapPost f))))

  mapPre-comp : {A B C D : CAT Γ} (f : MAP A B) (g : MAP B C)
    → (mapPre {D = D} f ∘ mapPre g) =₁ (mapPre (g ∘ f))
  mapPre-comp {C = C} {D} f g = uncurry-reflect (map-isAn C D) _ _
    ((mapPre-β (g ∘ f)) ⁻¹ ∙
    ((mapEval ◁ (productMap-cong (comp-unitˡ (id (Map C D))) (id₌ (g ∘ f)) ∙
       productMap-comp (id (Map C D)) (id (Map C D)) f g)) ∙
    (comp-assoc (productMap (id (Map C D)) f) (productMap (id (Map C D)) g) mapEval ∙
    ((mapPre-β g ▷ productMap (id (Map C D)) f) ∙ mapPre-uncurry f (mapPre g)))))
```

A chosen inverse induces the inverse on mapping animae, with both
identifications constructed from the preceding composition and identity laws.

```agda
module _ {Γ : Context} where
  mapPost-isEquiv : {A C D : CAT Γ} (f : MAP C D) → IsEquiv f
    → IsEquiv (mapPost {C = A} f)
  mapPost-isEquiv {A} {C} {D} f e = record
    { inverse = mapPost (IsEquiv.inverse e)
    ; left-inverse-law = (mapPost-comp f (IsEquiv.inverse e)) ⁻¹ ∙
        (mapPost⁼ (IsEquiv.left-inverse-law e) ∙ (mapPost-id A C) ⁻¹)
    ; right-inverse-law = (mapPost-comp (IsEquiv.inverse e) f) ⁻¹ ∙
        (mapPost⁼ (IsEquiv.right-inverse-law e) ∙ (mapPost-id A D) ⁻¹)
    }

  mapPre-isEquiv : {C D E : CAT Γ} (f : MAP C D) → IsEquiv f
    → IsEquiv (mapPre {D = E} f)
  mapPre-isEquiv {C} {D} {E} f e = record
    { inverse = mapPre (IsEquiv.inverse e)
    ; left-inverse-law = (mapPre-comp (IsEquiv.inverse e) f) ⁻¹ ∙
        (mapPre⁼ (IsEquiv.right-inverse-law e) ∙ (mapPre-id D E) ⁻¹)
    ; right-inverse-law = (mapPre-comp f (IsEquiv.inverse e)) ⁻¹ ∙
        (mapPre⁼ (IsEquiv.left-inverse-law e) ∙ (mapPre-id C E) ⁻¹)
    }
```

## Naming and composition

Naming is compatible with the actual pre- and postcomposition functors.

```agda
module _ {Γ : Context} where
  mapPost-name : {B C D : CAT Γ} (f : MAP C D) (g : MAP B C)
    → (mapPost f ∘ name g) =₁ (name (f ∘ g))
  mapPost-name f g = uncurry-reflect one-isAn _ _
    ((mapCurry-β one-isAn ((f ∘ g) ∘ pr₂)) ⁻¹ ∙
    ((comp-assoc pr₂ g f) ⁻¹ ∙
    ((f ◁ mapCurry-β one-isAn (g ∘ pr₂)) ∙ mapPost-uncurry f (name g))))

  mapPre-name : {B C D : CAT Γ} (f : MAP B C) (g : MAP C D)
    → (mapPre f ∘ name g) =₁ (name (g ∘ f))
  mapPre-name f g = uncurry-reflect one-isAn _ _
    ((mapCurry-β one-isAn ((g ∘ f) ∘ pr₂)) ⁻¹ ∙
    ((comp-assoc pr₂ f g) ⁻¹ ∙
    ((g ◁ pair-β₂ (id One ∘ pr₁) (f ∘ pr₂)) ∙
    (comp-assoc (productMap (id One) f) pr₂ g ∙
    ((mapCurry-β one-isAn (g ∘ pr₂) ▷ productMap (id One) f) ∙
       mapPre-uncurry f (name g))))))
```

## Natural evaluation identifications

The beta components are the same supplied currying identifications. Their
family laws use the exact curried actions above; no synthetic functoriality
of the external curry operation is assumed.

```agda
module _ {Γ : Context} where
  post-evaluation-operation : (C D E : CAT Γ)
    → N.Operation (MAP D E) (N.HomChange D E) (Map C D × C) E
  post-evaluation-operation C D E = record
    { value = λ f → uncurry (mapPost {C = C} f)
    ; action = λ α → uncurry⁼ (mapPost⁼ {C = C} α) }

  mapPost-β-naturality : (C D E : CAT Γ)
    → N.Naturality (post-evaluation-operation C D E)
        (N.Pre mapEval (N.Input D E)) mapPost-β
  mapPost-β-naturality C D E α = mapPost-β-natural α

  pre-evaluation-operation : (B C D : CAT Γ)
    → N.Operation (MAP B C) (N.HomChange B C) (Map C D × B) D
  pre-evaluation-operation B C D = record
    { value = λ f → uncurry (mapPre {D = D} f)
    ; action = λ α → uncurry⁼ (mapPre⁼ {D = D} α) }

  pre-evaluation-formula : (B C D : CAT Γ)
    → N.Operation (MAP B C) (N.HomChange B C) (Map C D × B) D
  pre-evaluation-formula B C D = record
    { value = λ f → mapEval ∘ productMap (id (Map C D)) f
    ; action = λ α → mapEval ◁ productMap-cong (const (id₌ (id (Map C D)))) α }

  mapPre-β-naturality : (B C D : CAT Γ)
    → N.Naturality (pre-evaluation-operation B C D) (pre-evaluation-formula B C D) mapPre-β
  mapPre-β-naturality B C D α = mapPre-β-natural α
```
