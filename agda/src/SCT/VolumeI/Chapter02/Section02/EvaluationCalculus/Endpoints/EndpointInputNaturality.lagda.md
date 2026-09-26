# Naturality in the evaluated object

Changing the chosen object commutes with inserting it in a family of
diagrams. We keep this comparison separate from naturality in the family:
both squares are needed to retain the endpoint equations of a triangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.EndpointInputNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointNaturality 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯
  using (post-square; quotient-square)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PC
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (pair-pre-natural-inputs; pair-pre-natural-substitution; move-square)
open PC vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-triangle₁; pair-cong-triangle₂; pair-cong-Iso₂)
open Structural vocabulary terminal products productLaws composition whiskering

module ProductInputs {X A B C D : CAT} (f : MAP A C) (g : MAP B D)
  {u u′ : MAP X A} {v v′ : MAP X B} (α : u =₁ u′) (β : v =₁ v′) where
  δ = pair-cong α β
  first : (u : MAP X A) (v : MAP X B) → ((f ∘ pr₁) ∘ pair u v) =₁ (f ∘ u)
  first u v = (f ◁ pair-β₁ u v) ∙ comp-assoc (pair u v) pr₁ f
  second : (u : MAP X A) (v : MAP X B) → ((g ∘ pr₂) ∘ pair u v) =₁ (g ∘ v)
  second u v = (g ◁ pair-β₂ u v) ∙ comp-assoc (pair u v) pr₂ g

  abstract
    first-square : (first u′ v′ ∙ ((f ∘ pr₁) ◁ δ)) =₂ ((f ◁ α) ∙ first u v)
    first-square = paste-squares
      (comp-assoc (pair u v) pr₁ f) (comp-assoc (pair u′ v′) pr₁ f)
      (f ◁ pair-β₁ u v) (f ◁ pair-β₁ u′ v′)
      ((f ∘ pr₁) ◁ δ) (f ◁ (pr₁ ◁ δ)) (f ◁ α)
      (postWhisker-comp-at δ pr₁ f)
      (post-square f _ _ _ _ (pair-cong-triangle₁ α β))

    second-square : (second u′ v′ ∙ ((g ∘ pr₂) ◁ δ)) =₂ ((g ◁ β) ∙ second u v)
    second-square = paste-squares
      (comp-assoc (pair u v) pr₂ g) (comp-assoc (pair u′ v′) pr₂ g)
      (g ◁ pair-β₂ u v) (g ◁ pair-β₂ u′ v′)
      ((g ∘ pr₂) ◁ δ) (g ◁ (pr₂ ◁ δ)) (g ◁ β)
      (postWhisker-comp-at δ pr₂ g)
      (post-square g _ _ _ _ (pair-cong-triangle₂ α β))

    natural : (productMap-pair f g u′ v′ ∙ (productMap f g ◁ δ)) =₂
      (pair-cong (f ◁ α) (g ◁ β) ∙ productMap-pair f g u v)
    natural = paste-squares
      (pair-pre (f ∘ pr₁) (g ∘ pr₂) (pair u v))
      (pair-pre (f ∘ pr₁) (g ∘ pr₂) (pair u′ v′))
      (pair-cong (first u v) (second u v))
      (pair-cong (first u′ v′) (second u′ v′))
      (productMap f g ◁ δ)
      (pair-cong ((f ∘ pr₁) ◁ δ) ((g ∘ pr₂) ◁ δ))
      (pair-cong (f ◁ α) (g ◁ β))
      ((pair-pre-natural-substitution (f ∘ pr₁) (g ∘ pr₂) δ) ⁻¹)
      (pair-square _ _ _ _ _ _ _ _ first-square second-square)
```

```agda
insert-cong : {X I : CAT} {x y : Obj-abs I} → x =₁ y →
  (insert {X = X} x) =₁ (insert y)
insert-cong {X} η = pair-cong (idIso (id X)) (η ▷ terminate X)

module InsertionObject {X Y I : CAT} (h : MAP X Y)
  {x y : Obj-abs I} (η : x =₁ y) where
  input-x = pair-pre (id Y) (const x) h
  input-y = pair-pre (id Y) (const y) h
  finish-x = pair-cong (comp-unitˡ h) (const-pre x h)
  finish-y = pair-cong (comp-unitˡ h) (const-pre y h)
  result = pair-cong (idIso h) (η ▷ terminate X)
  output-x = productMap-pair h (id I) (id X) (const x)
  output-y = productMap-pair h (id I) (id X) (const y)
  close-x = pair-cong (comp-unitʳ h) (comp-unitˡ (const x))
  close-y = pair-cong (comp-unitʳ h) (comp-unitˡ (const y))

  abstract
    first : ((finish-y ∙ input-y) ∙ (insert-cong η ▷ h)) =₂
      (result ∙ (finish-x ∙ input-x))
    first = paste-squares input-x input-y finish-x finish-y
      (insert-cong η ▷ h)
      (pair-cong (idIso (id Y) ▷ h) ((η ▷ terminate Y) ▷ h)) result
      ((pair-pre-natural-inputs (idIso (id Y)) (η ▷ terminate Y) h) ⁻¹)
      (pair-square _ _ _ _ _ _ _ _
        ((isoComp-unitˡ-at (comp-unitˡ h)) ⁻¹ ∙
          (isoComp-unitʳ-at (comp-unitˡ h) ∙
            isoComp-cong (idIso (comp-unitˡ h)) (preWhisker-idIso (id Y) h)))
        (application-natural (terminate Y) h
          (terminal-iso (terminate Y ∘ h) (terminate X)) η))

    second : ((close-y ∙ output-y) ∙ (productMap h (id I) ◁ insert-cong η)) =₂
      (result ∙ (close-x ∙ output-x))
    second = paste-squares output-x output-y close-x close-y
      (productMap h (id I) ◁ insert-cong η)
      (pair-cong (h ◁ idIso (id X)) (id I ◁ (η ▷ terminate X))) result
      (ProductInputs.natural h (id I) (idIso (id X)) (η ▷ terminate X))
      (pair-square _ _ _ _ _ _ _ _
        ((isoComp-unitˡ-at (comp-unitʳ h)) ⁻¹ ∙
          (isoComp-unitʳ-at (comp-unitʳ h) ∙
            isoComp-cong (idIso (comp-unitʳ h)) (postWhisker-idIso h (id X))))
        (postWhisker-id-at (η ▷ terminate X)))

    natural : (insert-natural h y ∙ (insert-cong η ▷ h)) =₂
      ((productMap h (id I) ◁ insert-cong η) ∙ insert-natural h x)
    natural = quotient-square (finish-x ∙ input-x) (close-x ∙ output-x)
      (finish-y ∙ input-y) (close-y ∙ output-y) _ _ result first second

module EvaluationObject {X I C : CAT} (h : MAP X (Fun I C))
  {x y : Obj-abs I} (η : x =₁ y) where
  product = productMap h (id I)
  source = insert-cong {X = Fun I C} η
  target = insert-cong {X = X} η

  abstract
    first :
      (((funEval ◁ insert-natural h y) ∙ comp-assoc h (insert y) funEval) ∙
        (evaluate-cong η ▷ h)) =₂
      ((funEval ◁ (product ◁ target)) ∙
        ((funEval ◁ insert-natural h x) ∙ comp-assoc h (insert x) funEval))
    first = paste-squares
      (comp-assoc h (insert x) funEval) (comp-assoc h (insert y) funEval)
      (funEval ◁ insert-natural h x) (funEval ◁ insert-natural h y)
      (evaluate-cong η ▷ h) (funEval ◁ (source ▷ h)) (funEval ◁ (product ◁ target))
      (whisker-mixed-at source h funEval)
      (post-square funEval _ _ _ _ (InsertionObject.natural h η))

    natural : (evaluate-uncurry y h ∙ (evaluate-cong η ▷ h)) =₂
      ((funUncurry h ◁ target) ∙ evaluate-uncurry x h)
    natural = paste-squares
      ((funEval ◁ insert-natural h x) ∙ comp-assoc h (insert x) funEval)
      ((funEval ◁ insert-natural h y) ∙ comp-assoc h (insert y) funEval)
      ((comp-assoc (insert x) product funEval) ⁻¹)
      ((comp-assoc (insert y) product funEval) ⁻¹)
      (evaluate-cong η ▷ h) (funEval ◁ (product ◁ target)) (funUncurry h ◁ target)
      first
      (move-square (comp-assoc (insert y) product funEval)
        (funUncurry h ◁ target) (funEval ◁ (product ◁ target))
        (comp-assoc (insert x) product funEval)
        (postWhisker-comp-at target product funEval))
```

The resulting restriction square changes the object while holding the
restriction map fixed. Its two routes use exactly `evaluate-pre` and
`evaluate-cong`, rather than replacement endpoint identifications.

```agda
module RestrictionObject {I J C : CAT} (f : MAP I J)
  {x y : Obj-abs I} (η : x =₁ y) where
  X = Fun J C
  F = productMap (id X) f
  δ = insert-cong {X = X} η
  β = funPre-β {D = C} f
  close-x = pair-cong (comp-unitˡ (id X)) ((comp-assoc (terminate X) x f) ⁻¹)
  close-y = pair-cong (comp-unitˡ (id X)) ((comp-assoc (terminate X) y f) ⁻¹)
  pair-x = productMap-pair (id X) f (id X) (const x)
  pair-y = productMap-pair (id X) f (id X) (const y)

  abstract
    insertion : ((close-y ∙ pair-y) ∙ (F ◁ δ)) =₂
      (insert-cong (f ◁ η) ∙ (close-x ∙ pair-x))
    insertion = paste-squares pair-x pair-y close-x close-y
      (F ◁ δ) (pair-cong (id X ◁ idIso (id X)) (f ◁ (η ▷ terminate X)))
      (insert-cong (f ◁ η))
      (ProductInputs.natural (id X) f (idIso (id X)) (η ▷ terminate X))
      (pair-square _ _ _ _ _ _ _ _
        ((isoComp-unitˡ-at (comp-unitˡ (id X))) ⁻¹ ∙
          (isoComp-unitʳ-at (comp-unitˡ (id X)) ∙
            isoComp-cong (idIso (comp-unitˡ (id X))) (postWhisker-idIso (id X) (id X))))
        (move-square (comp-assoc (terminate X) y f)
          ((f ◁ η) ▷ terminate X) (f ◁ (η ▷ terminate X))
          (comp-assoc (terminate X) x f) (whisker-mixed-at η (terminate X) f)))

    beta : (((β ▷ insert y) ∙ evaluate-uncurry y (funPre f)) ∙
      (evaluate-cong η ▷ funPre f)) =₂
      (((funEval ∘ F) ◁ δ) ∙ ((β ▷ insert x) ∙ evaluate-uncurry x (funPre f)))
    beta = paste-squares
      (evaluate-uncurry x (funPre f)) (evaluate-uncurry y (funPre f))
      (β ▷ insert x) (β ▷ insert y)
      (evaluate-cong η ▷ funPre f) (funUncurry (funPre f) ◁ δ) ((funEval ∘ F) ◁ δ)
      (EvaluationObject.natural (funPre f) η) (interchange-at β δ)

    associated :
      ((comp-assoc (insert y) F funEval ∙ ((β ▷ insert y) ∙ evaluate-uncurry y (funPre f))) ∙
        (evaluate-cong η ▷ funPre f)) =₂
      ((funEval ◁ (F ◁ δ)) ∙
        (comp-assoc (insert x) F funEval ∙ ((β ▷ insert x) ∙ evaluate-uncurry x (funPre f))))
    associated = paste-squares
      ((β ▷ insert x) ∙ evaluate-uncurry x (funPre f))
      ((β ▷ insert y) ∙ evaluate-uncurry y (funPre f))
      (comp-assoc (insert x) F funEval) (comp-assoc (insert y) F funEval)
      (evaluate-cong η ▷ funPre f) ((funEval ∘ F) ◁ δ) (funEval ◁ (F ◁ δ))
      beta (postWhisker-comp-at δ F funEval)

    natural : (evaluate-pre {C = C} f y ∙ (evaluate-cong η ▷ funPre f)) =₂
      (evaluate-cong (f ◁ η) ∙ evaluate-pre f x)
    natural = paste-squares
      (comp-assoc (insert x) F funEval ∙ ((β ▷ insert x) ∙ evaluate-uncurry x (funPre f)))
      (comp-assoc (insert y) F funEval ∙ ((β ▷ insert y) ∙ evaluate-uncurry y (funPre f)))
      (funEval ◁ (close-x ∙ pair-x)) (funEval ◁ (close-y ∙ pair-y))
      (evaluate-cong η ▷ funPre f) (funEval ◁ (F ◁ δ)) (evaluate-cong (f ◁ η))
      associated (post-square funEval _ _ _ _ insertion)
```
