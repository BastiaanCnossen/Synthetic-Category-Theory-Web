# Evaluating a family at an absolute object

Evaluation at a fixed object inserts that object as the second product
coordinate. The comparisons below relate this formula to Section 1.7's
evaluation functor, uncurrying, and restriction of a family of diagrams.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section01.EndpointEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section07.TerminalDomain 𝒯 M ℱ using (evalAt)
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ public

insert : {X I : CAT} → Obj-abs I → MAP X (X × I)
insert {X} x = pair (id X) (const x)

evaluate : {I C : CAT} → Obj-abs I → MAP (Fun I C) C
evaluate x = funEval ∘ insert x

evaluate-agrees : {I C : CAT} (x : Obj-abs I) → (evalAt {D = C} x) =₁ (evaluate x)
evaluate-agrees {I} {C} x = funEval ◁
  (pair-cong (comp-unitˡ (id (Fun I C))) (idIso (const x)) ∙
    productMap-pair (id (Fun I C)) x (id (Fun I C)) (terminate (Fun I C)))

insert-natural : {X Y I : CAT} (h : MAP X Y) (x : Obj-abs I) →
  (insert x ∘ h) =₁ (productMap h (id I) ∘ insert x)
insert-natural {X} {Y} {I} h x =
  (pair-cong (comp-unitʳ h) (comp-unitˡ (const x)) ∙
    productMap-pair h (id I) (id X) (const x)) ⁻¹ ∙
  (pair-cong (comp-unitˡ h) (const-pre x h) ∙ pair-pre (id Y) (const x) h)

evaluate-uncurry : {X I C : CAT} (x : Obj-abs I) (h : MAP X (Fun I C)) →
  (evaluate x ∘ h) =₁ (funUncurry h ∘ insert x)
evaluate-uncurry {I = I} x h = (comp-assoc (insert x) (productMap h (id I)) funEval) ⁻¹ ∙
  ((funEval ◁ insert-natural h x) ∙ comp-assoc h (insert x) funEval)

evaluate-curry : {X I C : CAT} (x : Obj-abs I) (H : MAP (X × I) C) →
  (evaluate x ∘ funCurry H) =₁ (H ∘ insert x)
evaluate-curry x H = (funCurry-β H ▷ insert x) ∙ evaluate-uncurry x (funCurry H)

evaluate-post : {I C D : CAT} (x : Obj-abs I) (F : MAP C D) →
  (evaluate x ∘ funPost F) =₁ (F ∘ evaluate x)
evaluate-post x F = comp-assoc (insert x) funEval F ∙
  ((funPost-β F ▷ insert x) ∙ evaluate-uncurry x (funPost F))

evaluate-post-at : {X I C D : CAT} (x : Obj-abs I) (F : MAP C D) (h : MAP X (Fun I C)) →
  (evaluate x ∘ (funPost F ∘ h)) =₁ (F ∘ (evaluate x ∘ h))
evaluate-post-at x F h = comp-assoc h (evaluate x) F ∙
  ((evaluate-post x F ▷ h) ∙ (comp-assoc h (funPost F) (evaluate x)) ⁻¹)

constantDiagram : (I C : CAT) → MAP C (Fun I C)
constantDiagram I C = funCurry pr₁

evaluate-constant : {I C : CAT} (x : Obj-abs I) →
  (evaluate x ∘ constantDiagram I C) =₁ (id C)
evaluate-constant {C = C} x = pair-β₁ (id C) (const x) ∙ evaluate-curry x pr₁

evaluate-name : {I C : CAT} (x : Obj-abs I) (f : MAP I C) →
  (evaluate x ∘ nameFun f) =₁ (f ∘ x)
evaluate-name x f = (f ◁ const-One x) ∙
  ((f ◁ pair-β₂ (id One) (const x)) ∙
    (comp-assoc (insert x) pr₂ f ∙ evaluate-curry x (f ∘ pr₂)))

evaluate-cong : {I C : CAT} {x y : Obj-abs I} → x =₁ y →
  (evaluate {C = C} x) =₁ (evaluate y)
evaluate-cong {I} {C} α = funEval ◁ pair-cong (idIso (id (Fun I C))) (α ▷ terminate (Fun I C))

evaluate-pre : {I J C : CAT} (f : MAP I J) (x : Obj-abs I) →
  (evaluate x ∘ funPre {D = C} f) =₁ (evaluate (f ∘ x))
evaluate-pre {I} {J} {C} f x = (funEval ◁
  (pair-cong (comp-unitˡ (id (Fun J C))) ((comp-assoc (terminate (Fun J C)) x f) ⁻¹) ∙
    productMap-pair (id (Fun J C)) f (id (Fun J C)) (const x))) ∙
  (comp-assoc (insert x) (productMap (id (Fun J C)) f) funEval ∙
    ((funPre-β f ▷ insert x) ∙ evaluate-uncurry x (funPre f)))

constantDiagram-point : {I C : CAT} (x : Obj-abs C) →
  (constantDiagram I C ∘ x) =₁ (nameFun (const {P = I} x))
constantDiagram-point {I} {C} x = funReflect _ _
  ((funCurry-β (const x ∘ pr₂)) ⁻¹ ∙
  ((comp-assoc pr₂ (terminate I) x) ⁻¹ ∙
  ((x ◁ terminal-iso _ _) ∙
  (pair-β₁ (x ∘ pr₁) (id I ∘ pr₂) ∙
    ((funCurry-β pr₁ ▷ productMap x (id I)) ∙ funUncurry-restrict (constantDiagram I C) x)))))
```
