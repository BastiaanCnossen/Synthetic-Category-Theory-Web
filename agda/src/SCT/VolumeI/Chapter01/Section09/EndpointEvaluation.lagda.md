# Evaluating a family at an absolute object

Evaluation at a fixed object inserts that object as the second product
coordinate. The comparisons below relate this formula to Section 1.6's
evaluation functor, uncurrying, and restriction of a family of diagrams.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section09.EndpointEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section06.Setup 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section03.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section06.TerminalDomain 𝒯 M ℱ using (evalAt)
open import SCT.VolumeI.Chapter01.Section06.AbsoluteObjects 𝒯 M ℱ public

insert : {X I : CAT} → Obj-abs I → MAP X (X × I)
insert {X} x = pair (id X) (const x)

evaluate : {I C : CAT} → Obj-abs I → MAP (Fun I C) C
evaluate x = funEval ∘ insert x

evaluate-agrees : {I C : CAT} (x : Obj-abs I) → =₁ (evalAt {D = C} x) (evaluate x)
evaluate-agrees {I} {C} x = funEval ◁
  (pair-cong (comp-unitˡ (id (Fun I C))) (idIso (const x)) ∙
    productMap-pair (id (Fun I C)) x (id (Fun I C)) (terminate (Fun I C)))

insert-natural : {X Y I : CAT} (h : MAP X Y) (x : Obj-abs I) →
  =₁ (insert x ∘ h) (productMap h (id I) ∘ insert x)
insert-natural {X} {Y} {I} h x = invIso
  (pair-cong (comp-unitʳ h) (comp-unitˡ (const x)) ∙
    productMap-pair h (id I) (id X) (const x)) ∙
  (pair-cong (comp-unitˡ h) (const-pre x h) ∙ pair-pre (id Y) (const x) h)

evaluate-uncurry : {X I C : CAT} (x : Obj-abs I) (h : MAP X (Fun I C)) →
  =₁ (evaluate x ∘ h) (funUncurry h ∘ insert x)
evaluate-uncurry {I = I} x h = invIso (comp-assoc (insert x) (productMap h (id I)) funEval) ∙
  ((funEval ◁ insert-natural h x) ∙ comp-assoc h (insert x) funEval)

evaluate-curry : {X I C : CAT} (x : Obj-abs I) (H : MAP (X × I) C) →
  =₁ (evaluate x ∘ funCurry H) (H ∘ insert x)
evaluate-curry x H = (funCurry-β H ▷ insert x) ∙ evaluate-uncurry x (funCurry H)

evaluate-post : {I C D : CAT} (x : Obj-abs I) (F : MAP C D) →
  =₁ (evaluate x ∘ funPost F) (F ∘ evaluate x)
evaluate-post x F = comp-assoc (insert x) funEval F ∙
  ((funPost-β F ▷ insert x) ∙ evaluate-uncurry x (funPost F))

evaluate-post-at : {X I C D : CAT} (x : Obj-abs I) (F : MAP C D) (h : MAP X (Fun I C)) →
  =₁ (evaluate x ∘ (funPost F ∘ h)) (F ∘ (evaluate x ∘ h))
evaluate-post-at x F h = comp-assoc h (evaluate x) F ∙
  ((evaluate-post x F ▷ h) ∙ invIso (comp-assoc h (funPost F) (evaluate x)))

constantDiagram : (I C : CAT) → MAP C (Fun I C)
constantDiagram I C = funCurry pr₁

evaluate-constant : {I C : CAT} (x : Obj-abs I) →
  =₁ (evaluate x ∘ constantDiagram I C) (id C)
evaluate-constant {C = C} x = pair-β₁ (id C) (const x) ∙ evaluate-curry x pr₁

evaluate-name : {I C : CAT} (x : Obj-abs I) (f : MAP I C) →
  =₁ (evaluate x ∘ nameFun f) (f ∘ x)
evaluate-name x f = (f ◁ const-One x) ∙
  ((f ◁ pair-β₂ (id One) (const x)) ∙
    (comp-assoc (insert x) pr₂ f ∙ evaluate-curry x (f ∘ pr₂)))

evaluate-cong : {I C : CAT} {x y : Obj-abs I} → =₁ x y →
  =₁ (evaluate {C = C} x) (evaluate y)
evaluate-cong {I} {C} α = funEval ◁ pair-cong (idIso (id (Fun I C))) (α ▷ terminate (Fun I C))

evaluate-pre : {I J C : CAT} (f : MAP I J) (x : Obj-abs I) →
  =₁ (evaluate x ∘ funPre {D = C} f) (evaluate (f ∘ x))
evaluate-pre {I} {J} {C} f x = (funEval ◁
  (pair-cong (comp-unitˡ (id (Fun J C))) (invIso (comp-assoc (terminate (Fun J C)) x f)) ∙
    productMap-pair (id (Fun J C)) f (id (Fun J C)) (const x))) ∙
  (comp-assoc (insert x) (productMap (id (Fun J C)) f) funEval ∙
    ((funPre-β f ▷ insert x) ∙ evaluate-uncurry x (funPre f)))

constantDiagram-point : {I C : CAT} (x : Obj-abs C) →
  =₁ (constantDiagram I C ∘ x) (nameFun (const {P = I} x))
constantDiagram-point {I} {C} x = funReflect _ _
  (invIso (funCurry-β (const x ∘ pr₂)) ∙
  (invIso (comp-assoc pr₂ (terminate I) x) ∙
  ((x ◁ terminal-iso _ _) ∙
  (pair-β₁ (x ∘ pr₁) (id I ∘ pr₂) ∙
    ((funCurry-β pr₁ ▷ productMap x (id I)) ∙ funUncurry-pre (constantDiagram I C) x)))))
```
