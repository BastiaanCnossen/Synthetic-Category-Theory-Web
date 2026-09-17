# Morphisms, natural transformations, and the arrow category

For `def:Morphisms`, an absolute morphism is a functor out of `[1]`.
A morphism with specified endpoints retains both identifications. The
arrow category gives the equivalent family presentation. No property of
the interval beyond its two objects is used in these definitions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking

module SCT.VolumeI.Chapter01.Section09.Morphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section09.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section06.IsomorphismLifting 𝒯 M ℱ using (funIsoReflect)
open Walking.WalkingMorphism I public

Ar : CAT → CAT
Ar C = Fun [1] C

Mor : CAT → Set m
Mor C = MAP [1] C

source target : {C : CAT} → Mor C → Obj-abs C
source f = f ∘ zero
target f = f ∘ one

ev₀ ev₁ : {C : CAT} → MAP (Ar C) C
ev₀ = evaluate zero
ev₁ = evaluate one

record Morphism {C : CAT} (x y : Obj-abs C) : Set m where
  field
    diagram : Mor C
    source-identification : =₁ (source diagram) x
    target-identification : =₁ (target diagram) y

NatTrans : (C D : CAT) → Set m
NatTrans C D = Mor (Fun C D)

transformation-diagram : {C D : CAT} → NatTrans C D → MAP ([1] × C) D
transformation-diagram = funUncurry

diagram-transformation : {C D : CAT} → MAP ([1] × C) D → NatTrans C D
diagram-transformation = funCurry

transformation-β : {C D : CAT} (H : MAP ([1] × C) D) →
  =₁ (transformation-diagram (diagram-transformation H)) H
transformation-β = funCurry-β

transformation-η : {C D : CAT} (α : NatTrans C D) →
  =₁ (diagram-transformation (transformation-diagram α)) α
transformation-η = funCurry-η
```

The following record is `con:Morphism_Expressions`. Its comparisons retain
compatibility with the displayed source and target, not just the interval
diagram. Currying and the endpoint evaluation comparison relate it to the
book's presentation by a functor `Γ × [1] → C`.

```agda
record MorphismExpression {Γ C : CAT} (f g : MAP Γ C) : Set m where
  field
    arrow : MAP Γ (Ar C)
    source-frame : =₁ (ev₀ ∘ arrow) f
    target-frame : =₁ (ev₁ ∘ arrow) g

record ExpressionIso {Γ C : CAT} {f g : MAP Γ C}
  (α β : MorphismExpression f g) : Set m where
  field
    comparison : =₁ (MorphismExpression.arrow α) (MorphismExpression.arrow β)
    source-compatible : =₂ (MorphismExpression.source-frame β ∙ (ev₀ ◁ comparison))
      (MorphismExpression.source-frame α)
    target-compatible : =₂ (MorphismExpression.target-frame β ∙ (ev₁ ◁ comparison))
      (MorphismExpression.target-frame α)

expression : {Γ C : CAT} {f g : MAP Γ C} (H : MAP (Γ × [1]) C) →
  =₁ (H ∘ insert zero) f → =₁ (H ∘ insert one) g → MorphismExpression f g
expression H α β = record
  { arrow = funCurry H
  ; source-frame = α ∙ evaluate-curry zero H
  ; target-frame = β ∙ evaluate-curry one H }

restrict-expression : {Γ Δ C : CAT} {f g : MAP Γ C} →
  MorphismExpression f g → (r : MAP Δ Γ) → MorphismExpression (f ∘ r) (g ∘ r)
restrict-expression α r = record
  { arrow = MorphismExpression.arrow α ∘ r
  ; source-frame = (MorphismExpression.source-frame α ▷ r) ∙
      invIso (comp-assoc r (MorphismExpression.arrow α) ev₀)
  ; target-frame = (MorphismExpression.target-frame α ▷ r) ∙
      invIso (comp-assoc r (MorphismExpression.arrow α) ev₁) }

retarget-expression : {Γ C : CAT} {f g f′ g′ : MAP Γ C} →
  MorphismExpression f g → =₁ f f′ → =₁ g g′ → MorphismExpression f′ g′
retarget-expression α p q = record
  { arrow = MorphismExpression.arrow α
  ; source-frame = p ∙ MorphismExpression.source-frame α
  ; target-frame = q ∙ MorphismExpression.target-frame α }

identityArrow : {C : CAT} → MAP C (Ar C)
identityArrow {C} = constantDiagram [1] C

identity-source : {C : CAT} → =₁ (ev₀ ∘ identityArrow) (id C)
identity-source = evaluate-constant zero

identity-target : {C : CAT} → =₁ (ev₁ ∘ identityArrow) (id C)
identity-target = evaluate-constant one

identity-boundary : {Γ C : CAT} (x : Obj-abs [1]) (f : MAP Γ C) →
  =₁ ((f ∘ pr₁) ∘ insert x) f
identity-boundary x f = comp-unitʳ f ∙ ((f ◁ pair-β₁ _ _) ∙ comp-assoc (insert x) pr₁ f)

constant-boundary : {C : CAT} (y : Obj-abs [1]) (x : Obj-abs C) → =₁ (const x ∘ y) x
constant-boundary y x = comp-unitʳ x ∙
  ((x ◁ terminal-iso (terminate [1] ∘ y) (id One)) ∙ comp-assoc y (terminate [1]) x)
identity-expression : {Γ C : CAT} (f : MAP Γ C) → MorphismExpression f f
identity-expression f = expression (f ∘ pr₁) (identity-boundary zero f) (identity-boundary one f)

isomorphism-expression : {Γ C : CAT} {f g : MAP Γ C} → =₁ f g → MorphismExpression f g
isomorphism-expression {f = f} α = record
  { arrow = MorphismExpression.arrow (identity-expression f)
  ; source-frame = MorphismExpression.source-frame (identity-expression f)
  ; target-frame = α ∙ MorphismExpression.target-frame (identity-expression f) }

post-boundary : {Γ C D : CAT} (x : Obj-abs [1]) (F : MAP C D) (h : MAP Γ (Ar C))
  {f : MAP Γ C} → =₁ (evaluate x ∘ h) f → =₁ (evaluate x ∘ (funPost F ∘ h)) (F ∘ f)
post-boundary x F h p = (F ◁ (p ∙ invIso (evaluate-uncurry x h))) ∙
  (comp-assoc (insert x) (funUncurry h) F ∙
    ((funPost-uncurry F h ▷ insert x) ∙ evaluate-uncurry x (funPost F ∘ h)))
post-expression : {Γ C D : CAT} (F : MAP C D) {f g : MAP Γ C} →
  MorphismExpression f g → MorphismExpression (F ∘ f) (F ∘ g)
post-expression F α = record
  { arrow = funPost F ∘ MorphismExpression.arrow α
  ; source-frame = post-boundary zero F (MorphismExpression.arrow α) (MorphismExpression.source-frame α)
  ; target-frame = post-boundary one F (MorphismExpression.arrow α) (MorphismExpression.target-frame α) }

post-identity-arrow : {Γ C D : CAT} (F : MAP C D) (f : MAP Γ C) →
  =₁ (MorphismExpression.arrow (post-expression F (identity-expression f)))
    (MorphismExpression.arrow (identity-expression (F ∘ f)))
post-identity-arrow F f = funIsoReflect _ _
  (invIso (funCurry-β ((F ∘ f) ∘ pr₁)) ∙
    (invIso (comp-assoc pr₁ f F) ∙
      ((F ◁ funCurry-β (f ∘ pr₁)) ∙ funPost-uncurry F (funCurry (f ∘ pr₁)))))
```



