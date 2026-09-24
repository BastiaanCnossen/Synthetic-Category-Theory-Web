# Morphisms, natural transformations, and the arrow category

Three declarations describe different aspects of `def:Morphisms`.
`Ar C = Fun [1] C` is the internal arrow category. `Mor C = MAP [1] C`
is the external type of absolute interval diagrams. `Morphism x y`
equips such a diagram with identifications of its source and target
with the specified objects `x` and `y`.

`NatTrans C D` is a morphism of `Fun C D`; its two endpoint functors
are determined by the diagram. `MorphismExpression`, below, uses the
arrow category to describe a family with specified endpoints.
No property of the interval beyond its two objects is used in these
definitions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section01.Morphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section07.IsomorphismLifting 𝒯 M ℱ using (funIsoReflect)
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
    source-identification : (source diagram) =₁ x
    target-identification : (target diagram) =₁ y

NatTrans : (C D : CAT) → Set m
NatTrans C D = Mor (Fun C D)

transformation-diagram : {C D : CAT} → NatTrans C D → MAP ([1] × C) D
transformation-diagram = funUncurry

diagram-transformation : {C D : CAT} → MAP ([1] × C) D → NatTrans C D
diagram-transformation = funCurry

transformation-β : {C D : CAT} (H : MAP ([1] × C) D) →
  (transformation-diagram (diagram-transformation H)) =₁ H
transformation-β = funCurry-β

transformation-η : {C D : CAT} (α : NatTrans C D) →
  (diagram-transformation (transformation-diagram α)) =₁ α
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
    source-frame : (ev₀ ∘ arrow) =₁ f
    target-frame : (ev₁ ∘ arrow) =₁ g

record ExpressionIso {Γ C : CAT} {f g : MAP Γ C}
  (α β : MorphismExpression f g) : Set m where
  field
    comparison : (MorphismExpression.arrow α) =₁ (MorphismExpression.arrow β)
    source-compatible : (MorphismExpression.source-frame β ∙ (ev₀ ◁ comparison)) =₂
      (MorphismExpression.source-frame α)
    target-compatible : (MorphismExpression.target-frame β ∙ (ev₁ ◁ comparison)) =₂
      (MorphismExpression.target-frame α)

expression : {Γ C : CAT} {f g : MAP Γ C} (H : MAP (Γ × [1]) C) →
  (H ∘ insert zero) =₁ f → (H ∘ insert one) =₁ g → MorphismExpression f g
expression H α β = record
  { arrow = funCurry H
  ; source-frame = α ∙ evaluate-curry zero H
  ; target-frame = β ∙ evaluate-curry one H }

restrict-expression : {Γ Δ C : CAT} {f g : MAP Γ C} →
  MorphismExpression f g → (r : MAP Δ Γ) → MorphismExpression (f ∘ r) (g ∘ r)
restrict-expression α r = record
  { arrow = MorphismExpression.arrow α ∘ r
  ; source-frame = (MorphismExpression.source-frame α ▷ r) ∙
      (comp-assoc r (MorphismExpression.arrow α) ev₀) ⁻¹
  ; target-frame = (MorphismExpression.target-frame α ▷ r) ∙
      (comp-assoc r (MorphismExpression.arrow α) ev₁) ⁻¹ }

retarget-expression : {Γ C : CAT} {f g f′ g′ : MAP Γ C} →
  MorphismExpression f g → f =₁ f′ → g =₁ g′ → MorphismExpression f′ g′
retarget-expression α p q = record
  { arrow = MorphismExpression.arrow α
  ; source-frame = p ∙ MorphismExpression.source-frame α
  ; target-frame = q ∙ MorphismExpression.target-frame α }

identityArrow : {C : CAT} → MAP C (Ar C)
identityArrow {C} = constantDiagram [1] C

identity-source : {C : CAT} → (ev₀ ∘ identityArrow) =₁ (id C)
identity-source = evaluate-constant zero

identity-target : {C : CAT} → (ev₁ ∘ identityArrow) =₁ (id C)
identity-target = evaluate-constant one

identity-boundary : {Γ C : CAT} (x : Obj-abs [1]) (f : MAP Γ C) →
  ((f ∘ pr₁) ∘ insert x) =₁ f
identity-boundary x f = comp-unitʳ f ∙ ((f ◁ pair-β₁ _ _) ∙ comp-assoc (insert x) pr₁ f)

constant-boundary : {C : CAT} (y : Obj-abs [1]) (x : Obj-abs C) → (const x ∘ y) =₁ x
constant-boundary y x = comp-unitʳ x ∙
  ((x ◁ terminal-iso (terminate [1] ∘ y) (id One)) ∙ comp-assoc y (terminate [1]) x)
identity-expression : {Γ C : CAT} (f : MAP Γ C) → MorphismExpression f f
identity-expression f = expression (f ∘ pr₁) (identity-boundary zero f) (identity-boundary one f)

isomorphism-expression : {Γ C : CAT} {f g : MAP Γ C} → f =₁ g → MorphismExpression f g
isomorphism-expression {f = f} α = record
  { arrow = MorphismExpression.arrow (identity-expression f)
  ; source-frame = MorphismExpression.source-frame (identity-expression f)
  ; target-frame = α ∙ MorphismExpression.target-frame (identity-expression f) }

post-boundary : {Γ C D : CAT} (x : Obj-abs [1]) (F : MAP C D) (h : MAP Γ (Ar C))
  {f : MAP Γ C} → (evaluate x ∘ h) =₁ f → (evaluate x ∘ (funPost F ∘ h)) =₁ (F ∘ f)
post-boundary x F h p = (F ◁ (p ∙ (evaluate-uncurry x h) ⁻¹)) ∙
  (comp-assoc (insert x) (funUncurry h) F ∙
    ((funPost-uncurry F h ▷ insert x) ∙ evaluate-uncurry x (funPost F ∘ h)))
post-expression : {Γ C D : CAT} (F : MAP C D) {f g : MAP Γ C} →
  MorphismExpression f g → MorphismExpression (F ∘ f) (F ∘ g)
post-expression F α = record
  { arrow = funPost F ∘ MorphismExpression.arrow α
  ; source-frame = post-boundary zero F (MorphismExpression.arrow α) (MorphismExpression.source-frame α)
  ; target-frame = post-boundary one F (MorphismExpression.arrow α) (MorphismExpression.target-frame α) }

post-identity-arrow : {Γ C D : CAT} (F : MAP C D) (f : MAP Γ C) →
  (MorphismExpression.arrow (post-expression F (identity-expression f))) =₁
    (MorphismExpression.arrow (identity-expression (F ∘ f)))
post-identity-arrow F f = funIsoReflect _ _
  ((funCurry-β ((F ∘ f) ∘ pr₁)) ⁻¹ ∙
    ((comp-assoc pr₁ f F) ⁻¹ ∙
      ((F ◁ funCurry-β (f ∘ pr₁)) ∙ funPost-uncurry F (funCurry (f ∘ pr₁)))))
```



