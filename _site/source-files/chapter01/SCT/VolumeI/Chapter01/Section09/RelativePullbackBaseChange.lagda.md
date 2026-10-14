# Pulling back global relative functors

Pull back both categories over the base. Restrict the universal relative
family to the pulled-back source, then factor its complete matching cone
through the pulled-back target. The second pullback projection supplies the
relative base triangle. Chosen relative currying gives the categorical
base-change functor, with both its complete relative beta and its actual
evaluated pullback-cone image.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section09.RelativePullbackBaseChange where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
  using (cone-action-One; cone-compose)
open import SCT.VolumeI.Chapter01.Section09.RelativeFunctorCategories
open import SCT.VolumeI.Chapter01.Section09.RelativeFamilyComparisons

module PullbackBaseChange {Γ : Context} {S T : CAT Γ}
  (u : MAP S T) (A B : CategoryOverBase T) where
  private
    C D : CAT Γ
    C = CategoryOverBase.category A
    D = CategoryOverBase.category B
    p : MAP C T
    p = CategoryOverBase.map A
    q : MAP D T
    q = CategoryOverBase.map B

  source-domain : CAT Γ
  source-domain = Pullback p u

  target-domain : CAT Γ
  target-domain = Pullback q u

  source-pullback : Cone p u source-domain
  source-pullback = pullback-cone p u

  target-pullback : Cone q u target-domain
  target-pullback = pullback-cone q u

  source-projection : MAP source-domain C
  source-projection = Cone.left source-pullback

  target-projection : MAP target-domain D
  target-projection = Cone.left target-pullback

  source-base : MAP source-domain S
  source-base = Cone.right source-pullback

  target-base : MAP target-domain S
  target-base = Cone.right target-pullback

  pulled-source : CategoryOverBase S
  pulled-source = category-over source-domain source-base

  pulled-target : CategoryOverBase S
  pulled-target = category-over target-domain target-base

  module Source = RelativeFunctorCategory A B
  module Target = RelativeFunctorCategory pulled-source pulled-target
  private
    module SourceFamilies = RelativeFamilies A B
  module TargetFamilies = RelativeFamilies pulled-source pulled-target

  parameter-category : CAT Γ
  parameter-category = Source.category

  universal-family : Source.Family parameter-category
  universal-family = functor-over
    (Cone.left (SourceFamilies.evaluated-cone Source.fiber))
    (Cone.match (SourceFamilies.evaluated-cone Source.fiber))

  private
    parameter : MAP (parameter-category × source-domain) parameter-category
    parameter = pr₁ {C = parameter-category} {D = source-domain}
    source-coordinate : MAP (parameter-category × source-domain) source-domain
    source-coordinate = pr₂ {C = parameter-category} {D = source-domain}
    ordinary-coordinate : MAP (parameter-category × C) C
    ordinary-coordinate = pr₂ {C = parameter-category} {D = C}
    evaluation : MAP (parameter-category × C) D
    evaluation = FunctorOverBase.functor universal-family
    structural-cell : (q ∘ evaluation) =₁ (p ∘ ordinary-coordinate)
    structural-cell = FunctorOverBase.cell universal-family

  restriction : MAP (parameter-category × source-domain) (parameter-category × C)
  restriction = pair parameter (source-projection ∘ source-coordinate)

  restriction-image : (ordinary-coordinate ∘ restriction) =₁
    (source-projection ∘ source-coordinate)
  restriction-image = pair-β₂ parameter (source-projection ∘ source-coordinate)

  private
    restricted-source : Cone p u (parameter-category × source-domain)
    restricted-source = cone-restrict source-coordinate source-pullback

  restriction-matching : (q ∘ (evaluation ∘ restriction)) =₁
    (u ∘ (source-base ∘ source-coordinate))
  restriction-matching = Cone.match restricted-source ∙
    ((p ◁ restriction-image) ∙
      (comp-assoc restriction ordinary-coordinate p ∙
        ((structural-cell ▷ restriction) ∙
          (comp-assoc restriction evaluation q) ⁻¹)))

  pulled-cone : Cone q u (parameter-category × source-domain)
  pulled-cone = record
    { left = evaluation ∘ restriction
    ; right = source-base ∘ source-coordinate
    ; match = restriction-matching }

  pulled-evaluation : MAP (parameter-category × source-domain) target-domain
  pulled-evaluation = pullback-factor pulled-cone

  pullback-computation : ConeIdentification₁
    (cone-restrict pulled-evaluation target-pullback) pulled-cone
  pullback-computation = pullback-factor-β pulled-cone

  underlying-pullback-image : (target-projection ∘ pulled-evaluation) =₁
    (evaluation ∘ restriction)
  underlying-pullback-image = ConeIdentification₁.left pullback-computation

  base-pullback-image : (target-base ∘ pulled-evaluation) =₁
    (source-base ∘ source-coordinate)
  base-pullback-image = ConeIdentification₁.right pullback-computation

  pulled-family : Target.Family parameter-category
  pulled-family = functor-over pulled-evaluation base-pullback-image

  private
    module Chosen = Target.ChosenFamily pulled-family

  functor : MAP Source.category Target.category
  functor = Chosen.factor

  recovered-family : Target.Family parameter-category
  recovered-family = Target.evaluated-family functor

  relative-computation : ConeIdentification₁
    (TargetFamilies.family-cone recovered-family)
    (TargetFamilies.family-cone pulled-family)
  relative-computation = TargetFamilies.FamilyComputation.comparison pulled-family

  evaluated-functor : MAP (parameter-category × source-domain) target-domain
  evaluated-functor = FunctorOverBase.functor recovered-family

  family-image : evaluated-functor =₁ pulled-evaluation
  family-image = Chosen.underlying-computation

  relative-matching-image : (base-pullback-image ∙ (target-base ◁ family-image)) =₂
    ((source-base ◁ id₌ source-coordinate) ∙ FunctorOverBase.cell recovered-family)
  relative-matching-image = ConeIdentification₁.compatible relative-computation

  evaluated-pullback-computation : ConeIdentification₁
    (cone-restrict evaluated-functor target-pullback) pulled-cone
  evaluated-pullback-computation = cone-compose pullback-computation
    (cone-action-One target-pullback family-image)
```

The two computation laws retain different specified data. The pullback
computation includes the target pullback's actual matching, while the
relative computation retains the selected triangle over the new base.
Its matching image relates the composed second projection to that selected
triangle with the explicit identity boundary. No agreement with a separately
chosen pointwise pullback factor or additional base-change coherence is
asserted here.
