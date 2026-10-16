# Nested pullbacks

A supplied universal cone supplies the inner factor. The outer and nested
pullbacks retain their actual chosen cones. Flattening pastes the two cones;
insertion uses the supplied universal factor and its complete beta.
The comparisons below expose the selected projection computations directly.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.NestedPullbacks where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-transport; equiv-compose)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; postWhisker-id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (replace-edges₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (comp₌-unitˡ-One; comp₌-unitʳ-One; comp₌-inverseʳ-One; preWhisker-inverse; postWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-triangle)
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.UniversalConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions using (pullback-cone-isPullback; pullback₁-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.ConePasting

module _ {Γ : Context} where
  module Nested {A B X Z Q : CAT Γ} (f : MAP A B) (g : MAP B Z) (h : MAP X Z)
    (t : Cone g h Q) (e : IsPullback t) where
    module Inner = UniversalCone t e
    module Paste = PasteCones f g t

    Outer : CAT Γ
    Outer = Pullback (g ∘ f) h

    NestedVertex : CAT Γ
    NestedVertex = Pullback f (Cone.left t)

    outer-cone : Cone (g ∘ f) h Outer
    outer-cone = pullback-cone (g ∘ f) h

    nested-cone : Cone f (Cone.left t) NestedVertex
    nested-cone = pullback-cone f (Cone.left t)

    flat-cone : Cone (g ∘ f) h NestedVertex
    flat-cone = Paste.paste nested-cone

    flatten : MAP NestedVertex Outer
    flatten = pullback-factor flat-cone

    flatten-β : ConeIdentification₁ (cone-restrict flatten outer-cone) flat-cone
    flatten-β = pullback-factor-β flat-cone

    inner-cone : Cone g h Outer
    inner-cone = postcompose-cone-left f g outer-cone

    inner : MAP Outer Q
    inner = Inner.factor inner-cone

    inner-β : ConeIdentification₁ (cone-restrict inner t) inner-cone
    inner-β = Inner.β inner-cone

    inner-left : (Cone.left t ∘ inner) =₁ (f ∘ Cone.left outer-cone)
    inner-left = ConeIdentification₁.left inner-β

    inner-right : (Cone.right t ∘ inner) =₁ Cone.right outer-cone
    inner-right = ConeIdentification₁.right inner-β

    insertion-cone : Cone f (Cone.left t) Outer
    insertion-cone = record
      { left = Cone.left outer-cone; right = inner; match = inner-left ⁻¹ }

    insert : MAP Outer NestedVertex
    insert = pullback-factor insertion-cone

    insert-β : ConeIdentification₁ (cone-restrict insert nested-cone) insertion-cone
    insert-β = pullback-factor-β insertion-cone

    insert-left : (Cone.left nested-cone ∘ insert) =₁ Cone.left outer-cone
    insert-left = ConeIdentification₁.left insert-β

    insert-right : (Cone.right nested-cone ∘ insert) =₁ inner
    insert-right = ConeIdentification₁.right insert-β
```


## The recovered inner comparison

The full inner cone comparison is assembled from restriction, the actual
flattening beta, and the pasted-cone comparison. Its specified first leg is
retained so that recovery can be used in the insertion matching.

```agda
    inner-left-at-flatten = restrict-triangle (Cone.left t) inner inner-left flatten
    inner-right-at-flatten = restrict-triangle (Cone.right t) inner inner-right flatten
    flatten-left = ConeIdentification₁.left flatten-β
    flatten-right = ConeIdentification₁.right flatten-β
    left-associator = comp-assoc flatten (Cone.left outer-cone) f
    prescribed-inner-left = Cone.match nested-cone ∙ ((f ◁ flatten-left) ∙ left-associator)

    inner-cone-comparison-raw : ConeIdentification₁
      (cone-restrict (inner ∘ flatten) t) (cone-restrict (Cone.right nested-cone) t)
    inner-cone-comparison-raw = cone-compose (Paste.postcompose-paste nested-cone)
      (cone-compose (postcompose-cone-left-identification f g flatten-β)
        (cone-compose (postcompose-cone-left-restrict f g flatten outer-cone)
          (cone-compose (cone-identification-restrict-One flatten inner-β)
            (cone-inverse (cone-restrict-assoc flatten inner t)))))

    inner-cone-comparison : ConeIdentification₁
      (cone-restrict (inner ∘ flatten) t) (cone-restrict (Cone.right nested-cone) t)
    inner-cone-comparison = record
      { left = prescribed-inner-left ∙ inner-left-at-flatten
      ; right = flatten-right ∙ inner-right-at-flatten
      ; compatible = replace-edges₌ (postWhisker g ◁ left-normal)
          (postWhisker h ◁ right-normal) (ConeIdentification₁.compatible inner-cone-comparison-raw) }
      where
      left-normal : ConeIdentification₁.left inner-cone-comparison-raw =₂
        (prescribed-inner-left ∙ inner-left-at-flatten)
      left-normal = (comp₌-assoc (Cone.match nested-cone)
          ((f ◁ flatten-left) ∙ left-associator) inner-left-at-flatten) ⁻¹ ∙
        comp₌-cong (id₌ (Cone.match nested-cone))
          ((comp₌-assoc (f ◁ flatten-left) left-associator inner-left-at-flatten) ⁻¹)

      right-normal : ConeIdentification₁.right inner-cone-comparison-raw =₂
        (flatten-right ∙ inner-right-at-flatten)
      right-normal = comp₌-unitˡ-One (flatten-right ∙ inner-right-at-flatten) ∙
        comp₌-cong (id₌ (id₌ (Cone.right t ∘ Cone.right nested-cone)))
          (comp₌-cong (id₌ flatten-right) (comp₌-unitˡ-One inner-right-at-flatten))

    module RecoveredInner = UniversalConeIdentification t e (inner ∘ flatten)
      (Cone.right nested-cone) inner-cone-comparison

    inner-identification : (inner ∘ flatten) =₁ Cone.right nested-cone
    inner-identification = RecoveredInner.identification

    inner-left-image : (Cone.left t ◁ inner-identification) =₂
      (prescribed-inner-left ∙ inner-left-at-flatten)
    inner-left-image = RecoveredInner.restriction₁

    inner-right-image : (Cone.right t ◁ inner-identification) =₂
      (flatten-right ∙ inner-right-at-flatten)
    inner-right-image = RecoveredInner.restriction₂
```



## The insertion round trip

```agda
    insertion-cone-comparison : ConeIdentification₁
      (cone-restrict flatten insertion-cone) nested-cone
    insertion-cone-comparison = record
      { left = flatten-left; right = inner-identification
      ; compatible = comp₌-cong (inner-left-image ⁻¹) (id₌ restricted-insertion-match) ∙
          cancellation ⁻¹ }
      where
      inner-associator = comp-assoc flatten inner (Cone.left t)
      triangle-at-flatten = inner-left ▷ flatten
      inverse-triangle-at-flatten = (inner-left ⁻¹) ▷ flatten
      restricted-insertion-match = Cone.match (cone-restrict flatten insertion-cone)

      triangle-cancellation : (triangle-at-flatten ∙ inverse-triangle-at-flatten) =₂ id₌ _
      triangle-cancellation = comp₌-inverseʳ-One triangle-at-flatten ∙
        comp₌-cong (id₌ triangle-at-flatten) (preWhisker-inverse inner-left flatten)

      transport-cancellation : (inner-left-at-flatten ∙ restricted-insertion-match) =₂
        (left-associator ⁻¹)
      transport-cancellation = comp₌-unitˡ-One (left-associator ⁻¹) ∙
        (comp₌-cong triangle-cancellation (id₌ (left-associator ⁻¹)) ∙
          ((comp₌-assoc triangle-at-flatten inverse-triangle-at-flatten (left-associator ⁻¹)) ⁻¹ ∙
            (comp₌-cong (id₌ triangle-at-flatten)
                (inv-comp-left inner-associator (inverse-triangle-at-flatten ∙ left-associator ⁻¹)) ∙
              comp₌-assoc triangle-at-flatten (inner-associator ⁻¹) restricted-insertion-match)))

      cancellation : ((prescribed-inner-left ∙ inner-left-at-flatten) ∙ restricted-insertion-match) =₂
        (Cone.match nested-cone ∙ (f ◁ flatten-left))
      cancellation = comp-inv-right (Cone.match nested-cone ∙ (f ◁ flatten-left)) left-associator ∙
        (comp₌-cong ((comp₌-assoc (Cone.match nested-cone) (f ◁ flatten-left) left-associator) ⁻¹)
            (id₌ (left-associator ⁻¹)) ∙
          (comp₌-cong (id₌ prescribed-inner-left) transport-cancellation ∙
            comp₌-assoc prescribed-inner-left inner-left-at-flatten restricted-insertion-match))

    insert-flatten : (insert ∘ flatten) =₁ id NestedVertex
    insert-flatten = pullback-reflect _ _
      (cone-compose (cone-inverse (cone-restrict-id nested-cone))
        (cone-compose insertion-cone-comparison
          (cone-compose (cone-identification-restrict-One flatten insert-β)
            (cone-inverse (cone-restrict-assoc flatten insert nested-cone)))))
```


## The flattening round trip

```agda
    pasted-insertion-comparison : ConeIdentification₁ (Paste.paste insertion-cone) outer-cone
    pasted-insertion-comparison = Paste.paste-factor outer-cone inner inner-β

    flatten-insert : (flatten ∘ insert) =₁ id Outer
    flatten-insert = pullback-reflect _ _
      (cone-compose (cone-inverse (cone-restrict-id outer-cone))
        (cone-compose pasted-insertion-comparison
          (cone-compose (Paste.paste-identification insert-β)
            (cone-compose (Paste.paste-restrict insert nested-cone)
              (cone-compose (cone-identification-restrict-One insert flatten-β)
                (cone-inverse (cone-restrict-assoc insert flatten outer-cone)))))))

    flatten-isEquiv : IsEquiv flatten
    flatten-isEquiv = record
      { inverse = insert; left-inverse-law = insert-flatten ⁻¹; right-inverse-law = flatten-insert ⁻¹ }

    insert-isEquiv : IsEquiv insert
    insert-isEquiv = record
      { inverse = flatten; left-inverse-law = flatten-insert ⁻¹; right-inverse-law = insert-flatten ⁻¹ }

  module ChosenNested {A B X Z : CAT Γ} (f : MAP A B) (g : MAP B Z) (h : MAP X Z) =
    Nested f g h (pullback-cone g h) (pullback-cone-isPullback g h)
```


## Equivalence of the nested projection

```agda
module _ {Γ : Context} where
  nested-projection-isEquiv : {A B X Z : CAT Γ}
    (f : MAP A B) (g : MAP B Z) (h : MAP X Z)
    → IsEquiv (pullback₁ {f = g} {g = h}) → IsEquiv (pullback₁ {f = g ∘ f} {g = h})
  nested-projection-isEquiv f g h ep = equiv-transport (pullback-factor-β₁ N.insertion-cone)
    (equiv-compose N.insert pullback₁ N.insert-isEquiv (pullback₁-isEquiv f pullback₁ ep))
    where module N = ChosenNested f g h


```
