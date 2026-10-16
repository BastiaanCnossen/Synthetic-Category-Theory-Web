# Natural transformation whiskering with common named endpoints

The arrows are the actual funPre and funPost actions. Endpoint frames are
chosen explicitly through internal composition and its common named-vertex
comparisons. Both endpoint equations are retained. No comparison with the
different frame choices of the deferred literal-square draft is asserted.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.NaturalTransformationWhiskering where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun using (funName)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre; funPost)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (MorphismFamily; MorphismFamilyIdentification; identity-family)
open import SCT.VolumeI.Chapter02.Section01.MorphismFunctor using (map-morphism-family)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (retarget-family)
open import SCT.VolumeI.Chapter02.Section02.ProductMorphismFamilies using (pair-morphism-family)
open import SCT.VolumeI.Chapter02.Section02.FixedInputMorphismFamilies using (module Transfer)
import SCT.VolumeI.Chapter02.Section02.FixedInputMorphismFamilies as Fixed
import SCT.VolumeI.Chapter02.Section02.InternalComposition as Internal

module _ {Γ : Context} where
  module Pre {B C D : CAT Γ} (u : MAP B C) {F G : MAP C D}
    (α : MorphismFamily (funName F) (funName G)) where
    private
      module InternalAction = Internal.At B C D
        using (composeFunctor; module FixRight; module Named)
    private
      module Coordinate = Fixed.FixRight {A = Fun C D} {B = Fun B C} (funName u)
        using (frame; insertion; module Arrow)
    private
      module Unary = InternalAction.FixRight u
        using (comparison)
    paired : MorphismFamily (pair (funName F) (funName u)) (pair (funName G) (funName u))
    paired = pair-morphism-family α (identity-family (funName u))
    private
      module Compared = Transfer {A = Fun C D} {B = Fun C D × Fun B C} {C = Fun B D}
        InternalAction.composeFunctor Coordinate.insertion (funPre {D = D} u) Unary.comparison
        {x = funName F} {x′ = funName G}
        {y = pair (funName F) (funName u)} {y′ = pair (funName G) (funName u)}
        {z = funName (F ∘ u)} {z′ = funName (G ∘ u)}
        α paired (Coordinate.frame (funName F)) (Coordinate.frame (funName G))
        (InternalAction.Named.comparison F u) (InternalAction.Named.comparison G u)
        (Coordinate.Arrow.comparison α)
        using (source-frame; target-frame; comparison)
    source-endpoint : (funPre {D = D} u ∘ funName F) =₁ funName (F ∘ u)
    source-endpoint = Compared.source-frame
    target-endpoint : (funPre {D = D} u ∘ funName G) =₁ funName (G ∘ u)
    target-endpoint = Compared.target-frame
    action : MorphismFamily (funName (F ∘ u)) (funName (G ∘ u))
    action = retarget-family (map-morphism-family (funPre {D = D} u) α) source-endpoint target-endpoint
    comparison : MorphismFamilyIdentification One
      (retarget-family (map-morphism-family InternalAction.composeFunctor paired)
        (InternalAction.Named.comparison F u) (InternalAction.Named.comparison G u)) action
    comparison = Compared.comparison

  module Post {B C D : CAT Γ} (F : MAP C D) {u v : MAP B C}
    (β : MorphismFamily (funName u) (funName v)) where
    private
      module InternalAction = Internal.At B C D
        using (composeFunctor; module FixLeft; module Named)
    private
      module Coordinate = Fixed.FixLeft {A = Fun C D} {B = Fun B C} (funName F)
        using (frame; insertion; module Arrow)
    private
      module Unary = InternalAction.FixLeft F
        using (comparison)
    paired : MorphismFamily (pair (funName F) (funName u)) (pair (funName F) (funName v))
    paired = pair-morphism-family (identity-family (funName F)) β
    private
      module Compared = Transfer {A = Fun B C} {B = Fun C D × Fun B C} {C = Fun B D}
        InternalAction.composeFunctor Coordinate.insertion (funPost {C = B} F) Unary.comparison
        {x = funName u} {x′ = funName v}
        {y = pair (funName F) (funName u)} {y′ = pair (funName F) (funName v)}
        {z = funName (F ∘ u)} {z′ = funName (F ∘ v)}
        β paired (Coordinate.frame (funName u)) (Coordinate.frame (funName v))
        (InternalAction.Named.comparison F u) (InternalAction.Named.comparison F v)
        (Coordinate.Arrow.comparison β)
        using (source-frame; target-frame; comparison)
    source-endpoint : (funPost {C = B} F ∘ funName u) =₁ funName (F ∘ u)
    source-endpoint = Compared.source-frame
    target-endpoint : (funPost {C = B} F ∘ funName v) =₁ funName (F ∘ v)
    target-endpoint = Compared.target-frame
    action : MorphismFamily (funName (F ∘ u)) (funName (F ∘ v))
    action = retarget-family (map-morphism-family (funPost {C = B} F) β) source-endpoint target-endpoint
    comparison : MorphismFamilyIdentification One
      (retarget-family (map-morphism-family InternalAction.composeFunctor paired)
        (InternalAction.Named.comparison F u) (InternalAction.Named.comparison F v)) action
    comparison = Compared.comparison

  pre-whisker : {B C D : CAT Γ} (u : MAP B C) {F G : MAP C D} →
    MorphismFamily (funName F) (funName G) → MorphismFamily (funName (F ∘ u)) (funName (G ∘ u))
  pre-whisker {B} {C} {D} u {F} {G} α = Pre.action {B} {C} {D} u {F} {G} α
  post-whisker : {B C D : CAT Γ} (F : MAP C D) {u v : MAP B C} →
    MorphismFamily (funName u) (funName v) → MorphismFamily (funName (F ∘ u)) (funName (F ∘ v))
  post-whisker {B} {C} {D} F {u} {v} β = Post.action {B} {C} {D} F {u} {v} β
```
