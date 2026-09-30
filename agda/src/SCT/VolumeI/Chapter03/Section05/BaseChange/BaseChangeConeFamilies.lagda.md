# The whole evaluated cone of actual base change

Restrict the base-change evaluation cone along a family of relative
functors. Its comparison retains the two projections and the matching.
For an identification of families, use the action of the actual
base-change functor and transport that whole cone comparison. This
avoids choosing a second native pullback lift for the identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeConeFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
  using (coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange 𝒯 M ℱ P using (module BaseChange)

module Families {C D S T : CAT} (p : MAP S T) (f : MAP C T) (g : MAP D T) where
  module BC = BaseChange p f g using (f′; g′; functor; cone; evaluation-comparison)
  Source = FunOver f g
  forget = Over.forget BC.f′ BC.g′
  evaluated = funUncurry (forget ∘ BC.functor)

  module At {X : CAT} (F : MAP X Source) where
    parameter = productMap F (id (Pullback f p))
    value = funUncurry (forget ∘ (BC.functor ∘ F))
    source = conePre value (pullbackCone g p)
    target = conePre parameter BC.cone
    abstract
      evaluation : value =₁ (evaluated ∘ parameter)
      evaluation = funUncurry-restrict (forget ∘ BC.functor) F ∙
        funUncurryIso ((comp-assoc F BC.functor forget) ⁻¹)
      comparison : ConeIso source target
      comparison = coneIso-compose (coneIso-pre parameter BC.evaluation-comparison)
        (coneIso-compose (coneIso-inverse (conePre-assoc parameter evaluated (pullbackCone g p)))
          (cone-action (pullbackCone g p) evaluation))

  module Identification {X : CAT} {F G : MAP X Source} (α : F =₁ G) where
    module Left = At F using (value; source; target; comparison)
    module Right = At G using (value; source; target; comparison)
    action : Left.value =₁ Right.value
    action = funUncurryIso (forget ◁ (BC.functor ◁ α))
    abstract
      comparison : ConeIso Left.target Right.target
      comparison = coneIso-compose Right.comparison
        (coneIso-compose (cone-action (pullbackCone g p) action)
          (coneIso-inverse Left.comparison))
```
