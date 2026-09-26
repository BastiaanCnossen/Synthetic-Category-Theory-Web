# Lifting through two successive postcompositions

Only the composite needs to be an equivalence. This is useful when
constant diagrams are followed by evaluation: neither functor on the
ambient base need be an equivalence separately.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.Whiskering as WE

module SCT.VolumeI.Chapter02.Section04.PullbackCalculus.DoubleWhiskering
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open WE vocabulary terminal products productLaws composition vertical whiskering using (post-composite)

module Double {C D E : CAT} (u : MAP C D) (v : MAP D E) (e : IsEquiv (v ∘ u)) where
  value : {Γ : CAT} → MAP Γ C → MAP Γ E
  value h = v ∘ (u ∘ h)

  module Lift {Γ : CAT} (h : MAP Γ E) where
    chosen = equiv-lift e h
    lift : MAP Γ C
    lift = FunctorLift.lift chosen
    comparison : value lift =₁ h
    comparison = FunctorLift.comparison chosen ∙ (comp-assoc lift u v) ⁻¹

  module Isomorphisms {Γ : CAT} (h k : MAP Γ C) where
    action : MAP (h ＝ k) (value h ＝ value k)
    action = postWhisker v ∘ postWhisker u
    action-isEquiv : IsEquiv action
    action-isEquiv = post-composite h k u v (postWhisker-isEquiv (v ∘ u) e h k)
    evaluate : (α : h =₁ k) → (action ∘ α) =₂ (v ◁ (u ◁ α))
    evaluate α = comp-assoc α (postWhisker u) (postWhisker v)

    module LiftIso (α : value h =₁ value k) where
      chosen = equiv-lift action-isEquiv α
      lift : h =₁ k
      lift = FunctorLift.lift chosen
      comparison : (v ◁ (u ◁ lift)) =₂ α
      comparison = FunctorLift.comparison chosen ∙ (evaluate lift) ⁻¹

    reflect : (α β : h =₁ k) → (v ◁ (u ◁ α)) =₂ (v ◁ (u ◁ β)) → α =₂ β
    reflect α β p = equiv-reflect action-isEquiv α β ((evaluate β) ⁻¹ ∙ (p ∙ evaluate α))
```
