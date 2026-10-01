# Transport for cartesian and cocartesian fibrations

The invertible unit or counit identifies directed evaluation of the
chosen lift with the input. Expressing this as a comparison of endpoint
cones gives transport, its source and target frames, and its image in
the base. This is the construction in
`sec:Covariant_Transport_For_Cocartesian_Fibrations`, for every absolute
parameter category. Initiality or terminality of the chosen lift is a
separate assertion and is not assumed in the construction.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section05.Transport
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section05.Fibrations 𝒯 M ℱ P I E S public
  using (module Fibration)
open import SCT.VolumeI.Chapter04.Section01.DirectedEvaluation 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SectionIdentifications 𝒯 M ℱ P I E S R
  using (left-section-identification; right-section-identification)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.SplitComparisonLifts 𝒯 P
  using (module Split)

module Covariant {A B : CAT} (f : MAP A B) (w : Fibration.CocartesianFibration f)
  {Γ : CAT} (x : MAP Γ A) (y : MAP Γ B)
  (β : MorphismExpression (f ∘ x) y) where
  open Evaluation f
  private module W = Fibration.CocartesianFibration w
  input = retarget-expression β (idIso (f ∘ x)) ((comp-unitˡ y) ⁻¹)
  target-cone = Left.cone x y input
  private
    module L = Split.At (Left.cone ev₀ (f ∘ ev₁) left-expression)
      W.lift (left-section-identification W.left-adjoint-section) target-cone
      using (factor; factor-β)

  lift : MAP Γ (Ar A)
  lift = L.factor

  lift-β : ConeIso
    (conePre lift (Left.cone ev₀ (f ∘ ev₁) left-expression)) target-cone
  lift-β = L.factor-β

  transport : MAP Γ A
  transport = ev₁ ∘ lift

  source-frame : (ev₀ ∘ lift) =₁ x
  source-frame = pair-β₁ x y ∙
    ((pr₁ ◁ ConeIso.rightIso lift-β) ∙ (project-pair₁ ev₀ (f ∘ ev₁) lift) ⁻¹)

  target-frame : (f ∘ transport) =₁ y
  target-frame = pair-β₂ x y ∙
    ((pr₂ ◁ ConeIso.rightIso lift-β) ∙
      ((project-pair₂ ev₀ (f ∘ ev₁) lift) ⁻¹ ∙ (comp-assoc lift ev₁ f) ⁻¹))

  image : (funPost f ∘ lift) =₁ MorphismExpression.arrow β
  image = ConeIso.leftIso lift-β

  lifted-expression : MorphismExpression x transport
  lifted-expression = record
    { arrow = lift ; source-frame = source-frame ; target-frame = idIso transport }

module Contravariant {A B : CAT} (f : MAP A B) (w : Fibration.CartesianFibration f)
  {Γ : CAT} (x : MAP Γ B) (y : MAP Γ A)
  (β : MorphismExpression x (f ∘ y)) where
  open Evaluation f
  private module W = Fibration.CartesianFibration w
  input = retarget-expression β ((comp-unitˡ x) ⁻¹) (idIso (f ∘ y))
  target-cone = Right.cone x y input
  private
    module L = Split.At (Right.cone (f ∘ ev₀) ev₁ right-expression)
      W.lift (right-section-identification W.right-adjoint-section) target-cone
      using (factor; factor-β)

  lift : MAP Γ (Ar A)
  lift = L.factor

  lift-β : ConeIso
    (conePre lift (Right.cone (f ∘ ev₀) ev₁ right-expression)) target-cone
  lift-β = L.factor-β

  transport : MAP Γ A
  transport = ev₀ ∘ lift

  source-frame : (f ∘ transport) =₁ x
  source-frame = pair-β₁ x y ∙
    ((pr₁ ◁ ConeIso.rightIso lift-β) ∙
      ((project-pair₁ (f ∘ ev₀) ev₁ lift) ⁻¹ ∙ (comp-assoc lift ev₀ f) ⁻¹))

  target-frame : (ev₁ ∘ lift) =₁ y
  target-frame = pair-β₂ x y ∙
    ((pr₂ ◁ ConeIso.rightIso lift-β) ∙ (project-pair₂ (f ∘ ev₀) ev₁ lift) ⁻¹)

  image : (funPost f ∘ lift) =₁ MorphismExpression.arrow β
  image = ConeIso.leftIso lift-β

  lifted-expression : MorphismExpression transport y
  lifted-expression = record
    { arrow = lift ; source-frame = idIso transport ; target-frame = target-frame }
```
