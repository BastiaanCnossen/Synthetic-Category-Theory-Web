# Recovery after uncurrying a transformation

Currying the evaluated transformation recovers the original framed
transformation. The proof first reflects the exchanged diagram comparison,
including both endpoint equations, and then uses diagram recovery.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingUncurryingRecovery
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingDiagramEndpoints as Normalization
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingExpressions as Currying
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingEndpointImages as Images
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurriedDiagramComparisons as Reflection
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DiagramExpressionIdentifications as Diagrams
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (expressionIso-compose; expressionIso-inverse)

module At {Γ X C : CAT} {f g : MAP Γ (Fun X C)} (α : MorphismExpression f g) where
  module N = Normalization.At 𝒯 M ℱ P I E α
    using (comparison; source-compatible; target-compatible; uncurried; module B; module Endpoint)
  module A = Currying.Curry 𝒯 M ℱ I f g N.uncurried
    using (diagram; first-curry; value; module Endpoint; module Source; module Target)
  module Original = MorphismExpression α
    using (arrow; source-frame; target-frame)
  module Recovery = Diagrams.Recovery 𝒯 M ℱ P I E α
    using (H; comparison; p; q)
  β : funUncurry A.first-curry =₁ A.diagram
  β = funCurry-β A.diagram
  δ : funUncurry A.first-curry =₁ funUncurry Recovery.H
  δ = N.comparison ∙ β
  module Reflected = Reflection.Reflect 𝒯 M ℱ P I E A.first-curry Recovery.H δ
    using (module WithEndpoints)

  module Endpoint (z : Obj-abs [1]) (h : MAP Γ (Fun X C))
    (a : (evaluate z ∘ Original.arrow) =₁ h)
    (b : (evaluate z ∘ N.B.arrow) =₁ funUncurry h) where
    module Old = N.Endpoint z a (b ∙ (evaluate-uncurry z N.B.arrow) ⁻¹)
      using (R; before)
    module New = A.Endpoint z h b
      using (reflected)
    module Image = Images.At.Endpoint 𝒯 M ℱ I f g N.uncurried z h b
      using (comparison)
    i = insert {X = Γ} z
    s = productMap i (id X)
    ρ : funUncurry (A.first-curry ∘ i) =₁ (funUncurry A.first-curry ∘ s)
    ρ = funUncurry-restrict A.first-curry i
    front = b ∙ (evaluate-uncurry z N.B.arrow) ⁻¹
    B : (funUncurry A.first-curry ∘ s) =₁ (A.diagram ∘ s)
    B = β ▷ s

    abstract
      compatible : (Old.R ∙ (N.comparison ▷ s)) =₂ (front ∙ Old.before) →
        (Old.R ∙ (δ ▷ s)) =₂ (funUncurryIso New.reflected ∙ ρ ⁻¹)
      compatible same = Image.comparison ⁻¹ ∙
        isoComp-cong same (idIso B) ∙
        (isoComp-assoc-at Old.R (N.comparison ▷ s) B) ⁻¹ ∙
        isoComp-cong (idIso Old.R) (preWhisker-isoComp-at N.comparison β s)

  module Source = Endpoint zero f Original.source-frame N.B.source-frame
    using (compatible)
  module Target = Endpoint one g Original.target-frame N.B.target-frame
    using (compatible)
  module Compared = Reflected.WithEndpoints A.Source.reflected A.Target.reflected Recovery.p Recovery.q
    (Source.compatible N.source-compatible) (Target.compatible N.target-compatible)
    using (value)

  value : ExpressionIso A.value α
  value = expressionIso-compose (expressionIso-inverse Recovery.comparison) Compared.value
```
