# Endpoint changes on framed morphism families

Changing both endpoint functors retargets the decoded expression by the
restricted endpoint identifications. The computation below compares the
whole mapped cone with the cone of that expression. In particular, it
keeps the base parameter and the specified paired matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberChangeExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberExpressions 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence
  vocabulary terminal products productLaws composition vertical whiskering using (pair-cong-comp)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering using (pair-pre-natural-inputs; move-square)
import SCT.VolumeI.Chapter01.Section06.Cospans.FamilyChange as Family
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberEquivalences as Equivalences

open Laws.PullbackStructure P using (pullbackCone)

module Along {B C : CAT} {u v u′ v′ : MAP B C}
  (α : u =₁ u′) (β : v =₁ v′) where
  private
    module Change = Family.Change 𝒯 P endpoints (pair-cong α β)
      using (value; computation; action; restrict)
    module Actual = Equivalences.ChangeEndpoints 𝒯 M ℱ P I α β using (map; map-isEquiv)
    module Original = Fiber u v using (decode; encode-decode)
    module Source = EndpointFiber u v
      using (base; category; cone)
    module Target = EndpointFiber u′ v′
      using (cone)

  module Encoded {Γ : CAT} (b : MAP Γ B) (f : MorphismExpression (u ∘ b) (v ∘ b)) where
    reframed : MorphismExpression (u′ ∘ b) (v′ ∘ b)
    reframed = retarget-expression f (α ▷ b) (β ▷ b)
    private
      p = pair-pre u v b
      p′ = pair-pre u′ v′ b
      a₀ = pair-cong (α ▷ b) (β ▷ b)
      θ = pair-cong α β ▷ b
      frames = pair-cong (MorphismExpression.source-frame f) (MorphismExpression.target-frame f)
      frames′ = pair-cong (MorphismExpression.source-frame reframed) (MorphismExpression.target-frame reframed)
      boundary = pair-pre ev₀ ev₁ (MorphismExpression.arrow f)
      abstract
        frame-change : ((p′ ⁻¹) ∙ a₀) =₂ (θ ∙ p ⁻¹)
        frame-change = move-square p′ θ a₀ p ((pair-pre-natural-inputs α β b) ⁻¹)
        matching : Cone.match (Target.cone b reframed) =₂ Cone.match (Change.value (Source.cone b f))
        matching = isoComp-assoc-at θ (p ⁻¹) (frames ∙ boundary) ∙
          isoComp-cong frame-change (idIso (frames ∙ boundary)) ∙
          (isoComp-assoc-at (p′ ⁻¹) a₀ (frames ∙ boundary)) ⁻¹ ∙
          isoComp-cong (idIso (p′ ⁻¹)) (isoComp-assoc-at a₀ frames boundary) ∙
          isoComp-cong (idIso (p′ ⁻¹))
            (isoComp-cong (pair-cong-comp (α ▷ b) (MorphismExpression.source-frame f)
              (β ▷ b) (MorphismExpression.target-frame f)) (idIso boundary))

    comparison : ConeIso (Change.value (Source.cone b f)) (Target.cone b reframed)
    comparison = cone-match-change _ _ _ _ (matching ⁻¹)

  module At {Γ : CAT} (s : Cone endpoints (pair u v) Γ) where
    original : MorphismExpression (u ∘ Cone.right s) (v ∘ Cone.right s)
    original = Original.decode s
    normalized : MorphismExpression (u′ ∘ Cone.right s) (v′ ∘ Cone.right s)
    normalized = Encoded.reframed (Cone.right s) original
    comparison : ConeIso (Change.value s) (Target.cone (Cone.right s) normalized)
    comparison = coneIso-compose (Encoded.comparison (Cone.right s) original)
      (Change.action (Original.encode-decode s))

  open Actual public using (map; map-isEquiv)
  universal = pullbackCone endpoints (pair u v)
  normalized = At.normalized universal
  cone = Target.cone Source.base normalized

  computation : ConeIso (conePre map (pullbackCone endpoints (pair u′ v′))) cone
  computation = coneIso-compose (At.comparison universal) Change.computation


  module Specified {Γ : CAT} (h : MAP Γ Source.category) (b : MAP Γ B)
    (f : MorphismExpression (u ∘ b) (v ∘ b))
    (Φ : ConeIso (conePre h universal) (Source.cone b f)) where
    family : MorphismExpression (u′ ∘ b) (v′ ∘ b)
    family = Encoded.reframed b f
    family-cone : Cone endpoints (pair u′ v′) Γ
    family-cone = Target.cone b family
    abstract
      family-computation : ConeIso
        (conePre (map ∘ h) (pullbackCone endpoints (pair u′ v′))) family-cone
      family-computation = coneIso-compose (Encoded.comparison b f)
        (coneIso-compose (Change.action Φ)
          (coneIso-compose (Change.restrict h universal)
            (coneIso-compose (coneIso-pre h Change.computation)
              (coneIso-inverse (conePre-assoc h map (pullbackCone endpoints (pair u′ v′)))))))
```
