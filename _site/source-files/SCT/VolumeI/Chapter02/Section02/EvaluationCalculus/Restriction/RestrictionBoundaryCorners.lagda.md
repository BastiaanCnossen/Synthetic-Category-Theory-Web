# Corner comparisons under a change of diagram shape

Restriction by a face and then by a shape map is compared with restriction
by the specified boundary edge. Evaluation carries this comparison and
its vertex identification. The resulting comparison of whole cones can
then be restricted to an arbitrary family.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionEndpointComposition as Composition
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionCornerTransport as Corners
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionBoundaryCorners
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionEvaluation 𝒯 M ℱ P public
open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.EndpointCornerFamilies 𝒯 M ℱ P using (evaluate-cong-inverse)
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P using (preComp; preCong)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-pre; conePre-assoc; coneIso-compose; coneIso-inverse; coneIso-adjust)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (post-square)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square; cancel-right; cancel-left; cancel-left-reflect)

module Edge {A K B C : CAT} (d : MAP A K) (j : MAP K B)
  (r : MAP A B) (α : (j ∘ d) =₁ r) (u : Obj-abs A) where
  pc = preComp {E = C} d j
  pg = preCong {E = C} α
  forward = pg ∙ pc
  backward = pc ⁻¹ ∙ pg ⁻¹
  ev = evaluate {C = C} u
  va = evaluate-cong {C = C} (comp-assoc u d j)
  vα = evaluate-cong {C = C} (α ▷ u)
  old = evaluate-pre {C = C} (j ∘ d) u
  new = evaluate-pre {C = C} r u
  route = evaluate-pre {C = C} j (d ∘ u) ∙
    ((evaluate-pre d u ▷ funPre j) ∙ (comp-assoc (funPre j) (funPre d) ev) ⁻¹)
  vertex = (α ▷ u) ∙ (comp-assoc u d j) ⁻¹

  abstract
    first : (old ∙ (ev ◁ pc)) =₂ (va ⁻¹ ∙ route)
    first = isoComp-cong (idIso (va ⁻¹)) (Composition.At.comparison 𝒯 M ℱ P d j u) ∙
      (cancel-left va (old ∙ (ev ◁ pc))) ⁻¹

    forward-image : (new ∙ (ev ◁ forward)) =₂ (evaluate-cong vertex ∙ route)
    forward-image = isoComp-cong
        ((isoComp-cong (idIso vα) (evaluate-cong-inverse (comp-assoc u d j)) ∙
          evaluate-cong-comp (α ▷ u) ((comp-assoc u d j) ⁻¹)) ⁻¹) (idIso route) ∙
      ((isoComp-assoc-at vα (va ⁻¹) route) ⁻¹ ∙
      (isoComp-cong (idIso vα) first ∙
      ((isoComp-assoc-at vα old (ev ◁ pc)) ∙
      (isoComp-cong (Restriction.natural α u) (idIso (ev ◁ pc)) ∙
      ((isoComp-assoc-at new (ev ◁ pg) (ev ◁ pc)) ⁻¹ ∙
        isoComp-cong (idIso new) (postWhisker-isoComp-at ev pg pc))))))

module Corner {A D K B C : CAT} (u : Obj-abs A) (v : Obj-abs D)
  (d : MAP A K) (k : MAP D K) (j : MAP K B)
  (δ : (d ∘ u) =₁ (k ∘ v))
  (r : MAP A B) (s : MAP D B)
  (α : (j ∘ d) =₁ r) (β : (j ∘ k) =₁ s)
  (ε : (r ∘ u) =₁ (s ∘ v))
  (shape : (ε ∙ Edge.vertex {C = C} d j r α u) =₂
    (Edge.vertex {C = C} k j s β v ∙ (j ◁ δ))) where
  module L = Edge {C = C} d j r α u
  module R = Edge {C = C} k j s β v
  module Inner = Corners.At 𝒯 M ℱ P {C = C} u v d k j δ
  p = L.new
  q = R.new
  vertex = evaluate-cong {C = C} ε
  χ = evaluate-cong {C = C} L.vertex
  ψ = evaluate-cong {C = C} R.vertex
  middle = evaluate-cong {C = C} (j ◁ δ)
  τ = q ⁻¹ ∙ (vertex ∙ p)
  outer : Cone (evaluate {C = C} u) (evaluate v) (Fun B C)
  outer = record { left = funPre r ; right = funPre s ; match = τ }

  abstract
    outer-square : (q ∙ τ) =₂ (vertex ∙ p)
    outer-square = cancel-inverse q (vertex ∙ p)

    vertex-square : (vertex ∙ χ) =₂ (ψ ∙ middle)
    vertex-square = evaluate-cong-comp R.vertex (j ◁ δ) ∙
      (evaluate-cong-Iso₂ shape ∙ (evaluate-cong-comp ε L.vertex) ⁻¹)

    compatible : (τ ∙ (evaluate u ◁ L.forward)) =₂
      ((evaluate v ◁ R.forward) ∙ Inner.matching)
    compatible = cancel-left-reflect q
      (isoComp-assoc-at q (evaluate v ◁ R.forward) Inner.matching ∙
      (isoComp-cong (R.forward-image ⁻¹) (idIso Inner.matching) ∙
      ((isoComp-assoc-at ψ Inner.right-route Inner.matching) ⁻¹ ∙
      (isoComp-cong (idIso ψ) (Inner.comparison ⁻¹) ∙
      (isoComp-assoc-at ψ middle Inner.left-route ∙
      (isoComp-cong vertex-square (idIso Inner.left-route) ∙
      ((isoComp-assoc-at vertex χ Inner.left-route) ⁻¹ ∙
      (isoComp-cong (idIso vertex) L.forward-image ∙
      (isoComp-assoc-at vertex p (evaluate u ◁ L.forward) ∙
      (isoComp-cong outer-square (idIso (evaluate u ◁ L.forward)) ∙
        (isoComp-assoc-at q τ (evaluate u ◁ L.forward)) ⁻¹))))))))))

  comparison : ConeIso (conePre (funPre j) Inner.cone) outer
  comparison = record
    { leftIso = L.forward ; rightIso = R.forward ; compatible = compatible }

  module Family {Γ : CAT} (W : MAP Γ (Fun B C)) where
    raw = coneIso-compose (conePre-assoc W (funPre j) Inner.cone)
      (coneIso-inverse (coneIso-pre W comparison))
    left = comp-assoc W (funPre j) (funPre d) ∙
      ((L.pc ▷ W) ⁻¹ ∙ (L.pg ▷ W) ⁻¹)
    right = comp-assoc W (funPre j) (funPre k) ∙
      ((R.pc ▷ W) ⁻¹ ∙ (R.pg ▷ W) ⁻¹)

    abstract
      left-normal : ConeIso.leftIso raw =₂ left
      left-normal = isoComp-cong (idIso (comp-assoc W (funPre j) (funPre d)))
        (inverse-composite (L.pg ▷ W) (L.pc ▷ W) ∙
          (＝-inv ◁ preWhisker-isoComp-at L.pg L.pc W))
      right-normal : ConeIso.rightIso raw =₂ right
      right-normal = isoComp-cong (idIso (comp-assoc W (funPre j) (funPre k)))
        (inverse-composite (R.pg ▷ W) (R.pc ▷ W) ∙
          (＝-inv ◁ preWhisker-isoComp-at R.pg R.pc W))

    value : ConeIso (conePre W outer) (conePre (funPre j ∘ W) Inner.cone)
    value = coneIso-adjust raw left right left-normal right-normal
```
