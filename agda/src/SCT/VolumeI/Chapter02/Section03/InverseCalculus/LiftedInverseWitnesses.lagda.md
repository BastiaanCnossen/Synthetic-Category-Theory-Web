# Reading absolute inverse witnesses from a lift

Decode the two triangles and their three edge comparisons. Their vertex
equations are then constructed by `AbsoluteInverseTriangles`, rather
than inferred by forgetting the endpoint frames. Together with
`invertible-lift`, this proves `rmk:Lift_To_Iso_Iff_Invertible` before
either Segal or Rezk is used.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.LiftedInverseWitnesses
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.AbsoluteInverseTriangles 𝒯 M ℱ P I E public
import SCT.VolumeI.Chapter02.Section03.InverseCalculus.InverseTriangleData 𝒯 M ℱ P I E as Data
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M using (oneProduct-in)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DiagramNames 𝒯 M ℱ using (named-restriction)

reflect-diagram-name : {A C : CAT} {f g : MAP A C} → nameFun f =₁ nameFun g → f =₁ g
reflect-diagram-name {A} {f = f} {g} δ = decode-nameFun g ∙
  ((funUncurryIso δ ▷ oneProduct-in A) ∙ (decode-nameFun f) ⁻¹)

decode-edge : {A B C : CAT} (τ : Obj-abs (Fun B C)) (r : MAP A B) (h : MAP A C) →
  (funPre r ∘ τ) =₁ nameFun h → (decodeFun τ ∘ r) =₁ h
decode-edge τ r h ε = reflect-diagram-name
  (ε ∙ ((funPre r ◁ name-decodeFun τ) ∙ (named-restriction r (decodeFun τ)) ⁻¹))

module ReadWitnesses {C : CAT} {x y : Obj-abs C}
  (f : Morphism x y) (w : IsoLift (nameFun (Morphism.diagram f))) where
  module W = IsoLift w
    using (comparison; lift)
  module U = Data.UniversalData C
    using (right-triangle; left-triangle; right-short; left-short; right-long; left-long)

  right-point left-point : Obj-abs (Triangles C)
  right-point = U.right-triangle ∘ W.lift
  left-point = U.left-triangle ∘ W.lift

  right-short : (edge₀ ∘ right-point) =₁ nameFun (Morphism.diagram f)
  right-short = W.comparison ∙ ((U.right-short ▷ W.lift) ∙
    (comp-assoc W.lift U.right-triangle edge₀) ⁻¹)
  left-short : (edge₂ ∘ left-point) =₁ nameFun (Morphism.diagram f)
  left-short = W.comparison ∙ ((U.left-short ▷ W.lift) ∙
    (comp-assoc W.lift U.left-triangle edge₂) ⁻¹)

  right-center = (pr₂ ∘ isoObjects) ∘ W.lift
  left-center = (pr₁ ∘ isoObjects) ∘ W.lift

  right-long : (edge₁ ∘ right-point) =₁ nameFun (const right-center)
  right-long = constantDiagram-point right-center ∙
    (comp-assoc W.lift (pr₂ ∘ isoObjects) identityArrow ∙
      ((U.right-long ▷ W.lift) ∙ (comp-assoc W.lift U.right-triangle edge₁) ⁻¹))
  left-long : (edge₁ ∘ left-point) =₁ nameFun (const left-center)
  left-long = constantDiagram-point left-center ∙
    (comp-assoc W.lift (pr₁ ∘ isoObjects) identityArrow ∙
      ((U.left-long ▷ W.lift) ∙ (comp-assoc W.lift U.left-triangle edge₁) ⁻¹))

  module RightWitness = Right f (decodeFun right-point)
    (decode-edge right-point d₀ (Morphism.diagram f) right-short)
    (decode-edge right-point d₁ (const right-center) right-long) using (inverse; witness)
  module LeftWitness = Left f (decodeFun left-point)
    (decode-edge left-point d₂ (Morphism.diagram f) left-short)
    (decode-edge left-point d₁ (const left-center) left-long) using (inverse; witness)

  inverse-data : IsInvertible f
  inverse-data = record
    { right-inverse = RightWitness.inverse ; left-inverse = LeftWitness.inverse
    ; right-inverse-triangle = RightWitness.witness ; left-inverse-triangle = LeftWitness.witness }

lift-invertible : {C : CAT} {x y : Obj-abs C} (f : Morphism x y) →
  IsoLift (nameFun (Morphism.diagram f)) → IsInvertible f
lift-invertible = ReadWitnesses.inverse-data
```
