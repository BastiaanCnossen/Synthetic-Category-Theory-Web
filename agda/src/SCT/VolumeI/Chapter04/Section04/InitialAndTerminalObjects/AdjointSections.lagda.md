# Universal objects give adjoint sections

An initial object defines a left adjoint section of the functor to the
terminal category, and a terminal object defines a right adjoint
section. This proves implication (1) to (2) in
`lem:Characterization_Initial_Objects` and its dual.

The universal arrow gives the counit or unit. One triangle follows from
uniqueness of arrows at the universal object, and the other lies in the
terminal category. The relevant unit or counit is invertible because
every expression in the terminal category has inverse equations.
The converse characterization and the relaxation criterion are not
asserted here.

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

module SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.AdjointSections
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.UniversalComparisons 𝒯 M ℱ P I
  using (initial-comparison; terminal-comparison)
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.ExpressionComparisons 𝒯 M ℱ P I
  using (reflect-retarget-comparison)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantFunctorExpressions 𝒯 M ℱ P I E
  using () renaming (terminal-expression-unique to terminal-expression-comparison)

private
  terminal-invertible : {Γ : CAT} {x y : MAP Γ One}
    (f : MorphismExpression x y) → IsInvertibleExpression f
  terminal-invertible {x = x} {y} f = record
    { right-inverse = isomorphism-expression (terminal-iso y x)
    ; left-inverse = isomorphism-expression (terminal-iso y x)
    ; right-inverse-law = terminal-expression-comparison _ _
    ; left-inverse-law = terminal-expression-comparison _ _ }

  initial-endomorphisms : {C : CAT} (x : Obj-abs C) → IsInitial x →
    (α β : MorphismExpression x x) → ExpressionIso α β
  initial-endomorphisms x e α β = reflect-retarget-comparison α β
    ((const-One x) ⁻¹) (idIso x)
    (initial-comparison x e x
      (retarget-expression α ((const-One x) ⁻¹) (idIso x))
      (retarget-expression β ((const-One x) ⁻¹) (idIso x)))

  terminal-endomorphisms : {C : CAT} (x : Obj-abs C) → IsTerminal x →
    (α β : MorphismExpression x x) → ExpressionIso α β
  terminal-endomorphisms x e α β = reflect-retarget-comparison α β
    (idIso x) ((const-One x) ⁻¹)
    (terminal-comparison x e x
      (retarget-expression α (idIso x) ((const-One x) ⁻¹))
      (retarget-expression β (idIso x) ((const-One x) ⁻¹)))

initial-adjunction : {C : CAT} (x : Obj-abs C) → IsInitial x → Adjunction x (terminate C)
initial-adjunction {C} x e = record
  { unit = isomorphism-expression (terminal-iso (id One) (terminate C ∘ x))
  ; counit = initial-expression x e (id C)
  ; left-triangle = initial-endomorphisms x e _ _
  ; right-triangle = terminal-expression-comparison _ _ }

terminal-adjunction : {C : CAT} (x : Obj-abs C) → IsTerminal x → Adjunction (terminate C) x
terminal-adjunction {C} x e = record
  { unit = terminal-expression x e (id C)
  ; counit = isomorphism-expression (terminal-iso (terminate C ∘ x) (id One))
  ; left-triangle = terminal-expression-comparison _ _
  ; right-triangle = terminal-endomorphisms x e _ _ }

initial-left-adjoint-section : {C : CAT} (x : Obj-abs C) → IsInitial x →
  LeftAdjointSection (terminate C) x
initial-left-adjoint-section x e = record
  { adjunction = initial-adjunction x e
  ; unit-invertible = terminal-invertible (Adjunction.unit (initial-adjunction x e)) }

terminal-right-adjoint-section : {C : CAT} (x : Obj-abs C) → IsTerminal x →
  RightAdjointSection (terminate C) x
terminal-right-adjoint-section x e = record
  { adjunction = terminal-adjunction x e
  ; counit-invertible = terminal-invertible (Adjunction.counit (terminal-adjunction x e)) }
```
