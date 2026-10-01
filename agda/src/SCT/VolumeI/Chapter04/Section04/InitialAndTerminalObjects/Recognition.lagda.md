# Recognizing initial and terminal objects

For `lem:Recognizing_Terminal_Objects`, first transport the defining
slice-projection equivalence along an identification of objects. The
cospan comparison retains both specified squares. Rezk then turns an
invertible canonical arrow into the required identification. Conversely,
the universal properties give both inverse equations for that arrow.

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

module SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.Recognition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.UniversalObjects 𝒯 M ℱ P I E S R public
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.UniversalInverseExpressions 𝒯 M ℱ P I E S
  using (IsInvertibleExpression)
open import SCT.VolumeI.Chapter02.Section03.Isomorphisms 𝒯 M ℱ P I E using (IsoLift)
open import SCT.VolumeI.Chapter02.Section03.RezkIdentification 𝒯 M ℱ P I E R using (module Identify)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberEquivalences 𝒯 M ℱ P I public
  using (module ChangeEndpoints)

initial-invariant : {C : CAT} {x y : Obj-abs C} → x =₁ y → IsInitial x → IsInitial y
initial-invariant {C} p = ChangeEndpoints.projection-isEquiv
  (p ▷ terminate C) (idIso (id C))

terminal-invariant : {C : CAT} {x y : Obj-abs C} → x =₁ y → IsTerminal x → IsTerminal y
terminal-invariant {C} p = ChangeEndpoints.projection-isEquiv
  (idIso (id C)) (p ▷ terminate C)

module InitialRecognition {C : CAT} (x y : Obj-abs C) (ex : IsInitial x) where
  universal-arrow : MorphismExpression (const {P = One} x) (const y)
  universal-arrow = initial-expression x ex (const y)

  invertible-to-initial : IsoLift (MorphismExpression.arrow universal-arrow) → IsInitial y
  invertible-to-initial w = initial-invariant
    (const-One y ∙ (Identify.identification universal-arrow w ∙ (const-One x) ⁻¹)) ex

  initial-to-invertible : IsInitial y → IsInvertibleExpression universal-arrow
  initial-to-invertible ey = record
    { right-inverse = InitialObjects.backward x y ex ey
    ; left-inverse = InitialObjects.backward x y ex ey
    ; right-inverse-law = InitialObjects.right-law x y ex ey
    ; left-inverse-law = InitialObjects.left-law x y ex ey }

  initial-to-lift : IsInitial y → IsoLift (MorphismExpression.arrow universal-arrow)
  initial-to-lift ey = invertible-expression-lift universal-arrow (initial-to-invertible ey)

module TerminalRecognition {C : CAT} (x y : Obj-abs C) (ex : IsTerminal x) where
  universal-arrow : MorphismExpression (const {P = One} y) (const x)
  universal-arrow = terminal-expression x ex (const y)

  invertible-to-terminal : IsoLift (MorphismExpression.arrow universal-arrow) → IsTerminal y
  invertible-to-terminal w = terminal-invariant
    ((const-One x ∙ (Identify.identification universal-arrow w ∙ (const-One y) ⁻¹)) ⁻¹) ex

  terminal-to-invertible : IsTerminal y → IsInvertibleExpression universal-arrow
  terminal-to-invertible ey = record
    { right-inverse = TerminalObjects.forward x y ex ey
    ; left-inverse = TerminalObjects.forward x y ex ey
    ; right-inverse-law = TerminalObjects.left-law x y ex ey
    ; left-inverse-law = TerminalObjects.right-law x y ex ey }

  terminal-to-lift : IsTerminal y → IsoLift (MorphismExpression.arrow universal-arrow)
  terminal-to-lift ey = invertible-expression-lift universal-arrow (terminal-to-invertible ey)
```
