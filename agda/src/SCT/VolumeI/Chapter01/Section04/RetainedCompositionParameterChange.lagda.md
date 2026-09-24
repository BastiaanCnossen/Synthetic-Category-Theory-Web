# Retained composition and change of parameter

The retained comparison has two coordinates. Its first coordinate keeps
the parameter, and its second coordinate is the chosen uncurrying
comparison. We first identify that second coordinate explicitly.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section04.ParameterChange as ParameterChange
import SCT.VolumeI.Chapter01.Section04.ParameterSquarePasting as ParameterSquarePasting
import SCT.VolumeI.Chapter01.Section04.RetainedParameterChangeProjections as ChangeProjections
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section03.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section04.RetainedCompositionBaseChange as BaseChange
import SCT.VolumeI.Chapter01.Section04.CompositionInputParameterChange as UncurriedChange

module SCT.VolumeI.Chapter01.Section04.RetainedCompositionParameterChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M
open MapComposition 𝒯 M
open InternalCoherence 𝒯 M
open ParameterChange 𝒯 M using (retained-parameter-change)
open ParameterSquarePasting 𝒯 using (paste)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (project-composite; cancel-left-reflect; cancel-left; move-square;
    pre-square-projection; substitution-square-projection)
open PairingCoherence vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-triangle₂; pair-iso-extensionality)
open ProductFunctorUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₂)
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre; transport-pre-assoc)

abstract
  projection-normalize : {X Y Z : CAT} (π : MAP Y Z)
    {f g : MAP X Y} {x y x′ y′ : MAP X Z}
    (bf : (π ∘ f) =₁ x) (bg : (π ∘ g) =₁ y)
    (α : f =₁ g) (α′ : x =₁ y)
    (a : x =₁ x′) (b : y =₁ y′) (δ : x′ =₁ y′)
    → (bg ∙ (π ◁ α)) =₂ (α′ ∙ bf)
    → (b ∙ α′) =₂ (δ ∙ a)
    → ((b ∙ bg) ∙ (π ◁ α)) =₂ (δ ∙ (a ∙ bf))
  projection-normalize π bf bg α α′ a b δ p q =
    isoComp-assoc-at δ a bf ∙
      (isoComp-cong q (idIso bf) ∙
        ((isoComp-assoc-at b α′ bf) ⁻¹ ∙
          (isoComp-cong (idIso b) p ∙ isoComp-assoc-at b bg (π ◁ α))))

  projection-compose : {X Y Z : CAT} (π : MAP Y Z)
    {f₀ f₁ f₂ : MAP X Y} {z₀ z₁ z₂ : MAP X Z}
    (b₀ : (π ∘ f₀) =₁ z₀) (b₁ : (π ∘ f₁) =₁ z₁)
    (b₂ : (π ∘ f₂) =₁ z₂)
    (β : f₁ =₁ f₂) (α : f₀ =₁ f₁)
    (β′ : z₁ =₁ z₂) (α′ : z₀ =₁ z₁)
    → (b₂ ∙ (π ◁ β)) =₂ (β′ ∙ b₁)
    → (b₁ ∙ (π ◁ α)) =₂ (α′ ∙ b₀)
    → (b₂ ∙ (π ◁ (β ∙ α))) =₂ ((β′ ∙ α′) ∙ b₀)
  projection-compose π b₀ b₁ b₂ β α β′ α′ p q =
    (isoComp-assoc-at β′ α′ b₀) ⁻¹ ∙
      (isoComp-cong (idIso β′) q ∙
        (isoComp-assoc-at β′ b₁ (π ◁ α) ∙
          (isoComp-cong p (idIso (π ◁ α)) ∙ project-composite π β α b₂)))

  projection-associator : {X Y Z K E : CAT} (π : MAP K E)
    (f : MAP X Y) (g : MAP Y Z) (h : MAP Z K)
    {u : MAP Z E} (b : (π ∘ h) =₁ u)
    →
        (transport-pre π h b (g ∘ f) ∙ (π ◁ comp-assoc f g h)) =₂
        (comp-assoc f g u ∙
          transport-pre π (h ∘ g) (transport-pre π h b g) f)
  projection-associator π f g h {u} b =
    isoComp-assoc-at (comp-assoc f g u)
      (transport-pre π h b g ▷ f) ((comp-assoc f (h ∘ g) π) ⁻¹) ∙
      (transport-pre-assoc π h u b g f) ⁻¹

  projection-nested-associator : {X Y Z K E : CAT} (π : MAP K E)
    (f : MAP X Y) (g : MAP Y Z) (h : MAP Z K)
    {ρ : MAP Z E} {u : MAP Y E}
    (q : (π ∘ h) =₁ ρ) (b : (ρ ∘ g) =₁ u)
    →
        ((transport-pre ρ g b f ∙ transport-pre π h q (g ∘ f)) ∙
          (π ◁ comp-assoc f g h)) =₂
        (transport-pre π (h ∘ g) (b ∙ transport-pre π h q g) f)
  projection-nested-associator π f g h {ρ} q b =
    let A = comp-assoc f g ρ
        B = comp-assoc f (h ∘ g) π
        t = transport-pre π h q g
        n = transport-pre π (h ∘ g) t f
        left = transport-pre ρ g b f
        right = transport-pre π h q (g ∘ f)
        image = π ◁ comp-assoc f g h
        expand = isoComp-assoc-at (b ▷ f) (t ▷ f) (B ⁻¹) ∙
          isoComp-cong (preWhisker-isoComp-at b t f) (idIso (B ⁻¹))
    in expand ⁻¹ ∙
      (isoComp-cong (idIso (b ▷ f)) (cancel-left A n) ∙
        (isoComp-assoc-at (b ▷ f) (A ⁻¹) (A ∙ n) ∙
          (isoComp-cong (idIso left) (projection-associator π f g h q) ∙
            isoComp-assoc-at left right image)))

abstract
  projection-inverse-action : {X Y Z : CAT} (π : MAP Y Z)
    {f g : MAP X Y} {x y : MAP X Z}
    (bf : (π ∘ f) =₁ x) (bg : (π ∘ g) =₁ y)
    (α : f =₁ g) (α′ : x =₁ y)
    → (bg ∙ (π ◁ α)) =₂ (α′ ∙ bf)
    → (bf ∙ (π ◁ α ⁻¹)) =₂ (α′ ⁻¹ ∙ bg)
  projection-inverse-action π bf bg α α′ compatible =
    let cancel-image = postWhisker-idIso π _ ∙
          ((postWhisker π ◁ isoComp-inverseʳ-at α) ∙
            (postWhisker-isoComp-at π α (α ⁻¹)) ⁻¹)
        left = isoComp-unitʳ-at bg ∙
          (isoComp-cong (idIso bg) cancel-image ∙
            (isoComp-assoc-at bg (π ◁ α) (π ◁ α ⁻¹) ∙
              (isoComp-cong (compatible ⁻¹) (idIso (π ◁ α ⁻¹)) ∙
                (isoComp-assoc-at α′ bf (π ◁ α ⁻¹)) ⁻¹)))
        right = isoComp-unitˡ-at bg ∙
          (isoComp-cong (isoComp-inverseʳ-at α′) (idIso bg) ∙
            (isoComp-assoc-at α′ (α′ ⁻¹) bg) ⁻¹)
    in cancel-left-reflect α′ (right ⁻¹ ∙ left)

  projection-inverse : {X Y Z : CAT} (π : MAP Y Z)
    {f g : MAP X Y} {z : MAP X Z}
    (bf : (π ∘ f) =₁ z) (bg : (π ∘ g) =₁ z) (α : f =₁ g)
    → (bg ∙ (π ◁ α)) =₂ bf
    → (bf ∙ (π ◁ α ⁻¹)) =₂ bg
  projection-inverse π bf bg α compatible =
    let cancel-image = postWhisker-idIso π _ ∙
          ((postWhisker π ◁ isoComp-inverseʳ-at α) ∙
            (postWhisker-isoComp-at π α (α ⁻¹)) ⁻¹)
    in isoComp-unitʳ-at bg ∙
      (isoComp-cong (idIso bg) cancel-image ∙
        (isoComp-assoc-at bg (π ◁ α) (π ◁ α ⁻¹) ∙
          isoComp-cong (compatible ⁻¹) (idIso (π ◁ α ⁻¹))))

module Evaluation (P : CAT) where
  open ParameterRetaining P
  open RetainedEvaluation P

  composite-evaluation : {C D E : CAT}
    (g : MAP (P × D) E) (f : MAP (P × C) D)
    → (pr₂ ∘ (retain g ∘ retain f)) =₁ (g ∘ retain f)
  composite-evaluation g f =
    (retain-evaluation g ▷ retain f) ∙ (comp-assoc (retain f) (retain g) pr₂) ⁻¹

  abstract
    retain-compose-evaluation : {C D E : CAT}
      (g : MAP (P × D) E) (f : MAP (P × C) D)
      → (retain-evaluation (g ∘ retain f) ∙ (pr₂ ◁ retain-compose g f)) =₂
          (composite-evaluation g f)
    retain-compose-evaluation g f = isoComp-unitˡ-at (composite-evaluation g f) ∙
      pair-pre-cong-triangle₂ pr₁ g (retain f)
        (retain-projection f) (idIso (g ∘ retain f))

    retained-compose-evaluation : {C D E : CAT}
      (g : MAP P (Map D E)) (f : MAP P (Map C D))
      →
          (composite-evaluation (mapUncurry g) (mapUncurry f) ∙
            (pr₂ ◁ retained-compose g f)) =₂
          (uncurry-compose g f ∙ retain-evaluation (mapUncurry (composeTerm g f)))
    retained-compose-evaluation g f =
      let u = uncurry-compose g f
          c = retain-compose (mapUncurry g) (mapUncurry f)
          e = composite-evaluation (mapUncurry g) (mapUncurry f)
          d = retain-evaluation (mapUncurry g ∘ retained f)
          inverse = projection-inverse pr₂ e d c
            (retain-compose-evaluation (mapUncurry g) (mapUncurry f))
      in pair-cong-triangle₂ (idIso pr₁) u ∙
        (isoComp-cong inverse (idIso (pr₂ ◁ retain-cong u)) ∙
          project-composite pr₂ (c ⁻¹) (retain-cong u) e)
```

```agda
open import SCT.VolumeI.Chapter01.Section04.RetainedCompositionRoutes 𝒯 M public
```

The following calculation projects a pasted square using a specified
evaluation of its outer functor. It is independent of mapping animae.

```agda
module EvaluationPaste {A₀ A₁ A₂ B₀ B₁ B₂ E : CAT}
  (f : MAP A₀ A₁) (g : MAP A₁ A₂) (F : MAP B₀ B₁) (G : MAP B₁ B₂)
  (s₀ : MAP A₀ B₀) (s₁ : MAP A₁ B₁) (s₂ : MAP A₂ B₂)
  (π : MAP B₂ E) (ρ : MAP A₂ E) (u : MAP B₁ E) (v : MAP A₁ E)
  (q : (π ∘ s₂) =₁ ρ) (b : (π ∘ G) =₁ u) (B : (ρ ∘ g) =₁ v)
  (β : (s₂ ∘ g) =₁ (G ∘ s₁)) (α : (s₁ ∘ f) =₁ (F ∘ s₀))
  (ν : v =₁ (u ∘ s₁)) where

  source-evaluation = transport-pre ρ g B f ∙ transport-pre π s₂ q (g ∘ f)
  first-evaluation = transport-pre π (s₂ ∘ g) (B ∙ transport-pre π s₂ q g) f
  second-evaluation = transport-pre π (G ∘ s₁) (transport-pre π G b s₁) f
  third-evaluation = transport-pre π G b (s₁ ∘ f)
  fourth-evaluation = transport-pre π G b (F ∘ s₀)
  target-evaluation = transport-pre π (G ∘ F) (transport-pre π G b F) s₀

  evaluation-action : (v ∘ f) =₁ ((u ∘ F) ∘ s₀)
  evaluation-action = (comp-assoc s₀ F u) ⁻¹ ∙
    ((u ◁ α) ∙ (comp-assoc f s₁ u ∙ (ν ▷ f)))

  abstract
    project-paste :
      (transport-pre π G b s₁ ∙ (π ◁ β)) =₂
        (ν ∙ (B ∙ transport-pre π s₂ q g))
      → (target-evaluation ∙ (π ◁ paste β α)) =₂
          (evaluation-action ∙ source-evaluation)
    project-paste square =
      let r₁ = (comp-assoc f g s₂) ⁻¹
          r₂ = β ▷ f
          r₃ = comp-assoc f s₁ G
          r₄ = G ◁ α
          r₅ = (comp-assoc s₀ F G) ⁻¹
          a₂ = ν ▷ f
          a₃ = comp-assoc f s₁ u
          a₄ = u ◁ α
          a₅ = (comp-assoc s₀ F u) ⁻¹
          first = (isoComp-unitˡ-at source-evaluation) ⁻¹ ∙
            projection-inverse π first-evaluation source-evaluation (comp-assoc f g s₂)
              (projection-nested-associator π f g s₂ q B)
          second = pre-square-projection π β ν
            (B ∙ transport-pre π s₂ q g) (transport-pre π G b s₁) f square
          third = projection-associator π f s₁ G b
          fourth = substitution-square-projection π G u b α
          fifth = projection-inverse-action π target-evaluation fourth-evaluation
            (comp-assoc s₀ F G) (comp-assoc s₀ F u)
            (projection-associator π s₀ F G b)
          firstTwo = isoComp-cong (isoComp-unitʳ-at a₂) (idIso source-evaluation) ∙
            projection-compose π source-evaluation first-evaluation second-evaluation
              r₂ r₁ a₂ (idIso (v ∘ f)) second first
          firstThree = projection-compose π source-evaluation second-evaluation third-evaluation
            r₃ (r₂ ∙ r₁) a₃ a₂ third firstTwo
          firstFour = projection-compose π source-evaluation third-evaluation fourth-evaluation
            r₄ (r₃ ∙ (r₂ ∙ r₁)) a₄ (a₃ ∙ a₂) fourth firstThree
      in projection-compose π source-evaluation fourth-evaluation target-evaluation
        r₅ (r₄ ∙ (r₃ ∙ (r₂ ∙ r₁))) a₅ (a₄ ∙ (a₃ ∙ a₂)) fifth firstFour
```

```agda
module ProjectedRoutes {P Q C D E : CAT}
  (g : MAP P (Map D E)) (f : MAP P (Map C D)) (σ : MAP Q P) where
  open Routes g f σ
  module CG = ChangeProjections.ProjectionRoutes 𝒯 M g σ
  module CH = ChangeProjections.ProjectionRoutes 𝒯 M (composeTerm g f) σ
  module EP = Evaluation P
  module EQ = Evaluation Q

  ug = mapUncurry g
  vg = mapUncurry (g ∘ σ)
  βg = pair-β₂ pr₁ ug
  βg′ = pair-β₂ pr₁ vg
  qE = comp-unitˡ (pr₂ {Q} {E}) ∙ pair-β₂ (σ ∘ pr₁) (id E ∘ pr₂)
  νg = mapUncurry-restrict g σ
  νH = mapUncurry-restrict (composeTerm g f) σ
  uP = uncurry-compose g f
  uQ = uncurry-compose (g ∘ σ) (f ∘ σ)

  module ProjectPaste = EvaluationPaste
    (RQ.retained (f ∘ σ)) (RQ.retained (g ∘ σ))
    (RP.retained f) (RP.retained g) σC σD σE
    pr₂ pr₂ ug vg qE βg βg′ κg κf νg

  source-evaluation : (pr₂ ∘ source) =₁
    (mapUncurry (composeTerm (g ∘ σ) (f ∘ σ)))
  source-evaluation = pair-β₂ pr₁ (mapUncurry (composeTerm (g ∘ σ) (f ∘ σ))) ∙
    transport-pre pr₂ σE qE (RQ.retained (composeTerm (g ∘ σ) (f ∘ σ)))

  target-evaluation = ProjectPaste.target-evaluation

  input-action = ProjectPaste.evaluation-action ∙ uQ
  output-action = (uP ▷ σC) ∙ (νH ∙ (mapUncurryIso δ) ⁻¹)

  abstract
    change-input-evaluation :
      (target-evaluation ∙ (pr₂ ◁ change-input)) =₂ (input-action ∙ source-evaluation)
    change-input-evaluation =
      let cQ = RQ.retained-compose (g ∘ σ) (f ∘ σ)
          R = RQ.retained (composeTerm (g ∘ σ) (f ∘ σ))
          RF = RQ.retained (f ∘ σ)
          RG = RQ.retained (g ∘ σ)
          bSource = transport-pre pr₂ σE qE R
          bTarget = transport-pre pr₂ σE qE (RG ∘ RF)
          base = pair-β₂ pr₁ (mapUncurry (composeTerm (g ∘ σ) (f ∘ σ)))
          composite = EQ.composite-evaluation vg (mapUncurry (f ∘ σ))
          inputSquare = projection-normalize pr₂ bSource bTarget (σE ◁ cQ) (pr₂ ◁ cQ)
            base composite uQ (substitution-square-projection pr₂ σE pr₂ qE cQ)
            (EQ.retained-compose-evaluation (g ∘ σ) (f ∘ σ))
          pasteSquare = ProjectPaste.project-paste CG.retained-change-evaluation
      in projection-compose pr₂ source-evaluation ProjectPaste.source-evaluation target-evaluation
        (paste κg κf) (σE ◁ cQ) ProjectPaste.evaluation-action uQ pasteSquare inputSquare

    restrict-output-evaluation :
      (target-evaluation ∙ (pr₂ ◁ restrict-output)) =₂ (output-action ∙ source-evaluation)
    restrict-output-evaluation =
      let R₀ = RQ.retained (composeTerm g f ∘ σ)
          R₁ = RQ.retained (composeTerm (g ∘ σ) (f ∘ σ))
          b₀ = transport-pre pr₂ σE qE R₀
          b₁ = transport-pre pr₂ σE qE R₁
          e₀ = pair-β₂ pr₁ (mapUncurry (composeTerm g f ∘ σ))
          e₁ = pair-β₂ pr₁ (mapUncurry (composeTerm (g ∘ σ) (f ∘ σ)))
          δImage = mapUncurryIso δ
          cP = RP.retained-compose g f
          postδ = σE ◁ RQ.retainedIso δ
          forwardδ = projection-normalize pr₂ b₀ b₁ postδ (pr₂ ◁ RQ.retainedIso δ)
            e₀ e₁ δImage
            (substitution-square-projection pr₂ σE pr₂ qE (RQ.retainedIso δ))
            (pair-cong-triangle₂ (idIso pr₁) δImage)
          inverseδ = projection-inverse-action pr₂ CH.evaluation-input source-evaluation
            postδ δImage forwardδ
          change = CH.retained-change-evaluation
          compose = pre-square-projection pr₂ cP uP
            (pair-β₂ pr₁ (mapUncurry (composeTerm g f)))
            (EP.composite-evaluation ug (mapUncurry f)) σC
            (EP.retained-compose-evaluation g f)
          initial = projection-compose pr₂ source-evaluation CH.evaluation-input CH.evaluation-output
            κcomp (postδ ⁻¹) νH (δImage ⁻¹) change inverseδ
      in projection-compose pr₂ source-evaluation CH.evaluation-output target-evaluation
        (cP ▷ σC) (κcomp ∙ postδ ⁻¹) (uP ▷ σC) (νH ∙ δImage ⁻¹) compose initial

  UncurriedSquare : Set m
  UncurriedSquare =
    ((ug ◁ κf) ∙
      (comp-assoc (RQ.retained (f ∘ σ)) σD ug ∙
        ((νg ▷ RQ.retained (f ∘ σ)) ∙ (uQ ∙ mapUncurryIso δ)))) =₂
    (comp-assoc σC (RP.retained f) ug ∙ ((uP ▷ σC) ∙ νH))

  abstract
    scalar-comparison : UncurriedSquare → input-action =₂ output-action
    scalar-comparison square =
      let A = comp-assoc σC (RP.retained f) ug
          b = ug ◁ κf
          c = comp-assoc (RQ.retained (f ∘ σ)) σD ug
          d = νg ▷ RQ.retained (f ∘ σ)
          η = mapUncurryIso δ
          t = b ∙ (c ∙ (d ∙ uQ))
          r = (uP ▷ σC) ∙ νH
          input-normal : input-action =₂ (A ⁻¹ ∙ t)
          input-normal = isoComp-cong (idIso (A ⁻¹))
              (isoComp-cong (idIso b) (isoComp-assoc-at c d uQ) ∙
                isoComp-assoc-at b (c ∙ d) uQ) ∙
            isoComp-assoc-at (A ⁻¹) (b ∙ (c ∙ d)) uQ
          square-normal : (A ∙ r) =₂ (t ∙ η)
          square-normal = (isoComp-assoc-at b (c ∙ (d ∙ uQ)) η) ⁻¹ ∙
            (isoComp-cong (idIso b) ((isoComp-assoc-at c (d ∙ uQ) η) ⁻¹) ∙
            (isoComp-cong (idIso b)
              (isoComp-cong (idIso c) ((isoComp-assoc-at d uQ η) ⁻¹)) ∙
                square ⁻¹))
      in isoComp-assoc-at (uP ▷ σC) νH (η ⁻¹) ∙
        (move-square A r t η square-normal ∙ input-normal)

    from-uncurried : UncurriedSquare → change-input =₂ restrict-output
    from-uncurried square = pair-iso-extensionality
      (BaseChange.Calculation.comparison 𝒯 M g f σ)
      (cancel-left-reflect target-evaluation
        (restrict-output-evaluation ⁻¹ ∙
          (isoComp-cong (scalar-comparison square) (idIso source-evaluation) ∙
            change-input-evaluation)))
```

The uncurried composition square supplies the last input. Thus the final
retained comparison has no extra coherence premise.

```agda
opaque
  retained-compose-parameter-change : {P Q C D E : CAT}
    (g : MAP P (Map D E)) (f : MAP P (Map C D)) (σ : MAP Q P)
    → (Routes.change-input g f σ) =₂ (Routes.restrict-output g f σ)
  retained-compose-parameter-change g f σ = ProjectedRoutes.from-uncurried g f σ
    (UncurriedChange.uncurry-compose-parameter-change 𝒯 M g f σ)
```
