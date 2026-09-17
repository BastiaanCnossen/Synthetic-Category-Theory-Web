# Retained composition and change of parameter

The retained comparison has two coordinates. Its first coordinate keeps
the parameter, and its second coordinate is the chosen uncurrying
comparison. We first identify that second coordinate explicitly.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section03.ParameterChange as ParameterChange
import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting as ParameterSquarePasting
import SCT.VolumeI.Chapter01.Section03.RetainedParameterChangeProjections as ChangeProjections
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section02.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section03.RetainedCompositionBaseChange as BaseChange
import SCT.VolumeI.Chapter01.Section03.CompositionInputParameterChange as UncurriedChange

module SCT.VolumeI.Chapter01.Section03.RetainedCompositionParameterChange
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
    (bf : NatIso (π ∘ f) x) (bg : NatIso (π ∘ g) y)
    (α : NatIso f g) (α′ : NatIso x y)
    (a : NatIso x x′) (b : NatIso y y′) (δ : NatIso x′ y′)
    → Iso₂ (bg ∙ (π ◁ α)) (α′ ∙ bf)
    → Iso₂ (b ∙ α′) (δ ∙ a)
    → Iso₂ ((b ∙ bg) ∙ (π ◁ α)) (δ ∙ (a ∙ bf))
  projection-normalize π bf bg α α′ a b δ p q =
    isoComp-assoc-at δ a bf ∙
      (isoComp-cong q (idIso bf) ∙
        (invIso (isoComp-assoc-at b α′ bf) ∙
          (isoComp-cong (idIso b) p ∙ isoComp-assoc-at b bg (π ◁ α))))

  projection-compose : {X Y Z : CAT} (π : MAP Y Z)
    {f₀ f₁ f₂ : MAP X Y} {z₀ z₁ z₂ : MAP X Z}
    (b₀ : NatIso (π ∘ f₀) z₀) (b₁ : NatIso (π ∘ f₁) z₁)
    (b₂ : NatIso (π ∘ f₂) z₂)
    (β : NatIso f₁ f₂) (α : NatIso f₀ f₁)
    (β′ : NatIso z₁ z₂) (α′ : NatIso z₀ z₁)
    → Iso₂ (b₂ ∙ (π ◁ β)) (β′ ∙ b₁)
    → Iso₂ (b₁ ∙ (π ◁ α)) (α′ ∙ b₀)
    → Iso₂ (b₂ ∙ (π ◁ (β ∙ α))) ((β′ ∙ α′) ∙ b₀)
  projection-compose π b₀ b₁ b₂ β α β′ α′ p q =
    invIso (isoComp-assoc-at β′ α′ b₀) ∙
      (isoComp-cong (idIso β′) q ∙
        (isoComp-assoc-at β′ b₁ (π ◁ α) ∙
          (isoComp-cong p (idIso (π ◁ α)) ∙ project-composite π β α b₂)))

  projection-associator : {X Y Z K E : CAT} (π : MAP K E)
    (f : MAP X Y) (g : MAP Y Z) (h : MAP Z K)
    {u : MAP Z E} (b : NatIso (π ∘ h) u)
    → Iso₂
        (transport-pre π h b (g ∘ f) ∙ (π ◁ comp-assoc f g h))
        (comp-assoc f g u ∙
          transport-pre π (h ∘ g) (transport-pre π h b g) f)
  projection-associator π f g h {u} b =
    isoComp-assoc-at (comp-assoc f g u)
      (transport-pre π h b g ▷ f) (invIso (comp-assoc f (h ∘ g) π)) ∙
      invIso (transport-pre-assoc π h u b g f)

  projection-nested-associator : {X Y Z K E : CAT} (π : MAP K E)
    (f : MAP X Y) (g : MAP Y Z) (h : MAP Z K)
    {ρ : MAP Z E} {u : MAP Y E}
    (q : NatIso (π ∘ h) ρ) (b : NatIso (ρ ∘ g) u)
    → Iso₂
        ((transport-pre ρ g b f ∙ transport-pre π h q (g ∘ f)) ∙
          (π ◁ comp-assoc f g h))
        (transport-pre π (h ∘ g) (b ∙ transport-pre π h q g) f)
  projection-nested-associator π f g h {ρ} q b =
    let A = comp-assoc f g ρ
        B = comp-assoc f (h ∘ g) π
        t = transport-pre π h q g
        n = transport-pre π (h ∘ g) t f
        left = transport-pre ρ g b f
        right = transport-pre π h q (g ∘ f)
        image = π ◁ comp-assoc f g h
        expand = isoComp-assoc-at (b ▷ f) (t ▷ f) (invIso B) ∙
          isoComp-cong (preWhisker-isoComp-at b t f) (idIso (invIso B))
    in invIso expand ∙
      (isoComp-cong (idIso (b ▷ f)) (cancel-left A n) ∙
        (isoComp-assoc-at (b ▷ f) (invIso A) (A ∙ n) ∙
          (isoComp-cong (idIso left) (projection-associator π f g h q) ∙
            isoComp-assoc-at left right image)))

abstract
  projection-inverse-action : {X Y Z : CAT} (π : MAP Y Z)
    {f g : MAP X Y} {x y : MAP X Z}
    (bf : NatIso (π ∘ f) x) (bg : NatIso (π ∘ g) y)
    (α : NatIso f g) (α′ : NatIso x y)
    → Iso₂ (bg ∙ (π ◁ α)) (α′ ∙ bf)
    → Iso₂ (bf ∙ (π ◁ invIso α)) (invIso α′ ∙ bg)
  projection-inverse-action π bf bg α α′ compatible =
    let cancel-image = postWhisker-idIso π _ ∙
          ((postWhisker π ◁ isoComp-inverseʳ-at α) ∙
            invIso (postWhisker-isoComp-at π α (invIso α)))
        left = isoComp-unitʳ-at bg ∙
          (isoComp-cong (idIso bg) cancel-image ∙
            (isoComp-assoc-at bg (π ◁ α) (π ◁ invIso α) ∙
              (isoComp-cong (invIso compatible) (idIso (π ◁ invIso α)) ∙
                invIso (isoComp-assoc-at α′ bf (π ◁ invIso α)))))
        right = isoComp-unitˡ-at bg ∙
          (isoComp-cong (isoComp-inverseʳ-at α′) (idIso bg) ∙
            invIso (isoComp-assoc-at α′ (invIso α′) bg))
    in cancel-left-reflect α′ (invIso right ∙ left)

  projection-inverse : {X Y Z : CAT} (π : MAP Y Z)
    {f g : MAP X Y} {z : MAP X Z}
    (bf : NatIso (π ∘ f) z) (bg : NatIso (π ∘ g) z) (α : NatIso f g)
    → Iso₂ (bg ∙ (π ◁ α)) bf
    → Iso₂ (bf ∙ (π ◁ invIso α)) bg
  projection-inverse π bf bg α compatible =
    let cancel-image = postWhisker-idIso π _ ∙
          ((postWhisker π ◁ isoComp-inverseʳ-at α) ∙
            invIso (postWhisker-isoComp-at π α (invIso α)))
    in isoComp-unitʳ-at bg ∙
      (isoComp-cong (idIso bg) cancel-image ∙
        (isoComp-assoc-at bg (π ◁ α) (π ◁ invIso α) ∙
          isoComp-cong (invIso compatible) (idIso (π ◁ invIso α))))

module Evaluation (P : CAT) where
  open ParameterRetaining P
  open RetainedEvaluation P

  composite-evaluation : {C D E : CAT}
    (g : MAP (P × D) E) (f : MAP (P × C) D)
    → NatIso (pr₂ ∘ (retain g ∘ retain f)) (g ∘ retain f)
  composite-evaluation g f =
    (retain-evaluation g ▷ retain f) ∙ invIso (comp-assoc (retain f) (retain g) pr₂)

  abstract
    retain-compose-evaluation : {C D E : CAT}
      (g : MAP (P × D) E) (f : MAP (P × C) D)
      → Iso₂ (retain-evaluation (g ∘ retain f) ∙ (pr₂ ◁ retain-compose g f))
          (composite-evaluation g f)
    retain-compose-evaluation g f = isoComp-unitˡ-at (composite-evaluation g f) ∙
      pair-pre-cong-triangle₂ pr₁ g (retain f)
        (retain-projection f) (idIso (g ∘ retain f))

    retained-compose-evaluation : {C D E : CAT}
      (g : MAP P (Map D E)) (f : MAP P (Map C D))
      → Iso₂
          (composite-evaluation (mapUncurry g) (mapUncurry f) ∙
            (pr₂ ◁ retained-compose g f))
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
          project-composite pr₂ (invIso c) (retain-cong u) e)
```

```agda
open import SCT.VolumeI.Chapter01.Section03.RetainedCompositionRoutes 𝒯 M public
```

The following calculation projects a pasted square using a specified
evaluation of its outer functor. It is independent of mapping animae.

```agda
module EvaluationPaste {A₀ A₁ A₂ B₀ B₁ B₂ E : CAT}
  (f : MAP A₀ A₁) (g : MAP A₁ A₂) (F : MAP B₀ B₁) (G : MAP B₁ B₂)
  (s₀ : MAP A₀ B₀) (s₁ : MAP A₁ B₁) (s₂ : MAP A₂ B₂)
  (π : MAP B₂ E) (ρ : MAP A₂ E) (u : MAP B₁ E) (v : MAP A₁ E)
  (q : NatIso (π ∘ s₂) ρ) (b : NatIso (π ∘ G) u) (B : NatIso (ρ ∘ g) v)
  (β : NatIso (s₂ ∘ g) (G ∘ s₁)) (α : NatIso (s₁ ∘ f) (F ∘ s₀))
  (ν : NatIso v (u ∘ s₁)) where

  source-evaluation = transport-pre ρ g B f ∙ transport-pre π s₂ q (g ∘ f)
  first-evaluation = transport-pre π (s₂ ∘ g) (B ∙ transport-pre π s₂ q g) f
  second-evaluation = transport-pre π (G ∘ s₁) (transport-pre π G b s₁) f
  third-evaluation = transport-pre π G b (s₁ ∘ f)
  fourth-evaluation = transport-pre π G b (F ∘ s₀)
  target-evaluation = transport-pre π (G ∘ F) (transport-pre π G b F) s₀

  evaluation-action : NatIso (v ∘ f) ((u ∘ F) ∘ s₀)
  evaluation-action = invIso (comp-assoc s₀ F u) ∙
    ((u ◁ α) ∙ (comp-assoc f s₁ u ∙ (ν ▷ f)))

  abstract
    project-paste :
      Iso₂ (transport-pre π G b s₁ ∙ (π ◁ β))
        (ν ∙ (B ∙ transport-pre π s₂ q g))
      → Iso₂ (target-evaluation ∙ (π ◁ paste β α))
          (evaluation-action ∙ source-evaluation)
    project-paste square =
      let r₁ = invIso (comp-assoc f g s₂)
          r₂ = β ▷ f
          r₃ = comp-assoc f s₁ G
          r₄ = G ◁ α
          r₅ = invIso (comp-assoc s₀ F G)
          a₂ = ν ▷ f
          a₃ = comp-assoc f s₁ u
          a₄ = u ◁ α
          a₅ = invIso (comp-assoc s₀ F u)
          first = invIso (isoComp-unitˡ-at source-evaluation) ∙
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
  νg = mapUncurry-pre g σ
  νH = mapUncurry-pre (composeTerm g f) σ
  uP = uncurry-compose g f
  uQ = uncurry-compose (g ∘ σ) (f ∘ σ)

  module ProjectPaste = EvaluationPaste
    (RQ.retained (f ∘ σ)) (RQ.retained (g ∘ σ))
    (RP.retained f) (RP.retained g) σC σD σE
    pr₂ pr₂ ug vg qE βg βg′ κg κf νg

  source-evaluation : NatIso (pr₂ ∘ source)
    (mapUncurry (composeTerm (g ∘ σ) (f ∘ σ)))
  source-evaluation = pair-β₂ pr₁ (mapUncurry (composeTerm (g ∘ σ) (f ∘ σ))) ∙
    transport-pre pr₂ σE qE (RQ.retained (composeTerm (g ∘ σ) (f ∘ σ)))

  target-evaluation = ProjectPaste.target-evaluation

  input-action = ProjectPaste.evaluation-action ∙ uQ
  output-action = (uP ▷ σC) ∙ (νH ∙ invIso (mapUncurryIso δ))

  abstract
    change-input-evaluation :
      Iso₂ (target-evaluation ∙ (pr₂ ◁ change-input)) (input-action ∙ source-evaluation)
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
      Iso₂ (target-evaluation ∙ (pr₂ ◁ restrict-output)) (output-action ∙ source-evaluation)
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
            κcomp (invIso postδ) νH (invIso δImage) change inverseδ
      in projection-compose pr₂ source-evaluation CH.evaluation-output target-evaluation
        (cP ▷ σC) (κcomp ∙ invIso postδ) (uP ▷ σC) (νH ∙ invIso δImage) compose initial

  UncurriedSquare : Set m
  UncurriedSquare = Iso₂
    ((ug ◁ κf) ∙
      (comp-assoc (RQ.retained (f ∘ σ)) σD ug ∙
        ((νg ▷ RQ.retained (f ∘ σ)) ∙ (uQ ∙ mapUncurryIso δ))))
    (comp-assoc σC (RP.retained f) ug ∙ ((uP ▷ σC) ∙ νH))

  abstract
    scalar-comparison : UncurriedSquare → Iso₂ input-action output-action
    scalar-comparison square =
      let A = comp-assoc σC (RP.retained f) ug
          b = ug ◁ κf
          c = comp-assoc (RQ.retained (f ∘ σ)) σD ug
          d = νg ▷ RQ.retained (f ∘ σ)
          η = mapUncurryIso δ
          t = b ∙ (c ∙ (d ∙ uQ))
          r = (uP ▷ σC) ∙ νH
          input-normal : Iso₂ input-action (invIso A ∙ t)
          input-normal = isoComp-cong (idIso (invIso A))
              (isoComp-cong (idIso b) (isoComp-assoc-at c d uQ) ∙
                isoComp-assoc-at b (c ∙ d) uQ) ∙
            isoComp-assoc-at (invIso A) (b ∙ (c ∙ d)) uQ
          square-normal : Iso₂ (A ∙ r) (t ∙ η)
          square-normal = invIso (isoComp-assoc-at b (c ∙ (d ∙ uQ)) η) ∙
            (isoComp-cong (idIso b) (invIso (isoComp-assoc-at c (d ∙ uQ) η)) ∙
            (isoComp-cong (idIso b)
              (isoComp-cong (idIso c) (invIso (isoComp-assoc-at d uQ η))) ∙
                invIso square))
      in isoComp-assoc-at (uP ▷ σC) νH (invIso η) ∙
        (move-square A r t η square-normal ∙ input-normal)

    from-uncurried : UncurriedSquare → Iso₂ change-input restrict-output
    from-uncurried square = pair-iso-extensionality
      (BaseChange.Calculation.comparison 𝒯 M g f σ)
      (cancel-left-reflect target-evaluation
        (invIso restrict-output-evaluation ∙
          (isoComp-cong (scalar-comparison square) (idIso source-evaluation) ∙
            change-input-evaluation)))
```

The uncurried composition square supplies the last input. Thus the final
retained comparison has no extra coherence premise.

```agda
opaque
  retained-compose-parameter-change : {P Q C D E : CAT}
    (g : MAP P (Map D E)) (f : MAP P (Map C D)) (σ : MAP Q P)
    → Iso₂ (Routes.change-input g f σ) (Routes.restrict-output g f σ)
  retained-compose-parameter-change g f σ = ProjectedRoutes.from-uncurried g f σ
    (UncurriedChange.uncurry-compose-parameter-change 𝒯 M g f σ)
```
