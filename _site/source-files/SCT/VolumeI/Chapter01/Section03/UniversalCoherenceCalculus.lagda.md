# Naturality and reflection for universal comparisons

This module proves naturality of the retained associator and unit routes,
and reflection under change of parameter. It also compares composition
squares after their source and target terms have been normalized. All
comparisons are those already selected in the earlier construction.

The higher proof bodies are opaque. Their boundaries remain visible,
and later proofs can use them without expanding their calculations again.
```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section03.CompositionPentagon as CompositionPentagon
import SCT.VolumeI.Chapter01.Section03.InternalPentagon as InternalPentagon
import SCT.VolumeI.Chapter01.Section03.ParameterChange as ParameterChange
import SCT.VolumeI.Chapter01.Section03.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section03.ParameterChangeNaturality as ParameterChangeNaturality
import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting as ParameterSquarePasting
import SCT.VolumeI.Chapter01.Section03.ParameterSquareNaturality as ParameterSquareNaturality
import SCT.VolumeI.Chapter01.Section03.ParameterSquareUnits as ParameterSquareUnits
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IteratedPairing

module SCT.VolumeI.Chapter01.Section03.UniversalCoherenceCalculus
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open Currying 𝒯 M
open MapComposition 𝒯 M
open InternalCoherence 𝒯 M
open CompositionPentagon 𝒯 M using
  (compose-triangle; module RetainedSquares; module RetainedNaturality; cancel-two-front)
open InternalPentagon 𝒯 M using (compose-pentagon; extend-square)
open ParameterChange 𝒯 M using
  (mapReflect-specialize-image; mapReflect-pre-image-β; mapUncurryIso-inverse; retained-parameter-change)
open ParameterChangeNaturality 𝒯 M using (retained-parameter-change-natural)
open ParameterSquarePasting 𝒯 using (paste)
open ParameterSquareNaturality 𝒯 using (paste-source-square; paste-source-normalization; paste-target-normalization)
open ParameterSquareUnits 𝒯 using (unit-square; paste-unitˡ; paste-unitʳ)
open CompositionNaturality 𝒯 M using (chain-input-squares)
open PairingCoherence vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-Iso₂; pair-iso-extensionality; pair-cong-comp)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left-reflect; cancel-left)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; preWhisker-comp-at; whisker-mixed-at; postWhisker-id-at; preWhisker-id-at)
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (hcomp-idOuter; hcomp-idInner)

opaque
  external-associator-natural : {A B C D : CAT}
    {f f′ : MAP A B} {g g′ : MAP B C} {h h′ : MAP C D}
    (γ : =₁ h h′) (β : =₁ g g′) (α : =₁ f f′)
    → =₂ (comp-assoc f′ g′ h′ ∙ ((γ ⋆ β) ⋆ α))
        ((γ ⋆ (β ⋆ α)) ∙ comp-assoc f g h)
  external-associator-natural {f = f} {f′} {g} {g′} {h} {h′} γ β α =
    let a = (h ∘ g) ◁ α
        b = (h ◁ β) ▷ f′
        c = (γ ▷ g′) ▷ f′
        r = h ◁ (g ◁ α)
        s = h ◁ (β ▷ f′)
        t = γ ▷ (g′ ∘ f′)
        A₀ = comp-assoc f g h
        A₁ = comp-assoc f′ g h
        A₂ = comp-assoc f′ g′ h
        A₃ = comp-assoc f′ g′ h′
        first-two = chain-input-squares A₀ A₁ A₂ a b r s
          (postWhisker-comp-at α g h) (whisker-mixed-at β f′ h)
        all-three = chain-input-squares A₀ A₂ A₃ (b ∙ a) c (s ∙ r) t
          first-two (preWhisker-comp-at γ g′ f′)
        expand-left = isoComp-assoc-at c b a ∙
          isoComp-cong (preWhisker-isoComp-at (γ ▷ g′) (h ◁ β) f′) (idIso a)
        collapse-right = isoComp-cong (idIso t) (invIso (postWhisker-isoComp-at h (β ▷ f′) (g ◁ α)))
    in isoComp-cong collapse-right (idIso A₀) ∙
      (all-three ∙ isoComp-cong (idIso A₃) expand-left)

  precomparison-square : {A B C : CAT} {f f′ : MAP A B}
    {g g′ G G′ : MAP B C} (p : =₁ g G) (q : =₁ g′ G′)
    (α : =₁ g g′) (δ : =₁ G G′) (β : =₁ f f′)
    → =₂ (q ∙ α) (δ ∙ p)
    → =₂ ((q ▷ f′) ∙ (α ⋆ β)) ((δ ⋆ β) ∙ (p ▷ f))
  precomparison-square {f = f} {f′} {g} {g′} {G} {G′} p q α δ β square =
    invIso (isoComp-assoc-at (δ ▷ f′) (G ◁ β) (p ▷ f)) ∙
    (isoComp-cong (idIso (δ ▷ f′)) (interchange-at p β) ∙
    (isoComp-assoc-at (δ ▷ f′) (p ▷ f′) (g ◁ β) ∙
    (isoComp-cong (preWhisker-isoComp-at δ p f′) (idIso (g ◁ β)) ∙
    (isoComp-cong (preWhisker f′ ◁ square) (idIso (g ◁ β)) ∙
    (isoComp-cong (invIso (preWhisker-isoComp-at q α f′)) (idIso (g ◁ β)) ∙
      invIso (isoComp-assoc-at (q ▷ f′) (α ▷ f′) (g ◁ β)))))))

  postcomparison-square : {A B C : CAT} {f f′ F F′ : MAP A B}
    {g g′ : MAP B C} (p : =₁ f F) (q : =₁ f′ F′)
    (α : =₁ f f′) (δ : =₁ F F′) (β : =₁ g g′)
    → =₂ (q ∙ α) (δ ∙ p)
    → =₂ ((g′ ◁ q) ∙ (β ⋆ α)) ((β ⋆ δ) ∙ (g ◁ p))
  postcomparison-square {f = f} {f′} {F} {F′} {g} {g′} p q α δ β square =
    invIso (isoComp-assoc-at (β ▷ F′) (g ◁ δ) (g ◁ p)) ∙
    (isoComp-cong (idIso (β ▷ F′)) (postWhisker-isoComp-at g δ p) ∙
    (isoComp-cong (idIso (β ▷ F′)) (postWhisker g ◁ square) ∙
    (isoComp-cong (idIso (β ▷ F′)) (invIso (postWhisker-isoComp-at g q α)) ∙
    (isoComp-assoc-at (β ▷ F′) (g ◁ q) (g ◁ α) ∙
    (isoComp-cong (invIso (interchange-at β q)) (idIso (g ◁ α)) ∙
      invIso (isoComp-assoc-at (g′ ◁ q) (β ▷ f′) (g ◁ α)))))))

```

The two normalizations of a triple composite are natural in all three
mapping terms. After these normalization squares are pasted with the
external associator square, their common target comparison cancels. The
unit routes use the same argument with the external unitors. These
calculations are between retained evaluations and require no anima
hypothesis on the common parameter.

```agda
module RouteNaturality (P : CAT) where
  open RetainedEvaluation P
  open RetainedNaturality P
  open RetainedSquares P using (retainedIso-id)

  left-comparison : {A B C D : CAT}
    (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
    → =₁ (retained (composeTerm (composeTerm h g) f))
        ((retained h ∘ retained g) ∘ retained f)
  left-comparison h g f = (retained-compose h g ▷ retained f) ∙ retained-compose (composeTerm h g) f

  right-comparison : {A B C D : CAT}
    (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
    → =₁ (retained (composeTerm h (composeTerm g f)))
        (retained h ∘ (retained g ∘ retained f))
  right-comparison h g f = (retained h ◁ retained-compose g f) ∙ retained-compose h (composeTerm g f)

  opaque
    route-square : {A B C D : CAT}
      (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
      → =₂ (right-comparison h g f ∙ associator-route h g f)
          (comp-assoc (retained f) (retained g) (retained h) ∙ left-comparison h g f)
    route-square h g f = cancel-two-front
      (retained h ◁ retained-compose g f) (retained-compose h (composeTerm g f))
      (comp-assoc (retained f) (retained g) (retained h) ∙ left-comparison h g f)

    left-natural : {A B C D : CAT}
      {h h′ : MAP P (Map C D)} {g g′ : MAP P (Map B C)} {f f′ : MAP P (Map A B)}
      (γ : =₁ h h′) (β : =₁ g g′) (α : =₁ f f′)
      → =₂ (left-comparison h′ g′ f′ ∙ retainedIso (composeTerm-cong (composeTerm-cong γ β) α))
          (((retainedIso γ ⋆ retainedIso β) ⋆ retainedIso α) ∙ left-comparison h g f)
    left-natural {h = h} {h′} {g} {g′} {f} {f′} γ β α =
      extend-square _ _ _ _ _ _ _
        (retained-compose-natural (composeTerm-cong γ β) α)
        (precomparison-square (retained-compose h g) (retained-compose h′ g′)
          (retainedIso (composeTerm-cong γ β)) (retainedIso γ ⋆ retainedIso β)
          (retainedIso α) (retained-compose-natural γ β))

    right-natural : {A B C D : CAT}
      {h h′ : MAP P (Map C D)} {g g′ : MAP P (Map B C)} {f f′ : MAP P (Map A B)}
      (γ : =₁ h h′) (β : =₁ g g′) (α : =₁ f f′)
      → =₂ (right-comparison h′ g′ f′ ∙ retainedIso (composeTerm-cong γ (composeTerm-cong β α)))
          ((retainedIso γ ⋆ (retainedIso β ⋆ retainedIso α)) ∙ right-comparison h g f)
    right-natural {h = h} {h′} {g} {g′} {f} {f′} γ β α =
      extend-square _ _ _ _ _ _ _
        (retained-compose-natural γ (composeTerm-cong β α))
        (postcomparison-square (retained-compose g f) (retained-compose g′ f′)
          (retainedIso (composeTerm-cong β α)) (retainedIso β ⋆ retainedIso α)
          (retainedIso γ) (retained-compose-natural β α))

    associator-natural : {A B C D : CAT}
      {h h′ : MAP P (Map C D)} {g g′ : MAP P (Map B C)} {f f′ : MAP P (Map A B)}
      (γ : =₁ h h′) (β : =₁ g g′) (α : =₁ f f′)
      → =₂ (associator-route h′ g′ f′ ∙ retainedIso (composeTerm-cong (composeTerm-cong γ β) α))
          (retainedIso (composeTerm-cong γ (composeTerm-cong β α)) ∙ associator-route h g f)
    associator-natural {h = h} {h′} {g} {g′} {f} {f′} γ β α =
      let L = left-comparison h g f
          L′ = left-comparison h′ g′ f′
          R = right-comparison h g f
          R′ = right-comparison h′ g′ f′
          a = associator-route h g f
          a′ = associator-route h′ g′ f′
          S = retainedIso (composeTerm-cong (composeTerm-cong γ β) α)
          T = retainedIso (composeTerm-cong γ (composeTerm-cong β α))
          l = (retainedIso γ ⋆ retainedIso β) ⋆ retainedIso α
          r = retainedIso γ ⋆ (retainedIso β ⋆ retainedIso α)
          A = comp-assoc (retained f) (retained g) (retained h)
          A′ = comp-assoc (retained f′) (retained g′) (retained h′)
      in cancel-left-reflect R′
        (isoComp-assoc-at R′ T a ∙
        (isoComp-cong (invIso (right-natural γ β α)) (idIso a) ∙
        (invIso (isoComp-assoc-at r R a) ∙
        (isoComp-cong (idIso r) (invIso (route-square h g f)) ∙
        (isoComp-assoc-at r A L ∙
        (isoComp-cong (external-associator-natural (retainedIso γ) (retainedIso β) (retainedIso α)) (idIso L) ∙
        (invIso (isoComp-assoc-at A′ l L) ∙
        (isoComp-cong (idIso A′) (left-natural γ β α) ∙
        (isoComp-assoc-at A′ L′ S ∙
        (isoComp-cong (route-square h′ g′ f′) (idIso S) ∙
          invIso (isoComp-assoc-at R′ a′ S)))))))))))

    left-unit-natural : {C D : CAT} {f f′ : MAP P (Map C D)} (α : =₁ f f′)
      → =₂ (left-unit-route f′ ∙ retainedIso (composeTerm-cong (idIso (identityTerm D)) α))
          (retainedIso α ∙ left-unit-route f)
    left-unit-natural {D = D} {f} {f′} α =
      let F = retained f
          F′ = retained f′
          J = retained (identityTerm D)
          ε = retained-identity D
          a = retainedIso (composeTerm-cong (idIso (identityTerm D)) α)
          b = J ◁ retainedIso α
          d = id (P × D) ◁ retainedIso α
          z = retainedIso α
          c = retained-compose (identityTerm D) f
          c′ = retained-compose (identityTerm D) f′
          e = ε ▷ F
          e′ = ε ▷ F′
          natural = isoComp-cong
            (hcomp-idOuter J z ∙ hcomp-cong (retainedIso-id (identityTerm D)) (idIso z)) (idIso c) ∙
            retained-compose-natural (idIso (identityTerm D)) α
          first = extend-square a b d c c′ e e′ natural (interchange-at ε z)
      in extend-square a d z (e ∙ c) (e′ ∙ c′) (comp-unitˡ F) (comp-unitˡ F′)
        first (postWhisker-id-at z)

    right-unit-natural : {C D : CAT} {f f′ : MAP P (Map C D)} (α : =₁ f f′)
      → =₂ (right-unit-route f′ ∙ retainedIso (composeTerm-cong α (idIso (identityTerm C))))
          (retainedIso α ∙ right-unit-route f)
    right-unit-natural {C = C} {f = f} {f′} α =
      let F = retained f
          F′ = retained f′
          J = retained (identityTerm C)
          ε = retained-identity C
          a = retainedIso (composeTerm-cong α (idIso (identityTerm C)))
          b = retainedIso α ▷ J
          d = retainedIso α ▷ id (P × C)
          z = retainedIso α
          c = retained-compose f (identityTerm C)
          c′ = retained-compose f′ (identityTerm C)
          e = F ◁ ε
          e′ = F′ ◁ ε
          natural = isoComp-cong
            (hcomp-idInner z J ∙ hcomp-cong (idIso z) (retainedIso-id (identityTerm C))) (idIso c) ∙
            retained-compose-natural α (idIso (identityTerm C))
          first = extend-square a b d c c′ e e′ natural (invIso (interchange-at z ε))
      in extend-square a d z (e ∙ c) (e′ ∙ c′) (comp-unitʳ F) (comp-unitʳ F′)
        first (preWhisker-id-at z)

```

For an anima parameter, the actual isomorphism functor of uncurrying
reflects these squares. Its identity and composition comparisons are kept
in the proof, so the conclusion concerns the chosen lifted comparisons.

```agda
composeTerm-Iso₂ : {P A B C : CAT}
  {g g′ : MAP P (Map B C)} {f f′ : MAP P (Map A B)}
  {α α′ : =₁ g g′} {β β′ : =₁ f f′}
  → =₂ α α′ → =₂ β β′
  → =₂ (composeTerm-cong α β) (composeTerm-cong α′ β′)
composeTerm-Iso₂ p q = postWhisker mapComp ◁ pair-cong-Iso₂ p q

composeTerm-cong-comp : {P A B C : CAT}
  {g₀ g₁ g₂ : MAP P (Map B C)} {f₀ f₁ f₂ : MAP P (Map A B)}
  (γ₂ : =₁ g₁ g₂) (γ₁ : =₁ g₀ g₁) (δ₂ : =₁ f₁ f₂) (δ₁ : =₁ f₀ f₁)
  → =₂ (composeTerm-cong (γ₂ ∙ γ₁) (δ₂ ∙ δ₁))
      (composeTerm-cong γ₂ δ₂ ∙ composeTerm-cong γ₁ δ₁)
composeTerm-cong-comp {A = A} {B} {C} γ₂ γ₁ δ₂ δ₁ =
  postWhisker-isoComp-at (mapComp {A} {B} {C}) (pair-cong γ₂ δ₂) (pair-cong γ₁ δ₁) ∙
    (postWhisker (mapComp {A} {B} {C}) ◁ pair-cong-comp γ₂ γ₁ δ₂ δ₁)

composeTerm-evaluate-factor : {P Q A B C : CAT}
  (g : MAP P (Map B C)) (f : MAP P (Map A B)) (σ : MAP Q P)
  {g₀ g₁ : MAP Q (Map B C)} {f₀ f₁ : MAP Q (Map A B)}
  (γ₀ : =₁ (g ∘ σ) g₀) (δ₀ : =₁ (f ∘ σ) f₀)
  (γ₁ : =₁ g₀ g₁) (δ₁ : =₁ f₀ f₁)
  → =₂ (composeTerm-evaluate g f σ (γ₁ ∙ γ₀) (δ₁ ∙ δ₀))
      (composeTerm-cong γ₁ δ₁ ∙ composeTerm-evaluate g f σ γ₀ δ₀)
composeTerm-evaluate-factor g f σ γ₀ δ₀ γ₁ δ₁ =
  isoComp-assoc-at (composeTerm-cong γ₁ δ₁) (composeTerm-cong γ₀ δ₀) (composeTerm-pre g f σ) ∙
    isoComp-cong (composeTerm-cong-comp γ₁ γ₀ δ₁ δ₀) (idIso (composeTerm-pre g f σ))

module DirectNaturality (P : CAT) (pAn : isAn P) where
  open RetainedEvaluation P
  open RetainedSquares P
  open RouteNaturality P

  opaque
    lift-square : {C D : CAT} {f g f′ g′ : MAP P (Map C D)}
      (a : =₁ f g) (a′ : =₁ f′ g′) (s : =₁ f f′) (t : =₁ g g′)
      (r : =₁ (retained f) (retained g)) (r′ : =₁ (retained f′) (retained g′))
      → =₂ (retainedIso a) r → =₂ (retainedIso a′) r′
      → =₂ (r′ ∙ retainedIso s) (retainedIso t ∙ r)
      → =₂ (a′ ∙ s) (t ∙ a)
    lift-square a a′ s t r r′ b b′ square = retainedIso-reflect pAn _ _
      (invIso (retainedIso-comp t a) ∙
      (isoComp-cong (idIso (retainedIso t)) (invIso b) ∙
      (square ∙
      (isoComp-cong b′ (idIso (retainedIso s)) ∙ retainedIso-comp a′ s))))

    associator : {A B C D : CAT}
      {h h′ : MAP P (Map C D)} {g g′ : MAP P (Map B C)} {f f′ : MAP P (Map A B)}
      (γ : =₁ h h′) (β : =₁ g g′) (α : =₁ f f′)
      → =₂ (compose-assoc pAn h′ g′ f′ ∙ composeTerm-cong (composeTerm-cong γ β) α)
          (composeTerm-cong γ (composeTerm-cong β α) ∙ compose-assoc pAn h g f)
    associator {h = h} {h′} {g} {g′} {f} {f′} γ β α =
      lift-square _ _ _ _ _ _ (compose-assoc-retained-β pAn h g f)
        (compose-assoc-retained-β pAn h′ g′ f′) (associator-natural γ β α)

    left-unit : {C D : CAT} {f f′ : MAP P (Map C D)} (α : =₁ f f′)
      → =₂ (compose-unitˡ pAn f′ ∙ composeTerm-cong (idIso (identityTerm D)) α)
          (α ∙ compose-unitˡ pAn f)
    left-unit {f = f} {f′} α = lift-square _ _ _ _ _ _
      (compose-unitˡ-retained-β pAn f) (compose-unitˡ-retained-β pAn f′) (left-unit-natural α)

    right-unit : {C D : CAT} {f f′ : MAP P (Map C D)} (α : =₁ f f′)
      → =₂ (compose-unitʳ pAn f′ ∙ composeTerm-cong α (idIso (identityTerm C)))
          (α ∙ compose-unitʳ pAn f)
    right-unit {f = f} {f′} α = lift-square _ _ _ _ _ _
      (compose-unitʳ-retained-β pAn f) (compose-unitʳ-retained-β pAn f′) (right-unit-natural α)

```

Changing a parameter need not be an equivalence. Nevertheless,
postcomposition with its product with an identity reflects comparisons
whose first projections agree: the second projection is unchanged, and
the first projection is supplied by base compatibility.

```agda
postWhisker-composite-reflect : {A B C D : CAT} {f g : MAP A B}
  (u : MAP B C) (v : MAP C D) {α β : =₁ f g}
  → =₂ (v ◁ (u ◁ α)) (v ◁ (u ◁ β))
  → =₂ ((v ∘ u) ◁ α) ((v ∘ u) ◁ β)
postWhisker-composite-reflect {f = f} {g} u v {α} {β} p =
  cancel-left-reflect (comp-assoc g u v)
    (invIso (postWhisker-comp-at β u v) ∙
      (isoComp-cong p (idIso (comp-assoc f u v)) ∙ postWhisker-comp-at α u v))

postWhisker-change-outer : {A B C : CAT} {f g : MAP A B}
  {u v : MAP B C} (η : =₁ u v) {α β : =₁ f g}
  → =₂ (u ◁ α) (u ◁ β) → =₂ (v ◁ α) (v ◁ β)
postWhisker-change-outer {f = f} {g} η {α} {β} p =
  cancel-right-reflect (η ▷ f)
    (interchange-at η β ∙
      (isoComp-cong (idIso (η ▷ g)) p ∙ invIso (interchange-at η α)))

parameter-change-second : {Q P D : CAT} (σ : MAP Q P)
  → =₁ (pr₂ ∘ productMap σ (id D)) (pr₂ {C = Q} {D = D})
parameter-change-second {D = D} σ = comp-unitˡ pr₂ ∙
  pair-β₂ (σ ∘ pr₁) (id D ∘ pr₂)

module ParameterReflection {Q P : CAT} (σ : MAP Q P) where
  open RetainedEvaluation Q
  open ParameterRetaining Q

  second-component : {X D : CAT} {f g : MAP X (Q × D)}
    {α β : =₁ f g}
    → =₂ (productMap σ (id D) ◁ α) (productMap σ (id D) ◁ β)
    → =₂ (pr₂ ◁ α) (pr₂ ◁ β)
  second-component {D = D} p = postWhisker-change-outer (parameter-change-second σ)
    (postWhisker-composite-reflect (productMap σ (id D)) pr₂ (postWhisker pr₂ ◁ p))

  retained-comparison : {C D : CAT} {f g : MAP Q (Map C D)}
    {α β : =₁ (retained f) (retained g)}
    → BaseCompatible α → BaseCompatible β
    → =₂ (productMap σ (id D) ◁ α) (productMap σ (id D) ◁ β)
    → =₂ α β
  retained-comparison {g = g} a b p = pair-iso-extensionality
    (cancel-left-reflect (retain-projection (mapUncurry g)) (invIso b ∙ a))
    (second-component p)

module NormalizedChange {P Q C D : CAT} (σ : MAP Q P) where
  module RP = RetainedEvaluation P
  module RQ = RetainedEvaluation Q
  module SQ = RetainedSquares Q
  module SP = RetainedSquares P
  s = productMap σ (id C)
  t = productMap σ (id D)

  image : {f g : MAP Q (Map C D)} → =₁ f g
    → =₁ (t ∘ RQ.retained f) (t ∘ RQ.retained g)
  image α = t ◁ RQ.retainedIso α

  opaque
    image-cong : {f g : MAP Q (Map C D)} {α β : =₁ f g}
      → =₂ α β → =₂ (image α) (image β)
    image-cong p = postWhisker t ◁ SQ.retainedIso-Iso₂ p

    image-id : (f : MAP Q (Map C D)) → =₂ (image (idIso f)) (idIso (t ∘ RQ.retained f))
    image-id f = postWhisker-idIso t (RQ.retained f) ∙ (postWhisker t ◁ SQ.retainedIso-id f)

    image-comp : {f g h : MAP Q (Map C D)} (β : =₁ g h) (α : =₁ f g)
      → =₂ (image (β ∙ α)) (image β ∙ image α)
    image-comp β α = postWhisker-isoComp-at t (RQ.retainedIso β) (RQ.retainedIso α) ∙
      (postWhisker t ◁ SQ.retainedIso-comp β α)

    image-inverse : {f g : MAP Q (Map C D)} (α : =₁ f g)
      → =₂ (image (invIso α)) (invIso (image α))
    image-inverse {f} α = cancel-right-reflect (image α)
      (invIso (isoComp-inverseˡ-at (image α)) ∙
      (image-id f ∙ (image-cong (isoComp-inverseˡ-at α) ∙ invIso (image-comp (invIso α) α))))

    image-specialize : {f g : MAP P (Map C D)} (α : =₁ f g)
      {f′ g′ : MAP Q (Map C D)} (L : =₁ (f ∘ σ) f′) (R : =₁ (g ∘ σ) g′)
      → =₂ (image (specialize α σ L R))
          (image R ∙ (image (α ▷ σ) ∙ invIso (image L)))
    image-specialize α L R =
      isoComp-cong (idIso (image R)) (isoComp-cong (idIso (image (α ▷ σ))) (image-inverse L)) ∙
      (isoComp-assoc-at (image R) (image (α ▷ σ)) (image (invIso L)) ∙
      (isoComp-cong (image-comp R (α ▷ σ)) (idIso (image (invIso L))) ∙
        image-comp (R ∙ (α ▷ σ)) (invIso L)))

  change : (f : MAP P (Map C D)) {f′ : MAP Q (Map C D)} (L : =₁ (f ∘ σ) f′)
    → =₁ (t ∘ RQ.retained f′) (RP.retained f ∘ s)
  change f L = retained-parameter-change f σ ∙ invIso (image L)

  opaque
    change-cancel : (f : MAP P (Map C D)) {f′ : MAP Q (Map C D)} (L : =₁ (f ∘ σ) f′)
      → =₂ (change f L ∙ image L) (retained-parameter-change f σ)
    change-cancel f L = isoComp-unitʳ-at (retained-parameter-change f σ) ∙
      (isoComp-cong (idIso (retained-parameter-change f σ)) (isoComp-inverseˡ-at (image L)) ∙
        isoComp-assoc-at (retained-parameter-change f σ) (invIso (image L)) (image L))

    change-compose : (f : MAP P (Map C D)) {f′ f″ : MAP Q (Map C D)}
      (L : =₁ (f ∘ σ) f′) (R : =₁ f′ f″)
      → =₂ (change f (R ∙ L) ∙ image R) (change f L)
    change-compose f L R = cancel-right-reflect (image L)
      (invIso (change-cancel f L) ∙
      (change-cancel f (R ∙ L) ∙
      (isoComp-cong (idIso (change f (R ∙ L))) (invIso (image-comp R L)) ∙
        isoComp-assoc-at (change f (R ∙ L)) (image R) (image L))))

    change-cong : (f : MAP P (Map C D)) {f′ : MAP Q (Map C D)}
      {L R : =₁ (f ∘ σ) f′} → =₂ L R → =₂ (change f L) (change f R)
    change-cong f {L = L} {R} p = cancel-right-reflect (image L)
      (isoComp-cong (idIso (change f R)) (invIso (image-cong p)) ∙
        (invIso (change-cancel f R) ∙ change-cancel f L))

    natural : {f g : MAP P (Map C D)} (α : =₁ f g)
      {f′ g′ : MAP Q (Map C D)} (L : =₁ (f ∘ σ) f′) (R : =₁ (g ∘ σ) g′)
      → =₂ (change g R ∙ image (specialize α σ L R))
          ((RP.retainedIso α ▷ s) ∙ change f L)
    natural {f} {g} α L R =
      let k = retained-parameter-change f σ
          k′ = retained-parameter-change g σ
          u = image L
          v = image R
          z = image (α ▷ σ)
          w = RP.retainedIso α ▷ s
      in isoComp-assoc-at w k (invIso u) ∙
        (isoComp-cong (retained-parameter-change-natural α σ) (idIso (invIso u)) ∙
        (invIso (isoComp-assoc-at k′ z (invIso u)) ∙
        (isoComp-cong (idIso k′) (cancel-left v (z ∙ invIso u)) ∙
        (isoComp-assoc-at k′ (invIso v) (v ∙ (z ∙ invIso u)) ∙
          isoComp-cong (idIso (change g R)) (image-specialize α L R)))))

    reflect-route : {f g : MAP P (Map C D)} (α : =₁ f g)
      {f′ g′ : MAP Q (Map C D)} (L : =₁ (f ∘ σ) f′) (R : =₁ (g ∘ σ) g′)
      (qAn : isAn Q)
      (routeP : =₁ (RP.retained f) (RP.retained g))
      (routeQ : =₁ (RQ.retained f′) (RQ.retained g′))
      → =₂ (RP.retainedIso α) routeP → RQ.BaseCompatible routeQ
      → =₂ (change g R ∙ (t ◁ routeQ)) ((routeP ▷ s) ∙ change f L)
      → =₂ (specialize α σ L R) (RQ.retained-reflect qAn routeQ)
    reflect-route {f} {g} α L R qAn routeP routeQ beta base-compatible square =
      let first = isoComp-cong (preWhisker s ◁ beta) (idIso (change f L)) ∙ natural α L R
          after-change = cancel-left-reflect (change g R) (invIso square ∙ first)
          retained = ParameterReflection.retained-comparison σ
            (RQ.retainedIso-base (specialize α σ L R)) base-compatible after-change
      in SQ.retainedIso-reflect qAn _ _ (invIso (RQ.retained-reflect-β qAn routeQ base-compatible) ∙ retained)

module NormalizedComposition {P Q : CAT} (σ : MAP Q P) where
  module RP = RetainedEvaluation P
  module RQ = RetainedEvaluation Q
  module Natural = RetainedNaturality Q
  module N (A B : CAT) = NormalizedChange {C = A} {D = B} σ

  s : (A : CAT) → MAP (Q × A) (P × A)
  s A = productMap σ (id A)

  BasicSquare : {A B C : CAT} (g : MAP P (Map B C)) (f : MAP P (Map A B)) → Set m
  BasicSquare {A} {B} {C} g f = =₂
    (paste (retained-parameter-change g σ) (retained-parameter-change f σ) ∙
      (s C ◁ RQ.retained-compose (g ∘ σ) (f ∘ σ)))
    ((RP.retained-compose g f ▷ s A) ∙ N.change A C (composeTerm g f) (composeTerm-pre g f σ))

  opaque
    normalize : {A B C : CAT} (g : MAP P (Map B C)) (f : MAP P (Map A B))
      {g′ : MAP Q (Map B C)} {f′ : MAP Q (Map A B)}
      (Lg : =₁ (g ∘ σ) g′) (Lf : =₁ (f ∘ σ) f′)
      → BasicSquare g f
      → =₂ (paste (N.change B C g Lg) (N.change A B f Lf) ∙ (s C ◁ RQ.retained-compose g′ f′))
          ((RP.retained-compose g f ▷ s A) ∙
            N.change A C (composeTerm g f) (composeTerm-evaluate g f σ Lg Lf))
    normalize {A} {B} {C} g f {g′} {f′} Lg Lf basic =
      let p = paste (N.change B C g Lg) (N.change A B f Lf)
          c = s C ◁ RQ.retained-compose (g ∘ σ) (f ∘ σ)
          c′ = s C ◁ RQ.retained-compose g′ f′
          δ = composeTerm-pre g f σ
          γ = composeTerm-cong Lg Lf
          action = N.image A C γ
          h = RQ.retainedIso Lg ⋆ RQ.retainedIso Lf
          output = RP.retained-compose g f ▷ s A
          natural = postWhisker-isoComp-at (s C) h (RQ.retained-compose (g ∘ σ) (f ∘ σ)) ∙
            ((postWhisker (s C) ◁ Natural.retained-compose-natural Lg Lf) ∙
              invIso (postWhisker-isoComp-at (s C) (RQ.retained-compose g′ f′) (RQ.retainedIso γ)))
          source = paste-source-normalization (retained-parameter-change g σ)
            (retained-parameter-change f σ) (RQ.retainedIso Lg) (RQ.retainedIso Lf)
          left-normal = basic ∙
            (isoComp-cong source (idIso c) ∙
            (invIso (isoComp-assoc-at p (s C ◁ h) c) ∙
            (isoComp-cong (idIso p) natural ∙ isoComp-assoc-at p c′ action)))
          right-normal = isoComp-cong (idIso output) (N.change-compose A C (composeTerm g f) δ γ) ∙
            isoComp-assoc-at output (N.change A C (composeTerm g f) (γ ∙ δ)) action
      in cancel-right-reflect action (invIso right-normal ∙ left-normal)


```
