# Coherence of parameter-retaining comparisons

The first component of a parameter-retaining comparison is part of its
mathematical data. These calculations check that component under vertical
composition, inversion, whiskering, and the primitive associator. They are
used to justify lifting a retained comparison without losing its first
projection witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section03.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.CoherenceTransport as CoherenceTransport
import SCT.VolumeI.Chapter01.Section03.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section02.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section02.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section02.Structural as Structural

module SCT.VolumeI.Chapter01.Section03.CompositionPentagon
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open InternalCoherence 𝒯 M
open MapComposition 𝒯 M
open Currying 𝒯 M
open CoherenceTransport 𝒯
open CompositionNaturality 𝒯 M using (uncurry-compose-natural)
open Structural vocabulary terminal products productLaws composition whiskering
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left; cancel-right; cancel-left-reflect; project-composite;
         pre-square-projection; substitution-square-projection; move-square)
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre; transport-pre-assoc; hcomp-idOuter; hcomp-idInner)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (triangle-whiskered; unit-square-projection)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (reassociateFour; cancel-inverse)
open ProductFunctorUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₁; pair-projections-triangle₁)
open PairingCoherence vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-triangle₁; pair-cong-id; pair-cong-comp; pair-cong-Iso₂)

module OverParameter (P : CAT) where
  Base : {C D : CAT} → MAP (P × C) (P × D) → Set m
  Base f = =₁ (pr₁ ∘ f) pr₁

  Square : {C D : CAT} {f g : MAP (P × C) (P × D)}
    → Base f → Base g → =₁ f g → Set m
  Square bf bg α = =₂ (bg ∙ (pr₁ ◁ α)) bf

  compose-base : {C D E : CAT}
    (g : MAP (P × D) (P × E)) (f : MAP (P × C) (P × D))
    → Base g → Base f → Base (g ∘ f)
  compose-base g f bg bf = bf ∙ transport-pre pr₁ g bg f

  compose-square : {C D : CAT} {f g h : MAP (P × C) (P × D)}
    (bf : Base f) (bg : Base g) (bh : Base h)
    (β : =₁ g h) (α : =₁ f g)
    → Square bg bh β → Square bf bg α → Square bf bh (β ∙ α)
  compose-square bf bg bh β α b a = a ∙
    (isoComp-cong b (idIso (pr₁ ◁ α)) ∙ project-composite pr₁ β α bh)

  inverse-square : {C D : CAT} {f g : MAP (P × C) (P × D)}
    (bf : Base f) (bg : Base g) (α : =₁ f g)
    → Square bf bg α → Square bg bf (invIso α)
  inverse-square bf bg α compatible =
    let cancel-image = postWhisker-idIso pr₁ _ ∙
          ((postWhisker pr₁ ◁ isoComp-inverseʳ-at α) ∙
            invIso (postWhisker-isoComp-at pr₁ α (invIso α)))
    in isoComp-unitʳ-at bg ∙
      (isoComp-cong (idIso bg) cancel-image ∙
      (isoComp-assoc-at bg (pr₁ ◁ α) (pr₁ ◁ invIso α) ∙
        isoComp-cong (invIso compatible) (idIso (pr₁ ◁ invIso α))))

  pre-square : {C D E : CAT}
    {g g′ : MAP (P × D) (P × E)} (f : MAP (P × C) (P × D))
    (bg : Base g) (bg′ : Base g′) (bf : Base f) (α : =₁ g g′)
    → Square bg bg′ α
    → Square (compose-base g f bg bf) (compose-base g′ f bg′ bf) (α ▷ f)
  pre-square {g = g} {g′} f bg bg′ bf α compatible =
    let first = pre-square-projection pr₁ α (idIso pr₁) bg bg′ f
          (invIso (isoComp-unitˡ-at bg) ∙ compatible)
        normalized = isoComp-unitˡ-at (transport-pre pr₁ g bg f) ∙
          isoComp-cong (preWhisker-idIso pr₁ f) (idIso (transport-pre pr₁ g bg f))
    in isoComp-cong (idIso bf) (normalized ∙ first) ∙
      isoComp-assoc-at bf (transport-pre pr₁ g′ bg′ f) (pr₁ ◁ (α ▷ f))

  post-square : {C D E : CAT}
    (g : MAP (P × D) (P × E)) {f f′ : MAP (P × C) (P × D)}
    (bg : Base g) (bf : Base f) (bf′ : Base f′) (α : =₁ f f′)
    → Square bf bf′ α
    → Square (compose-base g f bg bf) (compose-base g f′ bg bf′) (g ◁ α)
  post-square g {f} {f′} bg bf bf′ α compatible =
    isoComp-cong compatible (idIso (transport-pre pr₁ g bg f)) ∙
    (invIso (isoComp-assoc-at bf′ (pr₁ ◁ α) (transport-pre pr₁ g bg f)) ∙
    (isoComp-cong (idIso bf′) (substitution-square-projection pr₁ g pr₁ bg α) ∙
      isoComp-assoc-at bf′ (transport-pre pr₁ g bg f′) (pr₁ ◁ (g ◁ α))))

  associator-square : {A B C D : CAT}
    (h : MAP (P × C) (P × D)) (g : MAP (P × B) (P × C)) (f : MAP (P × A) (P × B))
    (bh : Base h) (bg : Base g) (bf : Base f)
    → Square
        (compose-base (h ∘ g) f (compose-base h g bh bg) bf)
        (compose-base h (g ∘ f) bh (compose-base g f bg bf))
        (comp-assoc f g h)
  associator-square h g f bh bg bf =
    let A = comp-assoc f g pr₁
        D′ = comp-assoc f (h ∘ g) pr₁
        t = transport-pre pr₁ h bh g ▷ f
        u = bg ▷ f
        v = transport-pre pr₁ h bh (g ∘ f)
        w = pr₁ ◁ comp-assoc f g h
        middle = isoComp-cong (invIso (preWhisker-isoComp-at bg (transport-pre pr₁ h bh g) f))
            (idIso (invIso D′)) ∙
          (invIso (isoComp-assoc-at u t (invIso D′)) ∙
          (isoComp-cong (idIso u) (isoComp-cong (cancel-left A t) (idIso (invIso D′))) ∙
            reassociateFour u (invIso A) (A ∙ t) (invIso D′)))
    in isoComp-cong (idIso bf)
        (middle ∙ isoComp-cong (idIso (transport-pre pr₁ g bg f))
          (invIso (transport-pre-assoc pr₁ h pr₁ bh g f))) ∙
      (isoComp-assoc-at bf (transport-pre pr₁ g bg f) (v ∙ w) ∙
        isoComp-assoc-at (bf ∙ transport-pre pr₁ g bg f) v w)

  left-unit-square : {C D : CAT} (f : MAP (P × C) (P × D)) (bf : Base f)
    → Square (compose-base (id (P × D)) f (comp-unitʳ pr₁) bf) bf (comp-unitˡ f)
  left-unit-square f bf = isoComp-cong (idIso bf)
    (invIso (cancel-right (comp-assoc f (id _) pr₁) (pr₁ ◁ comp-unitˡ f) ∙
      isoComp-cong (triangle-whiskered f pr₁) (idIso (invIso (comp-assoc f (id _) pr₁)))))

  right-unit-square : {C D : CAT} (f : MAP (P × C) (P × D)) (bf : Base f)
    → Square (compose-base f (id (P × C)) bf (comp-unitʳ pr₁)) bf (comp-unitʳ f)
  right-unit-square f bf = invIso (unit-square-projection pr₁ f pr₁ bf)
```

The retained unit and associator routes preserve the base projection.
Consequently the image of each lifted comparison agrees with its whole
retained route, with both projection witnesses accounted for.

```agda
module RetainedSquares (P : CAT) where
  open OverParameter P
  open ParameterRetaining P
  open RetainedEvaluation P

  retained-base : {C D : CAT} (f : MAP P (Map C D)) → Base (retained f)
  retained-base f = retain-projection (mapUncurry f)

  retain-cong-square : {C D : CAT} {f g : MAP (P × C) D} (α : =₁ f g)
    → Square (retain-projection f) (retain-projection g) (retain-cong α)
  retain-cong-square {f = f} α = isoComp-unitˡ-at (retain-projection f) ∙
    pair-cong-triangle₁ (idIso pr₁) α

  retain-compose-square : {C D E : CAT}
    (g : MAP (P × D) E) (f : MAP (P × C) D)
    → Square (compose-base (retain g) (retain f) (retain-projection g) (retain-projection f))
        (retain-projection (g ∘ retain f)) (retain-compose g f)
  retain-compose-square g f = pair-pre-cong-triangle₁ pr₁ g (retain f)
    (retain-projection f) (idIso (g ∘ retain f))

  retained-compose-square : {C D E : CAT}
    (g : MAP P (Map D E)) (f : MAP P (Map C D))
    → Square (retained-base (composeTerm g f))
        (compose-base (retained g) (retained f) (retained-base g) (retained-base f))
        (retained-compose g f)
  retained-compose-square g f =
    let b = compose-base (retained g) (retained f) (retained-base g) (retained-base f)
        d = retain-projection (mapUncurry g ∘ retained f)
        c = retain-compose (mapUncurry g) (mapUncurry f)
        e = retain-cong (uncurry-compose g f)
    in compose-square (retained-base (composeTerm g f)) d b (invIso c) e
      (inverse-square b d c (retain-compose-square (mapUncurry g) (mapUncurry f)))
      (retain-cong-square (uncurry-compose g f))

  retained-identity-square : (C : CAT)
    → Square (retained-base (identityTerm C)) (comp-unitʳ pr₁) (retained-identity C)
  retained-identity-square C = compose-square (retained-base (identityTerm C))
    (retain-projection pr₂) (comp-unitʳ pr₁) (retain-id C) (retain-cong (uncurry-identity P C))
    pair-projections-triangle₁ (retain-cong-square (uncurry-identity P C))

  left-unit-route-base : {C D : CAT} (f : MAP P (Map C D)) → BaseCompatible (left-unit-route f)
  left-unit-route-base {D = D} f =
    let F = retained f
        I = retained (identityTerm D)
        bF = retained-base f
        bI = retained-base (identityTerm D)
        b₀ = retained-base (composeTerm (identityTerm D) f)
        b₁ = compose-base I F bI bF
        b₂ = compose-base (id (P × D)) F (comp-unitʳ pr₁) bF
        α = retained-compose (identityTerm D) f
        β = retained-identity D ▷ F
        γ = comp-unitˡ F
    in compose-square b₀ b₂ bF γ (β ∙ α) (left-unit-square F bF)
      (compose-square b₀ b₁ b₂ β α
        (pre-square F bI (comp-unitʳ pr₁) bF (retained-identity D) (retained-identity-square D))
        (retained-compose-square (identityTerm D) f))

  right-unit-route-base : {C D : CAT} (f : MAP P (Map C D)) → BaseCompatible (right-unit-route f)
  right-unit-route-base {C = C} f =
    let F = retained f
        I = retained (identityTerm C)
        bF = retained-base f
        bI = retained-base (identityTerm C)
        b₀ = retained-base (composeTerm f (identityTerm C))
        b₁ = compose-base F I bF bI
        b₂ = compose-base F (id (P × C)) bF (comp-unitʳ pr₁)
        α = retained-compose f (identityTerm C)
        β = F ◁ retained-identity C
        γ = comp-unitʳ F
    in compose-square b₀ b₂ bF γ (β ∙ α) (right-unit-square F bF)
      (compose-square b₀ b₁ b₂ β α
        (post-square F bF bI (comp-unitʳ pr₁) (retained-identity C) (retained-identity-square C))
        (retained-compose-square f (identityTerm C)))

  associator-route-base : {A B C D : CAT}
    (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
    → BaseCompatible (associator-route h g f)
  associator-route-base h g f =
    let H = retained h
        G = retained g
        F = retained f
        bH = retained-base h
        bG = retained-base g
        bF = retained-base f
        HG = retained (composeTerm h g)
        GF = retained (composeTerm g f)
        bHG = retained-base (composeTerm h g)
        bGF = retained-base (composeTerm g f)
        b₀ = retained-base (composeTerm (composeTerm h g) f)
        b₁ = compose-base HG F bHG bF
        b₂ = compose-base (H ∘ G) F (compose-base H G bH bG) bF
        b₃ = compose-base H (G ∘ F) bH (compose-base G F bG bF)
        b₄ = compose-base H GF bH bGF
        b₅ = retained-base (composeTerm h (composeTerm g f))
        α = retained-compose (composeTerm h g) f
        β = retained-compose h g ▷ F
        γ = comp-assoc F G H
        δ = H ◁ retained-compose g f
        ε = retained-compose h (composeTerm g f)
        first = retained-compose-square (composeTerm h g) f
        second = pre-square F bHG (compose-base H G bH bG) bF
          (retained-compose h g) (retained-compose-square h g)
        third = associator-square H G F bH bG bF
        fourth = inverse-square b₄ b₃ δ
          (post-square H bH bGF (compose-base G F bG bF)
            (retained-compose g f) (retained-compose-square g f))
        fifth = inverse-square b₅ b₄ ε (retained-compose-square h (composeTerm g f))
    in compose-square b₀ b₄ b₅ (invIso ε) (invIso δ ∙ (γ ∙ (β ∙ α))) fifth
      (compose-square b₀ b₃ b₄ (invIso δ) (γ ∙ (β ∙ α)) fourth
      (compose-square b₀ b₂ b₃ γ (β ∙ α) third
      (compose-square b₀ b₁ b₂ β α second first)))

  compose-unitˡ-retained-β : {C D : CAT} (pAn : isAn P) (f : MAP P (Map C D))
    → =₂ (retainedIso (compose-unitˡ pAn f)) (left-unit-route f)
  compose-unitˡ-retained-β pAn f =
    retained-reflect-β pAn (left-unit-route f) (left-unit-route-base f)

  compose-unitʳ-retained-β : {C D : CAT} (pAn : isAn P) (f : MAP P (Map C D))
    → =₂ (retainedIso (compose-unitʳ pAn f)) (right-unit-route f)
  compose-unitʳ-retained-β pAn f =
    retained-reflect-β pAn (right-unit-route f) (right-unit-route-base f)

  compose-assoc-retained-β : {A B C D : CAT} (pAn : isAn P)
    (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
    → =₂ (retainedIso (compose-assoc pAn h g f)) (associator-route h g f)
  compose-assoc-retained-β pAn h g f =
    retained-reflect-β pAn (associator-route h g f) (associator-route-base h g f)

  retainedIso-Iso₂ : {C D : CAT} {f g : MAP P (Map C D)} {α β : =₁ f g}
    → =₂ α β → =₂ (retainedIso α) (retainedIso β)
  retainedIso-Iso₂ p = pair-cong-Iso₂ (idIso (idIso pr₁)) (mapUncurry-Iso₂ p)

  retainedIso-id : {C D : CAT} (f : MAP P (Map C D))
    → =₂ (retainedIso (idIso f)) (idIso (retained f))
  retainedIso-id f = pair-cong-id pr₁ (mapUncurry f) ∙
    pair-cong-Iso₂ (idIso (idIso pr₁)) (mapUncurryIso-id f)

  retainedIso-comp : {C D : CAT} {f g h : MAP P (Map C D)}
    (β : =₁ g h) (α : =₁ f g)
    → =₂ (retainedIso (β ∙ α)) (retainedIso β ∙ retainedIso α)
  retainedIso-comp β α = pair-cong-comp (idIso pr₁) (idIso pr₁) (mapUncurryIso β) (mapUncurryIso α) ∙
    pair-cong-Iso₂ (invIso (isoComp-unitˡ-at (idIso pr₁))) (mapUncurryIso-comp β α)

  retainedIso-reflect : {C D : CAT} (pAn : isAn P) {f g : MAP P (Map C D)}
    (α β : =₁ f g) → =₂ (retainedIso α) (retainedIso β) → =₂ α β
  retainedIso-reflect pAn {f} {g} α β p = mapReflect-Iso₂ pAn α β
    (forget-retainedIso β ∙
      (isoComp-cong (idIso (retain-evaluation (mapUncurry g)))
        (isoComp-cong (postWhisker pr₂ ◁ p) (idIso (invIso (retain-evaluation (mapUncurry f))))) ∙
        invIso (forget-retainedIso α)))
```

An arbitrary comparison of the middle functor with an identity may be moved
through the primitive triangle. This is the external triangle used for
the retained representing identity.

```agda
triangle-with-identity-comparison : {A B C : CAT}
  (g : MAP B C) (f : MAP A B) (j : MAP B B) (ε : =₁ j (id B))
  → =₂ ((comp-unitʳ g ▷ f) ∙ ((g ◁ ε) ▷ f))
      ((g ◁ (comp-unitˡ f ∙ (ε ▷ f))) ∙ comp-assoc f j g)
triangle-with-identity-comparison g f j ε =
  isoComp-cong (invIso (postWhisker-isoComp-at g (comp-unitˡ f) (ε ▷ f)))
    (idIso (comp-assoc f j g)) ∙
  (invIso (isoComp-assoc-at (g ◁ comp-unitˡ f) (g ◁ (ε ▷ f)) (comp-assoc f j g)) ∙
  (isoComp-cong (idIso (g ◁ comp-unitˡ f)) (whisker-mixed-at ε f g) ∙
  (isoComp-assoc-at (g ◁ comp-unitˡ f) (comp-assoc f (id _) g) ((g ◁ ε) ▷ f) ∙
    isoComp-cong (triangle-whiskered f g) (idIso ((g ◁ ε) ▷ f)))))

cancel-two-front : {X C : CAT} {f g h k : MAP X C}
  (b : =₁ h k) (a : =₁ g h) (x : =₁ f k)
  → =₂ ((b ∙ a) ∙ (invIso a ∙ (invIso b ∙ x))) x
cancel-two-front b a x = cancel-inverse b x ∙
  (isoComp-cong (idIso b) (cancel-inverse a (invIso b ∙ x)) ∙
    isoComp-assoc-at b a (invIso a ∙ (invIso b ∙ x)))

module RetainedNaturality (P : CAT) where
  open ParameterRetaining P
  open RetainedEvaluation P

  retain-cong-composition : {C D : CAT} {f g h : MAP (P × C) D}
    (β : =₁ g h) (α : =₁ f g)
    → =₂ (retain-cong (β ∙ α)) (retain-cong β ∙ retain-cong α)
  retain-cong-composition β α = pair-cong-comp (idIso pr₁) (idIso pr₁) β α ∙
    pair-cong-Iso₂ (invIso (isoComp-unitˡ-at (idIso pr₁))) (idIso (β ∙ α))

  from-uncurry-natural : {C D E : CAT}
    {g g′ : MAP P (Map D E)} {f f′ : MAP P (Map C D)}
    (α : =₁ g g′) (β : =₁ f f′)
    → =₂
        (uncurry-compose g′ f′ ∙ mapUncurryIso (composeTerm-cong α β))
        ((mapUncurryIso α ⋆ retainedIso β) ∙ uncurry-compose g f)
    → =₂
        (retained-compose g′ f′ ∙ retainedIso (composeTerm-cong α β))
        ((retainedIso α ⋆ retainedIso β) ∙ retained-compose g f)
  from-uncurry-natural {g = g} {g′} {f} {f′} α β natural =
    let u = uncurry-compose g f
        u′ = uncurry-compose g′ f′
        x = mapUncurryIso (composeTerm-cong α β)
        y = mapUncurryIso α ⋆ retainedIso β
        r = retain-compose (mapUncurry g) (mapUncurry f)
        r′ = retain-compose (mapUncurry g′) (mapUncurry f′)
        lifted = retain-cong-composition y u ∙
          (pair-cong-Iso₂ (idIso (idIso pr₁)) natural ∙
            invIso (retain-cong-composition u′ x))
        moved = move-square r′ (retainedIso α ⋆ retainedIso β) (retain-cong y) r
          (retain-compose-natural (mapUncurryIso α) (mapUncurryIso β))
    in isoComp-assoc-at (retainedIso α ⋆ retainedIso β) (invIso r) (retain-cong u) ∙
      (isoComp-cong moved (idIso (retain-cong u)) ∙
      (invIso (isoComp-assoc-at (invIso r′) (retain-cong y) (retain-cong u)) ∙
      (isoComp-cong (idIso (invIso r′)) lifted ∙
        isoComp-assoc-at (invIso r′) (retain-cong u′) (retainedIso (composeTerm-cong α β)))))

  retained-compose-natural : {C D E : CAT}
    {g g′ : MAP P (Map D E)} {f f′ : MAP P (Map C D)}
    (α : =₁ g g′) (β : =₁ f f′)
    → =₂ (retained-compose g′ f′ ∙ retainedIso (composeTerm-cong α β))
        ((retainedIso α ⋆ retainedIso β) ∙ retained-compose g f)
  retained-compose-natural α β = from-uncurry-natural α β (uncurry-compose-natural α β)
```

The next calculation isolates exactly the two composition-naturality squares
needed for the triangle. All endpoint changes and cancellations are proved
here. Supplying those two squares remains separate from the calculation.

```agda
module TriangleCalculation {P A B C : CAT} (pAn : isAn P)
  (g : MAP P (Map B C)) (f : MAP P (Map A B)) where
  open ParameterRetaining P
  open RetainedEvaluation P
  open RetainedSquares P

  G = retained g
  F = retained f
  I = identityTerm {P} B
  J = retained I
  ε = retained-identity B

  left : =₁ (composeTerm (composeTerm g I) f) (composeTerm g f)
  left = composeTerm-cong (compose-unitʳ pAn g) (idIso f)

  middle : =₁ (composeTerm (composeTerm g I) f) (composeTerm g (composeTerm I f))
  middle = compose-assoc pAn g I f

  right : =₁ (composeTerm g (composeTerm I f)) (composeTerm g f)
  right = composeTerm-cong (idIso g) (compose-unitˡ pAn f)

  source-comparison = (retained-compose g I ▷ F) ∙ retained-compose (composeTerm g I) f
  middle-comparison = (G ◁ retained-compose I f) ∙ retained-compose g (composeTerm I f)
  target-comparison = retained-compose g f

  external-left = (comp-unitʳ G ▷ F) ∙ ((G ◁ ε) ▷ F)
  external-middle = comp-assoc F J G
  external-right = G ◁ (comp-unitˡ F ∙ (ε ▷ F))

  LeftNaturality : Set m
  LeftNaturality = =₂ (target-comparison ∙ retainedIso left)
    ((retainedIso (compose-unitʳ pAn g) ⋆ retainedIso (idIso f)) ∙
      retained-compose (composeTerm g I) f)

  RightNaturality : Set m
  RightNaturality = =₂ (target-comparison ∙ retainedIso right)
    ((retainedIso (idIso g) ⋆ retainedIso (compose-unitˡ pAn f)) ∙
      retained-compose g (composeTerm I f))

  left-edge-image : LeftNaturality
    → =₂ (changeEndpoints source-comparison target-comparison (retainedIso left)) external-left
  left-edge-image natural =
    let c = retained-compose g I
        d = retained-compose (composeTerm g I) f
        β = G ◁ ε
        outer = comp-unitʳ G
        normalized = preWhisker-isoComp-at outer (β ∙ c) F ∙
          (preWhisker F ◁ compose-unitʳ-retained-β pAn g)
        expanded = isoComp-cong (idIso (outer ▷ F)) (preWhisker-isoComp-at β c F) ∙ normalized
        rebracket = isoComp-assoc-at external-left (c ▷ F) d ∙
          isoComp-cong (invIso (isoComp-assoc-at (outer ▷ F) (β ▷ F) (c ▷ F))) (idIso d)
        square = rebracket ∙
          (isoComp-cong expanded (idIso d) ∙
          (isoComp-cong
            (hcomp-idInner (retainedIso (compose-unitʳ pAn g)) F ∙
              hcomp-cong (idIso (retainedIso (compose-unitʳ pAn g))) (retainedIso-id f))
            (idIso d) ∙ natural))
    in square-to-changeEndpoints source-comparison target-comparison (retainedIso left) external-left square

  middle-edge-image :
    =₂ (changeEndpoints source-comparison middle-comparison (retainedIso middle)) external-middle
  middle-edge-image = square-to-changeEndpoints source-comparison middle-comparison
    (retainedIso middle) external-middle
    (cancel-two-front (G ◁ retained-compose I f) (retained-compose g (composeTerm I f))
      (external-middle ∙ source-comparison) ∙
      isoComp-cong (idIso middle-comparison) (compose-assoc-retained-β pAn g I f))

  right-edge-image : RightNaturality
    → =₂ (changeEndpoints middle-comparison target-comparison (retainedIso right)) external-right
  right-edge-image natural =
    let c = retained-compose I f
        d = retained-compose g (composeTerm I f)
        β = ε ▷ F
        outer = comp-unitˡ F
        normalized = postWhisker-isoComp-at G outer (β ∙ c) ∙
          (postWhisker G ◁ compose-unitˡ-retained-β pAn f)
        expanded = isoComp-cong (idIso (G ◁ outer)) (postWhisker-isoComp-at G β c) ∙ normalized
        rebracket = isoComp-assoc-at external-right (G ◁ c) d ∙
          (isoComp-cong
            (isoComp-cong (invIso (postWhisker-isoComp-at G outer β)) (idIso (G ◁ c)) ∙
              invIso (isoComp-assoc-at (G ◁ outer) (G ◁ β) (G ◁ c))) (idIso d))
        square = rebracket ∙
          (isoComp-cong expanded (idIso d) ∙
          (isoComp-cong
            (hcomp-idOuter G (retainedIso (compose-unitˡ pAn f)) ∙
              hcomp-cong (retainedIso-id g) (idIso (retainedIso (compose-unitˡ pAn f))))
            (idIso d) ∙ natural))
    in square-to-changeEndpoints middle-comparison target-comparison (retainedIso right) external-right square

  triangle : LeftNaturality → RightNaturality → =₂ left (right ∙ middle)
  triangle natural-left natural-right = retainedIso-reflect pAn left (right ∙ middle)
    (invIso (retainedIso-comp right middle) ∙
      changeEndpoints-reflect source-comparison target-comparison
        (retainedIso left) (retainedIso right ∙ retainedIso middle)
        (changeEndpoints-comp source-comparison middle-comparison target-comparison
          (retainedIso right) (retainedIso middle) ∙
        (invIso (isoComp-cong (right-edge-image natural-right) middle-edge-image) ∙
        (triangle-with-identity-comparison G F J ε ∙ left-edge-image natural-left))))
```

Both required naturality squares are supplied by the already proved
naturality of uncurrying composition. The resulting triangle is therefore
unconditional for the retained-route unitors and associator at an anima
parameter.

```agda
compose-triangle : {P A B C : CAT} (pAn : isAn P)
  (g : MAP P (Map B C)) (f : MAP P (Map A B))
  → =₂ (composeTerm-cong (compose-unitʳ pAn g) (idIso f))
      (composeTerm-cong (idIso g) (compose-unitˡ pAn f) ∙
        compose-assoc pAn g (identityTerm B) f)
compose-triangle {P} pAn g f = TriangleCalculation.triangle pAn g f
  (RetainedNaturality.retained-compose-natural P (compose-unitʳ pAn g) (idIso f))
  (RetainedNaturality.retained-compose-natural P (idIso g) (compose-unitˡ pAn f))
```
