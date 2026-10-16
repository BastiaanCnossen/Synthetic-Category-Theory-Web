# Products of pullback squares

The product of two supplied universal cones is universal. Its legs are
the literal product functors, and its matching pairs the two original
restricted matchings. Reading either coordinate retains a complete cone;
coordinate comparisons then reconstruct the comparison of the product cone.

The projection calculations, pairing and universal-cone recognition are
kept together here. No category of cones or additional coherence law is
assumed.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.ProductPullbacks where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (paste-square₌; transpose-square₌; post-square₌; replace-edges₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
  using (changeEndpoints; changeEndpoints-to-square; square-to-changeEndpoints;
    postWhisker-changeEndpoints; transport-square; reflect-transported-square;
    normalize-transported-square; cancel-endpoint-changes)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (restrict-triangle; restrict-triangle-assoc; restrict-square-One; restrict-change-square-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (postWhisker-comp-One; pentagon-whiskered)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair₌-extensionality)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone; ConeIdentification₁; cone-restrict)
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
  using (cone-compose; cone-inverse; cone-action-One; cone-restrict-assoc; cone-identification-restrict-One)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks using (Pullback; pullback-cone)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares
  using (IsPullback; module UniversalCone; isPullback-from-factor-and-reflection)

private
  module _ {Γ : Context} {P C : CAT Γ} where
    move-square : {f g f′ g′ : MAP P C}
      (b : g =₁ g′) (u : f =₁ g) (v : f′ =₁ g′) (a : f =₁ f′) →
      (b ∙ u) =₂ (v ∙ a) → (b ⁻¹ ∙ v) =₂ (u ∙ a ⁻¹)
    move-square b u v a square =
      let solved = comp₌-cong (id₌ (b ⁻¹)) square ∙ (inv-comp-left b u) ⁻¹
          rearranged = (comp₌-assoc (b ⁻¹) v a) ⁻¹ ∙ solved
      in (comp-inv-right (b ⁻¹ ∙ v) a ∙ comp₌-cong rearranged (id₌ (a ⁻¹))) ⁻¹

  module _ {Γ : Context} where
    restricted-normalization : {R T X Y Z : CAT Γ} (pi : MAP Y Z) (H : MAP X Y)
      (x : MAP T X) {y : MAP T Z} (n : (pi ∘ (H ∘ x)) =₁ y) (r : MAP R T) →
      (pi ∘ (H ∘ (x ∘ r))) =₁ (y ∘ r)
    restricted-normalization pi H x n r = restrict-triangle pi (H ∘ x) n r ∙
      (pi ◁ comp-assoc r x H) ⁻¹

    normalization-pre : {R T X Y Z : CAT Γ} (pi : MAP Y Z) (H : MAP X Y) (k : MAP X Z)
      (beta : (pi ∘ H) =₁ k) (x : MAP T X) (r : MAP R T)
      {y : MAP T Z} (n : (k ∘ x) =₁ y) →
      restricted-normalization pi H x (n ∙ restrict-triangle pi H beta x) r =₂
        (((n ▷ r) ∙ (comp-assoc r x k) ⁻¹) ∙ restrict-triangle pi H beta (x ∘ r))
    normalization-pre pi H k beta x r n =
      (comp₌-assoc (n ▷ r) (A ⁻¹) next) ⁻¹ ∙
        (comp₌-cong (id₌ (n ▷ r)) core ∙
          (comp₌-assoc (n ▷ r) (old ∙ corner) (edge ⁻¹) ∙
            (comp₌-cong (comp₌-assoc (n ▷ r) old corner) (id₌ (edge ⁻¹)) ∙
              comp₌-cong (comp₌-cong (preWhisker-comp₌ n (restrict-triangle pi H beta x) r)
                (id₌ corner)) (id₌ (edge ⁻¹)))))
      where
      A : ((k ∘ x) ∘ r) =₁ (k ∘ (x ∘ r))
      A = comp-assoc r x k
      old : ((pi ∘ (H ∘ x)) ∘ r) =₁ ((k ∘ x) ∘ r)
      old = restrict-triangle pi H beta x ▷ r
      next : (pi ∘ (H ∘ (x ∘ r))) =₁ (k ∘ (x ∘ r))
      next = restrict-triangle pi H beta (x ∘ r)
      corner : (pi ∘ ((H ∘ x) ∘ r)) =₁ ((pi ∘ (H ∘ x)) ∘ r)
      corner = (comp-assoc r (H ∘ x) pi) ⁻¹
      edge : (pi ∘ ((H ∘ x) ∘ r)) =₁ (pi ∘ (H ∘ (x ∘ r)))
      edge = pi ◁ comp-assoc r x H
      core : ((old ∙ corner) ∙ edge ⁻¹) =₂ (A ⁻¹ ∙ next)
      core = (move-square A (old ∙ corner) next edge
        ((restrict-triangle-assoc pi H beta x r) ⁻¹)) ⁻¹

    associator-corner : {R T X Y Z : CAT Γ}
      (r : MAP R T) (u : MAP T X) (pi : MAP X Y) (f : MAP Y Z) →
      ((comp-assoc u pi f ▷ r) ∙ (comp-assoc r u (f ∘ pi)) ⁻¹) =₂
        (((comp-assoc r (pi ∘ u) f) ⁻¹ ∙ (f ◁ (comp-assoc r u pi) ⁻¹)) ∙
          comp-assoc (u ∘ r) pi f)
    associator-corner r u pi f =
      comp₌-cong (comp₌-cong (id₌ ((comp-assoc r (pi ∘ u) f) ⁻¹))
        ((postWhisker-inverse f (comp-assoc r u pi)) ⁻¹))
        (id₌ (comp-assoc (u ∘ r) pi f)) ∙
      ((comp₌-assoc ((comp-assoc r (pi ∘ u) f) ⁻¹)
        ((f ◁ comp-assoc r u pi) ⁻¹) (comp-assoc (u ∘ r) pi f)) ⁻¹ ∙
        (pentagon-left-corner (comp-assoc (u ∘ r) pi f) (comp-assoc r u (f ∘ pi))
          (f ◁ comp-assoc r u pi) (comp-assoc r (pi ∘ u) f) (comp-assoc u pi f ▷ r)
          (pentagon-whiskered r u pi f)) ⁻¹)

    composite-normalization-pre : {R T X Y Z W : CAT Γ}
      (pi : MAP Y Z) (H : MAP X Y) (q : MAP X W) (f : MAP W Z)
      (beta : (pi ∘ H) =₁ (f ∘ q)) (u : MAP T X) (r : MAP R T) →
      restricted-normalization pi H u (comp-assoc u q f ∙ restrict-triangle pi H beta u) r =₂
        (((comp-assoc r (q ∘ u) f) ⁻¹ ∙ (f ◁ (comp-assoc r u q) ⁻¹)) ∙
          (comp-assoc (u ∘ r) q f ∙ restrict-triangle pi H beta (u ∘ r)))
    composite-normalization-pre pi H q f beta u r =
      comp₌-assoc ((comp-assoc r (q ∘ u) f) ⁻¹ ∙ (f ◁ (comp-assoc r u q) ⁻¹))
        (comp-assoc (u ∘ r) q f) (restrict-triangle pi H beta (u ∘ r)) ∙
        (comp₌-cong (associator-corner r u q f) (id₌ (restrict-triangle pi H beta (u ∘ r))) ∙
          normalization-pre pi H (f ∘ q) beta u r (comp-assoc u q f))

    extend-square : {P C : CAT Γ} {u u′ v v′ x y : MAP P C}
      (L : u =₁ u′) (R : v =₁ v′) (sigma : u =₁ v)
      (l : u =₁ x) (q : v =₁ y) (delta : x =₁ y) →
      (q ∙ sigma) =₂ (delta ∙ l) →
      ((q ∙ R ⁻¹) ∙ (R ∙ (sigma ∙ L ⁻¹))) =₂ (delta ∙ (l ∙ L ⁻¹))
    extend-square L R sigma l q delta square = comp₌-assoc delta l (L ⁻¹) ∙
      (comp₌-cong square (id₌ (L ⁻¹)) ∙
        ((comp₌-assoc q sigma (L ⁻¹)) ⁻¹ ∙
          (comp₌-cong (id₌ q) (inv-comp-left R (sigma ∙ L ⁻¹)) ∙
            comp₌-assoc q (R ⁻¹) (R ∙ (sigma ∙ L ⁻¹)))))

    coordinate-pre : {C D E Z S T : CAT Γ} {F : MAP C E} {G : MAP D E}
      (pi : MAP E Z) (t : Cone F G T) (r : MAP S T)
      {x y : MAP T Z} (l : (pi ∘ (F ∘ Cone.left t)) =₁ x)
      (q : (pi ∘ (G ∘ Cone.right t)) =₁ y)
      {x′ : MAP S Z} (l′ : (pi ∘ (F ∘ (Cone.left t ∘ r))) =₁ x′)
      (q′ : (pi ∘ (G ∘ (Cone.right t ∘ r))) =₁ (y ∘ r)) (D′ : x′ =₁ (x ∘ r)) →
      restricted-normalization pi F (Cone.left t) l r =₂ (D′ ∙ l′) →
      restricted-normalization pi G (Cone.right t) q r =₂ q′ →
      (q′ ∙ ((pi ◁ Cone.match (cone-restrict r t)) ∙ l′ ⁻¹)) =₂
        (((q ∙ ((pi ◁ Cone.match t) ∙ l ⁻¹)) ▷ r) ∙ D′)
    coordinate-pre {F = F} {G} pi t r {x} {y} l q l′ q′ D′ left right =
      square-to-changeEndpoints l′ q′ (pi ◁ Cone.match (cone-restrict r t)) (delta ∙ D′)
        ((comp₌-assoc delta D′ l′) ⁻¹ ∙
          (comp₌-cong (id₌ delta) left ∙
            (extend-square (pi ◁ L) (pi ◁ R) (pi ◁ (Cone.match t ▷ r))
              (restrict-triangle pi (F ∘ Cone.left t) l r)
              (restrict-triangle pi (G ∘ Cone.right t) q r) delta
              (restrict-square-One pi (Cone.match t) edge l q r
                (changeEndpoints-to-square l q (pi ◁ Cone.match t) edge (id₌ edge))) ∙
              (comp₌-cong (id₌ (restricted-normalization pi G (Cone.right t) q r))
                (postWhisker-changeEndpoints pi L R (Cone.match t ▷ r)) ∙
                comp₌-cong (right ⁻¹) (id₌ (pi ◁ Cone.match (cone-restrict r t)))))))
      where
      edge : x =₁ y
      edge = q ∙ ((pi ◁ Cone.match t) ∙ l ⁻¹)
      delta : (x ∘ r) =₁ (y ∘ r)
      delta = edge ▷ r
      L = comp-assoc r (Cone.left t) F
      R = comp-assoc r (Cone.right t) G
```

Reading a coordinate transports the projected matching along the two
specified projection triangles. Both comparison and restriction keep
these particular normalization paths.

```agda
module Coordinate {Γ : Context} {A B E A′ B′ E′ : CAT Γ}
  (F : MAP A E) (G : MAP B E) (f : MAP A′ E′) (g : MAP B′ E′)
  (p : MAP A A′) (q : MAP B B′) (pi : MAP E E′)
  (beta : (pi ∘ F) =₁ (f ∘ p)) (gamma : (pi ∘ G) =₁ (g ∘ q)) where
  left-normal : {T : CAT Γ} (u : MAP T A) → (pi ∘ (F ∘ u)) =₁ (f ∘ (p ∘ u))
  left-normal u = comp-assoc u p f ∙ restrict-triangle pi F beta u
  right-normal : {T : CAT Γ} (v : MAP T B) → (pi ∘ (G ∘ v)) =₁ (g ∘ (q ∘ v))
  right-normal v = comp-assoc v q g ∙ restrict-triangle pi G gamma v
  read : {T : CAT Γ} → Cone F G T → Cone f g T
  read t = record
    { left = p ∘ Cone.left t; right = q ∘ Cone.right t
    ; match = right-normal (Cone.right t) ∙
        ((pi ◁ Cone.match t) ∙ (left-normal (Cone.left t)) ⁻¹) }
  left-natural : {T : CAT Γ} {u v : MAP T A} (alpha : u =₁ v) →
    (left-normal v ∙ (pi ◁ (F ◁ alpha))) =₂ ((f ◁ (p ◁ alpha)) ∙ left-normal u)
  left-natural alpha = paste-square₌
    (restrict-change-square-One pi F (f ∘ p) beta alpha) (postWhisker-comp-One alpha p f)
  right-natural : {T : CAT Γ} {u v : MAP T B} (alpha : u =₁ v) →
    (right-normal v ∙ (pi ◁ (G ◁ alpha))) =₂ ((g ◁ (q ◁ alpha)) ∙ right-normal u)
  right-natural alpha = paste-square₌
    (restrict-change-square-One pi G (g ∘ q) gamma alpha) (postWhisker-comp-One alpha q g)
  read-identification : {T : CAT Γ} {s t : Cone F G T} →
    ConeIdentification₁ s t → ConeIdentification₁ (read s) (read t)
  read-identification {s = s} {t} Phi = record
    { left = p ◁ ConeIdentification₁.left Phi; right = q ◁ ConeIdentification₁.right Phi
    ; compatible = transport-square
        (left-normal (Cone.left s)) (left-normal (Cone.left t))
        (right-normal (Cone.right s)) (right-normal (Cone.right t))
        (pi ◁ Cone.match s) (pi ◁ Cone.match t)
        (pi ◁ (F ◁ ConeIdentification₁.left Phi)) (pi ◁ (G ◁ ConeIdentification₁.right Phi))
        (f ◁ (p ◁ ConeIdentification₁.left Phi)) (g ◁ (q ◁ ConeIdentification₁.right Phi))
        (left-natural (ConeIdentification₁.left Phi)) (right-natural (ConeIdentification₁.right Phi))
        (post-square₌ pi (ConeIdentification₁.compatible Phi)) }
  read-restrict : {S T : CAT Γ} (r : MAP S T) (t : Cone F G T) →
    ConeIdentification₁ (read (cone-restrict r t)) (cone-restrict r (read t))
  read-restrict r t = record
    { left = left-change; right = right-change
    ; compatible = normalize-transported-square AL AR delta delta′ (f ◁ left-change) (g ◁ right-change)
        (comp₌-assoc D (right-normal (v ∘ r))
          ((pi ◁ Cone.match (cone-restrict r t)) ∙ (left-normal (u ∘ r)) ⁻¹) ∙ calculation ⁻¹) }
    where
    u = Cone.left t
    v = Cone.right t
    left-change = (comp-assoc r u p) ⁻¹
    right-change = (comp-assoc r v q) ⁻¹
    AL = comp-assoc r (p ∘ u) f
    AR = comp-assoc r (q ∘ v) g
    L = AL ⁻¹ ∙ (f ◁ left-change)
    D = AR ⁻¹ ∙ (g ◁ right-change)
    delta = Cone.match (read t) ▷ r
    delta′ = Cone.match (read (cone-restrict r t))
    calculation = coordinate-pre pi t r (left-normal u) (right-normal v)
      (left-normal (u ∘ r)) (D ∙ right-normal (v ∘ r)) L
      (composite-normalization-pre pi F p f beta u r)
      (composite-normalization-pre pi G q g gamma v r)

private
  module ProductCoordinates {Γ : Context} {A₀ A₁ B₀ B₁ E₀ E₁ : CAT Γ}
    (f₀ : MAP A₀ E₀) (f₁ : MAP A₁ E₁) (g₀ : MAP B₀ E₀) (g₁ : MAP B₁ E₁) where
    F : MAP (A₀ × A₁) (E₀ × E₁)
    F = productMap f₀ f₁
    G : MAP (B₀ × B₁) (E₀ × E₁)
    G = productMap g₀ g₁
    module First = Coordinate F G f₀ g₀ pr₁ pr₁ pr₁
      (pair-β₁ (f₀ ∘ pr₁) (f₁ ∘ pr₂)) (pair-β₁ (g₀ ∘ pr₁) (g₁ ∘ pr₂))
    module Second = Coordinate F G f₁ g₁ pr₂ pr₂ pr₂
      (pair-β₂ (f₀ ∘ pr₁) (f₁ ∘ pr₂)) (pair-β₂ (g₀ ∘ pr₁) (g₁ ∘ pr₂))

    module Paired {T : CAT Γ} (s₀ : Cone f₀ g₀ T) (s₁ : Cone f₁ g₁ T) where
      p : MAP T (A₀ × A₁)
      p = pair (Cone.left s₀) (Cone.left s₁)
      q : MAP T (B₀ × B₁)
      q = pair (Cone.right s₀) (Cone.right s₁)
      left₀ = pair-β₁ (Cone.left s₀) (Cone.left s₁)
      left₁ = pair-β₂ (Cone.left s₀) (Cone.left s₁)
      right₀ = pair-β₁ (Cone.right s₀) (Cone.right s₁)
      right₁ = pair-β₂ (Cone.right s₀) (Cone.right s₁)
      delta₀ : (f₀ ∘ (pr₁ ∘ p)) =₁ (g₀ ∘ (pr₁ ∘ q))
      delta₀ = (g₀ ◁ right₀) ⁻¹ ∙ (Cone.match s₀ ∙ (f₀ ◁ left₀))
      delta₁ : (f₁ ∘ (pr₂ ∘ p)) =₁ (g₁ ∘ (pr₂ ∘ q))
      delta₁ = (g₁ ◁ right₁) ⁻¹ ∙ (Cone.match s₁ ∙ (f₁ ◁ left₁))
      epsilon₀ : (pr₁ ∘ (F ∘ p)) =₁ (pr₁ ∘ (G ∘ q))
      epsilon₀ = (First.right-normal q) ⁻¹ ∙ (delta₀ ∙ First.left-normal p)
      epsilon₁ : (pr₂ ∘ (F ∘ p)) =₁ (pr₂ ∘ (G ∘ q))
      epsilon₁ = (Second.right-normal q) ⁻¹ ∙ (delta₁ ∙ Second.left-normal p)
      cone : Cone F G T
      cone = record { left = p; right = q; match = pair₌ epsilon₀ epsilon₁ }
      first-match : Cone.match (First.read cone) =₂ delta₀
      first-match = cancel-endpoint-changes (First.left-normal p) (First.right-normal q) delta₀ ∙
        comp₌-cong (id₌ (First.right-normal q))
          (comp₌-cong (pair₌-β₁ epsilon₀ epsilon₁) (id₌ ((First.left-normal p) ⁻¹)))
      second-match : Cone.match (Second.read cone) =₂ delta₁
      second-match = cancel-endpoint-changes (Second.left-normal p) (Second.right-normal q) delta₁ ∙
        comp₌-cong (id₌ (Second.right-normal q))
          (comp₌-cong (pair₌-β₂ epsilon₀ epsilon₁) (id₌ ((Second.left-normal p) ⁻¹)))
      first : ConeIdentification₁ (First.read cone) s₀
      first = record
        { left = left₀; right = right₀
        ; compatible = comp₌-cong (id₌ (g₀ ◁ right₀)) (first-match ⁻¹) ∙
            (comp-inv-left (g₀ ◁ right₀) (Cone.match s₀ ∙ (f₀ ◁ left₀))) ⁻¹ }
      second : ConeIdentification₁ (Second.read cone) s₁
      second = record
        { left = left₁; right = right₁
        ; compatible = comp₌-cong (id₌ (g₁ ◁ right₁)) (second-match ⁻¹) ∙
            (comp-inv-left (g₁ ◁ right₁) (Cone.match s₁ ∙ (f₁ ◁ left₁))) ⁻¹ }

    reflect : {T : CAT Γ} {s t : Cone F G T} →
      ConeIdentification₁ (First.read s) (First.read t) →
      ConeIdentification₁ (Second.read s) (Second.read t) → ConeIdentification₁ s t
    reflect {s = s} {t} Phi Psi = record
      { left = L; right = R
      ; compatible = pair₌-extensionality first-square second-square }
      where
      L = pair₌ (ConeIdentification₁.left Phi) (ConeIdentification₁.left Psi)
      R = pair₌ (ConeIdentification₁.right Phi) (ConeIdentification₁.right Psi)
      left₀ = pair₌-β₁ (ConeIdentification₁.left Phi) (ConeIdentification₁.left Psi)
      left₁ = pair₌-β₂ (ConeIdentification₁.left Phi) (ConeIdentification₁.left Psi)
      right₀ = pair₌-β₁ (ConeIdentification₁.right Phi) (ConeIdentification₁.right Psi)
      right₁ = pair₌-β₂ (ConeIdentification₁.right Phi) (ConeIdentification₁.right Psi)
      first-square = (postWhisker-comp₌ pr₁ (G ◁ R) (Cone.match s)) ⁻¹ ∙
        (reflect-transported-square
          (First.left-normal (Cone.left s)) (First.right-normal (Cone.right s))
          (First.left-normal (Cone.left t)) (First.right-normal (Cone.right t))
          (pr₁ ◁ Cone.match s) (pr₁ ◁ Cone.match t) (pr₁ ◁ (F ◁ L)) (pr₁ ◁ (G ◁ R))
          (f₀ ◁ (pr₁ ◁ L)) (g₀ ◁ (pr₁ ◁ R)) (First.left-natural L) (First.right-natural R)
          (comp₌-cong (postWhisker g₀ ◁ right₀ ⁻¹) (id₌ (Cone.match (First.read s))) ∙
            (ConeIdentification₁.compatible Phi ∙
              comp₌-cong (id₌ (Cone.match (First.read t))) (postWhisker f₀ ◁ left₀))) ∙
          postWhisker-comp₌ pr₁ (Cone.match t) (F ◁ L))
      second-square = (postWhisker-comp₌ pr₂ (G ◁ R) (Cone.match s)) ⁻¹ ∙
        (reflect-transported-square
          (Second.left-normal (Cone.left s)) (Second.right-normal (Cone.right s))
          (Second.left-normal (Cone.left t)) (Second.right-normal (Cone.right t))
          (pr₂ ◁ Cone.match s) (pr₂ ◁ Cone.match t) (pr₂ ◁ (F ◁ L)) (pr₂ ◁ (G ◁ R))
          (f₁ ◁ (pr₂ ◁ L)) (g₁ ◁ (pr₂ ◁ R)) (Second.left-natural L) (Second.right-natural R)
          (comp₌-cong (postWhisker g₁ ◁ right₁ ⁻¹) (id₌ (Cone.match (Second.read s))) ∙
            (ConeIdentification₁.compatible Psi ∙
              comp₌-cong (id₌ (Cone.match (Second.read t))) (postWhisker f₁ ◁ left₁))) ∙
          postWhisker-comp₌ pr₂ (Cone.match t) (F ◁ L))
```

The square below has the literal productMap legs. Its matching is the
paired matching of the original cones restricted along the two product
projections. Coordinate reading supplies full beta laws for the factor;
coordinate reflection and product uniqueness supply reflection at the
product vertex.

```agda
module Product {Γ : Context} {A₀ A₁ B₀ B₁ E₀ E₁ S₀ S₁ : CAT Γ}
  {f₀ : MAP A₀ E₀} {f₁ : MAP A₁ E₁} {g₀ : MAP B₀ E₀} {g₁ : MAP B₁ E₁}
  (s₀ : Cone f₀ g₀ S₀) (s₁ : Cone f₁ g₁ S₁) where
  private
    module Coordinates = ProductCoordinates f₀ f₁ g₀ g₁
      using (F; G; module First; module Second; module Paired; reflect)
    module Pair = Coordinates.Paired (cone-restrict pr₁ s₀) (cone-restrict pr₂ s₁)
      using (cone; first; second)

  square : Cone (productMap f₀ f₁) (productMap g₀ g₁) (S₀ × S₁)
  square = Pair.cone

  private
    first-restriction : {T : CAT Γ} (h : MAP T (S₀ × S₁)) →
      ConeIdentification₁ (Coordinates.First.read (cone-restrict h square)) (cone-restrict (pr₁ ∘ h) s₀)
    first-restriction h = cone-compose (cone-restrict-assoc h pr₁ s₀)
      (cone-compose (cone-identification-restrict-One h Pair.first) (Coordinates.First.read-restrict h square))
    second-restriction : {T : CAT Γ} (h : MAP T (S₀ × S₁)) →
      ConeIdentification₁ (Coordinates.Second.read (cone-restrict h square)) (cone-restrict (pr₂ ∘ h) s₁)
    second-restriction h = cone-compose (cone-restrict-assoc h pr₂ s₁)
      (cone-compose (cone-identification-restrict-One h Pair.second) (Coordinates.Second.read-restrict h square))

    module Recognition (e₀ : IsPullback s₀) (e₁ : IsPullback s₁) where
      module U₀ = UniversalCone s₀ e₀ using (factor; β; reflect)
      module U₁ = UniversalCone s₁ e₁ using (factor; β; reflect)
      target : Cone Coordinates.F Coordinates.G (Pullback Coordinates.F Coordinates.G)
      target = pullback-cone Coordinates.F Coordinates.G
      factor₀ : MAP (Pullback Coordinates.F Coordinates.G) S₀
      factor₀ = U₀.factor (Coordinates.First.read target)
      factor₁ : MAP (Pullback Coordinates.F Coordinates.G) S₁
      factor₁ = U₁.factor (Coordinates.Second.read target)
      inverse : MAP (Pullback Coordinates.F Coordinates.G) (S₀ × S₁)
      inverse = pair factor₀ factor₁
      factorization : ConeIdentification₁ (cone-restrict inverse square) target
      factorization = Coordinates.reflect
        (cone-compose (U₀.β (Coordinates.First.read target))
          (cone-compose (cone-action-One s₀ (pair-β₁ factor₀ factor₁)) (first-restriction inverse)))
        (cone-compose (U₁.β (Coordinates.Second.read target))
          (cone-compose (cone-action-One s₁ (pair-β₂ factor₀ factor₁)) (second-restriction inverse)))
      reflect-maps : (h k : MAP (S₀ × S₁) (S₀ × S₁)) →
        ConeIdentification₁ (cone-restrict h square) (cone-restrict k square) → h =₁ k
      reflect-maps h k Phi = pair₌
        (U₀.reflect (pr₁ ∘ h) (pr₁ ∘ k)
          (cone-compose (first-restriction k)
            (cone-compose (Coordinates.First.read-identification Phi) (cone-inverse (first-restriction h)))))
        (U₁.reflect (pr₂ ∘ h) (pr₂ ∘ k)
          (cone-compose (second-restriction k)
            (cone-compose (Coordinates.Second.read-identification Phi) (cone-inverse (second-restriction h)))))

  square-isPullback : IsPullback s₀ → IsPullback s₁ → IsPullback square
  square-isPullback e₀ e₁ = isPullback-from-factor-and-reflection square
    (Recognition.inverse e₀ e₁) (Recognition.factorization e₀ e₁) (Recognition.reflect-maps e₀ e₁)
```

For a cone to paired functors, its native projection triangles have targets
the component functors themselves. Keep these direct triangles rather
than insert identity factorizations. This is the normalization used by
the existing Hom-family reader. The same restriction calculation above
supplies its original coordinate matching under parameter change.

```agda
module NativeCoordinate {Γ : Context} {A B E E′ : CAT Γ}
  (F : MAP A E) (G : MAP B E) (f : MAP A E′) (g : MAP B E′) (pi : MAP E E′)
  (beta : (pi ∘ F) =₁ f) (gamma : (pi ∘ G) =₁ g) where
  left-normal : {T : CAT Γ} (u : MAP T A) → (pi ∘ (F ∘ u)) =₁ (f ∘ u)
  left-normal u = restrict-triangle pi F beta u
  right-normal : {T : CAT Γ} (v : MAP T B) → (pi ∘ (G ∘ v)) =₁ (g ∘ v)
  right-normal v = restrict-triangle pi G gamma v
  edge : {T : CAT Γ} (t : Cone F G T) → (f ∘ Cone.left t) =₁ (g ∘ Cone.right t)
  edge t = right-normal (Cone.right t) ∙
    ((pi ◁ Cone.match t) ∙ (left-normal (Cone.left t)) ⁻¹)
  left-natural : {T : CAT Γ} {u v : MAP T A} (L : u =₁ v) →
    (left-normal v ∙ (pi ◁ (F ◁ L))) =₂ ((f ◁ L) ∙ left-normal u)
  left-natural L = restrict-change-square-One pi F f beta L
  right-natural : {T : CAT Γ} {u v : MAP T B} (R : u =₁ v) →
    (right-normal v ∙ (pi ◁ (G ◁ R))) =₂ ((g ◁ R) ∙ right-normal u)
  right-natural R = restrict-change-square-One pi G g gamma R
  edge-identification : {T : CAT Γ} {s t : Cone F G T} (Phi : ConeIdentification₁ s t) →
    (edge t ∙ (f ◁ ConeIdentification₁.left Phi)) =₂
      ((g ◁ ConeIdentification₁.right Phi) ∙ edge s)
  edge-identification {s = s} {t} Phi = transport-square
    (left-normal (Cone.left s)) (left-normal (Cone.left t))
    (right-normal (Cone.right s)) (right-normal (Cone.right t))
    (pi ◁ Cone.match s) (pi ◁ Cone.match t)
    (pi ◁ (F ◁ ConeIdentification₁.left Phi)) (pi ◁ (G ◁ ConeIdentification₁.right Phi))
    (f ◁ ConeIdentification₁.left Phi) (g ◁ ConeIdentification₁.right Phi)
    (left-natural (ConeIdentification₁.left Phi)) (right-natural (ConeIdentification₁.right Phi))
    (post-square₌ pi (ConeIdentification₁.compatible Phi))

  edge-reflect : {T : CAT Γ} (s t : Cone F G T)
    (L : Cone.left s =₁ Cone.left t) (R : Cone.right s =₁ Cone.right t) →
    (edge t ∙ (f ◁ L)) =₂ ((g ◁ R) ∙ edge s) →
    (pi ◁ (Cone.match t ∙ (F ◁ L))) =₂ (pi ◁ ((G ◁ R) ∙ Cone.match s))
  edge-reflect s t L R square = (postWhisker-comp₌ pi (G ◁ R) (Cone.match s)) ⁻¹ ∙
    (reflect-transported-square
      (left-normal (Cone.left s)) (right-normal (Cone.right s))
      (left-normal (Cone.left t)) (right-normal (Cone.right t))
      (pi ◁ Cone.match s) (pi ◁ Cone.match t) (pi ◁ (F ◁ L)) (pi ◁ (G ◁ R))
      (f ◁ L) (g ◁ R) (left-natural L) (right-natural R) square ∙
      postWhisker-comp₌ pi (Cone.match t) (F ◁ L))

  private
    normalization-restrict : {R T X Y Z : CAT Γ} (projection : MAP Y Z) (H : MAP X Y)
      (component : MAP X Z) (b : (projection ∘ H) =₁ component) (u : MAP T X) (r : MAP R T) →
      restricted-normalization projection H u (restrict-triangle projection H b u) r =₂
        ((comp-assoc r u component) ⁻¹ ∙ restrict-triangle projection H b (u ∘ r))
    normalization-restrict projection H component b u r =
      (move-square (comp-assoc r u component)
        ((restrict-triangle projection H b u ▷ r) ∙ (comp-assoc r (H ∘ u) projection) ⁻¹)
        (restrict-triangle projection H b (u ∘ r)) (projection ◁ comp-assoc r u H)
        ((restrict-triangle-assoc projection H b u r) ⁻¹)) ⁻¹

  edge-restrict : {R T : CAT Γ} (r : MAP R T) (t : Cone F G T) →
    edge (cone-restrict r t) =₂
      (comp-assoc r (Cone.right t) g ∙
        ((edge t ▷ r) ∙ (comp-assoc r (Cone.left t) f) ⁻¹))
  edge-restrict r t = (comp-inv-left AR (edge (cone-restrict r t)) ∙
    (comp₌-cong (id₌ AR) (comp₌-assoc (AR ⁻¹) rn middle) ∙
      comp₌-cong (id₌ AR) (calculation ⁻¹))) ⁻¹
    where
    AL = comp-assoc r (Cone.left t) f
    AR = comp-assoc r (Cone.right t) g
    ln = left-normal (Cone.left t ∘ r)
    rn = right-normal (Cone.right t ∘ r)
    middle = (pi ◁ Cone.match (cone-restrict r t)) ∙ ln ⁻¹
    calculation = coordinate-pre pi t r (left-normal (Cone.left t)) (right-normal (Cone.right t))
      ln (AR ⁻¹ ∙ rn) (AL ⁻¹)
      (normalization-restrict pi F f beta (Cone.left t) r)
      (normalization-restrict pi G g gamma (Cone.right t) r)
```
