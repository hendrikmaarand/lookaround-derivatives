import LookaroundDerivatives.Triple
import LookaroundDerivatives.Expressions
import LookaroundDerivatives.Lists
import LookaroundDerivatives.DerProperties


----------------------------------------------------------------------------

theorem wDBhd_0 [DecidableEq α] : ∀ (w : List α), wDBhd w `0 ≡ `0 := by
  intro w
  induction w
  try exact .refl rfl
  rw [wDBhd, DBhd]
  assumption

theorem wD_0 [DecidableEq α] : ∀ (w : List α), wD w `0 ≡ `0 := by
  intro w
  induction w
  try exact .refl rfl
  rw [wD, D]
  assumption

theorem wDAhd_0 [DecidableEq α] : ∀ (w : List α), wDAhd w `0 ≡ `0 := by
  intro w
  induction w
  try exact .refl rfl
  rw [wDAhd, DAhd]
  assumption

----------------------------------------------------------------------------

theorem wDBhd_bhd [DecidableEq α]
                  : ∀ (e : RE α) (w : List α),
                      wDBhd w (`◁ e) ≡ `◁ (wD w e) := by
  intro e w
  induction w generalizing e with
  | nil => exact .refl rfl
  | cons a w ih => rw [wDBhd, wD]
                   simp [DBhd]
                   apply ih

theorem wD_bhd_cons [DecidableEq α]
                    : ∀ (e : RE α) (a : α) (w : List α),
                        wD (a :: w) (`◁ e) ≡ `0 := by
  intro e a w
  rw [wD, D]
  apply wD_0

theorem wDAhd_bhd_cons [DecidableEq α]
                       : ∀ (e : RE α) (a : α) (w : List α),
                           wDAhd (a :: w) (`◁ e) ≡ wDAhd (a :: w) e := by
  intro e a w
  exact .refl rfl



----------------------------------------------------------------------------

theorem wDBhd_1 [DecidableEq α] : ∀ (w : List α), wDBhd w `1 ≡ `1 := by
  intro w
  induction w with
  | nil => exact .refl rfl
  | cons a w ih => assumption

theorem wD_1_cons [DecidableEq α]
                  : ∀ (a : α) (w : List α),
                      wD (a :: w) `1 ≡ `0 := by
  intro a w
  exact wD_0 w

theorem wDAhd_1_cons [DecidableEq α]
                     : ∀ (a : α) (w : List α),
                         wDAhd (a :: w) `1 ≡ `◁ `1 := by
  intro a w
  rw [wDAhd, DAhd]
  match w with
  | [] => exact .refl rfl
  | b :: w' => apply wDAhd_1_cons b


-----------------------------------------------------------------------------

theorem wDBhd_a [DecidableEq α] : ∀ (a : α) (w : List α), wDBhd w (`$ a) ≡ `$ a := by
  intro a w
  induction w
  try exact .refl rfl
  rw [wDBhd, DBhd]
  assumption

theorem wD_a_cons [DecidableEq α]
                  : ∀ (a b : α) (w : List α),
                      w = [] ∧ b = a ∧ wD (b :: w) (`$ a) ≡ `◁ `1
                      ∨
                      (w ≠ [] ∨ b ≠ a) ∧ wD (b :: w) (`$ a) ≡ `0 := by
  intro a b w
  if h : b = a then
    simp [h]
    cases w
    . rw [wD, wD, D]
      simp [eq_self]
      exact .refl rfl
    . simp
      rw [wD, wD, D]
      simp [eq_self]
      rw [D]
      apply wD_0
  else
    rw [wD, D]
    simp [h]
    apply wD_0

theorem wDAhd_a_cons [DecidableEq α]
                     : ∀ (a b : α) (w : List α),
                         wDAhd (b :: w) (`$ a) ≡ `0 := by
  intro a b w
  apply wDAhd_0

--------------------------------------------------------------------------

theorem wDBhd_ahd [DecidableEq α]
                  : ∀ (e : RE α) (w : List α),
                      wDBhd w (`▷ e) ≡ `▷ (wDBhd w e) := by
  intro e w
  induction w generalizing e with
  | nil => exact .refl rfl
  | cons a w ih => rw [wDBhd, DBhd, wDBhd]
                   apply ih

theorem wD_ahd_cons [DecidableEq α]
                    : ∀ (e : RE α) (a : α) (w : List α),
                        wD (a :: w) (`▷ e) ≡ `0 := by
  intro e a w
  apply wD_0

theorem wDAhd_ahd [DecidableEq α]
                  : ∀ (e : RE α) (w : List α),
                      wDAhd w (`▷ e) ≡ `▷ (wD w e) := by
  intro e w
  induction w generalizing e with
  | nil => exact .refl rfl
  | cons a w ih => rw [wDAhd, wD, DAhd]
                   apply ih




theorem wDAhd_cons {α} [DecidableEq α]
                   : ∀ (a : α) (w : List α) (e : RE α),
                       wDAhd (a :: w) e ≡ `▷ (wD w (extractLAhd a e)) := by
  intro a w e
  calc wDAhd (a :: w) e
    _ ≡ wDAhd w (DAhd a e)             := .refl rfl
    _ ≡ wDAhd w (`▷ (extractLAhd a e)) := wDAhd_cong (DAhd_exists a e)
    _ ≡ `▷ (wD w (extractLAhd a e))    := wDAhd_ahd (extractLAhd a e) w


theorem wDAhd_cons_mult_inter {α} [DecidableEq α] {a a' : α} {w w' : List α} {e f : RE α}
                              : wDAhd (a :: w) e `· wDAhd (a' :: w') f ≡
                                wDAhd (a :: w) e & wDAhd (a' :: w') f := by
  let e' := wD w  (extractLAhd a  e)
  let f' := wD w' (extractLAhd a' f)
  have eq  := wDAhd_cons a  w  e
  have eq' := wDAhd_cons a' w' f
  calc wDAhd (a :: w) e `· wDAhd (a' :: w') f
    _ ≡ `▷ e' `· `▷ f' := .multCong eq eq'
    _ ≡ `▷ e'  & `▷ f' := .lahdMultInter
    _ ≡ wDAhd (a :: w) e & wDAhd (a' :: w') f := .interCong (.sym eq) (.sym eq')



-- ACI of mult on nonepsilon lookahead derivatives

theorem wDAhd_cons_mult_assoc {α} [DecidableEq α] {a b : α} {x y : List α} {e f g : RE α}
                             : wDAhd (a :: x) e `· wDAhd (b :: y) f `· g
                               ≡
                               (wDAhd (a :: x) e `· wDAhd (b :: y) f) `· g := by
  let e' := wD x  (extractLAhd a e)
  let f' := wD y (extractLAhd b f)
  have eq  := wDAhd_cons a x e
  have eq' := wDAhd_cons b y f
  calc wDAhd (a :: x) e `· (wDAhd (b :: y) f `· g)
    _ ≡ `▷ e' `· (`▷ f' `· g)                       := .multCong eq (.multCong eq' (.refl rfl))
    _ ≡ (`▷ e' `· `▷ f') `· g                       := .lahdMultAssoc
    _ ≡ (wDAhd (a :: x) e `· wDAhd (b :: y) f) `· g := .multCong (.multCong (.sym eq) (.sym eq'))
                                                                 (.refl rfl)

theorem wDAhd_cons_mult_comm {α} [DecidableEq α] {a a' : α} {w w' : List α} {e f : RE α}
                             : wDAhd (a :: w)   e `· wDAhd (a' :: w') f
                               ≡
                               wDAhd (a' :: w') f `· wDAhd (a :: w)   e := by
  calc wDAhd (a :: w) e `· wDAhd (a' :: w') f
    _ ≡ wDAhd (a :: w) e & wDAhd (a' :: w') f  := wDAhd_cons_mult_inter
    _ ≡ wDAhd (a' :: w') f & wDAhd (a :: w) e  := .interComm
    _ ≡ wDAhd (a' :: w') f `· wDAhd (a :: w) e := .sym wDAhd_cons_mult_inter

theorem wDAhd_cons_mult_idem {α} [DecidableEq α] {a : α} {w : List α} {e : RE α}
                             : wDAhd (a :: w) e `· wDAhd (a :: w) e
                               ≡
                               wDAhd (a :: w) e := by
  calc wDAhd (a :: w) e `· wDAhd (a :: w) e
    _ ≡ wDAhd (a :: w) e & wDAhd (a :: w) e := wDAhd_cons_mult_inter
    _ ≡ wDAhd (a :: w) e                    := .sym .interIdem




----------------------------------------------------------------------------

theorem wDBhd_plus [DecidableEq α]
                   : ∀ (e f : RE α) (w : List α),
                       wDBhd w (e `+ f) ≡ wDBhd w e `+ wDBhd w f := by
  intro e f w
  induction w generalizing e f with
  | nil => exact .refl rfl
  | cons a w ih => rw [wDBhd, DBhd, wDBhd, wDBhd]
                   apply ih

theorem wD_plus [DecidableEq α]
                : ∀ (e f : RE α) (w : List α),
                    wD w (e `+ f) ≡ wD w e `+ wD w f := by
  intro e f w
  induction w generalizing e f with
  | nil => exact .refl rfl
  | cons a w ih => rw [wD, D, wD, wD]
                   apply ih

theorem wDAhd_plus [DecidableEq α]
                   : ∀ (e f : RE α) (w : List α),
                       wDAhd w (e `+ f) ≡ wDAhd w e `+ wDAhd w f := by
  intro e f w
  induction w generalizing e f with
  | nil => exact .refl rfl
  | cons a w ih => rw [wDAhd, DAhd, wDAhd, wDAhd]
                   apply ih

------------------------------------------------------------------------------

theorem wDBhd_inter [DecidableEq α]
                    : ∀ (e f : RE α) (w : List α),
                        wDBhd w (e & f) ≡ wDBhd w e & wDBhd w f := by
  intro e f w
  induction w generalizing e f with
  | nil => exact .refl rfl
  | cons a w ih => rw [wDBhd, DBhd, wDBhd, wDBhd]
                   apply ih

theorem wD_inter [DecidableEq α]
                 : ∀ (e f : RE α) (w : List α),
                     wD w (e & f) ≡ wD w e & wD w f := by
  intro e f w
  induction w generalizing e f with
  | nil => exact .refl rfl
  | cons a w ih => rw [wD, D, wD, wD]
                   apply ih

theorem wDAhd_inter [DecidableEq α]
                    : ∀ (e f : RE α) (w : List α),
                        wDAhd w (e & f) ≡ wDAhd w e & wDAhd w f := by
  intro e f w
  induction w generalizing e f with
  | nil => exact .refl rfl
  | cons a w ih => rw [wDAhd, DAhd, wDAhd, wDAhd]
                   apply ih

------------------------------------------------------------------------------

theorem wDBhd_diff [DecidableEq α]
                   : ∀ (e f : RE α) (w : List α),
                       wDBhd w (e `- f) ≡ wDBhd w e `- wDBhd w f := by
  intro e f w
  induction w generalizing e f with
  | nil => exact .refl rfl
  | cons a w ih => rw [wDBhd, DBhd, wDBhd, wDBhd]
                   apply ih

theorem wD_diff [DecidableEq α]
                : ∀ (e f : RE α) (w : List α),
                    wD w (e `- f) ≡ wD w e `- wD w f := by
  intro e f w
  induction w generalizing e f with
  | nil => exact .refl rfl
  | cons a w ih => rw [wD, D, wD, wD]
                   apply ih

theorem wDAhd_diff [DecidableEq α]
                   : ∀ (e f : RE α) (w : List α),
                       wDAhd w (e `- f) ≡ wDAhd w e `- wDAhd w f := by
  intro e f w
  induction w generalizing e f with
  | nil => exact .refl rfl
  | cons a w ih => rw [wDAhd, DAhd, wDAhd, wDAhd]
                   apply ih


-------------------------------------------------------------------------------
-- multShape is the form in which we represent derivatives of multiplications.

/-
For `e, f : RE α` and `a, b, c : α` we define `multShape` so that:

multShape e f [a,b,c] =
  wDAhd [a,b,c] (wD [] e)      `· wD [a,b,c] (wDBhd []      f) +
  wDAhd [b,c]   (wD [a] e)     `· wD [b,c]   (wDBhd [a]     f) +
  wDAhd [c]     (wD [a,b] e)   `· wD [c]     (wDBhd [a,b]   f) +
  wDAhd []      (wD [a,b,c] e) `· wD []      (wDBhd [a,b,c] f) +

-/

def multShape [DecidableEq α] (e f : RE α) (w : List α) :=
  toSum <| List.map (λ (p, s) => wDAhd s (wD p e) `· wD s (wDBhd p f))
                    (splits w)

theorem multShape_cons  [DecidableEq α]
                       (e f : RE α) (a : α) (w : List α)
                       : multShape e f (a :: w)
                         ≡
                         wDAhd (a :: w) e `· wD (a :: w) f
                         `+
                         multShape (D a e) (DBhd a f) w := by
  rw [multShape, splits_cons, multShape]
  have ⟨ps, eq⟩ := splits_ne w
  rw [eq]
  simp [toSum]
  apply Equiv.plusCong (.refl rfl)
  simp [wD, wDBhd]
  apply toSum_cons_equiv (.refl rfl)
  exact .refl rfl


theorem multShape_cong  [DecidableEq α]
                       {e e' f f' : RE α}
                       (h : e ≡ e') (h' : f ≡ f') (w : List α)
                       : multShape e f w ≡ multShape e' f' w := by
  match w with
  | [] => simp [multShape, splits, List.map, toSum]
          exact .plusCong (.multCong h h') (.refl rfl)
  | a :: w =>
      calc multShape e f (a :: w)
        _ ≡ wDAhd (a :: w) e `· wD (a :: w) f `+ multShape (D a e) (DBhd a f) w :=
          multShape_cons e f a w
        _ ≡ wDAhd (a :: w) e' `· wD (a :: w) f' `+ multShape (D a e') (DBhd a f') w :=
          .plusCong (.multCong (wDAhd_cong h) (wD_cong h'))
                    (multShape_cong (D_cong h) (DBhd_cong h') w)
        _ ≡ multShape e' f' (a :: w) :=
          .sym (multShape_cons e' f' a w)

theorem multShape_zero [DecidableEq α]
                       (f : RE α) (w : List α)
                       : multShape `0 f w ≡ `0 := by
  match w with
  | [] => simp [multShape, splits, List.map, toSum]
          apply Equiv.trans (.plusCong .multZeroL (.refl rfl))
          exact plus_zero_r
  | a :: w =>
      calc multShape `0 f (a :: w)
        _ ≡ wDAhd (a :: w) `0 `· wD (a :: w) f `+
            multShape (D a `0) (DBhd a f) w := by
          apply multShape_cons
        _ ≡ `0 `· wD (a :: w) f `+ multShape (D a `0) (DBhd a f) w :=
          .plusCong (.multCong (wDAhd_0 w) (.refl rfl))
                    (.refl rfl)
        _ ≡ `0 `+ multShape (D a `0) (DBhd a f) w :=
          .plusCong .multZeroL (.refl rfl)
        _ ≡ multShape `0 (DBhd a f) w :=
          .plusZeroL
        _ ≡ `0 :=
          multShape_zero (DBhd a f) w

theorem multShape_DAhd [DecidableEq α]
                       (e f : RE α) (a : α) (w : List α)
                       : multShape (DAhd a e) f w ≡ wDAhd w (DAhd a e) `· wD w f := by
  match w with
  | [] => exact plus_zero_r

  | b :: w =>
      calc multShape (DAhd a e) f (b :: w)
        _ ≡ wDAhd (b :: w) (DAhd a e) `· wD (b :: w) f `+
            multShape (D b (DAhd a e)) (DBhd b f) w :=
          by apply multShape_cons
        _ ≡ wDAhd (b :: w) (DAhd a e) `· wD (b :: w) f `+
            multShape `0 (DBhd b f) w :=
          .plusCong (.refl rfl)
                    (multShape_cong (D_after_DAhd_is_zero a b e) (.refl rfl) w)
        _ ≡ wDAhd (b :: w) (DAhd a e) `· wD (b :: w) f `+ `0 :=
          .plusCong (.refl rfl)
                    (multShape_zero (DBhd b f) w)
        _ ≡ wDAhd (b :: w) (DAhd a e) `· wD (b :: w) f :=
          plus_zero_r

theorem multShape_bhd [DecidableEq α]
                      (e f : RE α) (w : List α)
                      : multShape (`◁ e) f w ≡ wDAhd w (`◁ e) `· wD w f := by
  match w with
  | [] => exact plus_zero_r

  | b :: w =>
      calc multShape (`◁ e) f (b :: w)
        _ ≡ wDAhd (b :: w) (`◁ e) `· wD (b :: w) f `+
            multShape (D b (`◁ e)) (DBhd b f) w :=
          by apply multShape_cons
        _ ≡ wDAhd (b :: w) (`◁ e) `· wD (b :: w) f `+
            multShape `0 (DBhd b f) w :=
          .plusCong (.refl rfl)
                    (multShape_cong (by rw [D]; exact .refl rfl) (.refl rfl) w)
        _ ≡ wDAhd (b :: w) (`◁ e) `· wD (b :: w) f `+ `0 :=
          .plusCong (.refl rfl)
                    (multShape_zero (DBhd b f) w)
        _ ≡ wDAhd (b :: w) (`◁ e) `· wD (b :: w) f :=
          plus_zero_r


def multShapeFull [DecidableEq α] (e f : RE α) (y z : List α) :=
  toSum <| List.map (λ (p, s) => wDAhd (s ++ z) (wD p e)
                                 `· (wDAhd z (wD s (wDBhd p f))))
                    (splits y)


------------------------------------------------------------------------------
-- mult

theorem wDBhd_mult [DecidableEq α]
                   : ∀ (e f : RE α) (w : List α),
                       wDBhd w (e `· f) ≡ wDBhd w e `· wDBhd w f := by
  intro e f w
  induction w generalizing e f with
  | nil => exact .refl rfl
  | cons a w ih => rw [wDBhd, DBhd, wDBhd, wDBhd]
                   apply ih


theorem wD_mult [DecidableEq α]
                : ∀ (e f : RE α) (w : List α),
                    wD w (e `· f) ≡ multShape e f w := by
  intro e f w
  match w with
  | [] => --simp [multShape, splits, wDAhd, wDBhd, wD, toSum]
          exact .sym plus_zero_r
  | a :: w =>
      calc wD (a :: w) (e `· f)
        _ ≡ wD w (D a (e `· f)) :=
              .refl rfl
        _ ≡ wD w (D a e `· DBhd a f `+ DAhd a e `· D a f) :=
              .refl rfl
        _ ≡ wD w (D a e `· DBhd a f) `+ wD w (DAhd a e `· D a f) :=
              by apply wD_plus
        _ ≡ multShape (D a e) (DBhd a f) w `+ multShape (DAhd a e) (D a f) w :=
              .plusCong (wD_mult (D a e)    (DBhd a f) w)
                        (wD_mult (DAhd a e) (D a f)    w)
        _ ≡ multShape (D a e) (DBhd a f) w `+ wDAhd w (DAhd a e) `· wD w (D a f) :=
              .plusCong (.refl rfl)
                        (multShape_DAhd e (D a f) a w)
        _ ≡ multShape (D a e) (DBhd a f) w `+ wDAhd (a :: w) e `· wD (a :: w) f :=
              .refl rfl
        _ ≡ wDAhd (a :: w) e `· wD (a :: w) f `+ multShape (D a e) (DBhd a f) w :=
              .plusComm
        _ ≡ multShape e f (a :: w) :=
              .sym (multShape_cons e f a w)


theorem wDAhd_mult [DecidableEq α]
                   : ∀ (e f : RE α) (w : List α),
                       wDAhd w (e `· f) ≡ wDAhd w e `· wDAhd w f := by
  intro e f w
  induction w generalizing e f with
  | nil => exact .refl rfl
  | cons a w ih => rw [wDAhd, DAhd, wDAhd, wDAhd]
                   apply ih

theorem wDAhd_mult' [DecidableEq α]
                    : ∀ {e f : RE α} {w : List α},
                       wDAhd w (e `· f) ≡ wDAhd w e `· wDAhd w f := by
  apply wDAhd_mult

---------------------------------------------------------------------------

theorem wDAhd_toSum {α} [DecidableEq α]
                    : ∀ (es : List (RE α)) (w : List α),
                        wDAhd w (toSum es) ≡ toSum (List.map (wDAhd w) es) := by
  intro es w
  match w with
  | [] => simp [wDAhd]
          exact .refl rfl
  | a :: w' =>
      simp [wDAhd]
      apply Equiv.trans (wDAhd_cong (DAhd_toSum es a))
      apply Equiv.trans (wDAhd_toSum (List.map (DAhd a) es) w')
      rw [List.map_map]
      exact .refl rfl

theorem wDAhd_toMult' {α} [DecidableEq α]
                      : ∀ (es : List (RE α)) (e : RE α) (w : List α),
                          wDAhd w (toMult' es e) = toMult' (List.map (wDAhd w) es) (wDAhd w e) := by
  intro es e w
  match w with
  | [] => simp [wDAhd]
  | a :: w =>
      simp [wDAhd]
      rw [DAhd_toMult']
      rw [wDAhd_toMult']
      rw [List.map_map]
      rfl

-------------------------------------------------------------------------------
-- top

theorem wDBhd_top [DecidableEq α]
                  : ∀ (w : List α),
                      wDBhd w ⊤ ≡ ⊤ := by
  intro  w
  induction w
  . exact .refl rfl
  . rw [wDBhd, DBhd]; assumption



theorem wDAhd_bhd_1 [DecidableEq α] : ∀ (w : List α), wDAhd w (`◁ `1) ≡ `◁ `1 := by
  intro w
  induction w
  . exact .refl rfl
  . rw [wDAhd, DAhd, DAhd]
    assumption

theorem wD_top_cons [DecidableEq α]
                    : ∀ (a : α) (w : List α),
                        wD (a :: w) ⊤ ≡ `◁ `1 `· ⊤ := by
  intro a w
  rw [wD, D]

  apply Equiv.trans (wD_mult (`◁ `1) ⊤ w)
  apply Equiv.trans (multShape_bhd `1 ⊤ w)
  apply Equiv.trans (.multCong (wDAhd_bhd_1 w) (.refl rfl))
  match w with
  | [] => exact .refl rfl
  | b :: w' =>
      apply Equiv.trans (.multCong (.refl rfl) (wD_top_cons b w'))
      exact .sym lbhd_unit_mult_idem

theorem wDAhd_top_cons [DecidableEq α]
                       : ∀ (a : α) (w : List α),
                           wDAhd (a :: w) ⊤ ≡ `◁ `1 := by
  intro a w
  rw [wDAhd, DAhd]
  cases w
  . exact .refl rfl
  . apply wDAhd_bhd_1


----------------------------------------------------------------------------

theorem plusSwap {α : Type} {r s t : RE α} : r `+ (s `+ t) ≡ s `+ (r `+ t) :=
  .trans .plusAssoc
    (.trans (.plusCong .plusComm (.refl rfl))
            (.sym .plusAssoc))

theorem regroup {α} : ∀ (b1 b2 m1 m2 a1 a2 : RE α),
                        (b1 `+ b2) `+ (m1 `+ m2) `+ (a1 `+ a2)
                        ≡
                        (b1 `+ m1 `+ a1) `+ (b2 `+ m2 `+ a2) := by
  intro b1 b2 m1 m2 a1 a2
  calc (b1 `+ b2) `+ ((m1 `+ m2) `+ (a1 `+ a2))
      ≡ b1 `+ (b2 `+ ((m1 `+ m2) `+ (a1 `+ a2)))
        := .sym .plusAssoc
    _ ≡ b1 `+ (b2 `+ (m1 `+ (m2 `+ (a1 `+ a2))))
        := .plusCong (.refl rfl) (.plusCong (.refl rfl) (.sym .plusAssoc))
    _ ≡ b1 `+ (m1 `+ (b2 `+ (m2 `+ (a1 `+ a2))))
        := .plusCong (.refl rfl) plusSwap
    _ ≡ b1 `+ (m1 `+ (b2 `+ (a1 `+ (m2 `+ a2))))
        := .plusCong (.refl rfl) (.plusCong (.refl rfl) (.plusCong (.refl rfl) plusSwap))
    _ ≡ b1 `+ (m1 `+ (a1 `+ (b2 `+ (m2 `+ a2))))
        := .plusCong (.refl rfl) (.plusCong (.refl rfl) plusSwap)
    _ ≡ b1 `+ ((m1 `+ a1) `+ (b2 `+ (m2 `+ a2)))
        := .plusCong (.refl rfl) .plusAssoc
    _ ≡ (b1 `+ (m1 `+ a1)) `+ (b2 `+ (m2 `+ a2))
        := .plusAssoc


theorem wxD_plus {α} [DecidableEq α]
                 : ∀ (e f : RE α) (w : List α),
                     wxD w (e `+ f) ≡ wxD w e `+ wxD w f := by
  intro e f w
  match w with
  | [] => rw [wxD, wxD, wxD]
          exact .refl rfl
  | a :: w =>
      calc wxD (a :: w) (e `+ f)
        _ ≡ wxD w (DBhd a (e `+ f) `+ D a (e `+ f) `+ DAhd a (e `+ f))
          := .refl rfl
        _ ≡ wxD w (DBhd a (e `+ f)) `+ wxD w (D a (e `+ f) `+ DAhd a (e `+ f))
          := by apply wxD_plus
        _ ≡ wxD w (DBhd a (e `+ f)) `+ wxD w (D a (e `+ f)) `+ wxD w (DAhd a (e `+ f))
          := .plusCong (.refl rfl) (by apply wxD_plus)
        _ ≡ wxD w (DBhd a e `+ DBhd a f) `+ wxD w (D a e `+ D a f) `+ wxD w (DAhd a e `+ DAhd a f)
          := .refl rfl
        _ ≡ (wxD w (DBhd a e) `+ wxD w (DBhd a f))
            `+ (wxD w (D a e) `+ wxD w (D a f))
            `+ (wxD w (DAhd a e) `+ wxD w (DAhd a f))
          := .plusCong (by apply wxD_plus)
                       (.plusCong (by apply wxD_plus) (by apply wxD_plus))

        _ ≡ (wxD w (DBhd a e) `+ wxD w (D a e) `+ wxD w (DAhd a e)) `+
            (wxD w (DBhd a f) `+ wxD w (D a f) `+ wxD w (DAhd a f))
          := by apply regroup

        _ ≡ (wxD w (DBhd a e) `+ wxD w (D a e `+ DAhd a e)) `+
            (wxD w (DBhd a f) `+ wxD w (D a f `+ DAhd a f))
          := .plusCong (.plusCong (.refl rfl) (by apply Equiv.sym; apply wxD_plus))
                       (.plusCong (.refl rfl) (by apply Equiv.sym; apply wxD_plus))

        _ ≡ wxD w (DBhd a e `+ D a e `+ DAhd a e) `+ wxD w (DBhd a f `+ D a f `+ DAhd a f)
          := .plusCong (by apply Equiv.sym; apply wxD_plus)
                       (by apply Equiv.sym; apply wxD_plus)

        _ ≡ wxD (a :: w) e `+ wxD (a :: w) f := .refl rfl
