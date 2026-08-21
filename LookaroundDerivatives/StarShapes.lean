import LookaroundDerivatives.Triple
import LookaroundDerivatives.Expressions
import LookaroundDerivatives.Lists
import LookaroundDerivatives.DerProperties
import LookaroundDerivatives.Shapes



def wDAhdExprs {α} [DecidableEq α] (e : RE α) (ws : List (List α)) (w : List α) : List (RE α) :=
  List.map (λ (xs, y, zs) => wDAhd (zs.flatten ++ w) (wD y (wDBhd xs.flatten e)))
           (focus ws)


theorem wDAhdExprs_w_ne_ahd {α} [DecidableEq α]
                            (e : RE α) (ws : List (List α))
                            {w : List α} (ne : ¬ w = [])
                            : ∀ x ∈ wDAhdExprs e ws w,
                              ∃ x', x ≡ `▷ x' := by
  intro x x_in
  have ⟨a, w', w_eq⟩ := List.ne_nil_iff_exists_cons.mp ne
  rw [w_eq] at x_in
  simp [wDAhdExprs] at x_in
  obtain ⟨l, c, r, mem, eq⟩ := x_in
  rw [wDAhd_append] at eq
  rw [←eq]

  exists wD w' (extractLAhd a (wDAhd r.flatten (wD c (wDBhd l.flatten e))))
  exact wDAhd_cons a w' (wDAhd r.flatten (wD c (wDBhd l.flatten e)))


theorem wDAhdExprs_singleton {α} [DecidableEq α]
                             (e : RE α) (w w' : List α)
                             : wDAhdExprs e [w] w'
                               =
                               [wDAhd w' (wD w e)] := by
  rfl



theorem wDAhdExprs_append {α} [DecidableEq α]
                          (e : RE α) (ws ws' : List (List α)) (w : List α)
                          : wDAhdExprs e (ws ++ ws') w
                            =
                            wDAhdExprs e ws (ws'.flatten ++ w) ++
                            wDAhdExprs (wDBhd ws.flatten e) ws' w := by
  rw [wDAhdExprs, focus_append, List.map_append]
  apply List.append_eq_append_iff.mpr
  left
  exists []
  apply And.intro
  . rw [List.append_nil, wDAhdExprs]
    simp
  . rw [List.nil_append, wDAhdExprs]
    simp [wDBhd_append]








def starElem' {α} [DecidableEq α] (e : RE α) (ws : List (List α)) : RE α :=
  --let mults := List.map (λ (xs, y, zs) => wDAhd zs.flatten (wD y (wDBhd xs.flatten e)))
  --                      (focus ws)

  toMult' (wDAhdExprs e ws []) (wDBhd ws.flatten e)*


theorem starElem'Example1 (e : RE Char)
          : starElem' e [['a', 'b', 'c']]
            =
            wD ['a', 'b', 'c'] e `· (wDBhd ['a', 'b', 'c'] e)* :=
  rfl


theorem starElem'Example2 (e : RE Char)
          : starElem' e [['a', 'b'], ['c']]
            =
            wDAhd ['c'] (wD ['a', 'b'] e) `·
              wD ['c'] (wDBhd ['a', 'b'] e) `·
                (wDBhd ['a', 'b', 'c'] e)* :=
  rfl


theorem starElem'Example3 (e : RE Char)
          : starElem' e [['a'], ['b'], ['c']]
            =
            (wDAhd ['b', 'c'] (wD ['a'] e)) `·
              (wDAhd ['c'] (wD ['b'] (wDBhd ['a'] e))) `·
                wD ['c'] (wDBhd ['a', 'b'] e) `·
                  (wDBhd ['a', 'b', 'c'] e)* :=
  rfl


theorem starElem'_cons {α} [DecidableEq α]
                       : ∀ (e : RE α) (w : List α) (ws : List (List α)),
                           starElem' e (w :: ws)
                           =
                           wDAhd ws.flatten (wD w e) `· starElem' (wDBhd w e) ws := by
  intro e w ws
  simp [starElem', wDAhdExprs, focus, toMult', wDBhd, Function.comp_def, wDBhd_append]

theorem starElem'_snoc {α} [DecidableEq α]
                       : ∀ (e : RE α) (ws : List (List α)) (w : List α),
                           starElem' e (ws ++ [w])
                           =
                           toMult' (wDAhdExprs e ws w)
                                   (wD w (wDBhd ws.flatten e)
                                   `· (wDBhd (ws.flatten ++ w) e)*) := by
  intro e ws w
  rw [starElem', wDAhdExprs_append]
  rw [List.append_nil, List.flatten_singleton]
  rw [wDAhdExprs_singleton, wDAhd]
  rw [List.flatten_append, List.flatten_singleton]
  rw [toMult'_snoc]



theorem starElem'_exists {α} [DecidableEq α]
                         : ∀ (e : RE α) (ws : List (List α)),
                           ∃ (ts : List (List α × List α × List α)),
                             starElem' e ws
                             =
                             toMult' (List.map (λ (x, y, z) => wDAhd z (wD y (wDBhd x e))) ts)
                                     (wDBhd ws.flatten e)* := by
  intro e ws
  exists List.map (λ (xs, y, zs) => (xs.flatten, y, zs.flatten)) (focus ws)
  simp [starElem', wDAhdExprs, Function.comp_def]

---------------------------------------------------------------------

def starElemSnoc {α} [DecidableEq α] (e : RE α) (ws : List (List α)) (w : List α) : RE α :=
  toMult' (wDAhdExprs e ws w)
          (wD w (wDBhd ws.flatten e) `· (wDBhd (ws.flatten ++ w) e)*)


theorem starElemSnocExample1 (e : RE Char)
          : starElemSnoc e [] ['a', 'b', 'c']
            =
            wD ['a', 'b', 'c'] e `· (wDBhd ['a', 'b', 'c'] e)* :=
  rfl


theorem starElemSnocExample2 (e : RE Char)
          : starElemSnoc e [['a', 'b']] ['c']
            =
            wDAhd ['c'] (wD ['a', 'b'] e) `·
              wD ['c'] (wDBhd ['a', 'b'] e) `·
                (wDBhd ['a', 'b', 'c'] e)* :=
  rfl


theorem starElemSnocExample3 (e : RE Char)
          : starElemSnoc e [['a'], ['b']] ['c']
            =
            (wDAhd ['b', 'c'] (wD ['a'] e)) `·
              (wDAhd ['c'] (wD ['b'] (wDBhd ['a'] e))) `·
                wD ['c'] (wDBhd ['a', 'b'] e) `·
                  (wDBhd ['a', 'b', 'c'] e)* :=
  rfl

---------------------------------------------------------------------

-- Derivative of star is a sum of expressions and `starElem` is the shape of
-- summands in that sum.
def starElem {α} [DecidableEq α] (e : RE α) (ws : List (List α)) : RE α :=
  match ws with
  | []      => e*
  | w :: ws => List.foldl (flip wDAhd) (wD w e) ws `· starElem (wDBhd w e) ws

---------------------------------------------------------------------
-- examples

theorem starElemExample1 (e : RE Char)
          : starElem e [['a', 'b', 'c']]
            =
            wD ['a', 'b', 'c'] e `· (wDBhd ['a', 'b', 'c'] e)* :=
  rfl


theorem starElemExample2 (e : RE Char)
          : starElem e [['a', 'b'], ['c']]
            =
            wDAhd ['c'] (wD ['a', 'b'] e) `·
              wD ['c'] (wDBhd ['a', 'b'] e) `·
                (wDBhd ['a', 'b', 'c'] e)* :=
  rfl


theorem starElemExample3 (e : RE Char)
          : starElem e [['a'], ['b'], ['c']]
            =
            (wDAhd ['b', 'c'] (wD ['a'] e)) `·
              (wDAhd ['c'] (wD ['b'] (wDBhd ['a'] e))) `·
                wD ['c'] (wDBhd ['a', 'b'] e) `·
                  (wDBhd ['a', 'b', 'c'] e)* :=
  rfl

----------------------------------------------------------------------

theorem wDAhd_foldl_flatten {α} [DecidableEq α]
                            : ∀ (e : RE α) (ws : List (List α)),
                                List.foldl (flip wDAhd) e ws = wDAhd ws.flatten e := by
  intro e ws
  match ws with
  | [] => simp [wDAhd]
  | w :: ws => simp [flip, wDAhd_append]
               rw [wDAhd_foldl_flatten]

theorem starElem_defs {α} [DecidableEq α]
                      : ∀ (e : RE α) (ws : List (List α)),
                          starElem e ws = starElem' e ws := by
  intro e ws
  match ws with
  | [] => simp [starElem, starElem', wDAhdExprs, focus, wDBhd, toMult']
  | w :: ws =>
      simp [starElem, starElem'_cons, starElem_defs]
      rw [wDAhd_foldl_flatten]


----------------------------------------------------------------------

theorem D_starElem {α} [DecidableEq α]
                    (e : RE α) (a : α) {ws : List (List α)}
                    (ne : ¬ ws = [])
                    (h : ∀ w ∈ ws, ¬ w = [])
                    : D a (starElem e ws)
                      ≡
                      starElem e (addToLast a ws) `+
                      starElem e (ws ++ [[a]]) := by
  match ws with
  | [] => contradiction
  | w :: ws =>
      match ws with
      | [] => calc D a (starElem e [w])
          _ ≡ D a (wD w e) `· DBhd a (wDBhd w e)*
              `+
              DAhd a (wD w e) `· D a (wDBhd w e) `· (DBhd a (wDBhd w e))* := .refl rfl

          _ ≡ starElem e [w ++ [a]] `+ starElem e (w :: [[a]]) :=
              by simp only [starElem, List.foldl_cons, List.foldl_nil, flip]
                 simp only [wDBhd, DBhd, wDAhd, wD, wD_append, wDBhd_append]
                 exact .refl rfl

          _ ≡ starElem e (addToLast a [w]) `+ starElem e ([w] ++ [[a]]) := .refl rfl

      | w' :: ws => calc
              D a (starElem e (w :: w' :: ws))
          _ ≡ D a (List.foldl (flip wDAhd) (wD w e) (w' :: ws) `·
                     starElem (wDBhd w e) (w' :: ws)) := .refl rfl
          _ ≡ D a (List.foldl (flip wDAhd) (wD w e) (w' :: ws)) `·
                DBhd a (starElem (wDBhd w e) (w' :: ws))
              `+
              DAhd a (List.foldl (flip wDAhd) (wD w e) (w' :: ws)) `·
                D a (starElem (wDBhd w e) (w' :: ws)) := .refl rfl
          _ ≡ `0 `· DBhd a (starElem (wDBhd w e) (w' :: ws))
              `+
              DAhd a (List.foldl (flip wDAhd) (wD w e) (w' :: ws)) `·
                D a (starElem (wDBhd w e) (w' :: ws)) :=
              Equiv.plusCong (.multCong (D_after_wDAhd_is_zero_list a (wD w e) (by simp)
                                                                    (by intro y y_in
                                                                        simp [h, y_in]))
                                        (.refl rfl))
                             (.refl rfl)
          _ ≡ `0 `+
              DAhd a (List.foldl (flip wDAhd) (wD w e) (w' :: ws)) `·
                D a (starElem (wDBhd w e) (w' :: ws)) :=
              Equiv.plusCong Equiv.multZeroL (.refl rfl)

          _ ≡ DAhd a (List.foldl (flip wDAhd) (wD w e) (w' :: ws)) `·
                D a (starElem (wDBhd w e) (w' :: ws)) :=
              .plusZeroL

          _ ≡ DAhd a (List.foldl (flip wDAhd) (wD w e) (w' :: ws)) `·
                (starElem (wDBhd w e) (addToLast a (w' :: ws)) `+
                   starElem (wDBhd w e) (w' :: ws ++ [[a]])) :=
              .multCong (.refl rfl)
                        (D_starElem (wDBhd w e) a (by simp) -- IH
                                    (by intro w w_in
                                        simp [h, w_in]))

          _ ≡ DAhd a (List.foldl (flip wDAhd) (wD w e) (w' :: ws)) `·
                (starElem (wDBhd w e) (addToLast a (w' :: ws)))
              `+
              DAhd a (List.foldl (flip wDAhd) (wD w e) (w' :: ws)) `·
                (starElem (wDBhd w e) (w' :: ws ++ [[a]])) := .distrL -- distributivity

          _ ≡ List.foldl (flip wDAhd) (wD w e) (addToLast a (w' :: ws))
                `· starElem (wDBhd w e) (addToLast a (w' :: ws))
              `+
              List.foldl (flip wDAhd) (wD w e) (w' :: ws ++ [[a]])
                `· starElem (wDBhd w e) (w' :: ws ++ [[a]])
              := .plusCong (by simp [flip]
                               rw [foldl_addToLast (flip wDAhd) wDAhd_append]
                               simp [flip, wDAhd]
                               exact .refl rfl)
                           (by simp [flip, wDAhd]
                               exact .refl rfl)

          _ ≡ starElem e (w :: addToLast a (w' :: ws)) `+
                starElem e (w :: w' :: ws ++ [[a]]) := .refl rfl

          _ ≡ starElem e (addToLast a (w :: w' :: ws)) `+
                starElem e (w :: w' :: ws ++ [[a]]) := .refl rfl


---------------------------------------------------------------------------------------

-- The form of the derivatives of star
def starShape {α} [DecidableEq α] (e : RE α) (a : α) (w : List α) : RE α :=
  toSum (List.map (starElem e) (neSplits a w))


----------------------------------------------------------------------
-- examples

theorem example1 (e : RE Char) (a : Char)
                 : starShape e a []
                   =
                   D a e `· (DBhd a e)* `+ `0 := by
  --simp [starShape, neSplits, wD, wDBhd, starElem, toSum]
  rfl

theorem example2 (e : RE Char) (b c : Char)
                 : starShape e b [c]
                   =
                   wDAhd [] (wD [b, c] (wDBhd [] e))
                      `· (wDBhd [b, c] e)*
                   `+ wDAhd [c] (wD [b] (wDBhd [] e))
                      `· wDAhd [] (wD [c] (wDBhd [b] e))
                      `· (wDBhd [b, c] e)*
                   `+ `0 := by
  --simp [starShape, starElem, neSplits, wD, wDBhd, wDAhd, flip, toSum, addToHead]
  rfl


theorem example3 (e : RE Char) (a b c : Char)
                 : starShape e a [b, c]
                   =
                   wDAhd [] (wD [a, b, c] (wDBhd [] e))
                      `· (wDBhd [a, b, c] e)*
                   `+ wDAhd [b,c] (wD [a] (wDBhd [] e))
                      `· wDAhd [] (wD [b, c] (wDBhd [a] e))
                      `· (wDBhd [a, b, c] e)*
                   `+ wDAhd [c] (wD [a, b] (wDBhd [] e))
                      `· wDAhd [] (wD [c] (wDBhd [a, b] e))
                      `· (wDBhd [a, b, c] e)*
                   `+ wDAhd [b,c] (wD [a] (wDBhd [] e))
                      `· wDAhd [c] (wD [b] (wDBhd [a] e))
                      `· wDAhd [] (wD [c] (wDBhd [a, b] e))
                      `· (wDBhd [a, b, c] e)*
                   `+ `0 := by
  --simp [starShape, neSplits, addToHead]
  --simp [starElem, flip]
  --simp only [toSum]
  rfl

------------------------------------------------------------------------------


theorem starShape_snoc {α} [DecidableEq α]
                       : ∀ (e : RE α) (a b : α) (u : List α),
                           starShape e a (u ++ [b]) ≡ D b (starShape e a u) := by
  intro e a b u
  calc starShape e a (u ++ [b])
    _ ≡ toSum (List.map (starElem e) (neSplits a (u ++ [b]))) :=
        by exact .refl rfl

    _ ≡ toSum (List.map (starElem e) (List.map (addToLast b) (neSplits a u)
                                       ++ List.map (λ ws => ws ++ [[b]]) (neSplits a u))) :=
        by rw [neSplits_snoc]
           exact .refl rfl

    _ ≡ toSum (List.map (starElem e ∘ addToLast b) (neSplits a u)
               ++ List.map (starElem e ∘ λ ws => ws ++ [[b]]) (neSplits a u)) :=
        by simp [List.map_append]
           exact .refl rfl

    _ ≡ toSum (List.map (starElem e ∘ addToLast b) (neSplits a u))
          `+ toSum (List.map (starElem e ∘ λ ws => ws ++ [[b]]) (neSplits a u)) :=
        by exact toSum_append

    _ ≡ toSum (List.map (λ ws => starElem e (addToLast b ws) `+ starElem e (ws ++ [[b]]))
                        (neSplits a u)) :=
        by exact toSum_map_append

    _ ≡ toSum (List.map (D b ∘ starElem e) (neSplits a u)) :=
        by apply toSum_map
           intro ws ws_in
           apply Equiv.sym
           have ⟨ne, p⟩ := neSplits_elems_nonEmpty a u ws ws_in
           exact D_starElem e b ne p

    _ ≡ toSum (List.map (D b) (List.map (starElem e) (neSplits a u))) :=
        by exact .refl (congrArg toSum (Eq.symm List.map_map))

    _ ≡ D b (toSum (List.map (starElem e) (neSplits a u))) :=
        by apply Equiv.sym
           apply D_toSum

    _ ≡ D b (starShape e a u) :=
        by exact .refl rfl


theorem starShape_append {α} [DecidableEq α]
                         : ∀ (e : RE α) (a : α) (u v : List α),
                           starShape e a (u ++ v) ≡ wD v (starShape e a u) := by
  intro e a u v
  match v with
  | [] =>
      calc starShape e a (u ++ [])
      _ ≡ starShape e a u         := .refl (by rw [List.append_nil])
      _ ≡ wD [] (starShape e a u) := .refl (by rw [wD])

  | b :: v =>
      calc starShape e a (u ++ b :: v)
        _ ≡ starShape e a (u ++ [b] ++ v)   := .refl (by rw [List.append_cons])
        _ ≡ wD v (starShape e a (u ++ [b])) := starShape_append e a (u ++ [b]) v
        _ ≡ wD v (D b (starShape e a u))    := wD_cong (starShape_snoc e a b u)
        _ ≡ wD (b :: v) (starShape e a u)   := .refl rfl


theorem wD_star_starShape {α} [DecidableEq α]
                          : ∀ (e : RE α) (a : α) (w : List α),
                            wD (a :: w) e* ≡ starShape e a w := by
  intro e a w
  calc wD (a :: w) e*
    _ ≡ wD w (D a e*)           := .refl rfl
    _ ≡ wD w (D a e* `+ `0)     := wD_cong (.sym plus_zero_r)
    _ ≡ wD w (starShape e a []) := .refl rfl
    _ ≡ starShape e a ([] ++ w) := .sym (starShape_append e a [] w)
    _ ≡ starShape e a w         := .refl rfl


-------------------------------------------------------------------------------
-- star

theorem wDBhd_star [DecidableEq α]
                   : ∀ (e : RE α) (w : List α),
                       wDBhd w e* ≡ (wDBhd w e)* := by
  intro e w
  match w with
  | [] => exact .refl rfl
  | a :: w =>
      rw [wDBhd, DBhd, wDBhd]
      apply (wDBhd_star (DBhd a e) w)



theorem wD_star_eps [DecidableEq α]
                    : ∀ (e : RE α),
                    wD [] e* ≡ e* := by
  intro e
  exact .refl rfl

theorem wD_star_cons [DecidableEq α]
                     : ∀ (e : RE α) (a : α) (w : List α),
                         wD (a :: w) e* ≡ starShape e a w :=
  wD_star_starShape



theorem wDAhd_star_eps [DecidableEq α]
                       : ∀ (e : RE α),
                           wDAhd [] e* ≡ e* := by
  intro e
  exact .refl rfl

theorem wDAhd_star_cons [DecidableEq α]
                        : ∀ (e : RE α) (a : α) (w : List α),
                            wDAhd (a :: w) e* ≡ `◁ `1 := by
  intro e a w
  rw [wDAhd, DAhd]
  exact wDAhd_bhd_1 w


--------------------------------------------------------------------------------
