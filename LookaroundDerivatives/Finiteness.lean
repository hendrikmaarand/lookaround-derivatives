import LookaroundDerivatives.Triple
import LookaroundDerivatives.Expressions
import LookaroundDerivatives.Lists
import LookaroundDerivatives.DerProperties
import LookaroundDerivatives.Shapes
import LookaroundDerivatives.StarShapes
import LookaroundDerivatives.ExistDerSum



-- If `es` are the successors of e, then compute
-- the main summands for `e*` (nonempty match part)

def mainSummands {α} (es : List (RE α)) : List (RE α) :=
  -- for every subset ss of succs e
  -- (this subset represents the part where we have applied wDAhd)
  (subs es).flatMap λ ss =>
    -- and every successor e' of e
    -- (the last segment, only wD applied (and wDBhd))
    es.flatMap λ e' =>
      -- we take the following (shapes) of expressions:
      -- (ss part) `· e' `· `◁ `1   <-- the case where z ≠ [] as wDAhd (c :: z) of star is `◁ `1
      toMult' ss (e' `· `◁ `1) ::
      -- (ss part) `· e' `· e_b*
      es.map (λ e_b => toMult' ss (e' `· e_b*))



-- mainSummands of n elements = 2^n * n * (n + 1)

--#eval mainSummands [(`0 : RE Char), `1, `0] |> List.length


-- Overapproximation of iterated derivatives of e.
def succs (e : RE α) : List (RE α) :=
  match e with
  | .symbol b => [`0, `◁ `1, `$ b]

  | .zero => [`0]

  | .plus e f => List.productWith (· `+ ·)
                                  (succs e)
                                  (succs f)

  | .one => [`0, `1, `◁ `1]

  | .mult e f => List.map toSum
                          (neSubs <| List.productWith (· `· ·) (succs e) (succs f))

  | .etop => [`◁ `1, `◁ `1 `· ⊤, ⊤]

  | .inter e f => List.productWith (· & ·)
                                   (succs e)
                                   (succs f)

  | .sub e f => List.productWith (· `- ·)
                                 (succs e)
                                 (succs f)

  | .star e =>
      let e_succs := succs e
      let sumnds  := mainSummands e_succs

      [`◁ `1] -- wDAhd; wDBhd -> wDAhd
      ++
      List.map (λ eb => eb*) e_succs -- wDBhd
      ++
      List.map toSum (neSubs sumnds)

  | .lookbehind e => ((succs e).map (λ e' => `◁ e')) -- wDBhd
                     ++
                     [`0] -- wD
                     ++
                     succs e -- wDAhd

  | .lookahead e => [`0] -- wD
                    ++
                    (succs e).flatMap λ e' => [`▷ e'] -- wDBhd, wDAhd

#eval neSubs [1,1,1,1] |> List.length


-- #eval succs (`$ 'a')
-- #eval succs (`$ 'a' `+ `1)
-- #eval succs (`$ 'a' `+ `$ 'b')
-- #eval succs (`$ 'a' `· `$ 'b')

-- #eval succs (`$ 'a' `· `$ 'b') |> List.length -- 511


/-

If e has n successors, then e* has 1 + n + 2^(2^n * n * (n + 1)) - 1 successors


Example: `0 *
=================================

e_succs = 1
sumnds  = 4
neSubs smnds = 2^4 - 1

succs (`0 *) = 1 + 1 + (2^4 - 1) = 17


Example: `1 *
=================================

e_succs = 3
sumnds  = 96
neSubs smnds = 2^96 - 1

succs (`1 *) = 1 + 3 + (2^96 - 1)
             ~ 7.9 * 10^28

-/

-- #eval succs (`0 * : RE Char) |> List.length



theorem succs_self (e : RE α) : e ≡∈ succs e := by
  match e with
  | .symbol a =>
      exists `$ a
      simp [succs]
      exact .refl rfl

  | .zero =>
      exists `0
      simp [succs]
      exact .refl rfl

  | .plus e f =>
      have ⟨e', e_eq, e'_in⟩ := succs_self e
      have ⟨f', f_eq, f'_in⟩ := succs_self f
      exists e' `+ f'
      simp [succs, productWith_mem]
      apply And.intro (.plusCong e_eq f_eq)
      exists e', f'

  | .one =>
      exists `1
      simp [succs]
      exact .refl rfl

  | .mult e f =>
      have ⟨e', e_eq, e'_in⟩ := succs_self e
      have ⟨f', f_eq, f'_in⟩ := succs_self f
      exists e' `· f' `+ `0
      apply And.intro (.trans (.multCong e_eq f_eq) (.sym plus_zero_r))
      simp [succs]
      exists [e' `· f']
      simp [singleton_neSubs, productWith_mem, toSum]
      exists e', f'

  | .etop =>
      exists ⊤
      simp [succs]
      exact .refl rfl

  | .inter e f =>
      have ⟨e', e_eq, e'_in⟩ := succs_self e
      have ⟨f', f_eq, f'_in⟩ := succs_self f
      exists e' & f'
      simp [succs, productWith_mem]
      apply And.intro (.interCong e_eq f_eq)
      exists e', f'

  | .sub e f =>
      have ⟨e', e_eq, e'_in⟩ := succs_self e
      have ⟨f', f_eq, f'_in⟩ := succs_self f
      exists e' `- f'
      simp [succs, productWith_mem]
      apply And.intro (.subCong e_eq f_eq)
      exists e', f'

  | .star e =>
      have ⟨e', e_eq, e'_in⟩ := succs_self e
      exists (e'*)
      apply And.intro (.starCong e_eq)
      simp [succs, e'_in]

  | .lookbehind e =>
      have ⟨e', e_eq, e'_in⟩ := succs_self e
      exists `◁ e'
      apply And.intro (.lbhdCong e_eq)
      simp [succs, e'_in]

  | .lookahead e =>
      have ⟨e', e_eq, e'_in⟩ := succs_self e
      exists `▷ e'
      apply And.intro (.lahdCong e_eq)
      simp [succs, e'_in]


theorem starElem_summand {α} [DecidableEq α]
                         (e : RE α)
                         (x z : List α)
                         {ws : List (List α)}
                         (ws_ne : ¬ ws = [])
                         (ws_el_ne : ∀ w ∈ ws, ¬ w = [])
                         (hyp : ∀ (x y z : List α), wDAhd z (wD y (wDBhd x e)) ≡∈ succs e)
                         : wDAhd z (starElem (wDBhd x e) ws) ≡∈ mainSummands (succs e) := by
  match ws with
  | [] => contradiction
  | w :: ws =>

      have q := List.eq_nil_or_concat (w :: ws)
      simp at q
      have ⟨ws', w', ws_eq⟩ := q

      have w'_ne : ¬ w' = [] := by
        rw [ws_eq] at ws_el_ne
        simp [ws_el_ne]

      rw [starElem_defs]
      rw [ws_eq]
      rw [starElem'_snoc]
      rw [wDAhd_toMult']

      have sub : List.map (wDAhd z) (wDAhdExprs (wDBhd x e) ws' w') ≡⊆ succs e := by
        intro e' e'_in
        simp [wDAhdExprs] at e'_in
        obtain ⟨l, c, r, mem, eq⟩ := e'_in
        rw [←eq, ←wDBhd_append, ←wDAhd_append]

        have ⟨e_i, e_i_eq, e_i_in⟩ := hyp (x ++ l.flatten) c (r.flatten ++ w' ++ z)
        exists e_i

      have ⟨e', e'_eq, e'_in⟩ := hyp (x ++ ws'.flatten) w' z

      -- sps' is a subset (no longer up to)
      have ⟨sps', ls', sub', eq'⟩ := subsetUpTo_reprs' sub

      -- sps'' is a sublist of product of succs e and succs f
      have ⟨sps'', ne', sub'', eq''⟩ := exists_sublist_same sub'

      have sps_ahd := wDAhdExprs_w_ne_ahd (wDBhd x e) ws' w'_ne

      have sps''_eq : ∀ (r : RE α), (r ≡∈ List.map (wDAhd z) (wDAhdExprs (wDBhd x e) ws' w'))
                                    ↔
                                    r ≡∈ sps'' := by
        intro r
        constructor
        . intro r_in
          rw [eq'] at r_in
          obtain ⟨r', r_eq, r'_in⟩ := r_in
          rw [eq''] at r'_in
          exact ⟨r', r_eq, r'_in⟩
        . intro ⟨r', r_eq, r'_in⟩
          rw [←eq''] at r'_in
          apply (eq' r).mpr
          exact ⟨r', r_eq, r'_in⟩

      match z with
      | [] =>
          have ⟨e_b, e_b_eq, e_b_in⟩ := hyp (x ++ ws'.flatten ++ w') [] []

          simp [wDAhd, wDBhd_append]
          simp [wD, wDAhd, wDBhd_append] at e_b_eq e'_eq sps''_eq

          exists toMult' sps'' (e' `· e_b*)

          apply And.intro
          . calc toMult' (wDAhdExprs (wDBhd x e) ws' w')
                         (wD w' (wDBhd ws'.flatten (wDBhd x e))
                         `· (wDBhd w' (wDBhd ws'.flatten (wDBhd x e)))*)

              _ ≡ toMult' (wDAhdExprs (wDBhd x e) ws' w') (e' `· e_b*)
                := toMult'_base_eq (.multCong e'_eq
                                              (.starCong e_b_eq))

              _ ≡ toMult' sps'' (e' `· e_b*)
                := toMult'_mem_eq sps_ahd
                                  sps''_eq
                                  (.refl rfl)

          . simp [mainSummands]
            exists sps''
            apply And.intro
            . rw [subs_eq_neSubs]
              cases sps''
              . simp
              . simp [neSubs_complete (by simp) sub'']

            . exists e'
              simp [e'_in]
              right
              exists e_b

      | c :: z =>
          exists toMult' sps'' (e' `· `◁ `1)

          apply And.intro
          . apply toMult'_mem_eq
            . intro x x_in
              simp at x_in
              obtain ⟨r, r_in, x_eq⟩ := x_in
              rw [←x_eq]
              exists wD z (extractLAhd c r)
              exact wDAhd_cons c z r

            . exact sps''_eq

            . calc wDAhd (c :: z) (wD w' (wDBhd ws'.flatten (wDBhd x e))
                                  `· (wDBhd (ws'.flatten ++ w') (wDBhd x e))*)

                _ ≡ wDAhd (c :: z) (wD w' (wDBhd ws'.flatten (wDBhd x e)))
                    `· wDAhd (c :: z) (wDBhd (ws'.flatten ++ w') (wDBhd x e))*
                  := wDAhd_mult'

                _ ≡ wDAhd (c :: z) (wD w' (wDBhd (x ++ ws'.flatten) e))
                     `· wDAhd (c :: z) (wDBhd (ws'.flatten ++ w') (wDBhd x e))*
                  := .refl (by simp [wDBhd_append])

                _ ≡ e' `· `◁`1
                  := .multCong e'_eq (by simp [wDAhd_star_cons])

          . simp [mainSummands]
            exists sps''
            apply And.intro
            . rw [subs_eq_neSubs]
              cases sps''
              . simp
              . simp [neSubs_complete (by simp) sub'']

            . exists e'
              simp [e'_in]



theorem wDAhd_wD_wDBhd_succs {α} [DecidableEq α]
                             (e : RE α)
                             (x y z : List α)
                             : wDAhd z (wD y (wDBhd x e)) ≡∈ succs e := by
  match e with
  | .symbol a =>
      match y with
      | [] => match z with
              | [] => rw [wD, wDAhd, succs]
                      exists `$ a
                      simp [wDBhd_a]
              | c :: z => rw [wD, succs]
                          exists `0
                          simp
                          exact Equiv.trans (wDAhd_cong (wDBhd_a a x))
                                            (wDAhd_a_cons a c z)
      | b :: y =>
          apply Or.elim (wD_a_cons a b y)
          . intro ⟨y_eq, eq, p⟩
            subst y_eq eq
            exists `◁ `1
            simp [succs]
            calc wDAhd z (wD [b] (wDBhd x `$b))
            _ ≡ wDAhd z (wD [b] `$b) := wDAhd_cong (wD_cong (wDBhd_a b x))
            _ ≡ wDAhd z (`◁ `1)      := wDAhd_cong p
            _ ≡ `◁ `1                := wDAhd_bhd_1 z

          . intro ⟨p, eq⟩
            exists `0
            simp [succs]
            calc wDAhd z (wD (b :: y) (wDBhd x `$a))
            _ ≡ wDAhd z (wD (b :: y) `$a) := wDAhd_cong (wD_cong (wDBhd_a a x))
            _ ≡ wDAhd z `0                := wDAhd_cong eq
            _ ≡ `0                        := wDAhd_0 z

  | .zero =>
      rw [elemUpTo, succs]
      exists `0
      simp
      calc wDAhd z (wD y (wDBhd x `0))
        _ ≡ wDAhd z (wD y `0) := wDAhd_cong (wD_cong (wDBhd_0 x))
        _ ≡ wDAhd z `0        := wDAhd_cong (wD_0 y)
        _ ≡ `0                := wDAhd_0 z

  | .plus e f =>
      rw [elemUpTo, succs]
      have ⟨e', e'_eq, e'_in⟩ := wDAhd_wD_wDBhd_succs e x y z
      have ⟨f', f'_eq, f'_in⟩ := wDAhd_wD_wDBhd_succs f x y z
      exists e' `+ f'

      apply And.intro
      . calc wDAhd z (wD y (wDBhd x (e `+ f)))
        _ ≡ wDAhd z (wD y (wDBhd x e `+ wDBhd x f)) :=
          wDAhd_cong (wD_cong (wDBhd_plus e f x))
        _ ≡ wDAhd z (wD y (wDBhd x e) `+ wD y (wDBhd x f)) :=
          wDAhd_cong (wD_plus (wDBhd x e) (wDBhd x f) y)
        _ ≡ wDAhd z (wD y (wDBhd x e)) `+ wDAhd z (wD y (wDBhd x f)) :=
          wDAhd_plus (wD y (wDBhd x e)) (wD y (wDBhd x f)) z
        _ ≡ e' `+ f' :=
          .plusCong e'_eq f'_eq

      . rw [productWith_mem]
        exists e', f'

  | .one =>
      rw [elemUpTo, succs]
      match y with
      | [] =>
        match z with
        | [] => exists `1
                rw [wDAhd, wD]
                simp [wDBhd_1]

        | c :: z =>
            exists `◁ `1
            simp [wD]
            exact .trans (wDAhd_cong (wDBhd_1 x))
                         (wDAhd_1_cons c z)

      | b :: y =>
          exists `0
          simp
          calc wDAhd z (wD (b :: y) (wDBhd x `1))
            _ ≡ wDAhd z (wD (b :: y) `1) := wDAhd_cong (wD_cong (wDBhd_1 x))
            _ ≡ wDAhd z `0               := wDAhd_cong (wD_1_cons b y)
            _ ≡ `0                       := wDAhd_0 z

  | .mult e f =>
      rw [elemUpTo]
      rw [succs]

      -- derivatives for all splits of y
      let sps := List.map (λ (p, s) => (wDAhd (s ++ z) (wD p (wDBhd x e)) `·
                                        wDAhd z (wD s (wDBhd (x ++ p) f))))
                          (splits y)

      have sps_ne : ¬ sps = [] := by simp [sps]
                                     have ⟨pss, eq'⟩ := splits_ne y
                                     simp [eq']

      -- sps is a subset of product of succs e and succs f (up to equiv)
      have sub : sps ≡⊆ List.productWith (· `· ·) (succs e) (succs f) := by
        simp [sps]
        intro q q_mem
        simp at q_mem
        have ⟨p, s, ps_in, eq⟩ := q_mem
        rw [elemUpTo]
        simp [productWith_mem]

        have ⟨e', e'_eq, e'_in⟩ := wDAhd_wD_wDBhd_succs e x p (s ++ z)
        have ⟨f', f'_eq, f'_in⟩ := wDAhd_wD_wDBhd_succs f (x ++ p) s z

        exists e' `· f'
        constructor
        . rw [←eq]
          exact .multCong e'_eq f'_eq
        . exists e', f'

      -- sps' is a subset (no longer up to)
      have ⟨sps', ls', sub', eq'⟩ := subsetUpTo_reprs sub

      -- sps'' is a sublist of product of succs e and succs f
      have ⟨sps'', ne', sub'', eq''⟩ := exists_sublist_same sub'

      exists toSum sps''

      apply And.intro
      . calc wDAhd z (wD y (wDBhd x (e `· f)))
          _ ≡ wDAhd z (wD y (wDBhd x e `· wDBhd x f))
            := wDAhd_cong (wD_cong (wDBhd_mult e f x))
          _ ≡ wDAhd z (multShape (wDBhd x e) (wDBhd x f) y)
            := wDAhd_cong (wD_mult (wDBhd x e) (wDBhd x f) y)

          _ ≡ wDAhd z (toSum <| List.map (λ (p, s) => wDAhd s (wD p (wDBhd x e))
                                                      `· wD s (wDBhd p (wDBhd x f)))
                                         (splits y))
            := .refl rfl

          _ ≡ (toSum <| List.map (wDAhd z)
                                 (List.map (λ (p, s) => wDAhd s (wD p (wDBhd x e))
                                                        `· wD s (wDBhd p (wDBhd x f)))
                                              (splits y)))
            := by apply wDAhd_toSum

          _ ≡ (toSum <| List.map (λ (p, s) => wDAhd z (wDAhd s (wD p (wDBhd x e))
                                                       `· wD s (wDBhd p (wDBhd x f))))
                                 (splits y))
            := by simp [List.map_map]
                  exact .refl rfl

          _ ≡ toSum sps
            := by simp [sps, wDAhd_append, wDBhd_append]
                  apply toSum_map
                  intro (p, s) ps_in
                  apply wDAhd_mult

          _ ≡ toSum sps'
            := eq'
          _ ≡ toSum sps''
            := toSum_mem_eq eq''

      . simp
        exists sps''
        simp
        apply neSubs_complete
        . rw [List.eq_nil_iff_length_eq_zero, ls', ←List.eq_nil_iff_length_eq_zero] at sps_ne
          exact ne' sps_ne
        . exact sub''

  | .etop =>
      match y with
      | [] =>
          rw [wD, succs]
          match z with
          | [] => exists ⊤
                  simp [wDAhd, wDBhd_top]
          | c :: z =>
              exists `◁ `1
              simp
              exact Equiv.trans (wDAhd_cong (wDBhd_top x))
                                (wDAhd_top_cons c z)

      | b :: y =>
          rw [succs]
          match z with
          | [] => exists `◁ `1 `· ⊤
                  simp [wDAhd]
                  exact Equiv.trans (wD_cong (wDBhd_top x))
                                    (wD_top_cons b y)
          | c :: z => exists `◁ `1
                      simp
                      calc wDAhd (c :: z) (wD (b :: y) (wDBhd x ⊤))
                      _ ≡ wDAhd (c :: z) (wD (b :: y) ⊤)             := wDAhd_cong (wD_cong (wDBhd_top x))
                      _ ≡ wDAhd (c :: z) (`◁ `1 `· ⊤)                := wDAhd_cong (wD_top_cons b y)
                      _ ≡ wDAhd (c :: z) (`◁ `1) `· wDAhd (c :: z) ⊤ := wDAhd_mult (`◁ `1) ⊤ (c :: z)
                      _ ≡ `◁ `1 `· `◁ `1                             := .multCong (wDAhd_bhd_1 (c :: z))
                                                                                  (wDAhd_top_cons c z)
                      _ ≡ `◁`1                                       := .sym lbhd_unit_mult_idem'

  | .inter e f =>
      rw [elemUpTo, succs]
      have ⟨e', e'_eq, e'_in⟩ := wDAhd_wD_wDBhd_succs e x y z
      have ⟨f', f'_eq, f'_in⟩ := wDAhd_wD_wDBhd_succs f x y z
      exists e' & f'

      apply And.intro
      . calc wDAhd z (wD y (wDBhd x (e & f)))
        _ ≡ wDAhd z (wD y (wDBhd x e & wDBhd x f)) :=
          wDAhd_cong (wD_cong (wDBhd_inter e f x))
        _ ≡ wDAhd z (wD y (wDBhd x e) & wD y (wDBhd x f)) :=
          wDAhd_cong (wD_inter (wDBhd x e) (wDBhd x f) y)
        _ ≡ wDAhd z (wD y (wDBhd x e)) & wDAhd z (wD y (wDBhd x f)) :=
          wDAhd_inter (wD y (wDBhd x e)) (wD y (wDBhd x f)) z
        _ ≡ e' & f' :=
          .interCong e'_eq f'_eq

      . rw [productWith_mem]
        exists e', f'


  | .sub e f =>
      rw [elemUpTo, succs]
      have ⟨e', e'_eq, e'_in⟩ := wDAhd_wD_wDBhd_succs e x y z
      have ⟨f', f'_eq, f'_in⟩ := wDAhd_wD_wDBhd_succs f x y z
      exists e' `- f'

      apply And.intro
      . calc wDAhd z (wD y (wDBhd x (e `- f)))
        _ ≡ wDAhd z (wD y (wDBhd x e `- wDBhd x f)) :=
          wDAhd_cong (wD_cong (wDBhd_diff e f x))
        _ ≡ wDAhd z (wD y (wDBhd x e) `- wD y (wDBhd x f)) :=
          wDAhd_cong (wD_diff (wDBhd x e) (wDBhd x f) y)
        _ ≡ wDAhd z (wD y (wDBhd x e)) `- wDAhd z (wD y (wDBhd x f)) :=
          wDAhd_diff (wD y (wDBhd x e)) (wD y (wDBhd x f)) z
        _ ≡ e' `- f' :=
          .subCong e'_eq f'_eq

      . rw [productWith_mem]
        exists e', f'

  | .star e =>
      rw [elemUpTo]

      match y with
      | [] =>
          match z with
          | [] =>
              have ⟨e', e'_eq, e'_in⟩ := wDAhd_wD_wDBhd_succs e x [] []
              rw [wD, wDAhd] at *
              exists (e'*)
              apply And.intro
              . apply Equiv.trans
                apply wDBhd_star
                exact .starCong e'_eq
              . rw [succs]
                apply List.mem_append_left
                apply List.mem_append_right
                simp [e'_in]

          | c :: z =>
              exists `◁ `1
              rw [wD]
              apply And.intro
              . calc wDAhd (c :: z) (wDBhd x e*)
                _ ≡ wDAhd (c :: z) (wDBhd x e)* := wDAhd_cong (wDBhd_star e x)
                _ ≡ `◁`1                        := wDAhd_star_cons (wDBhd x e) c z

              . rw [succs]
                apply List.mem_append_left
                apply List.mem_append_left
                simp

      | b :: y =>

          have ih : ∀ (x y z : List α), wDAhd z (wD y (wDBhd x e)) ≡∈ succs e := by
            intro x y z
            exact wDAhd_wD_wDBhd_succs e x y z

          let sps := List.map (λ ws => wDAhd z (starElem (wDBhd x e) ws))
                              (neSplits b y)

          have sps_ne : ¬ sps = [] := by simp [sps]
                                         apply neSplits_nonEmpty

          have sub : sps ≡⊆ mainSummands (succs e) := by
            simp [sps]
            intro sp sp_mem
            simp at sp_mem

            obtain ⟨ws, ws_mem, eq⟩ := sp_mem
            have ⟨ws_ne, w_ne⟩ := neSplits_elems_nonEmpty b y ws ws_mem

            have lem := starElem_summand e x z ws_ne w_ne ih

            rw [eq] at lem
            exact lem

          have ⟨sps', ls', sub', eq'⟩ := subsetUpTo_reprs sub

          have ⟨sps'', ne', sub'', eq''⟩ := exists_sublist_same sub'

          exists toSum sps''
          apply And.intro
          . calc wDAhd z (wD (b :: y) (wDBhd x e*))
            _ ≡ wDAhd z (wD (b :: y) (wDBhd x e)*)
              := wDAhd_cong (wD_cong (wDBhd_star e x))

            _ ≡ wDAhd z (starShape (wDBhd x e) b y)
              := wDAhd_cong (wD_star_cons (wDBhd x e) b y)

            _ ≡ wDAhd z (toSum (List.map (starElem (wDBhd x e)) (neSplits b y)))
              := .refl rfl

            _ ≡ (toSum <| List.map (wDAhd z)
                                   (List.map (starElem (wDBhd x e))
                                             (neSplits b y)))
              := by apply wDAhd_toSum

            _ ≡ (toSum <| List.map (λ ws => wDAhd z (starElem (wDBhd x e) ws))
                                   (neSplits b y))
              := by rw [List.map_map]
                    exact .refl rfl

            _ ≡ toSum sps
              := .refl rfl

            _ ≡ toSum sps'
              := eq'

            _ ≡ toSum sps''
              := toSum_mem_eq eq''

          . rw [succs]
            apply List.mem_append_right
            rw [List.mem_map]
            exists sps''
            simp
            apply neSubs_complete
            . rw [List.eq_nil_iff_length_eq_zero, ls', ←List.eq_nil_iff_length_eq_zero] at sps_ne
              exact ne' sps_ne
            . exact sub''


  | .lookbehind e =>
      match y with
      | [] =>
          match z with
          | [] => rw [wD, wDAhd, succs]
                  have ⟨e', e'_eq, e'_in⟩ := wDAhd_wD_wDBhd_succs e [] x []
                  exists `◁ e'
                  apply And.intro
                  . rw [wDBhd, wDAhd] at e'_eq
                    exact Equiv.trans (wDBhd_bhd e x) (.lbhdCong e'_eq)
                  . simp [e'_in]

          | c :: z =>
              have ⟨e', e'_eq, e'_in⟩ := wDAhd_wD_wDBhd_succs e [] x (c :: z)
              rw [wD] at *
              exists e'
              apply And.intro
              . calc wDAhd (c :: z) (wDBhd x `◁e)
                _ ≡ wDAhd (c :: z) (`◁ (wD x e)) := wDAhd_cong (wDBhd_bhd e x)
                _ ≡ wDAhd (c :: z) (wD x e)      := wDAhd_bhd_cons (wD x e) c z
                _ ≡ e'                           := e'_eq
              . simp [succs, e'_in]

      | b :: y =>
          exists `0
          apply And.intro
          . calc wDAhd z (wD (b :: y) (wDBhd x `◁e))
            _ ≡ wDAhd z (wD (b :: y) (`◁ (wD x e))) := wDAhd_cong (wD_cong (wDBhd_bhd e x))
            _ ≡ wDAhd z `0                          := wDAhd_cong (wD_bhd_cons (wD x e) b y)
            _ ≡ `0                                  := wDAhd_0 z
          . simp [succs]

  | .lookahead e =>
      match y with
      | [] => have ⟨e', e'_eq, e'_in⟩ := wDAhd_wD_wDBhd_succs e x z []
              rw [wD]
              rw [wDAhd] at e'_eq
              exists `▷ e'
              apply And.intro
              . calc wDAhd z (wDBhd x `▷e)
                _ ≡ wDAhd z (`▷ (wDBhd x e)) := wDAhd_cong (wDBhd_ahd e x)
                _ ≡ `▷ (wD z (wDBhd x e))    := wDAhd_ahd (wDBhd x e) z
                _ ≡ `▷ e'                    := .lahdCong e'_eq
              . simp [succs, e'_in]

      | b :: y => exists `0
                  apply And.intro
                  . calc wDAhd z (wD (b :: y) (wDBhd x `▷e))
                    _ ≡ wDAhd z (wD (b :: y) (`▷ (wDBhd x e))) := wDAhd_cong (wD_cong (wDBhd_ahd e x))
                    _ ≡ wDAhd z `0                             := wDAhd_cong (wD_ahd_cons (wDBhd x e) b y)
                    _ ≡ `0                                     := wDAhd_0 z

                  . simp [succs]



#print axioms wDAhd_wD_wDBhd_succs



theorem wxD_succs {α} [DecidableEq α]
                  (e : RE α) (u : List α)
                  : wxD u e ≡∈ List.map toSum (neSubs (succs e)) := by
  let sps := List.map (flip tD e) (trpls u)

  have sps_ne : ¬ sps = [] := by
    simp [sps, trpls_ne]

  have sub : sps ≡⊆ succs e := by
    simp [sps]
    intro sp sp_mem
    simp at sp_mem
    obtain ⟨t, t_mem, sp_eq⟩ := sp_mem
    rw [←sp_eq]
    rw [flip, triple_eta t, tD]
    rw [behind, ahead, mtch]
    exact wDAhd_wD_wDBhd_succs e (behind t) (mtch t) (ahead t)

  have ⟨sps', ls', sub', eq'⟩ := subsetUpTo_reprs sub

  have ⟨sps'', ne', sub'', eq''⟩ := exists_sublist_same sub'

  exists toSum sps''
  apply And.intro
  . calc wxD u e
      _ ≡ toSum sps   := wxD_equiv u e
      _ ≡ toSum sps'  := eq'
      _ ≡ toSum sps'' := toSum_mem_eq eq''

  . simp
    exists sps''
    simp
    apply neSubs_complete
    . apply ne'
      intro eq
      rw [List.eq_nil_iff_length_eq_zero] at eq sps_ne
      rw [ls'] at sps_ne
      contradiction
    . exact sub''

#print axioms wxD_succs
